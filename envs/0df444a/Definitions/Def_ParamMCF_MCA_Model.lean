-- Prove2me | Definitions.Def_ParamMCF_MCA_Model
-- name    : ParamMCF_MCA_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:30.374543+00:00
-- url     : https://prove2.me/theorems/7c5834c9-4bfa-4f76-aca3-4e35837acf91
-- title:
--   §2, §3, §5.2–5.2.1, pp. 4–5, 15–17 — flow costs, approximation, and splines
-- statement:
--   For a finite directed network, the **net inflow** at a vertex is its incoming flow minus its outgoing flow. A flow is feasible for demand $d$ when its net inflow equals $d$ at every vertex; the directed case also requires nonnegative edge flows. A marginal cost $f_e$ gives the edge cost $F_e(x)=\int_0^x f_e(s)\,ds$, and total cost is the sum over edges. The optimal cost $C(d)$ is the infimum of total costs of feasible flows.
--
--   A marginal cost is strictly increasing and differentiable, is nonpositive on negative arguments, and is nonnegative on positive arguments. For balanced demands $b^0$ and $b$, the maximum total inflow is
--
--   $$x^{\max}=\max_{0\le\lambda\le\lambda^{\max}}\frac12\sum_{v\in V}|b_v^0+\lambda b_v|.$$
--
--   A feasible flow function $\widetilde x$ is $(\alpha,\beta)$ approximate if its cost under the *original* edge costs satisfies $\widetilde C(\lambda)\le\alpha C(\lambda)+\beta$ for every $\lambda\in[0,\lambda^{\max}]$. The linear spline $s_f$ joins values of $f$ at successive mesh points by straight chords, with the end chords continued outside the mesh interval.
--
--   These definitions fix the common model for the approximation theorem and its supporting results.
--
--   **Formalization Note** The edge cost is based at zero because the paper's integral from $l_e=-\infty$ is not finite for undirected flows. Only its directed ($x\ge0$) and undirected (free sign) cases are represented. An infimum represents the optimal cost; the paper's standing assumptions ensure that the feasible set is nonempty and its costs are bounded below.
-- source:
--   Joachims, Klimm & Warode, Approximate Parametric Computation of Minimum-Cost Flows with Convex Costs, arXiv:2203.13146v1, pp. 4–5, 15–17, Assumption 1, (5), (8), (14), §5.2.1

import Mathlib
import Definitions.Def_ParamMCF_MCA_Network

namespace ParamMCF.MCA

def netInflow {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (G : Network V E) (x : E → ℝ) (v : V) : ℝ :=
  (∑ e ∈ Finset.univ.filter (fun e => G.tgt e = v), x e) -
  (∑ e ∈ Finset.univ.filter (fun e => G.src e = v), x e)

def demand {V : Type*} (b0 b : V → ℝ) (lam : ℝ) : V → ℝ :=
  fun v => b0 v + lam * b v

def Feasible {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (G : Network V E) (directed : Bool) (d : V → ℝ) (x : E → ℝ) : Prop :=
  (∀ v, netInflow G x v = d v) ∧ (directed = true → ∀ e, 0 ≤ x e)

noncomputable def edgeCost (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..x, g s

noncomputable def cost {E : Type*} [Fintype E]
    (f : E → ℝ → ℝ) (x : E → ℝ) : ℝ :=
  ∑ e, edgeCost (f e) (x e)

def IsMinCostFlow {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (G : Network V E) (directed : Bool) (f : E → ℝ → ℝ)
    (d : V → ℝ) (x : E → ℝ) : Prop :=
  Feasible G directed d x ∧
  ∀ y, Feasible G directed d y → cost f x ≤ cost f y

noncomputable def optCost {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (G : Network V E) (directed : Bool) (f : E → ℝ → ℝ) (d : V → ℝ) : ℝ :=
  sInf (cost f '' {x | Feasible G directed d x})

def IsMarginalCost (g : ℝ → ℝ) : Prop :=
  StrictMono g ∧ Differentiable ℝ g ∧
  (∀ s, 0 < s → 0 ≤ g s) ∧ (∀ s, s < 0 → g s ≤ 0)

/-- The marginal-cost class used for the spline in Lemma 4. -/
def IsContinuousMarginalCost (g : ℝ → ℝ) : Prop :=
  Continuous g ∧ StrictMono g ∧
  (∀ s, 0 < s → 0 ≤ g s) ∧ (∀ s, s < 0 → g s ≤ 0)

noncomputable def xmax {V : Type*} [Fintype V]
    (b0 b : V → ℝ) (lamMax : ℝ) : ℝ :=
  sSup ((fun lam => (1 / 2 : ℝ) * ∑ v, |b0 v + lam * b v|) '' Set.Icc 0 lamMax)

def IsApproxMinCostFlowFun {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (G : Network V E) (directed : Bool) (f : E → ℝ → ℝ)
    (b0 b : V → ℝ) (lamMax alpha beta : ℝ) (xt : ℝ → E → ℝ) : Prop :=
  ∀ lam ∈ Set.Icc 0 lamMax,
    Feasible G directed (demand b0 b lam) (xt lam) ∧
    cost f (xt lam) ≤ alpha * optCost G directed f (demand b0 b lam) + beta

noncomputable def splinePiece (K : ℕ) (xs : Fin (K + 1) → ℝ)
    (g : ℝ → ℝ) (i : Fin K) (x : ℝ) : ℝ :=
  g (xs i.castSucc) +
    (x - xs i.castSucc) / (xs i.succ - xs i.castSucc) *
      (g (xs i.succ) - g (xs i.castSucc))

/-- Chord interpolation on the mesh; the first and last chords extend linearly outside it. -/
noncomputable def linSpline (K : ℕ) (xs : Fin (K + 1) → ℝ)
    (g : ℝ → ℝ) (x : ℝ) : ℝ := by
  classical
  by_cases hK : 0 < K
  · let candidate : Finset (Fin K) := Finset.univ.filter (fun i => x ≤ xs i.succ)
    by_cases hc : candidate.Nonempty
    · exact splinePiece K xs g (candidate.min' hc) x
    · exact splinePiece K xs g ⟨K - 1, Nat.sub_lt hK (by decide)⟩ x
  · exact g (xs 0)

end ParamMCF.MCA


