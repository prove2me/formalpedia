-- Prove2me | Definitions.Def_LogBarrierIPM_Iterations_Supplement_TropicalLP
-- name    : LogBarrierIPM_Iterations_Supplement_TropicalLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:10:03.074575+00:00
-- url     : https://prove2.me/theorems/bfb39f86-3887-4781-8019-9885206e077d
-- title:
--   The general Puiseux dual pair and its tropical central path
-- statement:
--   For $A\in K^{m\times n}$, $b\in K^m$, $c\in K^n$, let $\mathcal P=\{(x,w)\ge0:Ax+w=b\}$ and $\mathcal Q=\{(s,y)\ge0:s-A^\top y=c\}$, with $\mathcal F=\mathcal P\times\mathcal Q$. Strict feasibility is Assumption 13. The central-point predicate is system (17) for an arbitrary positive series $\boldsymbol\mu$, using the published real central-path system. Optimal pairs minimize $c^\top x$ and $b^\top y$, equivalently maximize $-b^\top y$ on the dual side, correcting the printed sign.
--   With $N=n+m$, the coordinate order is $(x,w)\mid(s,y)$. Define
--   $$\operatorname{tgap}(z)=\max_{k\in[N]}(z_k+z_{N+k}),\qquad F^\lambda=\{z\in\operatorname{val}(\mathcal F):\operatorname{tgap}(z)\le\lambda\}.$$
--   The tropical central path $C^{\rm trop}(\lambda)$ is computed as the finite greatest point of $F^\lambda$. Its zero default on invalid data is excluded by the greatest-element assertion in Theorem 15 under Assumption 13. The module also defines finite piecewise affine curves and the paired derivative $(e^K,e^{[N]\setminus K})$, for use in Proposition 16.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 16, def-tropical-central-path

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_PuiseuxGeometry
import Definitions.Def_LogBarrierIPM_Iterations_SlackLP

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

/-- Primal and dual feasible points, over K. -/
def kPrimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux) (b : Fin m → Puiseux) :
    Set ((Fin n → Puiseux) × (Fin m → Puiseux)) :=
  {z | ∀ᶠ t in atTop, evalMatrix A t *ᵥ evalFun z.1 t + evalFun z.2 t = evalFun b t ∧
    (∀ j, 0 ≤ (z.1 j).eval t) ∧ ∀ i, 0 ≤ (z.2 i).eval t}

def kDual {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux) (c : Fin n → Puiseux) :
    Set ((Fin n → Puiseux) × (Fin m → Puiseux)) :=
  {z | ∀ᶠ t in atTop, evalFun z.1 t - (evalMatrix A t)ᵀ *ᵥ evalFun z.2 t = evalFun c t ∧
    (∀ j, 0 ≤ (z.1 j).eval t) ∧ ∀ i, 0 ≤ (z.2 i).eval t}

def kFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux) : Set (PuiseuxSlackPoint n m) :=
  {z | (z.1, z.2.1) ∈ kPrimal A b ∧ (z.2.2.1, z.2.2.2) ∈ kDual A c}

/-- Assumption 13, with positivity in every coordinate. -/
def StrictlyFeasibleK {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux) : Prop :=
  ∃ z : PuiseuxSlackPoint n m, ∀ᶠ t in atTop,
    evalPoint z t ∈ strictlyFeasible (evalMatrix A t) (evalFun b t) (evalFun c t)

/-- System (17) for EVERY positive Puiseux parameter, rather than only monomials. -/
def IsCentralK {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux)
    (μ : Puiseux) (z : PuiseuxSlackPoint n m) : Prop :=
  ∀ᶠ t in atTop, IsSlackCentralPathPoint (evalMatrix A t) (evalFun b t)
    (evalFun c t) (μ.eval t) (evalPoint z t)

/-- Corrected dual objective: minimize bᵀy, equivalently maximize -bᵀy. -/
def OptimalPairK {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux) (z : PuiseuxSlackPoint n m) : Prop :=
  z ∈ kFeasible A b c ∧
  (∀ u ∈ kPrimal A b, ∀ᶠ t in atTop,
    evalFun c t ⬝ᵥ evalFun z.1 t ≤ evalFun c t ⬝ᵥ evalFun u.1 t) ∧
  (∀ v ∈ kDual A c, ∀ᶠ t in atTop,
    evalFun b t ⬝ᵥ evalFun z.2.2.2 t ≤ evalFun b t ⬝ᵥ evalFun v.2 t)

/-- The common 0-based layout is x,w | s,y. -/
def flattenReal {n m : ℕ} (z : PDPoint n m) : Fin ((n + m) + (n + m)) → ℝ :=
  Fin.append (Fin.append z.1 z.2.1) (Fin.append z.2.2.1 z.2.2.2)

noncomputable def halfVal {n m : ℕ} (z : (Fin n → Puiseux) × (Fin m → Puiseux)) :
    Fin (n + m) → WithBot ℝ := Fin.append (fun j => (z.1 j).val) (fun i => (z.2 i).val)

noncomputable def tropicalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux) :
    Set (Fin ((n + m) + (n + m)) → WithBot ℝ) := valPoint '' kFeasible A b c

/-- The tropical scalar product is max of pairwise sums; max empty = bottom. -/
def tropicalDot {N : ℕ} (u v : Fin N → WithBot ℝ) : WithBot ℝ :=
  Finset.univ.sup (fun i => u i + v i)

def tropicalGap {N : ℕ} (z : Fin (N + N) → WithBot ℝ) : WithBot ℝ :=
  tropicalDot (fun i => z (Fin.castAdd N i)) (fun i => z (Fin.natAdd N i))

noncomputable def tropicalSublevel {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux) (lam : WithBot ℝ) :
    Set (Fin ((n + m) + (n + m)) → WithBot ℝ) :=
  {z ∈ tropicalFeasible A b c | tropicalGap z ≤ lam}

noncomputable def primalSublevel {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (zstar : PuiseuxSlackPoint n m) (lam : WithBot ℝ) :
    Set (Fin (n + m) → WithBot ℝ) :=
  {u ∈ halfVal '' kPrimal A b | tropicalDot u (halfVal (zstar.2.2.1, zstar.2.2.2)) ≤ lam}

noncomputable def dualSublevel {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (c : Fin n → Puiseux) (zstar : PuiseuxSlackPoint n m) (lam : WithBot ℝ) :
    Set (Fin (n + m) → WithBot ℝ) :=
  {v ∈ halfVal '' kDual A c | tropicalDot (halfVal (zstar.1, zstar.2.1)) v ≤ lam}

def tropicalizeReal {d : ℕ} (x : Fin d → ℝ) : Fin d → WithBot ℝ := fun i => (x i : WithBot ℝ)

/-- The path is computed from F^lam by its greatest-element property. On invalid data with no
finite greatest element the default is zero; theorems assert correctness under Assumption 13. -/
noncomputable def tropicalPath {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux) (lam : ℝ) :
    Fin ((n + m) + (n + m)) → ℝ := by
  classical
  exact if h : ∃ x : Fin ((n + m) + (n + m)) → ℝ,
      IsGreatest (tropicalSublevel A b c (lam : WithBot ℝ)) (tropicalizeReal x)
    then h.choose else 0

/-- Finitely many affine pieces on the whole real line (including both unbounded tails). -/
def FinitePiecewiseAffine {d : ℕ} (C : ℝ → Fin d → ℝ) : Prop :=
  Continuous C ∧ ∃ B : Finset ℝ, ∀ a b : ℝ, a ≤ b →
    (∀ v ∈ B, v ∉ Set.Ioo a b) → ∃ u v : Fin d → ℝ,
      ∀ lam ∈ Set.Icc a b, C lam = u + lam • v

/-- The paired derivatives (e^K,e^[N]\K) in the common layout. -/
noncomputable def pairedDirection {N : ℕ} (K : Set (Fin N)) : Fin (N + N) → ℝ := by
  classical
  exact Fin.append (fun i => if i ∈ K then 1 else 0) (fun i => if i ∈ K then 0 else 1)

end LogBarrierIPM.Iterations.Supplement


