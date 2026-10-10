-- Prove2me | Definitions.Def_SDDiP_Conv_SND
-- name    : SDDiP_Conv_SND
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-10T03:46:35.718063+00:00
-- url     : https://prove2.me/theorems/bcba36a0-b7c8-409f-a8e1-c1240ad08d90
-- title:
--   The SND algorithm: cut model (3.2), backward step, forward tree solution (3.6), valid/tight/finite cuts (Definition 2), (A3), sampling with replacement
-- statement:
--   The stochastic nested decomposition (SND) algorithm (Algorithm 1) maintains at every node $n$ an approximate expected cost-to-go function
--   $$\psi^i_n(x) = \min\Big\{\theta : \theta\ge L_n,\ \ \theta \ge \sum_{m\in\mathcal C(n)} q_{nm}\big(v^\ell_m + (\pi^\ell_m)^\top x\big)\ \ \forall \ell = 1,\dots,i-1\Big\} \tag{3.2}$$
--   built from a lower bound $L_n$ and the cuts $(v^\ell_m, \pi^\ell_m)\in\mathbb R\times\mathbb R^d$ added so far; at the scenarios $\psi^i_n\equiv 0$. Initially no cut is present, so $\psi^1_n = L_n$.
--
--   Iteration $i$ consists of three steps.
--   1. **Sampling.** $M$ scenarios are drawn with replacement according to $\{p_n : n\in S_T\}$; $\Omega^i$ is the set of nodes on their root-to-scenario paths.
--   2. **Forward step.** The nodal problems $P^i_n(x^i_{a(n)}, \psi^i_n)$ are solved from the root down, giving the forward tree solution (3.6): $(x^i_1, y^i_1)$ solves the root problem with parent state $\bar x_0$, and $(x^i_n, y^i_n)$ solves the problem of $n$ with parent state $x^i_{a(n)}$. A **solver** is a map from (node, parent state, cost-to-go function) to a pair $(x,y)$; that it is a function is assumption (A3), and it is required to return an optimal solution of every feasible nodal problem (optimal solutions need not be unique).
--   3. **Backward step.** Every sampled node $n\in\Omega^i$ before the last stage receives the aggregated cut $\sum_{m\in\mathcal C(n)} q_{nm}(v^i_m + (\pi^i_m)^\top x)$ built from one cut $(v^i_m,\pi^i_m)$ per child; all other nodes keep their approximation.
--
--   Following Definition 2, the cuts of a run are
--   1. **valid** if $Q_m(x) \ge v^i_m + (\pi^i_m)^\top x$ for every $x\in\{0,1\}^d$ and every generated cut (3.4);
--   2. **tight** if every generated cut coincides at the forward state with the value of the *updated* nodal problem: $\underline Q^i_m(x^i_n, \psi^{i+1}_m) = v^i_m + (\pi^i_m)^\top x^i_n$ for $m\in\mathcal C(n)$ (3.5);
--   3. **finite** if all cuts generated during the run lie in one finite set.
--
--   The sampling with replacement is modelled on a probability space: the draws of all iterations are mutually independent random scenarios, each with law $\{p_n : n\in S_T\}$.
--
--   **Formalization Note** Iterations are indexed from $0$ in Lean (Lean iteration $i$ is the paper's iteration $i+1$). The run is infinite: the stopping criterion, the bounds LB and UB, and line 29 of Algorithm 1 play no role. Line 20 of Algorithm 1 writes $P^i_m(x^i_{a(n)},\psi^{i+1}_m)$, a misprint for $P^i_m(x^i_n,\psi^{i+1}_m)$; the Lean uses $x^i_n$. Definition 2(iii) speaks of finitely many cuts "in each iteration"; the proof of Theorem 2 uses one finite set for the whole run ("finitely many possible realizations … for all $i\ge 1$", p. 474), which is the reading formalized. The cut generator is an arbitrary function of the iteration and the child; the theorems constrain it only through validity, tightness and finiteness.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), §3.1 pp. 469–471 (sampling, Algorithm 1, (3.1), (3.2)); §3.3 p. 473 (Definition 2, (3.4), (3.5)); §3.4 p. 474 ((A3), (3.6))

import Mathlib
import Definitions.Def_SDDiP_Conv_Model

namespace SDDiP.Conv

open StochasticProg.Multistage MeasureTheory ProbabilityTheory

/-- A cut coefficient pair `(v, π) ∈ ℝ × ℝ^d`; it represents the affine function `x ↦ v + π^⊤ x`. -/
abbrev Cut (d : ℕ) := ℝ × (Fin d → ℝ)

/-- The value `v + π^⊤ x` of the cut `(v, π)` at a binary point `x`. -/
noncomputable def Cut.eval {d : ℕ} (κ : Cut d) (x : Fin d → Bool) : ℝ :=
  κ.1 + ∑ j, κ.2 j * toReal x j

/-- The value `v + π^⊤ x` of the cut `(v, π)` at a real point `x`. -/
noncomputable def Cut.evalReal {d : ℕ} (κ : Cut d) (x : Fin d → ℝ) : ℝ :=
  κ.1 + ∑ j, κ.2 j * x j

namespace Model

variable {H d ℓ : ℕ} (D : Model H d ℓ)

/-- The aggregated cut (3.2b) at node `n` built from one cut `(v_m, π_m)` per child `m ∈ C(n)`
(the family `κ` assigns a cut to every node; only the children of `n` are used):
`x ↦ Σ_{m ∈ C(n)} q_{nm} (v_m + π_m^⊤ x)`. -/
noncomputable def agg (n : D.T.Node) (κ : D.T.Node → Cut d) (x : Fin d → Bool) : ℝ :=
  ∑ m ∈ D.T.children n, D.q n m * (κ m).eval x

/-- The approximate expected cost-to-go function (3.2) of node `n` given the lower bound `L_n` and the
list of cut families added to `n` so far:
`ψ_n(x) = min { θ : θ ≥ L_n, θ ≥ Σ_{m ∈ C(n)} q_{nm}(v^ℓ_m + (π^ℓ_m)^⊤ x) for every listed ℓ }`,
i.e. the maximum of `L_n` and the aggregated cuts. At a leaf `ψ_n ≡ 0` ("the last stage problem does
not have a cost-to-go function, therefore ψ^i_n ≡ 0 for all i", p. 471). -/
noncomputable def psi (L : D.T.Node → ℝ) (cs : List (D.T.Node → Cut d)) (n : D.T.Node)
    (x : Fin d → Bool) : ℝ :=
  if D.IsLeaf n then 0 else cs.foldr (fun κ acc => max (D.agg n κ x) acc) (L n)

/-- Node `n` lies on the root-to-leaf path `P(ℓ)` of the scenario `ℓ`: it is `ℓ` or one of its
ancestors. -/
def OnPath (ℓ' : D.Leaf) (n : D.T.Node) : Prop :=
  ∃ j ≤ (D.T.stage ℓ'.1).val, (D.T.anc)^[j] ℓ'.1 = n

/-- Node `n` belongs to `Ω^i`, the union of the sampled scenario paths `ω^i_1, …, ω^i_M` of an
iteration whose sampled scenarios are `s : Fin M → Leaf` (sampling step, p. 469). -/
def Sampled {M : ℕ} (s : Fin M → D.Leaf) (n : D.T.Node) : Prop :=
  ∃ k, D.OnPath (s k) n

/-- The cut lists of the run of Algorithm 1 (SND, p. 470). Iteration `i` (Lean index from `0`; it is the
paper's iteration `i + 1`) samples the scenarios `s i`; in its backward step every sampled node `n ∈ Ω^i`
that is not in the last stage receives the aggregated cut (3.2b) built from the cuts `κ i m`,
`m ∈ C(n)` (lines 16–22); every other node keeps its list (line 24). Initially no node has a cut, so
`ψ^1_n = L_n` by (3.2). -/
noncomputable def cutLists {M : ℕ} (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) :
    ℕ → D.T.Node → List (D.T.Node → Cut d)
  | 0 => fun _ => []
  | i + 1 => fun n => by
      classical
      exact if D.Sampled (s i) n ∧ ¬ D.IsLeaf n then cutLists s κ i n ++ [κ i]
        else cutLists s κ i n

/-- The approximate expected cost-to-go functions `ψ^i_n` at the beginning of iteration `i` of the run
(Lean index `i`, paper index `i + 1`). -/
noncomputable def approx (L : D.T.Node → ℝ) {M : ℕ} (s : ℕ → Fin M → D.Leaf)
    (κ : ℕ → D.T.Node → Cut d) (i : ℕ) (n : D.T.Node) : (Fin d → Bool) → ℝ :=
  D.psi L (D.cutLists s κ i n) n

/-- A nodal solver: given a node `n`, a parent state `xa` and a cost-to-go function `ψ` on `{0,1}^d`, it
returns a pair `(x, y)`. Being a function of `(n, xa, ψ)` is assumption (A3) (p. 474): the same nodal
problem is always solved to the same solution. -/
abbrev Solver := D.T.Node → (Fin d → ℝ) → ((Fin d → Bool) → ℝ) → (Fin d → Bool) × (Fin ℓ → ℝ)

/-- The solver returns an optimal solution of every feasible nodal problem `P_n(xa, ψ)` of (3.1)
(uniqueness of optimal solutions is not assumed). -/
def IsOptimalSolver (sol : D.Solver) : Prop :=
  ∀ n xa ψ, (D.feasibleSet n xa).Nonempty → D.IsNodalOptimal n xa ψ (sol n xa ψ)

/-- The forward tree solution (3.6) (p. 474) defined by the cost-to-go approximations `Ψ`: at the root
`(x_1, y_1) = sol(1, x̄_0, Ψ_1)`, and at every other node `(x_n, y_n) = sol(n, x_{a(n)}, Ψ_n)`.
It is computed at every node of the tree, not only along the sampled paths. -/
noncomputable def fwdOf (sol : D.Solver) (Ψ : D.T.Node → (Fin d → Bool) → ℝ) (n : D.T.Node) :
    (Fin d → Bool) × (Fin ℓ → ℝ) :=
  sol n (if _h : n = D.T.root then D.x0 else toReal (fwdOf sol Ψ (D.T.anc n)).1) (Ψ n)
termination_by (D.T.stage n).val
decreasing_by
  have h1 : (D.T.stage n).val ≠ 0 := fun h0 => _h (D.T.root_unique n h0)
  have := D.T.anc_stage n h1
  omega

/-- The forward tree solution `{x^i_n, y^i_n}_{n ∈ T}` of iteration `i` of the run, (3.6). -/
noncomputable def forwardSol (L : D.T.Node → ℝ) (sol : D.Solver) {M : ℕ} (s : ℕ → Fin M → D.Leaf)
    (κ : ℕ → D.T.Node → Cut d) (i : ℕ) : D.TreeSol :=
  D.fwdOf sol (D.approx L s κ i)

/-- Definition 2 (i), valid cuts (3.4) (p. 473): every cut `(v^i_m, π^i_m)` generated in a backward step,
i.e. for a child `m ∈ C(n)` of a sampled node `n ∈ Ω^i`, satisfies
`Q_m(x) ≥ v^i_m + (π^i_m)^⊤ x` for every `x ∈ {0,1}^d`. -/
def ValidCuts {M : ℕ} (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) : Prop :=
  ∀ i n m, D.Sampled (s i) n → m ∈ D.T.children n → ∀ x, (κ i m).eval x ≤ D.Q m x

/-- Definition 2 (ii), tight cuts (3.5) (p. 473): every generated cut `(v^i_m, π^i_m)` coincides at the
forward-step state `x^i_n = x^i_{a(m)}` with the optimal value `Q̲^i_m(x^i_n, ψ^{i+1}_m)` of the nodal
problem of `m` with the *updated* approximation `ψ^{i+1}_m`. -/
def TightCuts (L : D.T.Node → ℝ) (sol : D.Solver) {M : ℕ} (s : ℕ → Fin M → D.Leaf)
    (κ : ℕ → D.T.Node → Cut d) : Prop :=
  ∀ i n m, D.Sampled (s i) n → m ∈ D.T.children n →
    D.nodalValue m (toReal (D.forwardSol L sol s κ i n).1) (D.approx L s κ (i + 1) m) =
      (κ i m).eval (D.forwardSol L sol s κ i n).1

/-- Definition 2 (iii), finite cuts, in the form the proof of Theorem 2 uses it (p. 474: "there are
finitely many possible realizations … for all i ≥ 1"): all cuts generated in the backward steps of the
run, over all iterations, lie in one finite set. -/
def FiniteCuts {M : ℕ} (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) : Prop :=
  ∃ C : Finset (Cut d), ∀ i n m, D.Sampled (s i) n → m ∈ D.T.children n → κ i m ∈ C

/-- The scenarios carry the discrete σ-algebra. -/
instance : MeasurableSpace D.Leaf := ⊤

/-- The sampling step done with replacement (p. 469): on a probability space `(Ω, P)`, iteration `i`
samples `M` scenarios `S i ω k`, `k < M`; all the draws `S i · k` (over all iterations `i` and all `k`)
are mutually independent random variables, and each is distributed according to `{p_n : n ∈ S_T}`. -/
def IsSampling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {M : ℕ}
    (S : ℕ → Ω → Fin M → D.Leaf) : Prop :=
  (∀ i k, Measurable (fun ω => S i ω k)) ∧
    iIndepFun (fun (ik : ℕ × Fin M) (ω : Ω) => S ik.1 ω ik.2) P ∧
    ∀ i k (n : D.Leaf), P {ω | S i ω k = n} = ENNReal.ofReal (D.p n.1)

end Model

end SDDiP.Conv


