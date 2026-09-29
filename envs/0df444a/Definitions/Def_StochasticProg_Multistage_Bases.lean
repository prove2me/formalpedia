-- Prove2me | Definitions.Def_StochasticProg_Multistage_Bases
-- name    : StochasticProg_Multistage_Bases
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:08:43.463064+00:00
-- url     : https://prove2.me/theorems/ebe96805-0a3e-419d-b9d8-a53b1f545b1a
-- title:
--   Simplex bases and cut coefficients of the nested L-shaped subproblems
-- statement:
--   The linear-algebraic machinery each node's local LP uses to produce a cut on its parent
--   (Birge & Louveaux Ch. 6, p. 288-289, Eqs. (1.1), (1.6)-(1.11); the same mechanism as the
--   two-stage L-shaped method's Ch. 5, pp. 219-220, applied node by node on the tree).
--
--   `Basis n m` is a basis of a node's own recourse matrix $W^{\mathrm{stage}}$: an injective
--   choice of $m$ of the $n$ columns. For a node $k$, basis $b$ and cost vector $q$,
--   `multiplier inst k b q` is the simplex multiplier $\pi=(W_b^T)^{-1}q_b$ it determines, and
--   `basisValue inst k b xp` is the value $\pi^T(h_k-T_kxp)$ it claims for node $k$'s local LP
--   at parent value $xp$. `IsOptimalAt inst k β xp` says $β$ is a genuine optimality witness for
--   node $k$: no feasible point of $k$'s plain local LP does better, and some feasible point
--   attains `basisValue`. `optCutCoeffs inst β j` is the resulting optimality-cut pair
--   $(E^{t-1}_j,e^{t-1}_j)$ of Eq. (1.1), aggregating a chosen basis for every child of $j$
--   with the conditional-probability weights $p^t_k/p^{t-1}_j$.
--
--   `FeasBasis n m` is a basis of a node's Step-2 feasibility-test LP (1.8)-(1.9) over the
--   extended matrix $[W\mid I\mid -I]$. `feasLPValue inst k xp` is that LP's true optimal
--   value — always well-defined and $0$ exactly when node $k$ is locally feasible at $xp$ (up
--   to the bound constraints, which this test LP does not model). `IsFeasBasisOptimalAt inst k
--   b xp` says $b$ attains it, and `feasCutCoeffs inst k b` is the resulting feasibility-cut
--   pair $(D^{t-1}_{a(k)},d^{t-1}_{a(k)})$ of Eqs. (1.10)-(1.11), added to node $k$'s parent.
--
--   **Formalization Note.** As documented in `MODERATION_NOTES.md`, a node's dual is read off
--   its *original* constraint (1.2) alone, not off (1.2)-(1.4) already extended by whatever
--   cuts have accumulated at that node itself — the book's own finiteness argument (p. 290)
--   additionally bounds the number of such *extended* bases as cuts accumulate, which this
--   mission does not re-derive; see *Formalization scope* in `description.md`. `Matrix.inv` of
--   a singular matrix returns the junk value $0$ in Mathlib; `multiplier`/`feasMultiplier` are
--   only ever used through `IsOptimalAt`/`IsFeasBasisOptimalAt`, which pin the basis to one
--   that actually attains the true LP value, so a junk choice can never satisfy those
--   predicates and never enters a proof.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, pp. 288-290, 219-220, Chapter 6, Section 6.1, Eqs. (1.1), (1.6)-(1.11)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_Multistage_Instance

namespace StochasticProg.Multistage

open scoped Matrix

variable {H n m : ℕ} {T : Tree H}

/-- A basis of node `j`'s own local LP (1.1)-(1.5) at the recourse matrix `W^{stage j}`: an
injective choice of `m` of the `n` columns, exactly as in the two-stage `L`-shaped method
(Birge & Louveaux Ch. 5, p. 220, "one of the finitely many different bases"). The dual it
determines is what feeds a cut on node `j`'s *parent* (`optCutCoeffs`) once `j` has a chosen
basis — the mechanism `Basis` supports here is the same one Chapter 5 uses for the (flat,
single-level) two-stage recourse LP, applied node by node on the tree. As documented in
`MODERATION_NOTES.md`, this mission's `Basis`/`FeasBasis` read node `j`'s dual off its
*original* constraint (1.2) alone, not off the constraint set (1.2)-(1.4) already extended by
whatever cuts have accumulated at `j` itself by the time the cut is generated — the book's own
finiteness argument (p. 290) additionally bounds the number of *extended* bases as cuts
accumulate, which this mission does not re-derive; see the Formalization scope in
`description.md`. -/
def Basis (n m : ℕ) : Type := {b : Fin m → Fin n // Function.Injective b}

noncomputable instance instFintypeBasis (n m : ℕ) : Fintype (Basis n m) := by
  classical exact Subtype.fintype _

noncomputable instance instDecidableEqBasis (n m : ℕ) : DecidableEq (Basis n m) := by
  classical exact Classical.decEq _

noncomputable instance instFintypeBasisFun (T : Tree H) (n m : ℕ) :
    Fintype (T.Node → Basis n m) := by
  classical exact Pi.instFintype

noncomputable instance instDecidableEqBasisFun (T : Tree H) (n m : ℕ) :
    DecidableEq (T.Node → Basis n m) := by
  classical exact Classical.decEq _

variable (inst : Instance H n m T)

/-- The simplex multiplier a basis `b` of node `k`'s recourse matrix `W^{stage k}` determines
for a cost vector `q`: `π = (W_bᵀ)⁻¹ q_b` (p. 219). -/
noncomputable def multiplier (k : T.Node) (b : Basis n m) (q : Fin n → ℝ) : Fin m → ℝ :=
  Matrix.mulVec (((inst.W (T.stage k)).submatrix id b.1)ᵀ)⁻¹ (fun i => q (b.1 i))

/-- The value basis `b` claims for node `k`'s local LP at parent value `xp`:
`πᵀ(h_k - T_k xp)` (the relation underlying Eq. (1.1)/(1.6), p. 289). -/
noncomputable def basisValue (k : T.Node) (b : Basis n m) (xp : Fin n → ℝ) : ℝ :=
  dotProduct (multiplier inst k b (inst.c k)) (inst.h k) -
    dotProduct (multiplier inst k b (inst.c k)) (transitionTerm inst k xp)

/-- `β k` is a valid optimality witness for node `k` at parent value `xp`: it attains the true
optimal value of node `k`'s local LP (1.1)-(1.5) with the currently recorded cuts ignored, in
the sense that no feasible point of the *plain* local LP does better (LP weak duality: this is
what strong duality delivers for an optimal basis). -/
def IsOptimalAt (k : T.Node) (β : Basis n m) (xp : Fin n → ℝ) : Prop :=
  (∀ xk : Fin n → ℝ, LocalFeasible inst k xp xk → basisValue inst k β xp ≤ dotProduct (inst.c k) xk) ∧
    ∃ xk : Fin n → ℝ, LocalFeasible inst k xp xk ∧ dotProduct (inst.c k) xk = basisValue inst k β xp

/-- The optimality-cut coefficients `(E^{t-1}_j, e^{t-1}_j)` of Eq. (1.1), p. 289, aggregating
a chosen basis `β k` for every child `k ∈ D^t(j)` of `j` with the conditional-probability
weights `p^t_k / p^{t-1}_j`. -/
noncomputable def optCutCoeffs (β : T.Node → Basis n m) (j : T.Node) :
    (Fin n → ℝ) × ℝ :=
  (fun i => ∑ k ∈ T.children j,
      (inst.p k / inst.p j) * dotProduct (multiplier inst k (β k) (inst.c k))
        (fun r => (inst.Tmat k) r i),
   ∑ k ∈ T.children j, (inst.p k / inst.p j) * dotProduct (multiplier inst k (β k) (inst.c k)) (inst.h k))

/-- A basis of node `k`'s Step-2 feasibility-test LP (1.8)-(1.9), an injective choice of `m`
columns from the extended matrix `[W | I | -I]`, as in the two-stage method (p. 220). -/
def FeasBasis (n m : ℕ) : Type := {b : Fin m → (Fin n ⊕ Fin m ⊕ Fin m) // Function.Injective b}

noncomputable instance instFintypeFeasBasis (n m : ℕ) : Fintype (FeasBasis n m) := by
  classical exact Subtype.fintype _

noncomputable instance instDecidableEqFeasBasis (n m : ℕ) : DecidableEq (FeasBasis n m) := by
  classical exact Classical.decEq _

/-- The extended constraint matrix `[W | I | -I]` of Eq. (1.9), for node `k`'s own recourse
matrix `W^{stage k}`. -/
def feasMatrix (k : T.Node) : Matrix (Fin m) (Fin n ⊕ Fin m ⊕ Fin m) ℝ :=
  fun i c => match c with
    | Sum.inl r => (inst.W (T.stage k)) i r
    | Sum.inr (Sum.inl r) => if i = r then 1 else 0
    | Sum.inr (Sum.inr r) => if i = r then -1 else 0

/-- The extended objective `min eᵀv⁺ + eᵀv⁻` of Eq. (1.8). -/
def feasCost : (Fin n ⊕ Fin m ⊕ Fin m) → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 1

/-- The simplex multiplier a feasibility basis `b` determines for node `k`: `σ = (([W|I|-I]_b)ᵀ)⁻¹ e_b`. -/
noncomputable def feasMultiplier (k : T.Node) (b : FeasBasis n m) : Fin m → ℝ :=
  Matrix.mulVec (((feasMatrix inst k).submatrix id b.1)ᵀ)⁻¹ (fun i => feasCost (b.1 i))

/-- The optimal value of node `k`'s Step-2 feasibility-test LP (1.8)-(1.9) given parent
value `xp`: always well-defined, nonnegative, and `0` exactly when `k` is locally feasible at
`xp` (up to the bound constraints, which the test LP does not model — see
`MODERATION_NOTES.md`). -/
noncomputable def feasLPValue (k : T.Node) (xp : Fin n → ℝ) : ℝ :=
  sInf {w : ℝ | ∃ y : Fin n → ℝ, ∃ vp vn : Fin m → ℝ,
    (∀ i, 0 ≤ y i) ∧ (∀ i, 0 ≤ vp i) ∧ (∀ i, 0 ≤ vn i) ∧
    Matrix.mulVec (inst.W (T.stage k)) y + vp - vn = inst.h k - transitionTerm inst k xp ∧
    w = (∑ i, vp i) + ∑ i, vn i}

/-- The value feasibility-basis `b` claims for node `k` at parent value `xp`: `σᵀ(h_k -
T_k xp)` (Eq. (1.10)-(1.11), read as a value). -/
noncomputable def feasBasisValue (k : T.Node) (b : FeasBasis n m) (xp : Fin n → ℝ) : ℝ :=
  dotProduct (feasMultiplier inst k b) (inst.h k) -
    dotProduct (feasMultiplier inst k b) (transitionTerm inst k xp)

/-- `b` is a valid Step-2 witness for node `k` at parent value `xp`: `b` attains the true
optimal value of the feasibility-test LP there. -/
def IsFeasBasisOptimalAt (k : T.Node) (b : FeasBasis n m) (xp : Fin n → ℝ) : Prop :=
  feasBasisValue inst k b xp = feasLPValue inst k xp

/-- The feasibility-cut coefficients `(D^{t-1}_{a(k)}, d^{t-1}_{a(k)})` of Eq. (1.10)-(1.11),
for node `k` and witness basis `b`; this cut is added to node `k`'s *parent*, `T.anc k`. -/
noncomputable def feasCutCoeffs (k : T.Node) (b : FeasBasis n m) : (Fin n → ℝ) × ℝ :=
  (fun i => dotProduct (feasMultiplier inst k b) (fun r => (inst.Tmat k) r i),
   dotProduct (feasMultiplier inst k b) (inst.h k))

end StochasticProg.Multistage


