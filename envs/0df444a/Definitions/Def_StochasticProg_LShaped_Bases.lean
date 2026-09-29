-- Prove2me | Definitions.Def_StochasticProg_LShaped_Bases
-- name    : StochasticProg_LShaped_Bases
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:04:57.444771+00:00
-- url     : https://prove2.me/theorems/cfa738ad-b5be-4dac-8e1f-f973f559cf69
-- title:
--   Simplex bases, multipliers and cut coefficients of the L-shaped subproblems
-- statement:
--   This bundle formalizes the linear-algebraic machinery the L-shaped method's Steps 2 and 3
--   build cuts from (Birge & Louveaux §5.1, pp. 183-184, 191, 219-220).
--
--   `posW inst t` says a vector $t\in\mathbb R^{m_2}$ is a nonnegative combination of the columns
--   of the fixed recourse matrix $W$ (`pos W`, p. 109 notation, reused in Chapter 5).
--
--   `Basis n2 m2` is a **basis of the second-stage subproblem** (1.5),
--   $\min\{q^Ty \mid Wy=h-Tx,\ y\ge0\}$: an injective choice of $m_2$ of the $n_2$ columns of $W$
--   (p. 220, "one of the finitely many different bases of (1.5)"). Because $\mathrm{Fin}\,m_2\to
--   \mathrm{Fin}\,n_2$ is finite, so is the set of injective choices — the structural fact the
--   finite-convergence proof rests on.
--
--   For a basis $b$ and second-stage cost vector $q$, `multiplier inst b q` is the **simplex
--   multiplier** $\pi = (W_b^T)^{-1}q_b$ that basis determines (p. 219, "$\pi^\nu_k$ the simplex
--   multipliers"), and `basisValue inst k b x` is the value $\pi^T(h_k-T_kx)$ that basis claims
--   at $x$ for scenario $k$ (p. 219, before Eq. (1.4)). `IsOptimalAt inst x β` says a per-scenario
--   family of bases $\beta$ is a genuine Step-3 witness: each `basisValue` actually equals the
--   true recourse value $Q(x,\xi_k)$ there (the LP-duality fact invoked on p. 219). `optCutCoeffs
--   inst β` is the resulting **optimality-cut** pair $(E,e)$ of Eqs. (1.6)-(1.7).
--
--   `FeasBasis n2 m2` is a basis of the **feasibility-test LP** (1.8)-(1.9),
--   $\min\{e^Tv^++e^Tv^- \mid Wy+Iv^+-Iv^-=h_k-T_kx,\ y,v^+,v^-\ge0\}$: an injective choice of
--   $m_2$ columns of the extended matrix $[W\mid I\mid -I]$ (`feasMatrix`, `feasCost`).
--   `feasMultiplier inst b` is the associated simplex multiplier $\sigma=([W|I|-I]_b^T)^{-1}e_b$
--   (p. 220, "$\sigma^\nu$"). `feasLPValue inst k x` is the LP's true optimal value — always
--   well-defined (taking $y=0$, $v^\pm$ absorbing $h_k-T_kx$, gives a feasible point) and $0$
--   exactly when scenario $k$ is second-stage feasible at $x$. `IsFeasBasisOptimalAt inst k b x`
--   says $b$ actually attains it, and `feasCutCoeffs inst k b` is the resulting **feasibility-cut**
--   pair $(D,d)$ of Eqs. (1.10)-(1.11).
--
--   **Formalization Note** `Matrix.inv` of a singular matrix returns the junk value $0$ in
--   Mathlib; `multiplier`/`feasMultiplier` are only ever used through `IsOptimalAt`/
--   `IsFeasBasisOptimalAt`, which pin the basis to one that actually attains the true LP value, so
--   a junk (non-basic) choice can never satisfy those predicates and never enters a proof.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, pp. 183-184, 191, 219-220, Chapter 5, Section 5.1 (Eqs. 1.5-1.11)

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance

namespace StochasticProg.LShaped

open StochasticProg.Recourse
open scoped Matrix

variable {n1 n2 m1 m2 K : ℕ}

/-- `t ∈ pos W`: `t` is a nonnegative combination of the columns of the fixed recourse
matrix `W` (Birge & Louveaux, Ch. 3, p. 109 notation, used again in Ch. 5 Theorem 1). -/
def posW (inst : Instance n1 n2 m1 m2 K) (t : Fin m2 → ℝ) : Prop :=
  ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧ Matrix.mulVec inst.W y = t

/-- A basis of the second-stage subproblem (1.5), `min qᵀy s.t. Wy = h - Tx, y ≥ 0`: an
injective choice of `m2` of the `n2` columns of `W` (p. 220, "one of the finitely many
different bases of (1.5)"). `Fin m2 → Fin n2` is finite, so the injective ones are too —
this is the structural fact the finite-convergence proof rests on. -/
def Basis (n2 m2 : ℕ) : Type := {b : Fin m2 → Fin n2 // Function.Injective b}

noncomputable instance instFintypeBasis (n2 m2 : ℕ) : Fintype (Basis n2 m2) := by
  classical exact Subtype.fintype _

noncomputable instance instDecidableEqBasis (n2 m2 : ℕ) : DecidableEq (Basis n2 m2) := by
  classical exact Classical.decEq _

/-- The simplex multiplier a basis `b` of `W` determines for a second-stage cost vector
`q` : the standard simplex-tableau dual price `π = (W_bᵀ)⁻¹ q_b` of the basic solution `b`
(p. 219, "`πᵏν` the simplex multipliers"). Singular `W_b` (a non-basis choice) is sent to
the junk value `0` by `Matrix.inv`, never invoked once `b` is required to be optimal via
`IsOptimalAt` below. -/
noncomputable def multiplier (inst : Instance n1 n2 m1 m2 K) (b : Basis n2 m2)
    (q : Fin n2 → ℝ) : Fin m2 → ℝ :=
  Matrix.mulVec ((inst.W.submatrix id b.1)ᵀ)⁻¹ (fun j => q (b.1 j))

/-- The value basis `b` (for scenario `k`) claims at `x`: `πᵀ(h_k - T_k x)` (the two
displayed relations on p. 219, before Eq. (1.4)). -/
noncomputable def basisValue (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : Basis n2 m2)
    (x : Fin n1 → ℝ) : ℝ :=
  dotProduct (multiplier inst b (inst.q k)) (inst.h k) -
    dotProduct (multiplier inst b (inst.q k)) (Matrix.mulVec (inst.T k) x)

noncomputable instance instFintypeBasisFun : Fintype (Fin K → Basis n2 m2) := by
  classical exact Pi.instFintype

noncomputable instance instDecidableEqBasisFun : DecidableEq (Fin K → Basis n2 m2) := by
  classical exact Classical.decEq _

/-- `β` (one basis per scenario) is a valid Step-3 witness at `x`: for every scenario `k`,
`β k` actually attains the true second-stage optimal value `Q(x, ξ_k)` — the content of LP
duality invoked on p. 219 ("`Q(xν, ξk) = (πνk)ᵀ(hk − Tkxν)`"). -/
def IsOptimalAt (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) (β : Fin K → Basis n2 m2) :
    Prop :=
  ∀ k, (basisValue inst k (β k) x : EReal) = QVal inst x k

/-- The optimality-cut coefficients `(E, e)` of Eq. (1.6)-(1.7), built from a Step-3 witness
`β`, one basis per scenario. -/
noncomputable def optCutCoeffs (inst : Instance n1 n2 m1 m2 K) (β : Fin K → Basis n2 m2) :
    (Fin n1 → ℝ) × ℝ :=
  (fun i => ∑ k, inst.p k * dotProduct (multiplier inst (β k) (inst.q k)) (fun r => inst.T k r i),
   ∑ k, inst.p k * dotProduct (multiplier inst (β k) (inst.q k)) (inst.h k))

/-- A basis of the Step-2 feasibility-test LP (1.8)-(1.9): an injective choice of `m2`
columns of the extended matrix `[W | I | -I]` (its columns indexed by `y`-columns,
`v⁺`-columns and `v⁻`-columns respectively). -/
def FeasBasis (n2 m2 : ℕ) : Type :=
  {b : Fin m2 → (Fin n2 ⊕ Fin m2 ⊕ Fin m2) // Function.Injective b}

noncomputable instance instFintypeFeasBasis (n2 m2 : ℕ) : Fintype (FeasBasis n2 m2) := by
  classical exact Subtype.fintype _

noncomputable instance instDecidableEqFeasBasis (n2 m2 : ℕ) : DecidableEq (FeasBasis n2 m2) := by
  classical exact Classical.decEq _

/-- The extended constraint matrix `[W | I | -I]` of Eq. (1.9). -/
def feasMatrix (inst : Instance n1 n2 m1 m2 K) :
    Matrix (Fin m2) (Fin n2 ⊕ Fin m2 ⊕ Fin m2) ℝ :=
  fun i c => match c with
    | Sum.inl j => inst.W i j
    | Sum.inr (Sum.inl j) => if i = j then 1 else 0
    | Sum.inr (Sum.inr j) => if i = j then -1 else 0

/-- The extended objective `min eᵀv⁺ + eᵀv⁻` of Eq. (1.8): `0` on the `y`-columns, `1` on
the `v⁺`/`v⁻`-columns. -/
def feasCost : (Fin n2 ⊕ Fin m2 ⊕ Fin m2) → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 1

/-- The simplex multiplier a feasibility basis `b` determines: `σ = (([W|I|-I]_b)ᵀ)⁻¹ e_b`
(p. 220, "`σν` the associated simplex multipliers"). -/
noncomputable def feasMultiplier (inst : Instance n1 n2 m1 m2 K) (b : FeasBasis n2 m2) :
    Fin m2 → ℝ :=
  Matrix.mulVec (((feasMatrix inst).submatrix id b.1)ᵀ)⁻¹ (fun j => feasCost (b.1 j))

/-- The optimal value of the Step-2 feasibility-test LP (1.8)-(1.9) at `x` for scenario
`k`: always well-defined (the system is feasible for any `x`, taking `y = 0` and `v⁺, v⁻`
to absorb `h_k - T_k x`), nonnegative, and `0` exactly when scenario `k` is second-stage
feasible at `x`. -/
noncomputable def feasLPValue (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (x : Fin n1 → ℝ) :
    ℝ :=
  sInf {w' : ℝ | ∃ y : Fin n2 → ℝ, ∃ vp vn : Fin m2 → ℝ,
    (∀ i, 0 ≤ y i) ∧ (∀ i, 0 ≤ vp i) ∧ (∀ i, 0 ≤ vn i) ∧
    Matrix.mulVec inst.W y + vp - vn = inst.h k - Matrix.mulVec (inst.T k) x ∧
    w' = (∑ i, vp i) + ∑ i, vn i}

/-- The value feasibility-basis `b` claims at `x` for scenario `k`: `σᵀ(h_k - T_k x)`
(Eq. (1.10)-(1.11), read as a value rather than as cut coefficients). -/
noncomputable def feasBasisValue (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : FeasBasis n2 m2)
    (x : Fin n1 → ℝ) : ℝ :=
  dotProduct (feasMultiplier inst b) (inst.h k) -
    dotProduct (feasMultiplier inst b) (Matrix.mulVec (inst.T k) x)

/-- `b` is a valid Step-2 witness at `x` for scenario `k`: `b` actually attains the true
optimal value of the feasibility-test LP (1.8) there. -/
def IsFeasBasisOptimalAt (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : FeasBasis n2 m2)
    (x : Fin n1 → ℝ) : Prop :=
  feasBasisValue inst k b x = feasLPValue inst k x

/-- The feasibility-cut coefficients `(D, d)` of Eq. (1.10)-(1.11), for scenario `k` and
witness basis `b`. -/
noncomputable def feasCutCoeffs (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : FeasBasis n2 m2) :
    (Fin n1 → ℝ) × ℝ :=
  (fun i => dotProduct (feasMultiplier inst b) (fun r => inst.T k r i),
   dotProduct (feasMultiplier inst b) (inst.h k))

end StochasticProg.LShaped


