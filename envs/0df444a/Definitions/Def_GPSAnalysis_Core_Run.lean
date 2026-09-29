-- Prove2me | Definitions.Def_GPSAnalysis_Core_Run
-- name    : GPSAnalysis_Core_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T07:22:21.250376+00:00
-- url     : https://prove2.me/theorems/2af7570e-5b5d-49f2-a543-f07f28fee501
-- title:
--   Generalized pattern search runs, assumptions A1-A3, and refining subsequences (Definition 3.5)
-- statement:
--   A **GPS setup** fixes the problem data of (1.1) (objective $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$, constraints $\ell\le Ax\le u$ with $\ell\le u$) and the algorithm's constants: a nonsingular $G\in\mathbb R^{n\times n}$ and an integer $\bar Z$ such that $D=G\bar Z$ is a positive spanning set, a **rational** $\tau>1$, and integers $w^-\le -1$ and $w^+\ge 0$.
--
--   A **GPS run** is a sequence of iterates $x_k\in\mathbb R^n$, mesh size parameters $\Delta_k$ with $\Delta_0>0$, poll sets $D_k\subseteq D$ (each a positive spanning set of columns of $D$) and integer exponents $w_k$, with $\Delta_{k+1}=\tau^{w_k}\Delta_k$ for all $k$, such that every iteration is of one of two kinds:
--
--   1. **Improved mesh point.** $x_{k+1}\in M_k\cap\Omega$, $f_\Omega(x_{k+1})<f_\Omega(x_k)$, and $0\le w_k\le w^+$ (rule (2.2)).
--   2. **Mesh local optimizer.** $f_\Omega(x_k)\le f_\Omega(x_k+\Delta_k d)$ for every $d\in D_k$, $x_{k+1}=x_k$, and $w^-\le w_k\le -1$ (rule (2.1)).
--
--   This is the paper's basic GPS algorithm with the SEARCH step, the choice of $D_k$ and the exponents left free: any mesh point may be proposed by the search, and the mesh is refined only when the complete poll over $D_k$ fails to improve.
--
--   The paper's assumptions are: **A1** $f_\Omega(x_0)<\infty$; **A2** the constraint matrix $A$ is rational; **A3** all iterates lie in a compact set.
--
--   **Definition 3.5.** A subsequence $\{x_k\}_{k\in K}$ of mesh local optimizers, indexed by an infinite set $K$, is a **refining subsequence** if $\{\Delta_k\}_{k\in K}$ converges to zero.
--
--   **Formalization Note** The kind of iteration $k$ is the predicate `meshLocalOpt k`. An infinite index set is written as a strictly increasing map $K:\mathbb N\to\mathbb N$. The powers $\tau^{w_k}$ are integer powers of the real number $\tau$.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), pp. 892-893, Section 2, rules (2.1), (2.2) and 'A basic GPS algorithm'; p. 894, assumptions A1-A3; p. 896, Definition 3.5

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh

open Filter Topology Matrix

namespace GPSAnalysis.Core

/-- The data of a generalized pattern search (GPS) on problem (1.1) of Audet–Dennis (2003):
the objective `f : ℝⁿ → ℝ ∪ {+∞}`, the linear constraints `ℓ ≤ A x ≤ u` (`ℓ ≤ u`), the
nonsingular generating matrix `G`, the integer matrix `Z̄` (so that `D = G Z̄` is a positive
spanning set), the rational mesh-update base `τ > 1`, and the integer exponent bounds
`w⁻ ≤ -1` and `w⁺ ≥ 0` of rules (2.1)–(2.2). -/
structure GPSSetup (n m p : ℕ) where
  /-- The objective `f : ℝⁿ → ℝ ∪ {+∞}`. -/
  f : (Fin n → ℝ) → WithTop ℝ
  /-- The constraint matrix `A`. -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- Lower bounds `ℓ ∈ (ℝ ∪ {±∞})ᵐ`. -/
  lo : Fin m → EReal
  /-- Upper bounds `u ∈ (ℝ ∪ {±∞})ᵐ`. -/
  up : Fin m → EReal
  lo_le_up : lo ≤ up
  /-- The nonsingular generating matrix `G`. -/
  G : Matrix (Fin n) (Fin n) ℝ
  G_nonsingular : IsUnit G.det
  /-- The integer matrix `Z̄` whose columns are the `z̄_j`. -/
  Zbar : Matrix (Fin n) (Fin p) ℤ
  /-- `D = G Z̄` is a positive spanning set of `ℝⁿ`. -/
  D_posSpanning : IsPositiveSpanning (dirMatrix G Zbar) Finset.univ
  /-- The rational constant `τ > 1`. -/
  τ : ℚ
  one_lt_τ : 1 < τ
  /-- The lower bound `w⁻ ≤ -1` on refinement exponents. -/
  wminus : ℤ
  wminus_le : wminus ≤ -1
  /-- The upper bound `w⁺ ≥ 0` on coarsening exponents. -/
  wplus : ℤ
  wplus_nonneg : 0 ≤ wplus

namespace GPSSetup

variable {n m p : ℕ} (P : GPSSetup n m p)

/-- The feasible region `Ω = {x : ℓ ≤ A x ≤ u}`. -/
def Ω : Set (Fin n → ℝ) := feasibleSet P.A P.lo P.up

/-- The barrier objective `f_Ω`. -/
noncomputable def fΩ : (Fin n → ℝ) → WithTop ℝ := barrier P.f P.Ω

/-- The direction matrix `D = G Z̄`. -/
def D : Matrix (Fin n) (Fin p) ℝ := dirMatrix P.G P.Zbar

/-- The direction `d_j ∈ D` (column `j` of `D`). -/
def dir (j : Fin p) : Fin n → ℝ := direction P.D j

end GPSSetup

/-- A run of the basic GPS algorithm (p. 893) on the setup `P`. The SEARCH step, the choice of
the poll sets `D_k ⊆ D` and the exponents `w_k` are free; every iteration `k` is either an
improved mesh point iteration or a mesh local optimizer iteration (`meshLocalOpt k`):

* improved mesh point: `x_{k+1} ∈ M_k ∩ Ω`, `f_Ω(x_{k+1}) < f_Ω(x_k)`, and
  `Δ_{k+1} = τ^{w_k} Δ_k` with `0 ≤ w_k ≤ w⁺` (rule (2.2));
* mesh local optimizer: `f_Ω(x_k) ≤ f_Ω(x_k + Δ_k d)` for all `d ∈ D_k`, `x_{k+1} = x_k`, and
  `Δ_{k+1} = τ^{w_k} Δ_k` with `w⁻ ≤ w_k ≤ -1` (rule (2.1)).

Every `D_k` is a positive spanning set made of columns of `D`, and `Δ_0 > 0`. -/
structure GPSRun {n m p : ℕ} (P : GPSSetup n m p) where
  /-- The iterates `x_k`. -/
  x : ℕ → (Fin n → ℝ)
  /-- The mesh size parameters `Δ_k`. -/
  Δ : ℕ → ℝ
  /-- The poll directions `D_k ⊆ D`, as a set of column indices. -/
  Dk : ℕ → Finset (Fin p)
  /-- The mesh update exponents `w_k`. -/
  w : ℕ → ℤ
  /-- `meshLocalOpt k` holds iff iterate `x_k` is a mesh local optimizer. -/
  meshLocalOpt : ℕ → Prop
  Δ_zero_pos : 0 < Δ 0
  Dk_posSpanning : ∀ k, IsPositiveSpanning P.D (Dk k)
  Δ_succ : ∀ k, Δ (k + 1) = ((P.τ : ℝ) ^ (w k)) * Δ k
  improved : ∀ k, ¬ meshLocalOpt k →
    x (k + 1) ∈ mesh P.D (x k) (Δ k) ∩ P.Ω ∧ P.fΩ (x (k + 1)) < P.fΩ (x k) ∧
      0 ≤ w k ∧ w k ≤ P.wplus
  localOpt : ∀ k, meshLocalOpt k →
    (∀ j ∈ Dk k, P.fΩ (x k) ≤ P.fΩ (x k + Δ k • P.dir j)) ∧ x (k + 1) = x k ∧
      P.wminus ≤ w k ∧ w k ≤ -1

/-- Assumption A1 (p. 894): `f_Ω(x_0) < ∞`. -/
def AssumptionA1 {n m p : ℕ} {P : GPSSetup n m p} (R : GPSRun P) : Prop :=
  P.fΩ (R.x 0) < ⊤

/-- Assumption A2 (p. 894): the constraint matrix `A` is rational. -/
def AssumptionA2 {n m p : ℕ} (P : GPSSetup n m p) : Prop :=
  IsRationalMatrix P.A

/-- Assumption A3 (p. 894): all iterates lie in a compact set. -/
def AssumptionA3 {n m p : ℕ} {P : GPSSetup n m p} (R : GPSRun P) : Prop :=
  ∃ X : Set (Fin n → ℝ), IsCompact X ∧ ∀ k, R.x k ∈ X

/-- Definition 3.5 (p. 896): the subsequence `{x_k}_{k ∈ K}`, `K = {K 0 < K 1 < ⋯}`, is a
refining subsequence if every `x_{K i}` is a mesh local optimizer and `Δ_{K i} → 0`. -/
def IsRefiningSubseq {n m p : ℕ} {P : GPSSetup n m p} (R : GPSRun P) (K : ℕ → ℕ) : Prop :=
  StrictMono K ∧ (∀ i, R.meshLocalOpt (K i)) ∧ Tendsto (fun i => R.Δ (K i)) atTop (𝓝 0)

end GPSAnalysis.Core


