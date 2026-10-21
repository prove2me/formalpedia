-- Prove2me | Definitions.Def_MatrixAnalytic_PHRenewal_PHRep
-- name    : MatrixAnalytic_PHRenewal_PHRep
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:04.499833+00:00
-- url     : https://prove2.me/theorems/7abbabd9-a695-4132-b946-8cf646540d71
-- title:
--   PH representation $(\boldsymbol\tau, T)$ of a PH renewal process, its phase generator $D = T + \boldsymbol t\cdot\boldsymbol\tau$, $\boldsymbol\pi$, $\Pi$ and $M$
-- statement:
--   Fix a finite set of phases $\{1,\dots,n\}$. A **PH representation** $(\boldsymbol\tau, T)$ consists of a row vector $\boldsymbol\tau$ and an $n\times n$ rate matrix $T$ such that, with the exit-rate column vector
--   $$\boldsymbol t = -T\mathbf 1,$$
--   one has (2.4)–(2.6): $T_{ii} < 0$, $T_{ij}\ge 0$ for $i\ne j$, $t_i\ge 0$, and $\boldsymbol\tau\ge\mathbf 0$. These are the parameters of a Markov process on $\{0,1,\dots,n\}$ with absorbing state $0$, initial distribution $(\tau_0,\boldsymbol\tau)$ and generator $\begin{bmatrix}0&\mathbf 0\\ \boldsymbol t&T\end{bmatrix}$. For the PH renewal process two standing assumptions are added: $T$ is nonsingular (p. 44) and there is **no atom at $0$** (p. 62), i.e. $\boldsymbol\tau\mathbf 1 = 1$, so $\tau_0 = 0$.
--
--   The file also defines the objects of Section 3.1 built from $(\boldsymbol\tau,T)$:
--
--   1. A rate matrix $A$ has a **positive-rate step** from $a$ to $b$ if $a\ne b$ and $A_{ab}>0$; a *path* is a finite chain of such steps (possibly empty).
--   2. $(\boldsymbol\tau,T)$ is **irreducible** (p. 63) if every phase $j$ is *transient* (there is a path in $T$ from $j$ to some phase $k$ with $t_k>0$, i.e. a path to the absorbing phase $0$) and *useful* (there is a path in $T$ to $j$ from some phase $i$ with $\tau_i>0$).
--   3. A matrix $D$ is an **irreducible generator** if every phase can be reached from every phase by a path of positive-rate steps of $D$.
--   4. The generator of the phase process, $D = T + \boldsymbol t\cdot\boldsymbol\tau$, where $\boldsymbol t\cdot\boldsymbol\tau$ is the outer product (column times row).
--   5. The row vector $\boldsymbol\pi = (\boldsymbol\tau T^{-1}\mathbf 1)^{-1}\boldsymbol\tau T^{-1}$ of (3.1) and the matrix $\Pi = \mathbf 1\cdot\boldsymbol\pi$ whose rows all equal $\boldsymbol\pi$.
--   6. The mean interrenewal time $M = \boldsymbol\tau(-T)^{-1}\mathbf 1$.
--
--   These are the data and the derived matrices on which every statement of the mission is made.
--
--   **Formalization Note** Phases are an arbitrary finite type `ι`; row vectors are functions `ι → ℝ` acting on the left (`v ᵥ* A`), column vectors act on the right (`A *ᵥ v`), and $\mathbf 1$ is `fun _ => 1`. Nonsingularity of $T$ is `IsUnit T.det`. $T^{-1}$ and $(-T)^{-1}$ are Mathlib's `Matrix` inverse, which is the true inverse because $T$ is nonsingular; the scalar $(\boldsymbol\tau T^{-1}\mathbf 1)^{-1}$ uses real division, so a statement about $\boldsymbol\pi$ that asserts $\boldsymbol\pi\mathbf 1 = 1$ also forces $\boldsymbol\tau T^{-1}\mathbf 1\ne 0$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 39, Eqs. (2.3)–(2.6) and Definition 2.3.1; p. 44 (T nonsingular); pp. 62–63 (no atom at 0, D = T + t·τ, irreducible representations); p. 64, Lemma 3.1.3 and Theorem 3.1.4 (π, Π, M)

import Mathlib

open Matrix

namespace MatrixAnalytic.PHRenewal

/-- The exit-rate column vector `t = -T 1` of a PH representation (Eq. (2.5): `T1 + t = 0`). -/
def exitVec {ι : Type*} [Fintype ι] (T : Matrix ι ι ℝ) : ι → ℝ :=
  -(T *ᵥ fun _ => 1)

/-- A PH representation `(τ, T)` on the finite phase set `ι` (Section 2.3, (2.3)–(2.6)), under the
standing assumptions of the PH renewal process: `T` is nonsingular (p. 44) and there is no atom
at `0` (p. 62), i.e. `τ₀ = 1 - τ1 = 0`. -/
structure IsPHRenewalRep {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) : Prop where
  /-- `τ` is a nonnegative row vector. -/
  tau_nonneg : ∀ i, 0 ≤ τ i
  /-- No atom at zero: `τ1 = 1`, equivalently `τ₀ = 0` by (2.6). -/
  tau_sum_one : ∑ i, τ i = 1
  /-- (2.4): `T_ii < 0`. -/
  diag_neg : ∀ i, T i i < 0
  /-- (2.4): `T_ij ≥ 0` for `i ≠ j`. -/
  offDiag_nonneg : ∀ i j, i ≠ j → 0 ≤ T i j
  /-- (2.4): `t_i ≥ 0`, where `t = -T1` by (2.5). -/
  exit_nonneg : ∀ i, 0 ≤ exitVec T i
  /-- Standing assumption of p. 44: the rate matrix `T` is nonsingular. -/
  nonsingular : IsUnit T.det

/-- One-step relation "the phase process can jump from `a` to `b` at a positive rate" for a rate
matrix `A`: `a ≠ b` and `A a b > 0`. A path in the transition diagram is a finite chain of such
jumps. -/
def PosRate {ι : Type*} (A : Matrix ι ι ℝ) (a b : ι) : Prop :=
  a ≠ b ∧ 0 < A a b

/-- An irreducible PH representation (p. 63): every phase `j` is *transient* (there is a path
from `j` to the absorbing phase `0`, i.e. a path within the transient phases from `j` to some
phase `k` with exit rate `t_k > 0`) and every phase is *useful* (there is a path to `j` from some
phase `i` with `τ_i > 0`). -/
def IsIrreducibleRep {ι : Type*} [Fintype ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ) : Prop :=
  (∀ j, ∃ k, Relation.ReflTransGen (PosRate T) j k ∧ 0 < exitVec T k) ∧
  (∀ j, ∃ i, 0 < τ i ∧ Relation.ReflTransGen (PosRate T) i j)

/-- An irreducible generator: every state can be reached from every state along a path of
positive off-diagonal rates. -/
def IsIrreducibleGen {ι : Type*} (D : Matrix ι ι ℝ) : Prop :=
  ∀ i j, Relation.ReflTransGen (PosRate D) i j

/-- The generator `D = T + t·τ` of the phase process of the PH renewal process (p. 62); `t·τ` is
the outer product (column `t` times row `τ`). -/
def phaseGen {ι : Type*} [Fintype ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  T + vecMulVec (exitVec T) τ

/-- The row vector `π = (τT⁻¹1)⁻¹ τT⁻¹` of (3.1). -/
noncomputable def statVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) : ι → ℝ :=
  ((τ ᵥ* T⁻¹) ⬝ᵥ (fun _ => 1))⁻¹ • (τ ᵥ* T⁻¹)

/-- The matrix `Π = 1·π` (Lemma 3.1.3): every row equals `π`. -/
noncomputable def statMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  vecMulVec (fun _ => 1) (statVec τ T)

/-- The mean interrenewal time `M = τ(-T)⁻¹1` (Theorem 3.1.4, by (2.13) with `k = 1`). -/
noncomputable def meanInterrenewal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) : ℝ :=
  τ ⬝ᵥ ((-T)⁻¹ *ᵥ fun _ => 1)

end MatrixAnalytic.PHRenewal


