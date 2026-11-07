-- Prove2me | Definitions.Def_PackingLPAccel_Regression
-- name    : PackingLPAccel_Regression
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:41.453338+00:00
-- url     : https://prove2.me/theorems/e4c0a1c6-74c0-4603-8cba-c4ddf33694dc
-- title:
--   Box-constrained positive $(\ell_2,\ell_p)$-regression and Algorithm 1
-- statement:
--   An instance has $a,u\in\mathbb R^D_{\ge0}$, nonnegative matrices $B^{(2)},B^{(p)}$ and an integer $p\ge2$. The problem is to maximize over $0\le y\le u$ the function
--
--   $$G(y)=a^\top y-\|B^{(2)}y\|_2^2-\|B^{(p)}y\|_p^p.$$
--
--   The module defines the potential $P_\kappa(y)=\kappa^{-1/2}\|B^{(2)}y\|_2+\kappa^{-1/p}\|B^{(p)}y\|_p$, its subgradient $\sigma_\kappa$, and Algorithm 1: with $\Lambda=4(1+\kappa^{-1}a^\top u+P_\kappa(u))$, $T=2\lceil\log_{1+1/p}\Lambda\rceil$ and $y=\Lambda^{-1}u$, repeat up to $T$ times the parallel update $y_i\leftarrow\min\{u_i,(1+1/p)y_i\}$ on the coordinates with $\sigma_\kappa(y)_i\le\frac1{16}\kappa^{-1}a_i$, and return $y$ as soon as $a^\top y\ge\kappa$. If no iteration returns, the output is FAIL.
--
--   **Formalization Note** The variables are indexed by any finite type, and Algorithm 1 is a mathematical function with values in `Option`. "A term with zero norm is set to 0" is automatic, since $0^{-1}=0$ in Lean. The input layout holds $D,m^{(2)},m^{(p)},N_2,N_p,p$, positions, a scalar, $a$, $u$ and values.
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Problem 4.4, p.15 (pdf 16); Algorithm 1, p.16 (pdf 17)

import Mathlib
import Definitions.Def_PackingLPAccel_Layout

namespace PackingLPAccel

/-!
# Box-constrained positive `(ℓ₂, ℓ_p)`-regression and Algorithm 1

Chen, Chen, Graur, Sidford, *Accelerated Parallel Algorithms for Packing Linear Programming*,
STOC 2027 submission (manuscript sha256 1dac7711…), Problem 4.4 (p.15) and Algorithm 1 (p.16).

**Formalization Note.**
* The index type of the variables is any finite type, so the same object serves the grid variables
  of Lemma 4.3. The machine-level statements take `Fin D`.
* `alg1Step` and `alg1` are mathematical functions; the machine appears only in the cost clauses.
* "A term with zero norm is set to 0" is automatic: `(0)⁻¹ = 0` in Lean, and `p - 1 ≥ 1`.
* `alg1Iter R κ t` is `y^{(t+1)}` of Claim 4.7.
* Layout: `I` holds `D, m₂, mₚ, N₂, Nₚ, p` and then positions of `B^{(2)}` and `B^{(p)}`; `M` holds a
  scalar (`δ` or `κ`), `a`, `u` and then the values. The output vector starts at
  `M (1 + 2D + N₂ + Nₚ)`.
-/

variable {ι : Type*} {m₂ mₚ : ℕ}

/-- The data of Problem 4.4. -/
structure RegInstance (ι : Type*) (m₂ mₚ : ℕ) where
  /-- The linear coefficient `a`. -/
  a : ι → ℝ
  /-- The upper bound `u`. -/
  u : ι → ℝ
  /-- The matrix `B^{(2)}`. -/
  B₂ : Matrix (Fin m₂) ι ℝ
  /-- The matrix `B^{(p)}`. -/
  Bₚ : Matrix (Fin mₚ) ι ℝ
  /-- The exponent `p`. -/
  p : ℕ

namespace RegInstance

/-- The conditions of Problem 4.4: everything is nonnegative and `p ≥ 2`. -/
def IsValid (R : RegInstance ι m₂ mₚ) : Prop :=
  (∀ i, 0 ≤ R.a i) ∧ (∀ i, 0 ≤ R.u i) ∧ (∀ i j, 0 ≤ R.B₂ i j) ∧ (∀ i j, 0 ≤ R.Bₚ i j) ∧ 2 ≤ R.p

/-- `y ∈ [0, u]`. -/
def InBox (R : RegInstance ι m₂ mₚ) (y : ι → ℝ) : Prop := ∀ i, 0 ≤ y i ∧ y i ≤ R.u i

variable [Fintype ι]

/-- `a⊤y`. -/
def linTerm (R : RegInstance ι m₂ mₚ) (y : ι → ℝ) : ℝ := ∑ i, R.a i * y i

/-- `(B^{(2)} y)_r`. -/
def row₂ (R : RegInstance ι m₂ mₚ) (y : ι → ℝ) (r : Fin m₂) : ℝ := ∑ i, R.B₂ r i * y i

/-- `(B^{(p)} y)_r`. -/
def rowₚ (R : RegInstance ι m₂ mₚ) (y : ι → ℝ) (r : Fin mₚ) : ℝ := ∑ i, R.Bₚ r i * y i

/-- `∥B^{(2)} y∥₂`. -/
noncomputable def norm₂ (R : RegInstance ι m₂ mₚ) (y : ι → ℝ) : ℝ :=
  Real.sqrt (∑ r, R.row₂ y r ^ 2)

/-- `∥B^{(p)} y∥_p`. -/
noncomputable def normₚ (R : RegInstance ι m₂ mₚ) (y : ι → ℝ) : ℝ :=
  (∑ r, |R.rowₚ y r| ^ R.p) ^ ((1 : ℝ) / R.p)

/-- `G(y) = a⊤y - ∥B^{(2)}y∥₂² - ∥B^{(p)}y∥_p^p`. -/
noncomputable def G (R : RegInstance ι m₂ mₚ) (y : ι → ℝ) : ℝ :=
  R.linTerm y - ∑ r, R.row₂ y r ^ 2 - ∑ r, |R.rowₚ y r| ^ R.p

/-- The potential `P_κ(y) = κ^{-1/2} ∥B^{(2)}y∥₂ + κ^{-1/p} ∥B^{(p)}y∥_p`. -/
noncomputable def potential (R : RegInstance ι m₂ mₚ) (κ : ℝ) (y : ι → ℝ) : ℝ :=
  κ ^ (-(1 / 2 : ℝ)) * R.norm₂ y + κ ^ (-((1 : ℝ) / R.p)) * R.normₚ y

/-- The subgradient `σ_κ(y)` of line 5 of Algorithm 1. -/
noncomputable def sigma (R : RegInstance ι m₂ mₚ) (κ : ℝ) (y : ι → ℝ) (i : ι) : ℝ :=
  κ ^ (-(1 / 2 : ℝ)) * (R.norm₂ y)⁻¹ * (∑ r, R.B₂ r i * R.row₂ y r) +
    κ ^ (-((1 : ℝ) / R.p)) * (R.normₚ y ^ (R.p - 1))⁻¹ * (∑ r, R.Bₚ r i * R.rowₚ y r ^ (R.p - 1))

open Classical in
/-- One parallel update (lines 6–7 of Algorithm 1). -/
noncomputable def alg1Step (R : RegInstance ι m₂ mₚ) (κ : ℝ) (y : ι → ℝ) (i : ι) : ℝ :=
  if R.sigma κ y i ≤ (1 / 16) * κ⁻¹ * R.a i then min (R.u i) ((1 + (R.p : ℝ)⁻¹) * y i) else y i

/-- `Λ = 4(1 + κ⁻¹ a⊤u + P_κ(u))` (line 1). -/
noncomputable def alg1Lam (R : RegInstance ι m₂ mₚ) (κ : ℝ) : ℝ :=
  4 * (1 + κ⁻¹ * R.linTerm R.u + R.potential κ R.u)

/-- `T = 2 ⌈log_{1 + 1/p} Λ⌉` (line 2). -/
noncomputable def alg1T (R : RegInstance ι m₂ mₚ) (κ : ℝ) : ℕ :=
  2 * ⌈Real.logb (1 + (R.p : ℝ)⁻¹) (R.alg1Lam κ)⌉₊

/-- `y^{(t+1)}`, starting from `y^{(1)} = Λ⁻¹ u` (line 3). -/
noncomputable def alg1Iter (R : RegInstance ι m₂ mₚ) (κ : ℝ) (t : ℕ) : ι → ℝ :=
  (R.alg1Step κ)^[t] (fun i => (R.alg1Lam κ)⁻¹ * R.u i)

open Classical in
/-- The loop of lines 4–9 with `fuel` iterations left. -/
noncomputable def alg1Loop (R : RegInstance ι m₂ mₚ) (κ : ℝ) : ℕ → (ι → ℝ) → Option (ι → ℝ)
  | 0, _ => none
  | fuel + 1, y =>
      if κ ≤ R.linTerm (R.alg1Step κ y) then some (R.alg1Step κ y)
      else alg1Loop R κ fuel (R.alg1Step κ y)

/-- Algorithm 1: `some y` for "return `y`", `none` for FAIL. -/
noncomputable def alg1 (R : RegInstance ι m₂ mₚ) (κ : ℝ) : Option (ι → ℝ) :=
  R.alg1Loop κ (R.alg1T κ) (R.alg1Iter κ 0)

end RegInstance

variable {D : ℕ}

/-- `N_reg = D + m^{(2)} + m^{(p)} + nnz(B^{(2)}) + nnz(B^{(p)})`. -/
def nReg (D m₂ mₚ N₂ Nₚ : ℕ) : ℕ := D + m₂ + mₚ + N₂ + Nₚ

/-- The integer list of a regression instance. -/
def regInts {N₂ Nₚ : ℕ} (R : RegInstance (Fin D) m₂ mₚ) (e₂ : Fin N₂ → Fin m₂ × Fin D)
    (eₚ : Fin Nₚ → Fin mₚ × Fin D) : List ℤ :=
  [(D : ℤ), (m₂ : ℤ), (mₚ : ℤ), (N₂ : ℤ), (Nₚ : ℤ), (R.p : ℤ)] ++ sparseIdx e₂ ++ sparseIdx eₚ

/-- The real list of a regression instance, with a scalar in front. -/
noncomputable def regReals {N₂ Nₚ : ℕ} (s : ℝ) (R : RegInstance (Fin D) m₂ mₚ)
    (e₂ : Fin N₂ → Fin m₂ × Fin D) (eₚ : Fin Nₚ → Fin mₚ × Fin D) : List ℝ :=
  s :: (List.ofFn R.a ++ List.ofFn R.u ++ sparseVals R.B₂ e₂ ++ sparseVals R.Bₚ eₚ)

/-- The initial state of a regression program. -/
noncomputable def regInit {N₂ Nₚ : ℕ} (s : ℝ) (R : RegInstance (Fin D) m₂ mₚ)
    (e₂ : Fin N₂ → Fin m₂ × Fin D) (eₚ : Fin Nₚ → Fin mₚ × Fin D) : State :=
  initState (regReals s R e₂ eₚ) (regInts R e₂ eₚ)

/-- The output vector of a regression program. -/
def regOutput (D N₂ Nₚ : ℕ) (s : State) : Fin D → ℝ :=
  fun i => s.M (1 + 2 * (D : ℤ) + (N₂ : ℤ) + (Nₚ : ℤ) + ((i : ℕ) : ℤ))

end PackingLPAccel


