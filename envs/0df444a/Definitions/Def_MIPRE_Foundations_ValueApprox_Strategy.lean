-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
-- name    : MIPRE_Foundations_ValueApprox_Strategy
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:09:38.06332+00:00
-- url     : https://prove2.me/theorems/2c96aa82-160a-47ba-b9d6-d4533e53cd4a
-- title:
--   Exact strategies with unnormalized states, and the quantum value from below
-- statement:
--   Let $G$ be a game on finite alphabets $X, Y, A, B$ (`MIPRE.Game X Y A B`). The core of `lem:value-lower-approx`: the quantum value exceeds a threshold iff some exact strategy with Gaussian-rational entries does (blueprint `lem:rational-strategies-suffice`).
--
--   **Born values on unbundled data.** `MIPRE.ValueApprox.bornValue G P Q ψ`, for `P : X → A → Matrix dA dA ℂ`, `Q : Y → B → Matrix dB dB ℂ` and any `ψ : dA × dB → ℂ`, is $\sum_{x,y,a,b}\mu(x,y)\,[D(x,y,a,b)]\,\mathrm{Re}\langle\psi,(P^a_x\otimes Q^b_y)\psi\rangle$; `S.value` is the `bornValue` of its data (`value_eq_bornValue`).
--
--   **Exact strategies.** `MIPRE.ValueApprox.ExactStrategy X Y A B` is raw data: dimensions `dA`, `dB`, operators `PA`, `PB` (matrices over `Fin dA`, `Fin dB`), and an unnormalized state `u : Fin dA × Fin dB → ℂ`. `ExactStrategy.IsValid c` says the data is a strategy (`isPVM_A`: every `c.PA x` is an `IsPVM`; `isPVM_B`; `u_ne_zero`), and `ExactStrategy.EntriesIn c K` says all entries of `PA`, `PB`, `u` lie in the subfield $K$. The value of the data in $G$ is
--   $$c.\mathrm{value}(G) = \frac{\mathrm{bornValue}(G,\ c.\mathrm{PA},\ c.\mathrm{PB},\ c.u)}{\mathrm{Re}(u^{*}\cdot u)};$$
--   `ExactStrategy.ψ c` is the normalized state $\|u\|^{-1}u$, and `ExactStrategy.toStrategy c G hc`, for valid data, is the tensor-product strategy with state $\psi$. `MIPRE.ValueApprox.pointMeasurement X a₀` always answers $a_0$ on $\mathbb{C}^{1}$.
--
--   The embedded lemmas are the Lipschitz estimate `abs_bornValue_sub_le` (with two auxiliaries: for projective operator families, operators moving by at most $\eta$ in operator norm and unit states by at most $\eta$ move the value by at most $4|A||B|\eta$), the normalization lemmas for $\psi$, `value_toStrategy`, soundness `value_le_quantumValue`, density `exists_exactStrategy_value_gt`, `nonempty_tensorProductStrategy`, and `lt_quantumValue_iff`: for $A$, $B$ nonempty and real $t$, $t < \mathrm{val}^{*}(G)$ iff some valid $c$ with Gaussian-rational entries has $t < c.\mathrm{value}(G)$.
--
--   **Formalization Note**. Validity is separate from the data so that the data can be enumerated and validity checked; `value` divides by `(star u ⬝ᵥ u).re` (total in Lean). The biconditional is sharp, with strict inequalities on both sides, because every candidate is exact; this departs from the paper's proof of statement (S) of `cor:mip-re`, which enumerates approximate candidates and repairs each by $T \mapsto T^{-1/2}$ conjugation with an explicit slack.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox/Strategy.lean; blueprint lem:rational-strategies-suffice; companion paper (vidick/MIPRE-proof), cor:mip-re, statement (S)

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox/Strategy.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense

/-!
# Exact strategies, and the quantum value from below

The mathematical core of `lem:value-lower-approx` (`MIP* ⊆ RE`): the quantum value of a game
exceeds a threshold `t` if and only if some *exact strategy* with Gaussian-rational entries has
value exceeding `t` (`MIPRE.ValueApprox.lt_quantumValue_iff`). Exact strategies
(`MIPRE.ValueApprox.ExactStrategy`) are the raw data of a tensor-product strategy with an
unnormalized state — dimensions, measurement operators, a state vector — with validity
(`ExactStrategy.IsValid`: projective measurements, nonzero state) a separate predicate, so that
the data can be enumerated and validity checked; their value (`ExactStrategy.value`) is the
Born-rule sum divided by `‖u‖²`, a rational function of the entries. The computability layer
enumerates the Gaussian-rational ones.

* Soundness (`ExactStrategy.value_le_quantumValue`): valid data describes a tensor-product
  strategy (`ExactStrategy.toStrategy`, normalizing the state) of the same value.
* Density (`exists_exactStrategy_value_gt`): every tensor-product strategy is approximated in
  value by valid Gaussian-rational exact strategies. The measurement operators are approximated
  by exact Gaussian-rational projective measurements (`IsPVM.exists_entriesIn_norm_sub_le`) and
  the state is rounded entrywise; the value is Lipschitz in the data (`abs_bornValue_sub_le`),
  with the crude but sufficient constant `4 |A| |B|`.

This departs from the paper's proof of statement (S) in `cor:mip-re`, which enumerates
*approximate* candidates — Gaussian-rational tuples satisfying relaxed POVM constraints — and
repairs each into an exact POVM by `T ↦ T^{-1/2}` conjugation (its Claims "Stability" and
"Density", with the explicit slack `Δ(d, k)`). Rounding at the level of the skew-Hermitian Cayley
generator (`MIPRE.Foundations.ValueApprox.Dense`) makes every candidate exact, so no repair, no
slack and no positive-semidefiniteness test are needed; the biconditional is then sharp.
-/

namespace MIPRE.ValueApprox

open Matrix WithLp
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-! ## The Born functional and its perturbation -/

section Born

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- The value in `G` of the strategy data `(P, Q, ψ)` — `TensorProductStrategy.value` on
unbundled data; the state need not be normalized. -/
noncomputable def bornValue (G : Game X Y A B) (P : X → A → Matrix dA dA ℂ)
    (Q : Y → B → Matrix dB dB ℂ) (ψ : dA × dB → ℂ) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    G.μ x y * (if G.D x y a b then 1 else 0) * (star ψ ⬝ᵥ ((P x a ⊗ₖ Q y b) *ᵥ ψ)).re

theorem _root_.MIPRE.TensorProductStrategy.value_eq_bornValue {G : Game X Y A B}
    (S : TensorProductStrategy G) : S.value = bornValue G S.PA.M S.PB.M S.ψ := rfl

/-- The Born term `re ⟨ψ, (P ⊗ Q) ψ⟩` is Lipschitz in the operators and in the unit state. -/
theorem abs_re_dotProduct_kronecker_sub_le (P P' : Matrix dA dA ℂ) (Q Q' : Matrix dB dB ℂ)
    {ψ ψ' : dA × dB → ℂ} (hψ : ‖(toLp 2 ψ : EuclideanSpace ℂ (dA × dB))‖ = 1)
    (hψ' : ‖(toLp 2 ψ' : EuclideanSpace ℂ (dA × dB))‖ = 1) :
    |(star ψ ⬝ᵥ ((P ⊗ₖ Q) *ᵥ ψ)).re - (star ψ' ⬝ᵥ ((P' ⊗ₖ Q') *ᵥ ψ')).re| ≤
      ‖P - P'‖ * ‖Q‖ + ‖P'‖ * ‖Q - Q'‖ +
        2 * (‖P'‖ * ‖Q'‖) * ‖(toLp 2 (ψ - ψ') : EuclideanSpace ℂ (dA × dB))‖ := by
  have h1 : ‖star ψ ⬝ᵥ (((P - P') ⊗ₖ Q) *ᵥ ψ)‖ ≤ ‖P - P'‖ * ‖Q‖ := by
    calc ‖star ψ ⬝ᵥ (((P - P') ⊗ₖ Q) *ᵥ ψ)‖
        ≤ ‖(P - P') ⊗ₖ Q‖ * ‖(toLp 2 ψ : EuclideanSpace ℂ (dA × dB))‖ *
            ‖(toLp 2 ψ : EuclideanSpace ℂ (dA × dB))‖ := norm_dotProduct_mulVec_le _ _ _
      _ = ‖(P - P') ⊗ₖ Q‖ := by rw [hψ, mul_one, mul_one]
      _ ≤ ‖P - P'‖ * ‖Q‖ := norm_kronecker_le _ _
  have h2 : ‖star ψ ⬝ᵥ ((P' ⊗ₖ (Q - Q')) *ᵥ ψ)‖ ≤ ‖P'‖ * ‖Q - Q'‖ := by
    calc ‖star ψ ⬝ᵥ ((P' ⊗ₖ (Q - Q')) *ᵥ ψ)‖
        ≤ ‖P' ⊗ₖ (Q - Q')‖ * ‖(toLp 2 ψ : EuclideanSpace ℂ (dA × dB))‖ *
            ‖(toLp 2 ψ : EuclideanSpace ℂ (dA × dB))‖ := norm_dotProduct_mulVec_le _ _ _
      _ = ‖P' ⊗ₖ (Q - Q')‖ := by rw [hψ, mul_one, mul_one]
      _ ≤ ‖P'‖ * ‖Q - Q'‖ := norm_kronecker_le _ _
  have h3 : ‖star (ψ - ψ') ⬝ᵥ ((P' ⊗ₖ Q') *ᵥ ψ)‖ ≤
      ‖P'‖ * ‖Q'‖ * ‖(toLp 2 (ψ - ψ') : EuclideanSpace ℂ (dA × dB))‖ := by
    calc ‖star (ψ - ψ') ⬝ᵥ ((P' ⊗ₖ Q') *ᵥ ψ)‖
        ≤ ‖P' ⊗ₖ Q'‖ * ‖(toLp 2 (ψ - ψ') : EuclideanSpace ℂ (dA × dB))‖ *
            ‖(toLp 2 ψ : EuclideanSpace ℂ (dA × dB))‖ := norm_dotProduct_mulVec_le _ _ _
      _ ≤ ‖P'‖ * ‖Q'‖ * ‖(toLp 2 (ψ - ψ') : EuclideanSpace ℂ (dA × dB))‖ * 1 := by
          rw [hψ]
          gcongr
          exact norm_kronecker_le _ _
      _ = _ := by ring
  have h4 : ‖star ψ' ⬝ᵥ ((P' ⊗ₖ Q') *ᵥ (ψ - ψ'))‖ ≤
      ‖P'‖ * ‖Q'‖ * ‖(toLp 2 (ψ - ψ') : EuclideanSpace ℂ (dA × dB))‖ := by
    calc ‖star ψ' ⬝ᵥ ((P' ⊗ₖ Q') *ᵥ (ψ - ψ'))‖
        ≤ ‖P' ⊗ₖ Q'‖ * ‖(toLp 2 ψ' : EuclideanSpace ℂ (dA × dB))‖ *
            ‖(toLp 2 (ψ - ψ') : EuclideanSpace ℂ (dA × dB))‖ := norm_dotProduct_mulVec_le _ _ _
      _ ≤ ‖P'‖ * ‖Q'‖ * 1 * ‖(toLp 2 (ψ - ψ') : EuclideanSpace ℂ (dA × dB))‖ := by
          rw [hψ']
          gcongr
          exact norm_kronecker_le _ _
      _ = _ := by ring
  rw [← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [dotProduct_kronecker_perturb]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add norm_add₃_le le_rfl).trans ?_
  linarith

/-- A `μ`-weighted, `D`-selected difference of Born sums is bounded termwise: if every term
moves by at most `c`, the sum moves by at most `|A| |B| c`. -/
theorem abs_sum_sub_sum_le (G : Game X Y A B) (t t' : X → Y → A → B → ℝ) {c : ℝ}
    (h : ∀ x y a b, |t x y a b - t' x y a b| ≤ c) :
    |(∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) * t x y a b) -
      ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) * t' x y a b| ≤
      Fintype.card A * Fintype.card B * c := by
  have hterm : ∀ x y a b,
      |G.μ x y * (if G.D x y a b then 1 else 0) * (t x y a b - t' x y a b)| ≤
        G.μ x y * c := by
    intro x y a b
    have hμ := G.μ_nonneg x y
    have hD : |if G.D x y a b then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> simp
    calc |G.μ x y * (if G.D x y a b then 1 else 0) * (t x y a b - t' x y a b)|
        = G.μ x y * |if G.D x y a b then (1 : ℝ) else 0| * |t x y a b - t' x y a b| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hμ]
      _ ≤ G.μ x y * 1 * c :=
          mul_le_mul (mul_le_mul_of_nonneg_left hD hμ) (h x y a b) (abs_nonneg _)
            (by linarith)
      _ = G.μ x y * c := by ring
  have key : ∀ x y,
      |∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) * (t x y a b - t' x y a b)| ≤
        Fintype.card A * Fintype.card B * (G.μ x y * c) := by
    intro x y
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a, |∑ b, G.μ x y * (if G.D x y a b then 1 else 0) * (t x y a b - t' x y a b)|
        ≤ ∑ a, ∑ b, |G.μ x y * (if G.D x y a b then 1 else 0) * (t x y a b - t' x y a b)| :=
          Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : A, ∑ _b : B, G.μ x y * c :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm x y a b
      _ = Fintype.card A * Fintype.card B * (G.μ x y * c) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x, |∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) * (t x y a b - t' x y a b)|
      ≤ ∑ x, ∑ y,
          |∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) * (t x y a b - t' x y a b)| :=
        Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, Fintype.card A * Fintype.card B * (G.μ x y * c) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => key x y
    _ = Fintype.card A * Fintype.card B * c * ∑ x, ∑ y, G.μ x y := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ = Fintype.card A * Fintype.card B * c := by rw [G.μ_sum_one, mul_one]

/-- The value is Lipschitz in the strategy data: if every measurement operator moves by at most
`η` in operator norm and the unit state by at most `η`, the value moves by at most
`4 |A| |B| η`. -/
theorem abs_bornValue_sub_le (G : Game X Y A B) {P P' : X → A → Matrix dA dA ℂ}
    {Q Q' : Y → B → Matrix dB dB ℂ} {ψ ψ' : dA × dB → ℂ}
    (hP' : ∀ x, IsPVM (P' x)) (hQ : ∀ y, IsPVM (Q y)) (hQ' : ∀ y, IsPVM (Q' y))
    (hψ : ‖(toLp 2 ψ : EuclideanSpace ℂ (dA × dB))‖ = 1)
    (hψ' : ‖(toLp 2 ψ' : EuclideanSpace ℂ (dA × dB))‖ = 1) {η : ℝ}
    (hPη : ∀ x a, ‖P x a - P' x a‖ ≤ η) (hQη : ∀ y b, ‖Q y b - Q' y b‖ ≤ η)
    (hψη : ‖(toLp 2 (ψ - ψ') : EuclideanSpace ℂ (dA × dB))‖ ≤ η) :
    |bornValue G P Q ψ - bornValue G P' Q' ψ'| ≤ Fintype.card A * Fintype.card B * (4 * η) := by
  refine abs_sum_sub_sum_le G (fun x y a b => (star ψ ⬝ᵥ ((P x a ⊗ₖ Q y b) *ᵥ ψ)).re)
    (fun x y a b => (star ψ' ⬝ᵥ ((P' x a ⊗ₖ Q' y b) *ᵥ ψ')).re) fun x y a b => ?_
  refine (abs_re_dotProduct_kronecker_sub_le (P x a) (P' x a) (Q y b) (Q' y b) hψ hψ').trans ?_
  have h1 := (hQ y).norm_le_one b
  have h2 := (hP' x).norm_le_one a
  have h3 := (hQ' y).norm_le_one b
  have h4 := hPη x a
  have h5 := hQη y b
  have hη : 0 ≤ η := (norm_nonneg _).trans hψη
  calc ‖P x a - P' x a‖ * ‖Q y b‖ + ‖P' x a‖ * ‖Q y b - Q' y b‖ +
        2 * (‖P' x a‖ * ‖Q' y b‖) * ‖(toLp 2 (ψ - ψ') : EuclideanSpace ℂ (dA × dB))‖
      ≤ η * 1 + 1 * η + 2 * (1 * 1) * η := by gcongr
    _ = 4 * η := by ring

end Born

/-! ## Exact strategies -/

/-- The raw data of a tensor-product strategy with an unnormalized state: dimensions,
measurement operators, and a state vector. Whether the data describes a strategy is the separate
predicate `ExactStrategy.IsValid`, so that the data can be enumerated and validity checked. -/
structure ExactStrategy (X Y A B : Type*) where
  /-- The dimension of the first player's space. -/
  dA : ℕ
  /-- The dimension of the second player's space. -/
  dB : ℕ
  /-- The first player's measurement operators. -/
  PA : X → A → Matrix (Fin dA) (Fin dA) ℂ
  /-- The second player's measurement operators. -/
  PB : Y → B → Matrix (Fin dB) (Fin dB) ℂ
  /-- The (unnormalized) shared state. -/
  u : Fin dA × Fin dB → ℂ

namespace ExactStrategy

variable (c : ExactStrategy X Y A B)

/-- The data describes a strategy: projective measurements and a nonzero state. -/
structure IsValid : Prop where
  isPVM_A : ∀ x, IsPVM (c.PA x)
  isPVM_B : ∀ y, IsPVM (c.PB y)
  u_ne_zero : c.u ≠ 0

/-- All entries of the data lie in the subfield `K`. -/
def EntriesIn (K : Subfield ℂ) : Prop :=
  (∀ x a, MIPRE.ValueApprox.EntriesIn K (c.PA x a)) ∧
    (∀ y b, MIPRE.ValueApprox.EntriesIn K (c.PB y b)) ∧ ∀ i, c.u i ∈ K

/-- The value of the data in `G`: the Born-rule sum for the unnormalized state, divided by
`‖u‖²`. A rational function of the entries. -/
noncomputable def value (G : Game X Y A B) : ℝ :=
  bornValue G c.PA c.PB c.u / (star c.u ⬝ᵥ c.u).re

/-- The normalized state `u / ‖u‖`. -/
noncomputable def ψ : Fin c.dA × Fin c.dB → ℂ :=
  ((‖(toLp 2 c.u : EuclideanSpace ℂ (Fin c.dA × Fin c.dB))‖ : ℂ)⁻¹) • c.u

theorem star_smul_dotProduct_mulVec_smul {n : Type*} [Fintype n] (k : ℂ) (T : Matrix n n ℂ)
    (u : n → ℂ) : star (k • u) ⬝ᵥ (T *ᵥ (k • u)) = (star k * k) * (star u ⬝ᵥ (T *ᵥ u)) := by
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    mul_assoc]

theorem star_ofReal_inv_mul_self (r : ℝ) :
    star ((r : ℂ)⁻¹) * (r : ℂ)⁻¹ = (((r ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

omit [Fintype X] [Fintype Y] in
theorem ψ_unit (hc : c.IsValid) : star c.ψ ⬝ᵥ c.ψ = 1 := by
  have hu : (toLp 2 c.u : EuclideanSpace ℂ (Fin c.dA × Fin c.dB)) ≠ 0 := by
    simpa using hc.u_ne_zero
  have hr : ‖(toLp 2 c.u : EuclideanSpace ℂ (Fin c.dA × Fin c.dB))‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  unfold ψ
  rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    star_ofReal_inv_mul_self, dotProduct_star_self_eq_ofReal, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (pow_ne_zero 2 hr), Complex.ofReal_one]

omit [Fintype X] [Fintype Y] in
theorem norm_toLp_ψ (hc : c.IsValid) :
    ‖(toLp 2 c.ψ : EuclideanSpace ℂ (Fin c.dA × Fin c.dB))‖ = 1 :=
  norm_toLp_eq_one_of_dotProduct (c.ψ_unit hc)

/-- The tensor-product strategy described by valid data: normalize the state. -/
noncomputable def toStrategy (G : Game X Y A B) (hc : c.IsValid) : TensorProductStrategy G where
  dA := c.dA
  dB := c.dB
  ψ := c.ψ
  ψ_unit := c.ψ_unit hc
  PA := { M := c.PA
          selfAdjoint := fun x a => (hc.isPVM_A x).conjTranspose_eq a
          projective := fun x a => (hc.isPVM_A x).mul_self a
          normalized := fun x => (hc.isPVM_A x).sum_eq_one }
  PB := { M := c.PB
          selfAdjoint := fun y b => (hc.isPVM_B y).conjTranspose_eq b
          projective := fun y b => (hc.isPVM_B y).mul_self b
          normalized := fun y => (hc.isPVM_B y).sum_eq_one }

/-- The value of the data is the value of the strategy it describes. -/
theorem value_toStrategy (G : Game X Y A B) (hc : c.IsValid) :
    (c.toStrategy G hc).value = c.value G := by
  rw [TensorProductStrategy.value_eq_bornValue]
  show bornValue G c.PA c.PB c.ψ = c.value G
  unfold value bornValue
  simp only [Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  unfold ψ
  rw [star_smul_dotProduct_mulVec_smul, star_ofReal_inv_mul_self, Complex.re_ofReal_mul,
    ← norm_sq_toLp]
  ring

theorem value_eq_bornValue_ψ (G : Game X Y A B) (hc : c.IsValid) :
    c.value G = bornValue G c.PA c.PB c.ψ :=
  (c.value_toStrategy G hc).symm

/-- Soundness: the value of valid data is at most the quantum value. -/
theorem value_le_quantumValue (G : Game X Y A B) (hc : c.IsValid) :
    c.value G ≤ quantumValue G := by
  rw [← c.value_toStrategy G hc]
  exact le_ciSup (TensorProductStrategy.bddAbove_range_value G) (c.toStrategy G hc)

end ExactStrategy

/-! ## Density -/

/-- Every tensor-product strategy is approximated, in value, by valid Gaussian-rational exact
strategies: round the measurements to exact Gaussian-rational projective measurements and the
state entrywise. -/
theorem exists_exactStrategy_value_gt (G : Game X Y A B) (S : TensorProductStrategy G) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c : ExactStrategy X Y A B, c.IsValid ∧ c.EntriesIn GaussianRat ∧
      S.value - ε < c.value G := by
  classical
  -- the rounding parameter
  set N : ℝ := Fintype.card A * Fintype.card B with hN
  have hN0 : 0 ≤ N := by positivity
  set η : ℝ := min 1 (ε / (4 * N + 1)) with hη_def
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : N * (4 * η) < ε := by
    calc N * (4 * η) ≤ N * (4 * (ε / (4 * N + 1))) := by gcongr; exact min_le_right _ _
      _ = ε * (4 * N / (4 * N + 1)) := by ring
      _ < ε * 1 := by
          gcongr
          rw [div_lt_one (by positivity)]
          linarith
      _ = ε := mul_one ε
  -- the measurements
  choose PA' hPA' hPA'K hPA'η using fun x => (S.PA.isPVM x).exists_entriesIn_norm_sub_le hη
  choose PB' hPB' hPB'K hPB'η using fun y => (S.PB.isPVM y).exists_entriesIn_norm_sub_le hη
  -- the state
  have hψnorm : ‖(toLp 2 S.ψ : EuclideanSpace ℂ (Fin S.dA × Fin S.dB))‖ = 1 :=
    norm_toLp_eq_one_of_dotProduct S.ψ_unit
  have hδ : 0 < η / (4 * (Fintype.card (Fin S.dA × Fin S.dB) + 1)) := by positivity
  obtain ⟨u, huK, huη⟩ := exists_forall_mem_norm_sub_le S.ψ hδ
  have huψ : ‖(toLp 2 (u - S.ψ) : EuclideanSpace ℂ (Fin S.dA × Fin S.dB))‖ ≤ η / 4 := by
    have hc : (0 : ℝ) ≤ Fintype.card (Fin S.dA × Fin S.dB) := by positivity
    calc ‖(toLp 2 (u - S.ψ) : EuclideanSpace ℂ (Fin S.dA × Fin S.dB))‖
        ≤ Fintype.card (Fin S.dA × Fin S.dB) *
            (η / (4 * (Fintype.card (Fin S.dA × Fin S.dB) + 1))) :=
          norm_toLp_le_card_mul_of_forall_norm_le hδ.le fun i => by
            rw [Pi.sub_apply, norm_sub_rev]
            exact huη i
      _ ≤ η / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, zero_sub, toLp_neg, norm_neg, hψnorm] at huψ
    linarith
  -- assemble the data
  have hvalid : (⟨S.dA, S.dB, PA', PB', u⟩ : ExactStrategy X Y A B).IsValid := ⟨hPA', hPB', hu0⟩
  refine ⟨⟨S.dA, S.dB, PA', PB', u⟩, hvalid, ⟨hPA'K, hPB'K, huK⟩, ?_⟩
  rw [ExactStrategy.value_eq_bornValue_ψ _ G hvalid, TensorProductStrategy.value_eq_bornValue]
  have hψ' := ExactStrategy.norm_toLp_ψ _ hvalid
  have hψψ' : ‖(toLp 2 (S.ψ - (⟨S.dA, S.dB, PA', PB', u⟩ : ExactStrategy X Y A B).ψ) :
      EuclideanSpace ℂ (Fin S.dA × Fin S.dB))‖ ≤ η := by
    rw [toLp_sub, norm_sub_rev, ← toLp_sub]
    calc ‖(toLp 2 ((⟨S.dA, S.dB, PA', PB', u⟩ : ExactStrategy X Y A B).ψ - S.ψ) :
          EuclideanSpace ℂ (Fin S.dA × Fin S.dB))‖
        ≤ 2 * ‖(toLp 2 (u - S.ψ) : EuclideanSpace ℂ (Fin S.dA × Fin S.dB))‖ :=
          norm_toLp_normalize_sub_le u S.ψ hψnorm hu0
      _ ≤ 2 * (η / 4) := by gcongr
      _ ≤ η := by linarith
  have hb := abs_bornValue_sub_le G hPA' (fun y => S.PB.isPVM y) hPB' hψnorm hψ' hPA'η hPB'η hψψ'
  have := (abs_sub_le_iff.mp hb).1
  linarith

/-! ## The quantum value from below -/

/-- The projective measurement on `ℂ¹` that always answers `a₀`. -/
def pointMeasurement (X : Type*) {A : Type*} [Fintype A] [DecidableEq A] (a₀ : A) :
    ProjectiveMeasurement X A (Matrix (Fin 1) (Fin 1) ℂ) where
  M _ a := if a = a₀ then 1 else 0
  selfAdjoint _ a := by split_ifs <;> simp
  projective _ a := by split_ifs <;> simp
  normalized _ := by simp

/-- A strategy exists as soon as both answer alphabets are nonempty: one-dimensional spaces and
the measurements that always answer `a₀`, `b₀`. -/
theorem nonempty_tensorProductStrategy [Nonempty A] [Nonempty B] (G : Game X Y A B) :
    Nonempty (TensorProductStrategy G) := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty A›
  obtain ⟨b₀⟩ := ‹Nonempty B›
  refine ⟨⟨1, 1, fun _ => 1, ?_, pointMeasurement X a₀, pointMeasurement Y b₀⟩⟩
  show ∑ _i : Fin 1 × Fin 1, star (1 : ℂ) * 1 = 1
  simp

/-- **The quantum value from below.** `val*(G) > t` if and only if some valid exact strategy
with Gaussian-rational entries has value greater than `t`. This is the mathematical content of
`lem:value-lower-approx`: the right-hand side is a semi-decidable condition, as the
Gaussian-rational data can be enumerated, validity is a finite set of polynomial identities in
the entries, and the value is a rational function of them. -/
theorem lt_quantumValue_iff [Nonempty A] [Nonempty B] (G : Game X Y A B) (t : ℝ) :
    t < quantumValue G ↔
      ∃ c : ExactStrategy X Y A B, c.IsValid ∧ c.EntriesIn GaussianRat ∧ t < c.value G := by
  constructor
  · intro ht
    have := nonempty_tensorProductStrategy G
    obtain ⟨S, hS⟩ :=
      (lt_ciSup_iff (TensorProductStrategy.bddAbove_range_value G)).mp ht
    obtain ⟨c, hc, hcK, hlt⟩ := exists_exactStrategy_value_gt G S (sub_pos.mpr hS)
    exact ⟨c, hc, hcK, by linarith⟩
  · rintro ⟨c, hc, -, hlt⟩
    exact hlt.trans_le (c.value_le_quantumValue G hc)

end MIPRE.ValueApprox


