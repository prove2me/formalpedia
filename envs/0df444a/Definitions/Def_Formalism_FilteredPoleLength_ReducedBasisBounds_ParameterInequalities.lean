-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ParameterInequalities
-- name    : Formalism_FilteredPoleLength_ReducedBasisBounds_ParameterInequalities
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:27.01983+00:00
-- url     : https://prove2.me/theorems/917caf2a-5694-467f-af12-fd95721bc9b8
-- title:
--   Parameter Inequalities
-- statement:
--   Definitions and structural lemmas for Parameter Inequalities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/ReducedBasisBounds/ParameterInequalities.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Finset Matrix
open scoped RealInnerProductSpace BigOperators
def CompletingSquare : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, 0 ≤ B x x) →
    ∀ (q : ℝ), 0 < q → ∀ χ : V,
      (∀ u : V, -(B χ χ / 2) / q ≤ B χ u + q * (B u u / 2)) ∧
      B χ ((-(1 / q)) • χ) + q * (B ((-(1 / q)) • χ) ((-(1 / q)) • χ) / 2) = -(B χ χ / 2) / q
def CosetMinUnique : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) →
    ∀ (X : AddSubgroup V) (q : ℝ) (χ : V),
      (∀ z : V, B (χ + q • z) (χ + q • z) / 2 - B χ χ / 2 = q * (B χ z + q * (B z z / 2))) ∧
      (0 < q → (∀ z ∈ X, z ≠ 0 → |B χ z| < q * (B z z / 2)) →
        ∀ z ∈ X, z ≠ 0 → B χ χ / 2 < B (χ + q • z) (χ + q • z) / 2)
def ReducedBasisNear : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) →
    ∀ (S : AddSubgroup V) (b w : V), w ∈ S →
      (∀ s ∈ S, B (b - w) (b - w) ≤ B (b - s) (b - s)) →
      (∀ z ∈ S, |B (b - w) z| ≤ B z z / 2) ∧ B (b - w) (b - w) ≤ B b b
def ReducedBasisBound : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, 0 ≤ B x x) →
    ∀ (X S : AddSubgroup V) (b w : V) (d' : ℝ), S ≤ X → b ∈ X → w ∈ S → 1 ≤ d' →
      (∀ s ∈ S, B (b - w) (b - w) ≤ B (b - s) (b - s)) →
      (∀ z ∈ X, z ∉ S → B b b / 2 / d' ≤ B z z / 2) →
      ∀ z ∈ X, |B (b - w) z| ≤ 2 * Real.sqrt d' * (B z z / 2)
def CharacterBounds : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, 0 ≤ B x x) →
    ∀ (X : AddSubgroup V) (ι : Type) [Fintype ι] (e : ι → ℕ) (b : ι → V) (DF M0 Cφ : ℝ),
      (∑ i, (e i : ℝ)) ≤ DF → 0 ≤ M0 → 0 ≤ Cφ →
      (∀ i, ∀ z ∈ X, |B (b i) z| ≤ M0 * (B z z / 2)) →
      (∀ i, B (b i) (b i) / 2 ≤ Cφ) →
      (∀ z ∈ X, |B (∑ i, (e i : ℝ) • b i) z| ≤ DF * M0 * (B z z / 2)) ∧
      B (∑ i, (e i : ℝ) • b i) (∑ i, (e i : ℝ) • b i) / 2 ≤ DF ^ 2 * Cφ
def JetJoint : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, 0 ≤ B x x) →
    ∀ (X : AddSubgroup V) (ι : Type) [Fintype ι] (e : ι → ℕ) (b : ι → V) (DF M0 q : ℝ),
      (∑ i, (e i : ℝ)) ≤ DF → 0 ≤ M0 → 0 < q → DF * M0 < q →
      (∀ z ∈ X, z ≠ 0 → 0 < B z z) →
      (∀ i, ∀ z ∈ X, |B (b i) z| ≤ M0 * (B z z / 2)) →
      ∀ z ∈ X, z ≠ 0 →
        B (∑ i, (e i : ℝ) • b i) (∑ i, (e i : ℝ) • b i) / 2 <
          B ((∑ i, (e i : ℝ) • b i) + q • z) ((∑ i, (e i : ℝ) • b i) + q • z) / 2
def TieBound : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) →
    ∀ (Γ : AddSubgroup V) (x : V) (r : ℝ),
      (∀ g ∈ Γ, B x x / 2 ≤ B (x + g) (x + g) / 2) →
      ∀ g ∈ Γ,
        r ^ 2 * (r ^ 2 - 1) * (B g g / 2) ≤
            B (x + r ^ 2 • g) (x + r ^ 2 • g) / 2 - B x x / 2 ∧
        (1 < r ^ 2 → 0 < B g g → B x x / 2 < B (x + r ^ 2 • g) (x + r ^ 2 • g) / 2)
def EtFactorCount : Prop :=
  ∀ (α : Type) (G : Finset α) (v : α → ℝ) (φ : ℝ) (r1 r : ℕ) (i : ℝ), 0 < r1 → 0 ≤ i →
    (G.card : ℝ) = 2 * (r1 : ℝ) ^ 4 * i →
    (∀ g ∈ G, φ / (r1 : ℝ) ^ 4 ≤ v g) →
    2 * i * φ ≤ ∑ g ∈ G, v g ∧
    (0 < i → ((r : ℝ) * (G.card : ℝ)) / i = 2 * (r1 : ℝ) ^ 4 * (r : ℝ))
def EtCombination : Prop :=
  ∀ (σ : Type) [Fintype σ] (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    (κ : Type) (C : Finset κ) (ℓ : κ → σ → R),
    (∀ c ∈ C, ∃ s, ℓ c s ≠ 0) →
    ∃ x : σ → ℕ, (∀ s, x s ≤ C.card) ∧ ∀ c ∈ C, ∑ s, (x s : R) * ℓ c s ≠ 0
def TraceDomination : Prop :=
  ∀ (n : ℕ) (A P : Matrix (Fin n) (Fin n) ℝ), A.PosSemidef → P.PosDef →
    ∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ (P⁻¹ * A).trace * (x ⬝ᵥ (P *ᵥ x))
def OrderChain : Prop :=
  ∀ (lmax2 pairing μ l1sq d' RR : ℝ), 0 ≤ pairing → 0 < RR → 0 < l1sq →
    lmax2 ≤ 2 * pairing * μ → μ * l1sq ≤ d' ^ 2 → 1 / RR ≤ l1sq →
    lmax2 ≤ 2 * RR * d' ^ 2 * pairing
def GaussUnfold : Prop :=
  ∀ (d : ℕ) (q : ℝ), 0 < q → ∀ c : EuclideanSpace ℝ (Fin d),
    ∫ u : EuclideanSpace ℝ (Fin d), Real.exp (-(4 * Real.pi * inner ℝ c u) - 2 * q * Real.pi * ‖u‖ ^ 2) =
      (2 * q) ^ (-(d : ℝ) / 2) * Real.exp (2 * Real.pi * ‖c‖ ^ 2 / q)
def PackingCount : Prop :=
  ∀ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin n))) (δ R : ℝ), 0 < δ → δ ≤ R →
    (∀ x ∈ P, ‖x‖ ≤ R) → (∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y) →
    (P.card : ℝ) ≤ (3 * R / δ) ^ n
def DetPerturbation : Prop :=
  ∀ (𝕜 : Type) [NormedField 𝕜] (i : ℕ) (κ : Type) [Fintype κ] (w : κ → Fin i → 𝕜)
    (σ₀ : Fin i → κ) (ε : Fin i → κ → 𝕜) (Δmax : ℝ),
    (∀ σ : Fin i → κ, ‖(Matrix.of fun a j => w (σ j) a).det‖ ≤ Δmax) →
    ‖(Matrix.of fun a j => (w (σ₀ j) + ∑ k, ε j k • w k) a).det -
        (Matrix.of fun a j => w (σ₀ j) a).det‖ ≤
      ((∏ j, (1 + ∑ k, ‖ε j k‖)) - 1) * Δmax
def DetPerturbNumeric : Prop :=
  ∀ ρ : ℕ, 1 ≤ ρ → (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ - 1 ≤ 1 / 2
def CauchyBinetMax : Prop :=
  ∀ (i N r : ℕ) (M : Matrix (Fin i) (Fin N) ℂ), M * Mᴴ = 1 → N ≤ r →
    ∃ s : Fin i → Fin N, StrictMono s ∧ (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(M.submatrix id s).det‖
def RadiusChoice : Prop :=
  ∀ (c q A : ℝ), 0 < c → 0 < q → 0 ≤ A →
    q * Real.pi * (c / (2 * Real.pi * A + Real.sqrt (q * c))) ^ 2 / 2 ≤ Real.pi * c / 2 ∧
    2 * Real.pi * (c / (2 * Real.pi * A + Real.sqrt (q * c))) * A ≤ c
def FloorDivisionGaps : Prop :=
  ∀ (T D r nW c a am : ℤ), 0 < T → 0 ≤ D → 0 ≤ r →
    ((T + D + 2 + 2) * ((c + 2) / (T + D + 2)) - c =
        2 * ((c + 2) / (T + D + 2)) + 2 - (c + 2) % (T + D + 2) ∧
      (T + D + 2 + 2 * r ≤ (c + 2) / (T + D + 2) →
        0 ≤ 2 * ((c + 2) / (T + D + 2)) + 2 - (c + 2) % (T + D + 2))) ∧
    ((T + D + 2 + 2) * ((a - (D + 2) * nW - 2 * r) / (T + D + 2)) - a =
        2 * ((a - (D + 2) * nW - 2 * r) / (T + D + 2)) - (D + 2) * nW - 2 * r -
          (a - (D + 2) * nW - 2 * r) % (T + D + 2) ∧
      (19 * T ≤ 10 * ((a - (D + 2) * nW - 2 * r) / (T + D + 2)) → (D + 2) * nW + 2 * r ≤ T →
        5 * (D + 2) ≤ 9 * T →
        1 ≤ 2 * ((a - (D + 2) * nW - 2 * r) / (T + D + 2)) - (D + 2) * nW - 2 * r -
          (a - (D + 2) * nW - 2 * r) % (T + D + 2))) ∧
    ((T + D + 2 + 2) * (am / (T + D + 2)) - am = 2 * (am / (T + D + 2)) - am % (T + D + 2) ∧
      (19 * T ≤ 10 * (am / (T + D + 2)) → 5 * (D + 2) ≤ 9 * T →
        1 ≤ 2 * (am / (T + D + 2)) - am % (T + D + 2)))
def LastEntryL : Prop :=
  ∀ (T D r nW a : ℤ), 0 < T → 0 ≤ D → 0 ≤ r → 0 ≤ nW →
    2 * T ^ 2 ≤ a → (D + 2) * nW + 2 * r ≤ T → 40 * (D + 2) ≤ T →
    19 * T ≤ 10 * ((a - (D + 2) * nW - 2 * r) / (T + D + 2))
def LastEntryLMinus : Prop :=
  ∀ (T D am : ℤ), 0 < T → 0 ≤ D → 2 * T ^ 2 ≤ am → 40 * (D + 2) ≤ T →
    19 * T ≤ 10 * (am / (T + D + 2))
def ParameterInequalities : Prop :=
  ∀ (q RR PP DF M0 T g0 Cd : ℝ), 1 ≤ RR → 1 ≤ PP → 1 ≤ DF → 0 ≤ M0 → 0 ≤ T → 0 ≤ g0 →
    (M0 < PP → RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → DF * M0 < q) ∧
    (0 < q → T * g0 * RR * PP * DF ^ 2 ≤ q → T * (RR * PP * DF ^ 2 / q) * g0 ≤ 1) ∧
    (0 < q → 2 * Cd ≤ RR * PP → 2 * Cd * DF ^ 2 / q ≤ RR * PP * DF ^ 2 / q)
end Formalism.LatticeBaseChangeAlt


