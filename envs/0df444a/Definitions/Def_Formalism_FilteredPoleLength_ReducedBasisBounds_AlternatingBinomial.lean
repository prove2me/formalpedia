-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_AlternatingBinomial
-- name    : Formalism_FilteredPoleLength_ReducedBasisBounds_AlternatingBinomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:42.077831+00:00
-- url     : https://prove2.me/theorems/8663e3a7-f22a-4f56-81de-31b0fe7870ed
-- title:
--   Alternating Binomial
-- statement:
--   Definitions and structural lemmas for Alternating Binomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/ReducedBasisBounds/AlternatingBinomial.lean

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
open Real
def TieBoundN : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) →
    ∀ (Γ : AddSubgroup V) (x : V),
      (∀ y ∈ Γ, B x x / 2 ≤ B (x + y) (x + y) / 2) →
      ∀ g ∈ Γ, ∀ N : ℕ, 2 ≤ N →
        B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2 - B x x / 2 =
            (N : ℝ) * B x g + (N : ℝ) ^ 2 * (B g g / 2) ∧
        (N : ℝ) * ((N : ℝ) - 1) * (B g g / 2) ≤
            B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2 - B x x / 2 ∧
        (0 < B g g → B x x / 2 < B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2)
def FPrimeWeights : Prop :=
  ∀ (T D r nW n' c ap am : ℤ), 0 < T → 0 ≤ D →
    let T' := T + D + 2
    let cW := (c + 2) / T'
    let rem := (c + 2) % T'
    let apW := (ap - (D + 2) * nW - 2 * r) / T'
    let s₁ := (ap - (D + 2) * nW - 2 * r) % T'
    let amW := am / T'
    let s₂ := am % T'
    (c - T * cW = (D + 2) * cW + rem - 2 ∧ (1 ≤ cW → 0 ≤ c - T * cW)) ∧
    (ap - T * apW = (D + 2) * apW + (D + 2) * nW + 2 * r + s₁ ∧
      (0 ≤ apW → 0 ≤ nW → 1 ≤ r → 1 ≤ ap - T * apW)) ∧
    (am - T * amW = (D + 2) * amW + s₂ ∧ (0 ≤ amW → 0 ≤ am - T * amW) ∧
      (1 ≤ amW → 1 ≤ am - T * amW)) ∧
    (n' ≤ nW → r ≤ nW → 0 ≤ nW → (D + 3) * nW ≤ (D + 4) * nW - n' ∧ r ≤ (D + 4) * nW - n')
def RemClass : Prop :=
  ∀ (T D r nW nV f c ap am : ℤ), 0 < T → 0 ≤ D → 1 ≤ r → 2 ≤ nW → 1 ≤ f →
    let T' := T + D + 2
    let n' := nV - T * nW
    let cW := (c + 2) / T'
    let rem := (c + 2) % T'
    let apW := (ap - (D + 2) * nW - 2 * r) / T'
    let s₁ := (ap - (D + 2) * nW - 2 * r) % T'
    let amW := am / T'
    let s₂ := am % T'
    let nrem := nV - T' * nW - (2 * r - 2)
    (c - T' * cW + 2 = rem ∧ 0 ≤ rem ∧ rem < T') ∧
    ap - T' * apW = (D + 2) * nW + 2 * r + s₁ ∧
    am - T' * amW = s₂ ∧
    nrem = n' - (D + 2) * nW - 2 * r + 2 ∧
    (n' ≤ nW → nrem < 0) ∧
    (ap - T' * apW) + (am - T' * amW) + nrem - r + 1 = s₁ + s₂ + n' + 3 - r ∧
    s₁ + s₂ + n' + 3 - r < n' + 2 + 2 * T' ∧
    (8 * f * r + 4 ≤ n' → 0 < s₁ + s₂ + n' + 3 - r) ∧
    (-2 + (D + 2) * cW + rem = c - T * cW ∧
      (D + 2) * apW + (ap - T' * apW) = ap - T * apW ∧
      (D + 2) * amW + (am - T' * amW) = am - T * amW ∧
      (2 * r - 2) + (D + 2) * nW + nrem = n')
def JetGapColumns : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ v, 0 ≤ B v v) →
    ∀ (X : AddSubgroup V) (J ι : Type) [Fintype J] [Fintype ι] (b : J → V)
      (M₀ Cφ DF q μ : ℝ),
      (∀ j, ∀ w ∈ X, |B (b j) w| ≤ M₀ * (B w w / 2)) →
      (∀ j, B (b j) (b j) / 2 ≤ Cφ) →
      (∀ w ∈ X, w ≠ 0 → μ ≤ B w w / 2) → 0 < μ → 0 ≤ M₀ → DF * M₀ < q → 0 ≤ Cφ →
      ∀ e : J → ι → ℕ, (∑ j, ∑ k, (e j k : ℝ)) ≤ DF →
        (∀ z : ι → V, (∀ k, z k ∈ X) →
          |∑ k, B (∑ j, (e j k : ℝ) • b j) (z k)| ≤ DF * M₀ * ∑ k, B (z k) (z k) / 2) ∧
        (∀ z : ι → V, (∀ k, z k ∈ X) → z ≠ 0 →
          (q - DF * M₀) * μ ≤
            ∑ k, B (∑ j, (e j k : ℝ) • b j) (z k) + q * ∑ k, B (z k) (z k) / 2) ∧
        0 < (q - DF * M₀) * μ ∧
        ∑ k, B (∑ j, (e j k : ℝ) • b j) (∑ j, (e j k : ℝ) • b j) / 2 ≤ DF ^ 2 * Cφ
def AlternatingBinomial : Prop :=
  ∀ (σ R : Type) [Fintype σ] [DecidableEq σ] [CommRing R] (a : σ → ℕ) (T : σ → R),
    ∑ e ∈ Fintype.piFinset (fun j => Finset.range (a j + 1)),
        (-1 : R) ^ (∑ j, (a j - e j)) * ((∏ j, (a j).choose (e j) : ℕ) : R) *
          ∏ j, (1 + T j) ^ (e j) =
      ∏ j, T j ^ (a j)
def DescentNoLinearTerm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V) (w₀ w₀b : V →ₗ[ℝ] V),
    (∀ x y, B x y = B y x) → (∀ x y, B x (w₀ y) = B (w₀b x) y) → w₀ + w₀b = LinearMap.id →
    ∀ z, B z (w₀ z) = B z z / 2
def DescentCocycle : Prop :=
  ∀ (X Y M : Type) [AddCommGroup X] [AddCommGroup Y] [CommGroup M] (τ : X → Y → M)
    (lam : X →+ Y) (w₀ w₀b : X →+ X),
    (∀ x x' y, τ (x + x') y = τ x y * τ x' y) → (∀ x y y', τ x (y + y') = τ x y * τ x y') →
    (∀ z z', τ z' (lam (w₀ z)) = τ z (lam (w₀b z'))) → (∀ z, w₀ z + w₀b z = z) →
    ∀ z z', τ (z + z') (lam (w₀ (z + z'))) =
      τ z (lam (w₀ z)) * τ z' (lam (w₀ z')) * τ z (lam z')
def CBConstant : Prop :=
  ∀ (RR PP dp DF n₁ nW q g' : ℝ), 0 ≤ RR → 0 ≤ dp → 1 ≤ DF → 0 ≤ n₁ → n₁ ≤ nW → 0 < q →
    q ≤ g' → nW * dp ^ 4 / 4 + 2 * dp ^ 3 ≤ PP →
    (n₁ * dp * (RR * dp ^ 3) / (4 * g') + 2 * (RR * dp ^ 3) * DF ^ 2 / g' ≤
        (nW * dp ^ 4 / 4 + 2 * dp ^ 3 * DF ^ 2) * RR / q ∧
      (nW * dp ^ 4 / 4 + 2 * dp ^ 3 * DF ^ 2) * RR / q ≤ RR * PP * DF ^ 2 / q) ∧
    (∀ Xq : ℝ, Xq ≤ q → Xq ≤ g') ∧
    (∀ D g : ℝ, 0 ≤ D → (D + 4) * DF ≤ q - 2 → q ≤ g → DF < g - 1)
def NuStarSum : Prop :=
  ∀ (DF D q g₁ g₂ RR PP : ℝ), 1 ≤ DF → 0 ≤ D → 0 ≤ RR → 0 ≤ PP → 8 ≤ RR ^ 4 * PP ^ 3 →
    RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → (D + 4) * DF ≤ q - 2 → q ≤ g₁ → q ≤ g₂ →
    DF / (g₁ - 1) < 1 ∧ DF / (g₂ - 1) < 1 ∧
      DF * (Real.log g₁ / (g₁ - 1) + Real.log g₂ / (g₂ - 1)) < 1
def columnOperation {R : Type} [CommRing R] {i N : ℕ} (x : Fin i → Fin N → R) (a b : Fin i) :
    MvPolynomial (Fin i × Fin N) R →ₗ[R] MvPolynomial (Fin i × Fin N) R :=
  ∑ k, x a k • (MvPolynomial.pderiv (b, k) :
    Derivation R (MvPolynomial (Fin i × Fin N) R) (MvPolynomial (Fin i × Fin N) R)).toLinearMap
def columnOperationComposite {R : Type} [CommRing R] {i N : ℕ} (x : Fin i → Fin N → R) (c : ℕ)
    (s : Fin c → Equiv.Perm (Fin i)) :
    MvPolynomial (Fin i × Fin N) R →ₗ[R] MvPolynomial (Fin i × Fin N) R :=
  (Finset.univ : Finset (Fin c × Fin i)).toList.foldr
    (fun p acc => columnOperation x p.2 (s p.1 p.2) ∘ₗ acc) LinearMap.id
def DetPowerIdentity : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (i N c : ℕ) (x η : Fin i → Fin N → R),
    (∑ s : Fin c → Equiv.Perm (Fin i),
        (∏ t, ((Equiv.Perm.sign (s t) : ℤ) : R)) • columnOperationComposite x c s)
      (∏ b : Fin i, (MvPolynomial.C ((c.factorial : R)⁻¹) *
        (∑ k, MvPolynomial.C (η b k) * MvPolynomial.X (b, k)) ^ c)) =
    MvPolynomial.C ((Matrix.of fun a b : Fin i => ∑ k, η b k * x a k).det ^ c)
def DetProductRest : Prop :=
  ∀ (i c : ℕ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
    ((2 : ℝ) ^ c + ε) ^ i - (2 : ℝ) ^ (c * i) ≤ (i : ℝ) * ε * ((2 : ℝ) ^ c + 1) ^ i
def CovolAbsorb : Prop :=
  ∀ (A κ₀ φ : ℝ), 0 < A → 0 < κ₀ → 0 < φ →
    A * Real.log (κ₀ * φ) ≤ φ + A * Real.log (A * κ₀) ∧
    (∀ (i K PP lEt : ℝ), 0 ≤ i → K + A * Real.log (A * κ₀) ≤ PP →
      lEt ≤ i * (K + A * Real.log (κ₀ * φ) - 2 * π * φ) →
      lEt ≤ -i * ((2 * π - 1) * φ - PP)) ∧
    (∀ (RR dp lmax cov : ℝ) (d : ℕ), 0 ≤ lmax → cov ≤ lmax ^ d →
      lmax ^ 2 ≤ 4 * RR * dp ^ 2 * φ → cov ≤ (4 * RR * dp ^ 2 * φ) ^ ((d : ℝ) / 2))
def MinimumChainBounds : Prop :=
  ∀ (dp lmax2 φ RR PP r₁ r E0 minQ δ : ℝ), 0 ≤ dp → 0 ≤ φ → 0 ≤ RR → 1 ≤ r₁ → 0 ≤ r →
    minQ ≤ dp * lmax2 / (4 * r₁ ^ 2) → lmax2 ≤ 2 * RR * dp ^ 2 * φ → E0 ≤ r * minQ →
    r * dp ^ 3 ≤ PP →
    minQ ≤ RR * dp ^ 3 * φ / (2 * r₁ ^ 2) ∧ E0 ≤ r * RR * dp ^ 3 * φ / (2 * r₁ ^ 2) ∧
      E0 ≤ RR * PP * φ ∧
      (φ ≤ r₁ ^ 4 * E0 → φ ≤ 2 * r₁ ^ 4 * E0 / 2) ∧
      (2 * r₁ ^ 4 * r) * δ - 2 * r₁ ^ 4 * E0 = 2 * r₁ ^ 4 * (r * δ - E0)
end Formalism.LatticeBaseChangeAlt


