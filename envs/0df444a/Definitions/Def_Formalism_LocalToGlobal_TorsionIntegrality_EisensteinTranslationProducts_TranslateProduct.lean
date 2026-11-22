-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:23.238854+00:00
-- url     : https://prove2.me/theorems/3f5b7621-afb2-4c05-9608-68fce4a22a22
-- title:
--   Translate Product
-- statement:
--   Definitions and structural lemmas for Translate Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/TranslateProduct.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have h := L.indep
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp this).resolve_left hc
def LatticeOnly : Prop :=
  ∀ L L' : PeriodPair, L.lattice = L'.lattice →
    wZeta L = wZeta L' ∧ wSigma L = wSigma L' ∧ wEta L = wEta L' ∧ area L = area L' ∧ s2 L = s2 L' ∧
    sgStar L = sgStar L' ∧ L.weierstrassP = L'.weierstrassP ∧ L.g₂ = L'.g₂ ∧ L.g₃ = L'.g₃
def Homogeneity : Prop :=
  ∀ (L : PeriodPair) (c : ℂ) (hc : c ≠ 0),
    (∀ z, z ∈ (scalePair L c hc).lattice ↔ c⁻¹ * z ∈ L.lattice) ∧
    (∀ z, wZeta (scalePair L c hc) (c * z) = c⁻¹ * wZeta L z) ∧
    (∀ z, wSigma (scalePair L c hc) (c * z) = c * wSigma L z) ∧
    (∀ z, (scalePair L c hc).weierstrassP (c * z) = (c ^ 2)⁻¹ * L.weierstrassP z) ∧
    (∀ z, wEta (scalePair L c hc) (c * z) = c⁻¹ * wEta L z) ∧
    area (scalePair L c hc) = ‖c‖ ^ 2 * area L ∧
    s2 (scalePair L c hc) = (c ^ 2)⁻¹ * s2 L ∧
    (∀ z, sgStar (scalePair L c hc) (c * z) = c * sgStar L z) ∧
    (∀ t z, th0 (scalePair L c hc) (c * t) (c * z) = th0 L t z) ∧
    (scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ ∧ (scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃
def MulStable (L : PeriodPair) (α : ℂ) : Prop := ∀ ω ∈ L.lattice, α * ω ∈ L.lattice
def IsKerReps (L : PeriodPair) (α : ℂ) (S : Finset ℂ) : Prop :=
  (∀ P ∈ S, α * P ∈ L.lattice ∧ P ∉ L.lattice) ∧
  (∀ P ∈ S, ∀ Q ∈ S, P - Q ∈ L.lattice → P = Q) ∧
  (∀ z, α * z ∈ L.lattice → z ∉ L.lattice → ∃ P ∈ S, z - P ∈ L.lattice)
def KerRepsExist : Prop :=
  ∀ (L : PeriodPair) (α : ℂ), α ≠ 0 → MulStable L α → ∃ S : Finset ℂ, IsKerReps L α S
def KerRepsCard : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ((S.card : ℝ) + 1) = Complex.normSq α
def MulStableIntegral : Prop :=
  ∀ (L : PeriodPair) (α : ℂ), MulStable L α →
    ∃ t n : ℤ, α + conj α = (t : ℂ) ∧ α * conj α = (n : ℂ) ∧ α ^ 2 - (t : ℂ) * α + (n : ℂ) = 0
def IsogenyP : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ∀ z, α * z ∉ L.lattice →
      α ^ 2 * L.weierstrassP (α * z)
        = L.weierstrassP z + ∑ P ∈ S, (L.weierstrassP (z + P) - L.weierstrassP P)
def IsogenySigma : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ∀ z, z ∉ L.lattice →
      sgStar L (α * z) ^ 2
        = α ^ 2 * sgStar L z ^ (2 * (S.card + 1)) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP P)
def QuasiPeriodConstIsogeny : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    (α ^ 2 - (Complex.normSq α : ℂ)) * s2 L = ∑ P ∈ S, L.weierstrassP P
def HalfShift : Prop :=
  ∀ (L : PeriodPair) (t z : ℂ), t ∉ L.lattice → 2 * t ∈ L.lattice → z ∉ L.lattice → z + t ∉ L.lattice →
    (L.weierstrassP (z + t) - L.weierstrassP t) * (L.weierstrassP z - L.weierstrassP t)
      = 3 * L.weierstrassP t ^ 2 - L.g₂ / 4
def PSecond : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice →
    HasDerivAt L.derivWeierstrassP (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z
def TranslateProduct : Prop :=
  ∀ (L : PeriodPair) (P Q z : ℂ), Q ∉ L.lattice → z + P ∉ L.lattice →
    opU L (P + Q) (sgStar L) z * opU L (P - Q) (sgStar L) z
      = opU L Q (sgStar L) 0 ^ 2 * (L.weierstrassP Q - L.weierstrassP (z + P))
        * opU L P (sgStar L) z ^ 2
end Formalism.L2.Th1.F


