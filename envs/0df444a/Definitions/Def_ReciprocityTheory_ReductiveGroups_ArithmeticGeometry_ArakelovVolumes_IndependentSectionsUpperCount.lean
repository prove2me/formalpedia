-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IndependentSectionsUpperCount
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IndependentSectionsUpperCount
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:34.917351+00:00
-- url     : https://prove2.me/theorems/3844ead5-6bae-49a3-afb8-40286dafd2e3
-- title:
--   Independent Sections Upper Count
-- statement:
--   Definitions and structural lemmas for Independent Sections Upper Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IndependentSectionsUpperCount.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_BasePsiLeviLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetIndepStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR
open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
noncomputable section
def mono {n : ℕ} {ι Y : Type*} (s : Fin n → ι → Y → ℂ) (α : Fin n → ℕ) (j : ι) (y : Y) : ℂ :=
  ∏ k, s k j y ^ α k
def lead {n δ : ℕ} {ι Y : Type*} (s : Fin n → ι → Y → ℂ) (w0 : ι → Y → ℂ)
    (t : Fin δ → ι → Y → ℂ) (T a0 : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) : ι → Y → ℂ :=
  fun j y => ∑ α ∈ multiLt n a0, ∑ k,
    cc α k * mono s α j y * w0 j y ^ (T - ∑ q, α q) * t k j y
def ExistsPointLeviLogNormSqPos (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (C : Cusp A) (X : ArchIn A C),
    Continuous C.la1 → (∀ ε : ℝ, 0 < ε → IsCompact {y | ε ≤ C.la1 y}) →
    ∃ y, ∀ ξ : Fin n → ℂ, ξ ≠ 0 →
      0 < A.leviAt (A.pick y) (fun x => Real.log (∑ k, ‖X.w k (A.pick y) x‖ ^ 2)) y ξ
def DeterminantLatticeStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (C : Cusp A) (X : ArchIn A C) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ),
    FlatDatum A C X w0 s De → ∀ v : Y → ℂ, ∃ F : ι → Y → ℂ,
      A.IsSec X.Fp F ∧ Bdd A X.Fp F ∧ C.van X.Fp 0 F ∧ ∀ P ∈ A.zeroSet s, F (A.pick P) P = v P
def EigenIntegralityStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (C : Cusp A) (X : ArchIn A C) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ) (δ : ℕ) (t : Fin δ → ι → Y → ℂ),
    FlatDatum A C X w0 s De → (∀ k, A.IsSec X.Fp (t k)) → (∀ k, Bdd A X.Fp (t k)) →
    IsValBasis A s δ t →
    ∀ f : ι → Y → ℂ, A.IsSec (X.Fp + X.T • X.L) f →
      ∫⁻ y, ENNReal.ofReal (A.nsq (X.Fp + X.T • X.L) f y * A.sqn X.L X.w y ^ (-(X.T : ℝ))) ∂A.mu
        < ⊤ →
      ∃ (cc : (Fin n → ℕ) → Fin δ → ℂ) (h : (Fin n → ℕ) → ι → Y → ℂ),
        (∀ α ∈ Finset.Nat.antidiagonalTuple n (X.T - n),
          A.IsSec (X.Fp + n • X.L) (h α) ∧ Bdd A (X.Fp + n • X.L) (h α) ∧
            C.van (X.Fp + n • X.L) 0 (h α)) ∧
        ∀ j y, y ∈ (A.chart j).source →
          f j y = lead s w0 t X.T (X.T - n) cc j y +
            ∑ α ∈ Finset.Nat.antidiagonalTuple n (X.T - n), mono s α j y * h α j y
def BoundedSectionIntegrable (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (C : Cusp A) (X : ArchIn A C) (F : ι → Y → ℂ),
    A.IsSec (X.Fp + X.T • X.L) F → Bdd A (X.Fp + X.T • X.L) F → C.van (X.Fp + X.T • X.L) X.c1 F →
    ∫⁻ y, ENNReal.ofReal (A.nsq (X.Fp + X.T • X.L) F y * A.sqn X.L X.w y ^ (-(X.T : ℝ))) ∂A.mu < ⊤
def IndependentSectionsUpperCount (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (C : Cusp A) (X : ArchIn A C) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ),
    FlatDatum A C X w0 s De → ∀ (r : ℕ) (f : Fin r → ι → Y → ℂ),
      (∀ q, A.IsSec (X.Fp + X.T • X.L) (f q)) → (∀ q, Bdd A (X.Fp + X.T • X.L) (f q)) →
      (∀ a : Fin r → ℂ, (∀ j y, y ∈ (A.chart j).source → ∑ q, a q * f q j y = 0) → a = 0) →
      r ≤ (A.zeroSet s).ncard * (X.T + 2 * n + 6).choose n
def IndependentSectionsLowerCount (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (C : Cusp A) (X : ArchIn A C) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ),
    FlatDatum A C X w0 s De →
    ∃ f : Fin ((A.zeroSet s).ncard * (X.T + n).choose n) → ι → Y → ℂ,
      (∀ q, A.IsSec (X.Fp + X.T • X.L) (f q) ∧ Bdd A (X.Fp + X.T • X.L) (f q) ∧
        C.van (X.Fp + X.T • X.L) X.c1 (f q)) ∧
      ∀ a : Fin ((A.zeroSet s).ncard * (X.T + n).choose n) → ℂ,
        (∀ j y, y ∈ (A.chart j).source → ∑ q, a q * f q j y = 0) → a = 0
def LeadingSectionsIndependent (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (C : Cusp A) (X : ArchIn A C) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ) (δ : ℕ) (t : Fin δ → ι → Y → ℂ),
    FlatDatum A C X w0 s De → (∀ k, A.IsSec X.Fp (t k)) → IsValBasis A s δ t →
    ∀ cc : (Fin n → ℕ) → Fin δ → ℂ,
      (∀ P ∈ A.zeroSet s, A.VanishOrd (lead s w0 t X.T (X.T - n) cc) P (X.T - n)) →
      ∀ α ∈ multiLt n (X.T - n), ∀ k, cc α k = 0
end
end ReciprocityTheory.ChartRestriction.G.AR


