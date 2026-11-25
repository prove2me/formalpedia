-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLocalizeBundle
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLocalizeBundle
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:27:41.633342+00:00
-- url     : https://prove2.me/theorems/5f57dfa3-e848-5bce-b644-8c25167a076b
-- title:
--   PLocalize Bundle
-- statement:
--   Definitions and structural lemmas for PLocalize Bundle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLocalizeBundle.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeBundleSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
noncomputable section
universe u u' w
section BaseChange
variable {S : Type u} [CommRing S] {O : Type u'} [CommRing O] [Algebra S O]
  {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem map_mem_monos_base {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    map (algebraMap S O) s ∈ monos (S := O) I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]
    exact Submonoid.subset_closure ⟨i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
theorem mem_chartRing_base {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ chartRing O x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  exact ⟨map (algebraMap S O) f, map (algebraMap S O) s, e, map_mem_monos_base hs, hf.map _,
    hse.map _, by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩
theorem smul_mem_span_base {I : Chart x} (P : Set Ω) (a : chartRing S x I) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing O x I) P) : a • y ∈ Submodule.span (chartRing O x I) P := by
  have : a • y = (⟨(a : Ω), mem_chartRing_base a.2⟩ : chartRing O x I) • y := by
    rw [chartRing_smul_def, chartRing_smul_def]
  rw [this]
  exact Submodule.smul_mem _ _ hy
theorem span_base_span (I : Chart x) (P : Set Ω) :
    Submodule.span (chartRing O x I) (Submodule.span (chartRing S x I) P : Set Ω) =
      Submodule.span (chartRing O x I) P := by
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.span_induction
      (p := fun y _ => y ∈ Submodule.span (chartRing O x I) P) ?_ ?_ ?_ ?_ hy
    · intro z hz; exact Submodule.subset_span hz
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact smul_mem_span_base P a hz
  · exact Submodule.span_mono Submodule.subset_span
theorem isUnit_base {I J : Chart x} (h : I.1 ⊆ J.1) {a : chartRing S x I}
    (ha : IsUnit (chartIncl h a)) :
    IsUnit (chartIncl h (⟨(a : Ω), mem_chartRing_base a.2⟩ : chartRing O x I)) := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp ha
  refine isUnit_iff_exists_inv.mpr ⟨⟨(v : Ω), mem_chartRing_base v.2⟩, Subtype.ext ?_⟩
  have := congrArg Subtype.val hv
  change (a : Ω) * (v : Ω) = 1 at this
  change (a : Ω) * (v : Ω) = 1
  exact this
theorem LocalizeBundle.mem_iff_baseChange (M : LineBundle S x) (I J : Chart x) (h : I.1 ⊆ J.1)
    (y : Ω) :
    y ∈ (M.toSubSystem.baseChange O).sub J ↔
      ∃ a : chartRing O x I, IsUnit (chartIncl h a) ∧
        (a : Ω) • y ∈ (M.toSubSystem.baseChange O).sub I := by
  constructor
  · intro hy
    change y ∈ Submodule.span (chartRing O x J) (M.sub J : Set Ω) at hy
    let T : Submodule (chartRing O x J) Ω :=
      { carrier := {y | ∃ a : chartRing O x I, IsUnit (chartIncl h a) ∧
          (a : Ω) • y ∈ Submodule.span (chartRing O x I) (M.sub I : Set Ω)}
        add_mem' := by
          rintro y₁ y₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
          refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
          have : ((a₁ * a₂ : chartRing O x I) : Ω) • (y₁ + y₂) =
              a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
            change (a₁ : Ω) * a₂ * (y₁ + y₂) = (a₂ : Ω) * ((a₁ : Ω) * y₁) + (a₁ : Ω) * ((a₂ : Ω) * y₂)
            ring
          rw [this]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
        zero_mem' := ⟨1, by rw [map_one]; exact isUnit_one, by
          rw [smul_zero]; exact Submodule.zero_mem _⟩
        smul_mem' := by
          rintro b y ⟨a, ha, hay⟩
          obtain ⟨c, hc, hcb⟩ := exists_isUnit_mul_mem (S := O) h b
          refine ⟨c * a, by rw [map_mul]; exact hc.mul ha, ?_⟩
          have : ((c * a : chartRing O x I) : Ω) • (b • y) =
              (⟨(c : Ω) * b, hcb⟩ : chartRing O x I) • ((a : Ω) • y) := by
            change (c : Ω) * a * ((b : Ω) * y) = (c : Ω) * b * ((a : Ω) * y)
            ring
          rw [this]
          exact Submodule.smul_mem _ _ hay }
    have hle : Submodule.span (chartRing O x J) (M.sub J : Set Ω) ≤ T := by
      refine Submodule.span_le.mpr fun m hm => ?_
      obtain ⟨a, ha, ham⟩ := (M.mem_iff I J h m).mp hm
      exact ⟨⟨(a : Ω), mem_chartRing_base a.2⟩, isUnit_base h ha, Submodule.subset_span ham⟩
    exact hle hy
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hJ := (M.toSubSystem.baseChange O).mono I J h _ hay
    have hinv : ((↑u⁻¹ : chartRing O x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy : y = (↑u⁻¹ : chartRing O x J) • ((a : Ω) • y) := by
      rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
    rw [hy]
    exact Submodule.smul_mem _ _ hJ
theorem LocalizeBundle.fg_baseChange (M : LineBundle S x) (I : Chart x) :
    ((M.toSubSystem.baseChange O).sub I).FG := by
  obtain ⟨s, hs⟩ := M.fg I
  refine ⟨s, ?_⟩
  change Submodule.span (chartRing O x I) (s : Set Ω) =
    Submodule.span (chartRing O x I) (M.sub I : Set Ω)
  rw [← hs, span_base_span]
theorem LocalizeBundle.invertible_baseChange (M : LineBundle S x) (I : Chart x) :
    ∃ Q' : Submodule (chartRing O x I) Ω, (M.toSubSystem.baseChange O).sub I * Q' = 1 := by
  obtain ⟨Q', hQ⟩ := M.invertible I
  refine ⟨Submodule.span (chartRing O x I) (Q' : Set Ω), ?_⟩
  change Submodule.span (chartRing O x I) (M.sub I : Set Ω) *
    Submodule.span (chartRing O x I) (Q' : Set Ω) = 1
  rw [Submodule.span_mul_span, ← span_base_span (S := S) (O := O) I,
    ← Submodule.mul_eq_span_mul_set, hQ, Submodule.one_eq_span (R := chartRing S x I),
    span_base_span]
  exact (Submodule.one_eq_span).symm
def LocalizeBundle.lineBundleBaseChange (M : LineBundle S x) : LineBundle O x :=
  { M.toSubSystem.baseChange O with
    mem_iff := LocalizeBundle.mem_iff_baseChange M
    fg := LocalizeBundle.fg_baseChange M
    invertible := LocalizeBundle.invertible_baseChange M }
end BaseChange
end
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


