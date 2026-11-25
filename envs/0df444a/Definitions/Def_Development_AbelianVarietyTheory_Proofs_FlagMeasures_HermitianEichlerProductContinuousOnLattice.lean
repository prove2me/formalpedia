-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianEichlerProductContinuousOnLattice
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianEichlerProductContinuousOnLattice
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:58.225795+00:00
-- url     : https://prove2.me/theorems/e8f98033-5f43-5e67-95b3-b06397194896
-- title:
--   Hermitian Eichler Product Continuous On Lattice
-- statement:
--   Definitions and structural lemmas for Hermitian Eichler Product Continuous On Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianEichlerProductContinuousOnLattice.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
namespace GlobalTheory.HL.EichCont
section Abstract
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ}
def IntV (v : Fin N → E) : Prop := ∀ j, v j ∈ O
def Bd (A : Module.End E (Fin N → E)) (t : F) : Prop :=
  ∀ m, IntV O m → ∃ m', IntV O m' ∧ A m = algebraMap F E t • m'
def Cont {Q : Type} (near : F → Q → Prop) (G : Q → Module.End E (Fin N → E))
    (A : Module.End E (Fin N → E)) : Prop :=
  ∀ c : F, c ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ q, near d q → Bd O (G q - A) c
variable {O}
theorem IntV.add {v w : Fin N → E} (hv : IntV O v) (hw : IntV O w) : IntV O (v + w) :=
  fun j => O.add_mem (hv j) (hw j)
theorem IntV.smul {z : E} (hz : z ∈ O) {v : Fin N → E} (hv : IntV O v) : IntV O (z • v) :=
  fun j => O.mul_mem hz (hv j)
theorem IntV.zero : IntV O (0 : Fin N → E) := fun _ => O.zero_mem
theorem Bd.mono {A : Module.End E (Fin N → E)} {t o : F} (h : Bd O A (t * o))
    (ho : algebraMap F E o ∈ O) : Bd O A t := by
  intro m hm
  obtain ⟨m', hm', e⟩ := h m hm
  exact ⟨algebraMap F E o • m', hm'.smul ho, by rw [e, map_mul, mul_smul]⟩
theorem Bd.add {A B : Module.End E (Fin N → E)} {t : F} (hA : Bd O A t) (hB : Bd O B t) :
    Bd O (A + B) t := by
  intro m hm
  obtain ⟨a, ha, ea⟩ := hA m hm
  obtain ⟨b, hb, eb⟩ := hB m hm
  exact ⟨a + b, ha.add hb, by rw [LinearMap.add_apply, ea, eb, smul_add]⟩
theorem Bd.mul {A B : Module.End E (Fin N → E)} {t s : F} (hA : Bd O A t) (hB : Bd O B s) :
    Bd O (A * B) (t * s) := by
  intro m hm
  obtain ⟨b, hb, eb⟩ := hB m hm
  obtain ⟨a, ha, ea⟩ := hA b hb
  exact ⟨a, ha, by rw [Module.End.mul_apply, eb, map_smul, ea, smul_smul, ← map_mul, mul_comm]⟩
theorem Bd.zero (t : F) : Bd O (0 : Module.End E (Fin N → E)) t :=
  fun _ _ => ⟨0, IntV.zero, by simp⟩
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O)
include hden
theorem exists_den {ι : Type} [Fintype ι] (z : ι → E) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ ∀ i, algebraMap F E a * z i ∈ O := by
  choose a ha0 haO haz using fun i => hden (z i)
  have hP : ∀ s : Finset ι, algebraMap F E (∏ i ∈ s, a i) ∈ O := fun s => by
    rw [map_prod]; exact prod_mem fun i _ => haO i
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.2 fun i _ => ha0 i, hP _, fun i => ?_⟩
  have e : algebraMap F E (∏ j, a j) * z i =
      algebraMap F E (∏ j ∈ Finset.univ.erase i, a j) * (algebraMap F E (a i) * z i) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul]; ring
  rw [e]
  exact O.mul_mem (hP _) (haz i)
theorem Bd.exists (A : Module.End E (Fin N → E)) :
    ∃ w : F, w ≠ 0 ∧ algebraMap F E w ∈ O ∧ Bd O A w⁻¹ := by
  obtain ⟨w, hw0, hwO, hw⟩ := exists_den hden
    (fun p : Fin N × Fin N => A (fun j => if p.1 = j then 1 else 0) p.2)
  refine ⟨w, hw0, hwO, fun m hm =>
    ⟨∑ i, m i • (algebraMap F E w • A (fun j => if i = j then 1 else 0)), fun j => ?_, ?_⟩⟩
  · rw [Finset.sum_apply]
    exact sum_mem fun i _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact O.mul_mem (hm i) (hw (i, j))
  · rw [LinearMap.pi_apply_eq_sum_univ A m, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm (m i) (algebraMap F E w), smul_smul, ← map_mul, inv_mul_cancel₀ hw0, map_one,
      one_smul]
theorem Cont.mul {Q : Type} {near : F → Q → Prop}
    (hnear : ∀ a b : F, a ≠ 0 → b ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ q, near d q → near a q ∧ near b q)
    {G H : Q → Module.End E (Fin N → E)} {A B : Module.End E (Fin N → E)}
    (hG : Cont O near G A) (hH : Cont O near H B) : Cont O near (fun q => G q * H q) (A * B) := by
  intro c hc
  obtain ⟨w₁, hw₁, hw₁O, hA⟩ := Bd.exists hden A
  obtain ⟨w₂, hw₂, hw₂O, hB⟩ := Bd.exists hden B
  obtain ⟨ε, hε, hεO, hεc⟩ := hden (algebraMap F E c⁻¹)
  have hεc' : algebraMap F E (ε * c⁻¹) ∈ O := by rw [map_mul]; exact hεc
  have hwO : algebraMap F E (w₁ * w₂) ∈ O := by rw [map_mul]; exact O.mul_mem hw₁O hw₂O
  have hA' : Bd O A (w₁ * w₂)⁻¹ :=
    Bd.mono (o := w₂) (by rwa [show (w₁ * w₂)⁻¹ * w₂ = w₁⁻¹ by field_simp]) hw₂O
  have hB' : Bd O B (w₁ * w₂)⁻¹ :=
    Bd.mono (o := w₁) (by rwa [show (w₁ * w₂)⁻¹ * w₁ = w₂⁻¹ by field_simp]) hw₁O
  have hα : ε * (w₁ * w₂) ≠ 0 := mul_ne_zero hε (mul_ne_zero hw₁ hw₂)
  obtain ⟨d₁, hd₁, h1⟩ := hG _ hα
  obtain ⟨d₂, hd₂, h2⟩ := hH _ hα
  obtain ⟨d, hd, hn⟩ := hnear d₁ d₂ hd₁ hd₂
  refine ⟨d, hd, fun q hq => ?_⟩
  have hGq := h1 q (hn q hq).1
  have hHq := h2 q (hn q hq).2
  have e : G q * H q - A * B = (G q - A) * (H q - B) + ((G q - A) * B + A * (H q - B)) := by
    noncomm_ring
  show Bd O (G q * H q - A * B) c
  rw [e]
  refine Bd.add ?_ (Bd.add ?_ ?_)
  · refine Bd.mono (o := (ε * c⁻¹) * (ε * (w₁ * w₂) * (w₁ * w₂))) ?_ ?_
    · rw [show c * ((ε * c⁻¹) * (ε * (w₁ * w₂) * (w₁ * w₂))) = (ε * (w₁ * w₂)) * (ε * (w₁ * w₂)) by
        field_simp]
      exact hGq.mul hHq
    · have hwO' : algebraMap F E w₁ * algebraMap F E w₂ ∈ O := O.mul_mem hw₁O hw₂O
      simp only [map_mul]
      exact O.mul_mem hεc (O.mul_mem (O.mul_mem hεO hwO') hwO')
  · refine Bd.mono (o := ε * c⁻¹) ?_ hεc'
    rw [show c * (ε * c⁻¹) = (ε * (w₁ * w₂)) * (w₁ * w₂)⁻¹ by field_simp]
    exact hGq.mul hB'
  · refine Bd.mono (o := ε * c⁻¹) ?_ hεc'
    rw [show c * (ε * c⁻¹) = (w₁ * w₂)⁻¹ * (ε * (w₁ * w₂)) by field_simp]
    exact hA'.mul hHq
theorem Cont.prod {Q : Type} {near : F → Q → Prop}
    (hnear : ∀ a b : F, a ≠ 0 → b ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ q, near d q → near a q ∧ near b q) :
    ∀ (r : ℕ) (G : Fin r → Q → Module.End E (Fin N → E)) (A : Fin r → Module.End E (Fin N → E)),
      (∀ i, Cont O near (G i) (A i)) →
      Cont O near (fun q => (List.ofFn fun i => G i q).prod) (List.ofFn A).prod
  | 0, G, A, _ => fun c _ => ⟨1, one_ne_zero, fun q _ => by simpa using Bd.zero (O := O) (N := N) c⟩
  | r + 1, G, A, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact Cont.mul hden hnear (h 0)
      (Cont.prod hnear r (fun i => G i.succ) (fun i => A i.succ) fun i => h i.succ)
end Abstract
section Eich
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
end Eich
section Lat
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {O : Subring E} {N : ℕ}
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O)
include hden
end Lat
end GlobalTheory.HL.EichCont


