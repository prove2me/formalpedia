-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalTraceReject
-- name    : PretorsionImageClosed_LinearQuiver_IntervalTraceReject
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T03:28:37.269793+00:00
-- url     : https://prove2.me/theorems/b01403c1-ae19-5a79-9846-339d746db018
-- title:
--   Interval Trace Reject
-- statement:
--   Definitions and structural lemmas for Interval Trace Reject, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_canonicalHom_eq
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_canonicalHom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_comp
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_id
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_intervalIncl
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_zero
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_bot_or_eq_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_hom_ext_coord
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_le_suffix
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_bot_le
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_def

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement Subcategory
namespace LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
theorem intervalIncl_le_refl (a d : Fin n) : intervalIncl k d (le_refl a) = 𝟙 (interval k a d) :=
  hom_ext_coord fun i => by rw [coord_intervalIncl, coord_id]
theorem intervalProj_eq_canonicalHom (a : Fin n) {ℓ d : Fin n} (h : ℓ ≤ d) :
    intervalProj k a h = canonicalHom (k := k) (le_refl a) h := by
  rw [canonicalHom_eq, intervalIncl_le_refl, Category.comp_id]
theorem coord_intervalProj (a : Fin n) {ℓ d : Fin n} (h : ℓ ≤ d) (i : Fin n) :
    coord (intervalProj k a h) i = if a ≤ i ∧ i ≤ ℓ then 1 else 0 := by
  rw [intervalProj_eq_canonicalHom, coord_canonicalHom]
theorem intervalIncl_comp_intervalProj {c u ℓ d : Fin n} (hcu : c ≤ u) (hℓd : ℓ ≤ d) :
    intervalIncl k d hcu ≫ intervalProj k c hℓd = canonicalHom (k := k) hcu hℓd := by
  apply hom_ext_coord
  intro i
  rw [coord_comp, coord_intervalIncl, coord_intervalProj, coord_canonicalHom]
  by_cases h1 : u ≤ i ∧ i ≤ ℓ
  · rw [if_pos h1, if_pos ⟨h1.1, h1.2.trans hℓd⟩, if_pos ⟨hcu.trans h1.1, h1.2⟩, one_mul]
  · rw [if_neg h1]
    by_cases h2 : u ≤ i ∧ i ≤ d
    · rw [if_pos h2, one_mul, if_neg]
      intro h3
      exact h1 ⟨h2.1, h3.2⟩
    · rw [if_neg h2, zero_mul]
theorem canonicalHom_eq_zero_of_lt {c u ℓ d : Fin n} (hcu : c ≤ u) (hℓd : ℓ ≤ d) (h : ℓ < u) :
    canonicalHom (k := k) hcu hℓd = 0 := by
  apply hom_ext_coord
  intro i
  rw [coord_canonicalHom, coord_zero, if_neg]
  rintro ⟨h1, h2⟩
  exact (h.trans_le h1).not_ge h2
theorem kernelSubobject_intervalProj {c ℓ d v : Fin n} (hℓd : ℓ ≤ d) (hcv : c ≤ v)
    (hv : ℓ.val + 1 = v.val) :
    kernelSubobject (intervalProj k c hℓd) = suffix c d v hcv := by
  have hℓv : ℓ < v := Fin.lt_def.2 (by omega)
  apply le_antisymm
  · rcases eq_bot_or_eq_suffix (kernelSubobject (intervalProj k c hℓd)) with h0 | ⟨u', hcu', -, hK⟩
    · rw [h0]
      exact bot_le
    · have hvu' : v ≤ u' := by
        by_contra hlt
        have hu'ℓ : u' ≤ ℓ := Fin.le_def.2 (by have := Fin.lt_def.1 (not_le.1 hlt); omega)
        have hle : suffix c d u' hcu' ≤ kernelSubobject (intervalProj k c hℓd) := hK.ge
        rw [Subobject.le_kernelSubobject_iff, suffix, ← Subobject.underlyingIso_hom_comp_eq_mk,
          Category.assoc] at hle
        have hle' : intervalIncl k d hcu' ≫ intervalProj k c hℓd = 0 :=
          (cancel_epi (Subobject.underlyingIso (intervalIncl k d hcu')).hom).1
            (by rw [hle, comp_zero])
        rw [intervalIncl_comp_intervalProj] at hle'
        have := congrArg (fun η => coord η u') hle'
        simp only [coord_canonicalHom, coord_zero] at this
        rw [if_pos ⟨le_rfl, hu'ℓ⟩] at this
        exact one_ne_zero this
      rw [hK]
      exact suffix_le_suffix hcv hvu'
  · apply le_kernelSubobject
    rw [suffix, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
      intervalIncl_comp_intervalProj, canonicalHom_eq_zero_of_lt hcv hℓd hℓv, comp_zero]
def cokernelSuffixIso {c ℓ d v : Fin n} (hℓd : ℓ ≤ d) (hcv : c ≤ v) (hv : ℓ.val + 1 = v.val) :
    cokernel (suffix (k := k) c d v hcv).arrow ≅ interval k c ℓ :=
  eqToIso (congrArg (fun S : Subobject (interval k c d) => cokernel S.arrow)
    (kernelSubobject_intervalProj hℓd hcv hv).symm) ≪≫
    cokernelKernelSubobjectArrowIso (intervalProj k c hℓd)
variable {T F : Subcategory (Statement.LinRep k n)}
end LinearQuiver
end PretorsionImageClosed


