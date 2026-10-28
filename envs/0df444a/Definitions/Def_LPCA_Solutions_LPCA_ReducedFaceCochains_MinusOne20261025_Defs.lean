-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_MinusOne20261025_Defs
-- name    : LPCA_Solutions_LPCA_ReducedFaceCochains_MinusOne20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T01:30:42.096394+00:00
-- url     : https://prove2.me/theorems/67d6d415-b07a-4997-b34c-d2abe7f11b56
-- title:
--   Reduced Face Cochains — degree minus-one interval dependencies
-- statement:
--   Selected constructions and proved compatibility results for reduced face cochains, used in the explicit degree-minus-one interval presentations. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   A direct description of every intrinsic reduced-cochain term.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Proposition3.12 and Corollary6.4, with their formalization dependencies. Certified Lean source: Solutions/LPCA_ReducedFaceCochains.lean, selected declarations in lines 51–85; source SHA-256 b06bce6018570dded687b1c1b6aa3755eb1f32a17db3ead32d9fbeb292733c92; exact-source certificate Sapelo2 job 49311470.

import Mathlib
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_of_subset_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]







variable (k : Type u) [Field k]





/-- A direct description of every intrinsic reduced-cochain term. -/
noncomputable def reducedFaceComplexComponentIso (rank : V ↪ ℕ) (K : Complex V) (r : ℤ) :
    (reducedFaceComplex k rank K).X r ≅ ModuleCat.of k (ReducedFaceIndex K r → k) := by
  letI : LinearOrder V := rankLinearOrder rank
  let e : Proofs.BassLyubeznik.BassStatic.Signed.Idx
      (Proofs.BassLyubeznik.SrFamily.faceFamily (toSignedComplex K)) (-1) r ≃
        ReducedFaceIndex K r :=
    Equiv.subtypeEquivRight (fun F => by
      change (F ∈ K.faces ∧ (F.card : ℤ) = r - (-1)) ↔
        (F ∈ K.faces ∧ (F.card : ℤ) = r + 1)
      simp only [sub_neg_eq_add])
  exact (LinearEquiv.funCongrLeft k k e.symm).toModuleIso

theorem reducedFaceIndex_isEmpty_below (K : Complex V) (r : ℤ) (hr : r < -1) :
    IsEmpty (ReducedFaceIndex K r) := by
  refine ⟨fun F => ?_⟩
  have hc := F.property.2
  omega

theorem reducedFaceComplexComponent_isZero_below (rank : V ↪ ℕ) (K : Complex V)
    (r : ℤ) (hr : r < -1) : IsZero ((reducedFaceComplex k rank K).X r) := by
  haveI := reducedFaceIndex_isEmpty_below K r hr
  have hz : IsZero (ModuleCat.of k (ReducedFaceIndex K r → k)) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  exact hz.of_iso (reducedFaceComplexComponentIso k rank K r)

theorem reducedFaceIndex_negOne_iff (K : Complex V) (F : Finset V) :
    (F ∈ K.faces ∧ (F.card : ℤ) = (-1 : ℤ) + 1) ↔ F = ∅ ∧ ∅ ∈ K.faces := by
  constructor
  · rintro ⟨hface, hc⟩
    have hzero : F.card = 0 := by omega
    have hF : F = ∅ := Finset.card_eq_zero.mp hzero
    exact ⟨hF, hF ▸ hface⟩
  · rintro ⟨rfl, hface⟩
    exact ⟨hface, by simp⟩

end LPCA


