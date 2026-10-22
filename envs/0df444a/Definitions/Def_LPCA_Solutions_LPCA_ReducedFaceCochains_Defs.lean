-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
-- name    : LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:39:57.995153+00:00
-- url     : https://prove2.me/theorems/acea35c6-d46a-4fac-b075-056e588f82cc
-- title:
--   Reduced Face Cochains for localized persistent commutative algebra
-- statement:
--   This bundle supplies reduced Face Cochains for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Reuse the existing finite downward-closed face-family model. Both models admit the void complex and the complex containing only the empty face.
--   - The orientation order supplied by the chosen rank, preserving the existing equality decider on vertices.
--   - The intrinsic reduced cochain indices. In particular the empty face occurs in degree -1, rather than being omitted or truncated.
--   - The existing signed simplicial cochain complex, with the usual reduced offset -1, applied to the same finite face family. Its differential uses the orientation induced by rank. It is independent of localized polynomial rings.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_ReducedFaceCochains.lean, selected declarations in lines 16–49; source SHA-256 b06bce6018570dded687b1c1b6aa3755eb1f32a17db3ead32d9fbeb292733c92; source certificate Sapelo2 job 49172236.

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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- Reuse the existing finite downward-closed face-family model. Both models
admit the void complex and the complex containing only the empty face. -/
def toSignedComplex (K : Complex V) : Proofs.BassLyubeznik.SrFamily.SComplex V :=
  ⟨K.faces, fun _ _ hs hts => K.down_closed hs hts⟩

/-- The orientation order supplied by the chosen rank, preserving the
existing equality decider on vertices. -/
def rankLinearOrder (rank : V ↪ ℕ) : LinearOrder V :=
  let decV : DecidableEq V := inferInstance
  let orderV := LinearOrder.lift' rank rank.injective
  { orderV with
    toDecidableEq := decV
    compare := fun v w => @compareOfLessAndEq V v w orderV.toLT
      (orderV.toDecidableLT v w) decV
    compare_eq_compareOfLessAndEq := by intro v w; rfl }

/-- The intrinsic reduced cochain indices. In particular the empty face
occurs in degree -1, rather than being omitted or truncated. -/
abbrev ReducedFaceIndex (K : Complex V) (r : ℤ) : Type u :=
  {F : Finset V // F ∈ K.faces ∧ (F.card : ℤ) = r + 1}

variable (k : Type u) [Field k]

/-- The existing signed simplicial cochain complex, with the usual reduced
offset -1, applied to the same finite face family. Its differential uses the
orientation induced by rank. It is independent of localized polynomial rings. -/
noncomputable def reducedFaceComplex (rank : V ↪ ℕ) (K : Complex V) :
    CochainComplex (ModuleCat.{u} k) ℤ := by
  letI : LinearOrder V := rankLinearOrder rank
  exact Proofs.BassLyubeznik.BassStatic.redCochain k (toSignedComplex K) (-1)

noncomputable def reducedFaceCohomology (rank : V ↪ ℕ) (K : Complex V) (r : ℤ) :
    ModuleCat.{u} k :=
  (reducedFaceComplex k rank K).homology r









end LPCA


