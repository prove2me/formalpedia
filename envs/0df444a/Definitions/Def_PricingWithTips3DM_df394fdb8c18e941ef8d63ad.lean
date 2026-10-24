-- Prove2me | Definitions.Def_PricingWithTips3DM_df394fdb8c18e941ef8d63ad
-- name    : PricingWithTips3DM_df394fdb8c18e941ef8d63ad
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:02:46.30983+00:00
-- url     : https://prove2.me/theorems/e0bc7609-77be-4118-be56-2ba153bb2082
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_CLRS3DM_HardnessAssembly
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_d0a75b5422439c89978ca2df
import Definitions.Def_PricingWithTips3DM_2b0077f418bcfcd2e91e29dd
import Definitions.Def_PricingWithTips3DM_016f4b89ca40933af432d715
import Definitions.Def_PricingWithTips3DM_36f8af72b5600c8711e12fba
import Definitions.Def_PricingWithTips3DM_5958e576b6128d87fe27a8c4
import Definitions.Def_PricingWithTips_NPHardness
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
The all-alphabet NP-hardness assembly.  Every mathematical and complexity
component is discharged here except the single concrete compiler lemma saying
that the fixed guarded CLRS-3CNF-to-3DM map emits the mission's incidence-table
encoding in polynomial time.
-/

namespace PricingWithTips.CLRS3DM

open Hardness Hardness.Cert

theorem clrs_threeCNFSat_npHard :
    CLRS.Chapter34.NPHard CLRS.Chapter34.ThreeCNFSat :=
  CLRS.Chapter34.NPHard.of_reducible CLRS.Chapter34.SAT_npHard
    CLRS.Chapter34.Turing.TM3CNF.sat_reducible_to_threeCNFSat

def reduction (input : List CLRS.Chapter34.CNFSym) : ThreeDMInstance :=
  Certified3DM.certifiedSatToThreeDM
    (CLRS3CNFBridge.guardedCertCNF input)

theorem reduction_correct (input : List CLRS.Chapter34.CNFSym) :
    input ∈ CLRS.Chapter34.ThreeCNFSat ↔ ThreeDMYes (reduction input) :=
  (CLRS3CNFBridge.threeCNFSat_iff_guardedCertSAT input).trans
    (Certified3DM.concrete_sat_iff_certifiedThreeDM _)

theorem polynomiallyVerifiable_to_CLRS {Γ : Type} {L : Set (List Γ)}
    (h : PolynomiallyVerifiable L) :
    CLRS.Chapter34.PolyTimeVerifiable L := by
  rcases h with ⟨V, p, hV, hcorrect⟩
  refine ⟨V, p, ?_, hcorrect⟩
  change Nonempty (Turing.TM2ComputableInPolyTime
    (fun pair : List Γ × List Γ =>
      pair.1.map some ++ [none] ++ pair.2.map some)
    (fun b : Bool => [b])
    (fun pair : List Γ × List Γ => V pair.1 pair.2)) at hV
  change Nonempty (Turing.TM2ComputableInPolyTime
    (fun pair : List Γ × List Γ =>
      pair.1.map some ++ [none] ++ pair.2.map some)
    (fun b : Bool => [b])
    (fun pair : List Γ × List Γ => V pair.1 pair.2))
  exact hV

/-- Once the one fixed 3CNF-to-incidence-table compiler is supplied, the
mission's exact all-alphabet NP-hardness statement follows by native TM2
composition from the verified CLRS Cook--Levin theorem. -/
theorem threeDM_np_hard_of_reduction_polytime
    (hreduction : Nonempty (Turing.TM2ComputableInPolyTime
      (id : List CLRS.Chapter34.CNFSym → List CLRS.Chapter34.CNFSym)
      encodeThreeDMInstance reduction)) :
    NPHardMarketPredicate ThreeDMYes := by
  intro Γ L hL
  obtain ⟨f, hf, hcorrect⟩ :=
    clrs_threeCNFSat_npHard Γ L
      (polynomiallyVerifiable_to_CLRS hL)
  refine ⟨reduction ∘ f, ?_, ?_⟩
  · exact CLRS.Chapter34.PolyTimeComputable.comp hf hreduction
  · intro x
    exact (hcorrect x).trans (reduction_correct (f x))

end PricingWithTips.CLRS3DM


