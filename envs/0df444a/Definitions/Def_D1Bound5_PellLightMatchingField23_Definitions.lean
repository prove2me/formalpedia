-- Prove2me | Definitions.Def_D1Bound5_PellLightMatchingField23_Definitions
-- name    : D1Bound5_PellLightMatchingField23_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:32:21.368306+00:00
-- url     : https://prove2.me/theorems/982bea02-1191-4b03-a31c-22b56b4f14be
-- title:
--   Pell Light Matching Field23
-- statement:
--   Exact integer magnitudes, modular square masks and index witnesses for the finite Pell matching certificates. The named objects in this bundle include `PellMatchingLightProduction.pellMagnitudes_23`, `PellMatchingLightProduction.pellMasks_23`, `PellMatchingLightProduction.pellWitnesses_23`. The accompanying auxiliary certificates are included with their original proofs.
-- source:
--   D1Bound5/PellLightMatchingField23.lean, lines 7-8, SHA-256 40f5ab43c67a5bc2640223f182f45bca09ddf5d99896fe3e690a24a0c1503712; D1Bound5/PellLightMatchingField23.lean, lines 10-11, SHA-256 40f5ab43c67a5bc2640223f182f45bca09ddf5d99896fe3e690a24a0c1503712; D1Bound5/PellLightMatchingField23.lean, lines 13-14, SHA-256 40f5ab43c67a5bc2640223f182f45bca09ddf5d99896fe3e690a24a0c1503712; D1Bound5/PellLightMatchingField23.lean, lines 16-18, SHA-256 40f5ab43c67a5bc2640223f182f45bca09ddf5d99896fe3e690a24a0c1503712; D1Bound5/PellLightMatchingField23.lean, lines 20-22, SHA-256 40f5ab43c67a5bc2640223f182f45bca09ddf5d99896fe3e690a24a0c1503712; D1Bound5/PellLightMatchingField23.lean, lines 24-26, SHA-256 40f5ab43c67a5bc2640223f182f45bca09ddf5d99896fe3e690a24a0c1503712. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_757efc71f33ef4b34c3f
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_d6bf477c47c155d88714
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_ac981091ead8fef618e8
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_1136c0be3f3c3777a518
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_ab017b67ad8c38d0a28d
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_7a01f4d4c46f0da98406
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_27926fa7c69314b98f3e
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_795a225c360a62312a6a
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_ac082356b63dd3a84ff5
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_732e39cac900bfa4f286
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_79a90464631217b8ff80
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_b1f13a777df5ff27e7f5
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_939d64d6de62f894e14d
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_c03aee0178337119e7c1
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_64b7f8eba9d0d00ea581
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_67ea804442f1fd8f4a76
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_b96188aabcffefcc1ed8
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_f2c9663e88ea2c519b9e
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_2026fea78f16437eb661
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_c35a6c0604c1b4eca754
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_a37f47bb704cfcf42775
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_da7c8f5e6c427b7e7308
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_725652ab8ce922d9b307
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_a94030d82a07b7507b4a
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_557be29ea083ddd30502
import Init
import Definitions.Def_D1Bound5_PellLightMatching_Definitions

section
namespace D1Bound5.PellMatchingLightProduction
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def pellMagnitudes_23 : List Int :=
  (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_757efc71f33ef4b34c3f (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_d6bf477c47c155d88714 _root_.D1Bound5.Prove2MeTransfer.pellSlice_ac981091ead8fef618e8))

def pellMasks_23 : List PellLightSquareMasks :=
  [⟨4,19,13⟩,⟨10,571,571⟩,⟨12,5659,5659⟩,⟨16,107287,23785⟩,⟨18,199411,199411⟩,⟨28,332473075,332473075⟩,⟨30,303908791,1843574857⟩,⟨36,96068509339,41370444133⟩,⟨42,3678700564051,3678700564051⟩,⟨52,5310023542746835,3697175711994157⟩,⟨60,1662926210933060155,642916798280633797⟩,⟨66,61808106872519771731,61808106872519771731⟩,⟨82,2911111237809585785085595,2911111237809585785085595⟩]

def pellWitnesses_23 : List (List (Nat × Nat)) :=
  (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_1136c0be3f3c3777a518 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_ab017b67ad8c38d0a28d (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_7a01f4d4c46f0da98406 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_27926fa7c69314b98f3e (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_795a225c360a62312a6a (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_ac082356b63dd3a84ff5 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_732e39cac900bfa4f286 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_79a90464631217b8ff80 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_b1f13a777df5ff27e7f5 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_939d64d6de62f894e14d (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_c03aee0178337119e7c1 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_64b7f8eba9d0d00ea581 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_67ea804442f1fd8f4a76 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_b96188aabcffefcc1ed8 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_f2c9663e88ea2c519b9e (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_2026fea78f16437eb661 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_c35a6c0604c1b4eca754 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_a37f47bb704cfcf42775 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_da7c8f5e6c427b7e7308 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_725652ab8ce922d9b307 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_a94030d82a07b7507b4a _root_.D1Bound5.Prove2MeTransfer.pellSlice_557be29ea083ddd30502)))))))))))))))))))))

theorem pellMasks_23_valid :
    (pellMasks_23.all fun m => m.validBool 23) = true := by
  decide +kernel

theorem pellMatching_23_checked :
    pellLightMatchingCheck pellMasks_23 pellMagnitudes_23 pellWitnesses_23 = true := by
  decide +kernel

theorem pellMagnitudes_23_large :
    (pellMagnitudes_23.all fun x => decide (2 ≤ x)) = true := by
  decide +kernel

end D1Bound5.PellMatchingLightProduction
end


