-- Prove2me | Definitions.Def_D1Bound5_PellLightPrefixData1_Definitions_001
-- name    : D1Bound5_PellLightPrefixData1_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:33:52.536986+00:00
-- url     : https://prove2.me/theorems/8ac33169-284d-466b-97dc-dcc82556315c
-- title:
--   Pell Light Prefix Data1 001
-- statement:
--   Exact integer magnitude lists and their finite Pell-prefix certificates. The named objects in this bundle include `PellLightProduction.magnitudes_7`, `PellLightProduction.magnitudes_15`, `PellLightProduction.magnitudes_23`, `PellLightProduction.magnitudes_31`, `PellLightProduction.magnitudes_39`, `PellLightProduction.magnitudes_47`, `PellLightProduction.magnitudes_55`, `PellLightProduction.magnitudes_71` and 1 further declarations. The accompanying auxiliary certificates are included with their original proofs.
-- source:
--   D1Bound5/PellLightPrefixData1.lean, lines 7-8, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 10-12, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 14-15, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 17-19, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 21-22, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 24-26, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 28-29, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 31-33, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 35-36, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 38-40, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 42-43, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 45-47, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 49-50, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 52-54, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 56-57, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 59-61, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608; D1Bound5/PellLightPrefixData1.lean, lines 63-64, SHA-256 06f14e76b7b838013cd6cb30af06a28ef1182577fc701d039d235691ceb1f608. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_4c9c267cfd262b6ddca1
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_c6fd455dd2469ae362d8
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_2ac5e73f07cab6a70ca6
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_00347b19dd0f10b58cdd
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_fadb003757831903f157
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_602550a2c0d7fdae690f
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_b103e284aa72738e50df
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_4320cfc43dc4d5fb21bf
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_d0347572582dc0d723cf
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_09d09ff0ef9aa2a59bbb
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_45e090a5c34afbdc2a31
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_8b9dfe6bd53f96bae7a8
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_12c35ec966f1a791000e
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_b46d175d5bb032106fbe
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellSlice_54d7799ce633eca3d3cf
import Init
import Definitions.Def_D1Bound5_PellLightCF_Definitions

section
namespace D1Bound5.PellLightProduction
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def magnitudes_7 : List Int :=
  (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_4c9c267cfd262b6ddca1 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_c6fd455dd2469ae362d8 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_2ac5e73f07cab6a70ca6 _root_.D1Bound5.Prove2MeTransfer.pellSlice_00347b19dd0f10b58cdd)))

theorem checked_7 :
    pellLightFiniteCheck 7 2 (10^275) 915 magnitudes_7 = true := by
  decide +kernel

def magnitudes_15 : List Int :=
  []

theorem checked_15 :
    pellLightFiniteCheck 15 3 (10^275) 614 magnitudes_15 = true := by
  decide +kernel

def magnitudes_23 : List Int :=
  (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_fadb003757831903f157 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_602550a2c0d7fdae690f _root_.D1Bound5.Prove2MeTransfer.pellSlice_b103e284aa72738e50df))

theorem checked_23 :
    pellLightFiniteCheck 23 4 (10^275) 654 magnitudes_23 = true := by
  decide +kernel

def magnitudes_31 : List Int :=
  (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_4320cfc43dc4d5fb21bf _root_.D1Bound5.Prove2MeTransfer.pellSlice_d0347572582dc0d723cf)

theorem checked_31 :
    pellLightFiniteCheck 31 5 (10^275) 632 magnitudes_31 = true := by
  decide +kernel

def magnitudes_39 : List Int :=
  []

theorem checked_39 :
    pellLightFiniteCheck 39 6 (10^275) 324 magnitudes_39 = true := by
  decide +kernel

def magnitudes_47 : List Int :=
  (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_09d09ff0ef9aa2a59bbb _root_.D1Bound5.Prove2MeTransfer.pellSlice_45e090a5c34afbdc2a31)

theorem checked_47 :
    pellLightFiniteCheck 47 6 (10^275) 554 magnitudes_47 = true := by
  decide +kernel

def magnitudes_55 : List Int :=
  []

theorem checked_55 :
    pellLightFiniteCheck 55 7 (10^275) 488 magnitudes_55 = true := by
  decide +kernel

def magnitudes_71 : List Int :=
  (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_8b9dfe6bd53f96bae7a8 _root_.D1Bound5.Prove2MeTransfer.pellSlice_12c35ec966f1a791000e)

theorem checked_71 :
    pellLightFiniteCheck 71 8 (10^275) 572 magnitudes_71 = true := by
  decide +kernel

def magnitudes_79 : List Int :=
  (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.pellSlice_b46d175d5bb032106fbe _root_.D1Bound5.Prove2MeTransfer.pellSlice_54d7799ce633eca3d3cf)































end D1Bound5.PellLightProduction
end


