-- Prove2me | Definitions.Def_Tablet_CutTypeI
-- name    : Tablet_CutTypeI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:17:33.495797+00:00
-- url     : https://prove2.me/theorems/5db717ff-52d0-5cf1-a4b7-2f3a223e40ee
-- title:
--   Cut Type I
-- statement:
--   Definitions and structural lemmas for Cut Type I, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CutTypeI.lean

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_TypeICutPointExists
import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_BasicCutClosed
import Definitions.Def_Tablet_BasicCutCurrent
import Definitions.Def_Tablet_BasicCutLength
import Definitions.Def_Tablet_BasicCutResolutionGeneral
import Definitions.Def_Tablet_BasicCutDiscardedResolutionGeneral
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_ArcShortWindowEdgeCount
import Definitions.Def_Tablet_ArcDeltaEpsNCount
import Definitions.Def_Tablet_C1SmallBall
import Definitions.Def_Tablet_FullBallLem
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_RestrictLSI
import Definitions.Def_Tablet_RestrictFullIsSelf
import Definitions.Def_Tablet_RestrictMeasureFormula
import Definitions.Def_Tablet_MorreyResolutionAdditive
import Definitions.Def_Tablet_MorreySubadditive
import Definitions.Def_Tablet_GeodesicMorreyLeTwo
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_BasicCutDiscardedEval
import Definitions.Def_Tablet_dGamma
import Theorems.Thm_ArcDeltaEpsNCount
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_ArcShortWindowEdgeCount
import Theorems.Thm_BasicCutClosed
import Theorems.Thm_BasicCutCurrent
import Theorems.Thm_BasicCutDiscardedEval
import Theorems.Thm_BasicCutDiscardedResolutionGeneral
import Theorems.Thm_BasicCutLength
import Theorems.Thm_BasicCutResolutionGeneral
import Theorems.Thm_C1SmallBall
import Theorems.Thm_FullBallLem
import Theorems.Thm_GeodesicMorreyLeTwo
import Theorems.Thm_MorreyResolutionAdditive
import Theorems.Thm_MorreySubadditive
import Theorems.Thm_RestrictFullIsSelf
import Theorems.Thm_RestrictLSI
import Theorems.Thm_RestrictMeasureFormula
import Theorems.Thm_RestrictPiecewiseGeodesic
import Theorems.Thm_TypeICutPointExists

set_option autoImplicit false
open Set ENNReal


