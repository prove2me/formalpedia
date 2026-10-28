-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData8_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:45:08.720712+00:00
-- url     : https://prove2.me/theorems/685a86af-d845-4f61-98ec-6bfad417b237
-- title:
--   Small Pair Light Adaptive Data8
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared8.leftCached000`, `PairLightAdaptivePrepared8.leftRows000`, `PairLightAdaptivePrepared8.leftCached001`, `PairLightAdaptivePrepared8.leftRows001`, `PairLightAdaptivePrepared8.leftCached002`, `PairLightAdaptivePrepared8.leftRows002`, `PairLightAdaptivePrepared8.leftCached003`, `PairLightAdaptivePrepared8.leftRows003` and 24 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData8.lean, lines 8-8, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 9-9, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 11-11, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 12-12, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 14-14, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 15-15, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 17-17, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 18-18, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 20-20, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 21-21, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 23-23, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 24-24, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 26-26, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 27-27, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 29-29, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 30-30, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 32-32, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 33-33, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 35-35, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 36-36, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 38-38, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 39-39, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 41-41, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 42-42, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 44-44, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 45-45, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 47-47, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 48-48, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 50-50, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 51-51, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 53-53, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c; D1Bound5/SmallPairLightAdaptiveData8.lean, lines 54-54, SHA-256 53629c646ece2c5994c61f13c8319f4c621a2d42f34e128a7906c4105bb4ed2c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCached000 : List PairLightCachedVertex := PairLightPrepared8.leftCached
noncomputable def leftRows000 : List (Nat × List Nat) := PairLightPrepared8.leftRows

noncomputable def leftCached001 : List PairLightCachedVertex := leftCached000.drop 58
noncomputable def leftRows001 : List (Nat × List Nat) := leftRows000.drop 58

noncomputable def leftCached002 : List PairLightCachedVertex := leftCached001.drop 63
noncomputable def leftRows002 : List (Nat × List Nat) := leftRows001.drop 63

noncomputable def leftCached003 : List PairLightCachedVertex := leftCached002.drop 71
noncomputable def leftRows003 : List (Nat × List Nat) := leftRows002.drop 71

noncomputable def leftCached004 : List PairLightCachedVertex := leftCached003.drop 82
noncomputable def leftRows004 : List (Nat × List Nat) := leftRows003.drop 82

noncomputable def leftCached005 : List PairLightCachedVertex := leftCached004.drop 102
noncomputable def leftRows005 : List (Nat × List Nat) := leftRows004.drop 102

noncomputable def leftCached006 : List PairLightCachedVertex := leftCached005.drop 151
noncomputable def leftRows006 : List (Nat × List Nat) := leftRows005.drop 151

noncomputable def leftCached007 : List PairLightCachedVertex := leftCached006.drop 189
noncomputable def leftRows007 : List (Nat × List Nat) := leftRows006.drop 189

noncomputable def rightCached000 : List PairLightCachedVertex := PairLightPrepared8.rightCached
noncomputable def rightRows000 : List (Nat × List Nat) := PairLightPrepared8.rightRows

noncomputable def rightCached001 : List PairLightCachedVertex := rightCached000.drop 58
noncomputable def rightRows001 : List (Nat × List Nat) := rightRows000.drop 58

noncomputable def rightCached002 : List PairLightCachedVertex := rightCached001.drop 63
noncomputable def rightRows002 : List (Nat × List Nat) := rightRows001.drop 63

noncomputable def rightCached003 : List PairLightCachedVertex := rightCached002.drop 71
noncomputable def rightRows003 : List (Nat × List Nat) := rightRows002.drop 71

noncomputable def rightCached004 : List PairLightCachedVertex := rightCached003.drop 82
noncomputable def rightRows004 : List (Nat × List Nat) := rightRows003.drop 82

noncomputable def rightCached005 : List PairLightCachedVertex := rightCached004.drop 101
noncomputable def rightRows005 : List (Nat × List Nat) := rightRows004.drop 101

noncomputable def rightCached006 : List PairLightCachedVertex := rightCached005.drop 149
noncomputable def rightRows006 : List (Nat × List Nat) := rightRows005.drop 149

noncomputable def rightCached007 : List PairLightCachedVertex := rightCached006.drop 194
noncomputable def rightRows007 : List (Nat × List Nat) := rightRows006.drop 194


end D1Bound5.PairLightAdaptivePrepared8
end


