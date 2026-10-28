-- Prove2me | Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
-- name    : D1Bound5_OneSmallCutoffArithmetic_Definitions_002
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:06:53.100994+00:00
-- url     : https://prove2.me/theorems/2b589c24-a2a2-488a-9c3d-2b29b6c25a12
-- title:
--   One Small Cutoff Arithmetic 002
-- statement:
--   Definitions for one small cutoff arithmetic in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `oneSmallCutoffRow_45`, `oneSmallCutoffRow_46`, `oneSmallCutoffRow_47`, `oneSmallCutoffRow_48`, `oneSmallCutoffRow_49`, `oneSmallCutoffRow_50`, `oneSmallCutoffRow_51`, `oneSmallCutoffRow_52` and 5 further declarations.
-- source:
--   D1Bound5/OneSmallCutoffArithmetic.lean, lines 369-370, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 375-376, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 381-382, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 387-388, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 393-394, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 399-400, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 405-406, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 411-412, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 417-418, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 423-424, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 429-430, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 435-436, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 441-498, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt



namespace OneSmallCutoffRow



























end OneSmallCutoffRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0





















































































































































































def oneSmallCutoffRow_45 : OneSmallCutoffRow :=
  ⟨⟨1, 4, (1, 0), (-5, 1), (-4, -1), 3059⟩, 559986669/500000000, 1544080889/5000000000, 9797958971/2000000000, 44, 367, 176, 6049, 57935, 579⟩



def oneSmallCutoffRow_46 : OneSmallCutoffRow :=
  ⟨⟨1, 4, (1, 0), (-5, 1), (-4, 3), 3090⟩, 549806133/625000000, 1204507891/10000000000, 9797958971/2000000000, 44, 367, 176, 6049, 57935, 263⟩



def oneSmallCutoffRow_47 : OneSmallCutoffRow :=
  ⟨⟨1, 4, (1, 0), (-4, 3), (-1, 5), 6843⟩, 6030071489/10000000000, 382490393/10000000000, 63245553203/10000000000, 32, 229, 126, 3718, 28965, 115⟩



def oneSmallCutoffRow_48 : OneSmallCutoffRow :=
  ⟨⟨1, 5, (1, 0), (-6, 1), (-5, -1), 5592⟩, 4947007813/5000000000, 2171270299/10000000000, 5916079783/1000000000, 40, 324, 161, 5305, 46974, 532⟩



def oneSmallCutoffRow_49 : OneSmallCutoffRow :=
  ⟨⟨1, 5, (1, 0), (-6, 1), (-5, 3), 5661⟩, 64161779/80000000, 902122561/10000000000, 5916079783/1000000000, 40, 324, 161, 5305, 46974, 266⟩



def oneSmallCutoffRow_50 : OneSmallCutoffRow :=
  ⟨⟨1, 5, (1, 0), (-5, 3), (-2, 5), 11532⟩, 232171797/400000000, 159470581/5000000000, 7416198487/1000000000, 31, 226, 124, 3660, 28401, 133⟩



def oneSmallCutoffRow_51 : OneSmallCutoffRow :=
  ⟨⟨1, 6, (1, 0), (-7, 1), (-6, -1), 9289⟩, 8941157631/10000000000, 39733471/250000000, 34641016151/5000000000, 37, 296, 151, 4834, 40902, 499⟩



def oneSmallCutoffRow_52 : OneSmallCutoffRow :=
  ⟨⟨1, 6, (1, 0), (-7, 1), (-6, 3), 9415⟩, 371365489/500000000, 9/128, 34641016151/5000000000, 37, 296, 151, 4834, 40902, 269⟩



def oneSmallCutoffRow_53 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (1, 1), (-1, -3), (-4, 0), 1281⟩, 2390165397/1250000000, 729/512, 11180339887/5000000000, 77, 803, 387, 17946, 216405, 540⟩



def oneSmallCutoffRow_54 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (1, 1), (-1, -3), (4, -4), 2561⟩, 13139872527/10000000000, 1340942383/2500000000, 11180339887/5000000000, 77, 803, 387, 17946, 216405, 182⟩



def oneSmallCutoffRow_55 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (1, 1), (3, 1), (8, 4), 6401⟩, 3510697937/10000000000, 4913/64000, 11180339887/5000000000, 19, 38, 41, 370, 985, 38⟩



def oneSmallCutoffRow_56 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (1, 0), (3, 0), (8, 0), 1024⟩, 1822916667/5000000000, 37252903/625000000, 3, 12, 41, 25, 300, 1100, 34⟩



def oneSmallCutoffRows : List OneSmallCutoffRow :=
  [oneSmallCutoffRow_0,
   oneSmallCutoffRow_1,
   oneSmallCutoffRow_2,
   oneSmallCutoffRow_3,
   oneSmallCutoffRow_4,
   oneSmallCutoffRow_5,
   oneSmallCutoffRow_6,
   oneSmallCutoffRow_7,
   oneSmallCutoffRow_8,
   oneSmallCutoffRow_9,
   oneSmallCutoffRow_10,
   oneSmallCutoffRow_11,
   oneSmallCutoffRow_12,
   oneSmallCutoffRow_13,
   oneSmallCutoffRow_14,
   oneSmallCutoffRow_15,
   oneSmallCutoffRow_16,
   oneSmallCutoffRow_17,
   oneSmallCutoffRow_18,
   oneSmallCutoffRow_19,
   oneSmallCutoffRow_20,
   oneSmallCutoffRow_21,
   oneSmallCutoffRow_22,
   oneSmallCutoffRow_23,
   oneSmallCutoffRow_24,
   oneSmallCutoffRow_25,
   oneSmallCutoffRow_26,
   oneSmallCutoffRow_27,
   oneSmallCutoffRow_28,
   oneSmallCutoffRow_29,
   oneSmallCutoffRow_30,
   oneSmallCutoffRow_31,
   oneSmallCutoffRow_32,
   oneSmallCutoffRow_33,
   oneSmallCutoffRow_34,
   oneSmallCutoffRow_35,
   oneSmallCutoffRow_36,
   oneSmallCutoffRow_37,
   oneSmallCutoffRow_38,
   oneSmallCutoffRow_39,
   oneSmallCutoffRow_40,
   oneSmallCutoffRow_41,
   oneSmallCutoffRow_42,
   oneSmallCutoffRow_43,
   oneSmallCutoffRow_44,
   oneSmallCutoffRow_45,
   oneSmallCutoffRow_46,
   oneSmallCutoffRow_47,
   oneSmallCutoffRow_48,
   oneSmallCutoffRow_49,
   oneSmallCutoffRow_50,
   oneSmallCutoffRow_51,
   oneSmallCutoffRow_52,
   oneSmallCutoffRow_53,
   oneSmallCutoffRow_54,
   oneSmallCutoffRow_55,
   oneSmallCutoffRow_56]







end D1Bound5
end


