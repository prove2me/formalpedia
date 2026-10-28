-- Prove2me | Definitions.Def_D1Bound5_SmallTripleExtensionData5_Definitions
-- name    : D1Bound5_SmallTripleExtensionData5_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:36:28.105431+00:00
-- url     : https://prove2.me/theorems/885040fc-9f00-40df-9c44-6cdebe633684
-- title:
--   Small Triple Extension Data5
-- statement:
--   Definitions for small triple extension data5 in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `smallTripleAnchorA_5`, `smallTripleAnchorB_5`, `smallTripleAnchorC_5`, `smallTriplePairClosure_5`, `smallTripleAllowed_5`.
-- source:
--   D1Bound5/SmallTripleExtensionData5.lean, lines 8-8, SHA-256 0f52c03dcb1aef0af13ae431869add34d508399252e4add0eccf7dd09dc092de; D1Bound5/SmallTripleExtensionData5.lean, lines 9-9, SHA-256 0f52c03dcb1aef0af13ae431869add34d508399252e4add0eccf7dd09dc092de; D1Bound5/SmallTripleExtensionData5.lean, lines 10-10, SHA-256 0f52c03dcb1aef0af13ae431869add34d508399252e4add0eccf7dd09dc092de; D1Bound5/SmallTripleExtensionData5.lean, lines 12-84, SHA-256 0f52c03dcb1aef0af13ae431869add34d508399252e4add0eccf7dd09dc092de; D1Bound5/SmallTripleExtensionData5.lean, lines 86-88, SHA-256 0f52c03dcb1aef0af13ae431869add34d508399252e4add0eccf7dd09dc092de. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def smallTripleAnchorA_5 : QuadInt 0 2 := ⟨1,-1⟩
def smallTripleAnchorB_5 : QuadInt 0 2 := ⟨1,1⟩
def smallTripleAnchorC_5 : QuadInt 0 2 := ⟨-2,0⟩

def smallTriplePairClosure_5 : List (QuadInt 0 2) := [
  ⟨-1326533741234356353218663833901520887754,0⟩,
  ⟨-95240837551170383713837915369096707992,0⟩,
  ⟨-6837984482029018775066981265833024130,0⟩,
  ⟨-490945197235879137099822352565629824,0⟩,
  ⟨-35248279273289144330531670085793402,0⟩,
  ⟨-2530712590168883527621028635477800,0⟩,
  ⟨-181696989075225056162730810895794,0⟩,
  ⟨-13045256884267258657202717063312,0⟩,
  ⟨-936607304516565038107227990570,0⟩,
  ⟨-67245378964651876298474804664,0⟩,
  ⟨-4828000988561230071419274722,0⟩,
  ⟨-346634875205344701395041440,0⟩,
  ⟨-24887264313595748111305434,0⟩,
  ⟨-1786825184995772163234632,0⟩,
  ⟨-128288276345062173979410,0⟩,
  ⟨-9210683835098272477104,0⟩,
  ⟨-661297346313640700042,0⟩,
  ⟨-47479013292697323480,0⟩,
  ⟨-3408839784121828674,0⟩,
  ⟨-244743685008277952,0⟩,
  ⟨-17571805994062650,0⟩,
  ⟨-1261598908599144,0⟩,
  ⟨-90578726325362,0⟩,
  ⟨-6503259955920,0⟩,
  ⟨-466913057514,0⟩,
  ⟨-33522849272,0⟩,
  ⟨-2406832290,0⟩,
  ⟨-172802784,0⟩,
  ⟨-12406682,0⟩,
  ⟨-890760,0⟩,
  ⟨-63954,0⟩,
  ⟨-4592,0⟩,
  ⟨-330,0⟩,
  ⟨-24,0⟩,
  ⟨-2,0⟩,
  ⟨0,0⟩,
  ⟨6,0⟩,
  ⟨88,0⟩,
  ⟨1230,0⟩,
  ⟨17136,0⟩,
  ⟨238678,0⟩,
  ⟨3324360,0⟩,
  ⟨46302366,0⟩,
  ⟨644908768,0⟩,
  ⟨8982420390,0⟩,
  ⟨125108976696,0⟩,
  ⟨1742543253358,0⟩,
  ⟨24270496570320,0⟩,
  ⟨338044408731126,0⟩,
  ⟨4708351225665448,0⟩,
  ⟨65578872750585150,0⟩,
  ⟨913395867282526656,0⟩,
  ⟨12721963269204788038,0⟩,
  ⟨177194089901584505880,0⟩,
  ⟨2467995295352978294286,0⟩,
  ⟨34374740045040111614128,0⟩,
  ⟨478778365335208584303510,0⟩,
  ⟨6668522374647880068635016,0⟩,
  ⟨92880534879735112376586718,0⟩,
  ⟨1293658965941643693203579040,0⟩,
  ⟨18018344988303276592473519846,0⟩,
  ⟨250963170870304228601425698808,0⟩,
  ⟨3495466047195955923827486263470,0⟩,
  ⟨48685561489873078704983381989776,0⟩,
  ⟨678102394811027145945939861593398,0⟩,
  ⟨9444747965864506964538174680317800,0⟩,
  ⟨131548369127292070357588505662855806,0⟩,
  ⟨1832232419816224478041700904599663488,0⟩,
  ⟨25519705508299850622226224158732433030,0⟩,
  ⟨355443644696381684233125437317654398936,0⟩,
  ⟨4950691320241043728641529898288429152078,0⟩
]

def smallTripleAllowed_5 : List (QuadInt 0 2) := [
  ⟨-24,0⟩
]









end D1Bound5
end


