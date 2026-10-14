-- Prove2me | Definitions.Def_TaoFivePrimes_RH14To100MomentCheckInterface
-- name    : TaoFivePrimes_RH14To100MomentCheckInterface
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T02:01:20.61908+00:00
-- url     : https://prove2.me/theorems/49329904-bc6e-4d9c-84d1-688067b853ff
-- title:
--   RH height 14–100 — moment validation types and functions
-- statement:
--   Lightweight types and Boolean validation functions for the original height-14–100 moment certificates. This interface defines the quadrature weights, moment arithmetic and record schemas, but contains no reconstructed panel bank or checked certificate values. The analytic moment theorem is separate.
-- source:
--   sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03), https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a. Theta/Mellin foundations attributed to Gabewhigham. Ordinary definitions extracted from the locally kernel-verified pilot.

/- Ordinary moment-certificate data structures and proposed values from
sometik179's original height-14–100 certificate. Theta/Mellin: Gabewhigham.
No analytic moment enclosure is asserted by this arithmetic data interface. -/
import Definitions.Def_TaoFivePrimes_RH14To100ThetaInterface
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs


set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.ambiguousOpen false
namespace RH14MomentEnclosureProof
section Height100Module62

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Finset
open scoped BigOperators

namespace CertifiedGlobalJetCenters
open _root_.CertifiedGlobalJetCenters
open CertifiedJetRecords CertifiedThetaPoints CertifiedFixedPoint
open _root_.CertifiedJetRecords _root_.CertifiedThetaPoints _root_.CertifiedFixedPoint
open CertifiedMomentConvolution CertifiedZetaQuadrature
open _root_.CertifiedMomentConvolution _root_.CertifiedZetaQuadrature

def addLists : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x::xs,y::ys => (x+y)::addLists xs ys

def sumLists : List (List ℤ) → List ℤ
  | [] => []
  | xs::xss => addLists xs (sumLists xss)

noncomputable def centerNumerators (i : Fin 16) : List ℤ :=
  addLists (List.replicate 184 0)
    (sumLists (List.ofFn (fun n : Fin 8 => (recordAt i n).fs)))

end CertifiedGlobalJetCenters

end Height100Module62

section Height100Module63

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedPackedCorrelation
open _root_.CertifiedPackedCorrelation
open CertifiedSignedODEConvolution CertifiedListODEVectors CertifiedPackedConvolution
open _root_.CertifiedSignedODEConvolution _root_.CertifiedListODEVectors _root_.CertifiedPackedConvolution

end CertifiedPackedCorrelation

end Height100Module63

section Height100Module64

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CertifiedMomentWeights
open _root_.CertifiedMomentWeights
open CertifiedMomentConvolution
open _root_.CertifiedMomentConvolution

def denominator : ℕ := 233398525209048950364126761403658816544333459669051688264166752003070906265328000

def weight (j : ℕ) : ℕ := if j%2=0 then 2*(denominator/(j+1)) else 0
def weights : List ℕ := List.ofFn (fun j : Fin 184 => weight j.val)

end CertifiedMomentWeights

end Height100Module64

section Height100Module65

namespace CertifiedExponentialIntegerSequence
open _root_.CertifiedExponentialIntegerSequence

end CertifiedExponentialIntegerSequence

end Height100Module65

section Height100Module66

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators
namespace CertifiedMomentArithmetic
open _root_.CertifiedMomentArithmetic
open CertifiedFixedPoint CertifiedExponentialIntegerSequence
open _root_.CertifiedFixedPoint _root_.CertifiedExponentialIntegerSequence
open CertifiedMomentConvolution
open _root_.CertifiedMomentConvolution

def qSequence : List ℕ := expSeq 12 184 0 (Nat.factorial 184)
def centerSequence (p : ℕ) : List ℕ := expSeq p 512 0 (Nat.factorial 512)
def scaledCorrelations (B : List ℤ) : List ℤ :=
  List.zipWith (fun b e => b*(e:ℤ)) B qSequence

def momentDenominator : ℕ :=
  16*scale310*CertifiedMomentWeights.denominator*(Nat.factorial 184)*(Nat.factorial 512)

end CertifiedMomentArithmetic

end Height100Module66

section Height100Module67

set_option autoImplicit false
namespace CertifiedPackedExtraction
open _root_.CertifiedPackedExtraction
open CertifiedSignedODEConvolution
open _root_.CertifiedSignedODEConvolution

end CertifiedPackedExtraction

end Height100Module67

section Height100Module68

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentRecords
open _root_.CertifiedMomentRecords
open CertifiedGlobalJetCenters CertifiedThetaCandidates CertifiedThetaPoints
open _root_.CertifiedGlobalJetCenters _root_.CertifiedThetaCandidates _root_.CertifiedThetaPoints
open CertifiedJetRecords CertifiedFixedPoint CertifiedPackedConvolution
open _root_.CertifiedJetRecords _root_.CertifiedFixedPoint _root_.CertifiedPackedConvolution
open CertifiedMomentArithmetic CertifiedListODEVectors CertifiedPackedExtraction
open _root_.CertifiedMomentArithmetic _root_.CertifiedListODEVectors _root_.CertifiedPackedExtraction

structure Record where
  h : List ℤ
  b : List ℤ
  z : List ℤ
  cp : ℕ
  cm : ℕ
  pp : ℕ
  pm : ℕ
  deriving Repr

def correlationBits : ℕ := 1536
def momentBits : ℕ := 7168

def correlationProduct (h : List ℕ) : ℕ :=
  encode correlationBits h.reverse * encode correlationBits CertifiedMomentWeights.weights

def panelParameter (i : Fin 16) : ℕ := 12*(2*i.val+1)

def momentProduct (c : List ℕ) (p : ℕ) : ℕ :=
  (encode momentBits c*encode momentBits (centerSequence p)) %
    Nat.shiftLeft 1 (momentBits*512)

def initialCondition (d : Record) : Prop :=
  d.h.length=184 ∧ d.b.length=184 ∧ d.z.length=256
instance (d : Record) : Decidable (initialCondition d) := inferInstanceAs (Decidable (_∧_∧_))

def correlationCarry (d : Record) : Prop :=
  (positiveList d.h).reverse.sum*CertifiedMomentWeights.weights.sum<2^correlationBits ∧
  (negativeList d.h).reverse.sum*CertifiedMomentWeights.weights.sum<2^correlationBits
instance (d : Record) : Decidable (correlationCarry d) := inferInstanceAs (Decidable (_∧_))

end CertifiedMomentRecords

end Height100Module68

section Height100Module69

namespace CertifiedExponentialSequenceCheck
open _root_.CertifiedExponentialSequenceCheck
open CertifiedExponentialIntegerSequence
open _root_.CertifiedExponentialIntegerSequence

end CertifiedExponentialSequenceCheck

end Height100Module69

section Height100Module70

namespace CertifiedPackedExponentialSequence
open _root_.CertifiedPackedExponentialSequence
open CertifiedPackedConvolution CertifiedExponentialSequenceCheck
open _root_.CertifiedPackedConvolution _root_.CertifiedExponentialSequenceCheck

end CertifiedPackedExponentialSequence

end Height100Module70

section Height100Module71

namespace CertifiedChunkedExponentialSequence
open _root_.CertifiedChunkedExponentialSequence
open CertifiedPackedConvolution CertifiedPackedExponentialSequence
open _root_.CertifiedPackedConvolution _root_.CertifiedPackedExponentialSequence

end CertifiedChunkedExponentialSequence

end Height100Module71

section Height100Module72

namespace CertifiedChunkedEncoding
open _root_.CertifiedChunkedEncoding
open CertifiedPackedConvolution CertifiedPackedExponentialSequence
open _root_.CertifiedPackedConvolution _root_.CertifiedPackedExponentialSequence
open CertifiedChunkedExponentialSequence
open _root_.CertifiedChunkedExponentialSequence

end CertifiedChunkedEncoding

end Height100Module72

section Height100Module73

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentSequenceCache
open _root_.CertifiedMomentSequenceCache
open CertifiedMomentRecords CertifiedMomentArithmetic CertifiedPackedConvolution
open _root_.CertifiedMomentRecords _root_.CertifiedMomentArithmetic _root_.CertifiedPackedConvolution
open CertifiedExponentialIntegerSequence CertifiedExponentialSequenceCheck
open _root_.CertifiedExponentialIntegerSequence _root_.CertifiedExponentialSequenceCheck
open CertifiedChunkedEncoding CertifiedListODEVectors CertifiedPackedExtraction
open _root_.CertifiedChunkedEncoding _root_.CertifiedListODEVectors _root_.CertifiedPackedExtraction

structure Aux where
  e : List ℕ
  chunks : List ℕ
  c : List ℤ

noncomputable def checkAux (i : Fin 16) (d : Record) (a : Aux) : Bool :=
  decide (a.e.length = 512) && decide (a.e.headD 0 = Nat.factorial 512) &&
  checkSteps (panelParameter i) 0 a.e &&
  checkChunks momentBits 32 a.e a.chunks &&
  decide (a.c = scaledCorrelations d.b)

noncomputable def checkCore (i : Fin 16) (d : Record) (a : Aux) : Bool :=
  decide (initialCondition d) && decide (d.h = CertifiedGlobalJetCenters.centerNumerators i) &&
  decide (correlationCarry d) &&
  decide (d.cp = correlationProduct (positiveList d.h)) &&
  decide (d.cm = correlationProduct (negativeList d.h)) &&
  decide (d.b = extract correlationBits 1 184
    (d.cp >>> (correlationBits*183)) (d.cm >>> (correlationBits*183))) &&
  decide ((positiveList a.c).sum*a.e.sum < 2^momentBits ∧
    (negativeList a.c).sum*a.e.sum < 2^momentBits) &&
  decide (d.pp = (encode momentBits (positiveList a.c)*encode (momentBits*32) a.chunks) %
    Nat.shiftLeft 1 (momentBits*512)) &&
  decide (d.pm = (encode momentBits (negativeList a.c)*encode (momentBits*32) a.chunks) %
    Nat.shiftLeft 1 (momentBits*512)) &&
  decide (d.z = extract momentBits 2 256 d.pp d.pm)

noncomputable def checkCached (i : Fin 16) (d : Record) (a : Aux) : Bool :=
  checkAux i d a && checkCore i d a

end CertifiedMomentSequenceCache

end Height100Module73

end RH14MomentEnclosureProof
namespace RH14MomentCertificateData
structure CheckedPanel (i : Fin 16) where
  record : RH14MomentEnclosureProof.CertifiedMomentRecords.Record
  cache : RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux
  valid : RH14MomentEnclosureProof.CertifiedMomentSequenceCache.checkCached i record cache = true
end RH14MomentCertificateData
def TaoFivePrimes_RH14To100MomentCheckInterface : Nat := 14


