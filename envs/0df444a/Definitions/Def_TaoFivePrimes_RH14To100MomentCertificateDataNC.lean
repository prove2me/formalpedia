-- Prove2me | Definitions.Def_TaoFivePrimes_RH14To100MomentCertificateDataNC
-- name    : TaoFivePrimes_RH14To100MomentCertificateDataNC
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T02:09:36.596043+00:00
-- url     : https://prove2.me/theorems/c9dbd842-b7f0-414a-b5e6-b0b516f24c91
-- title:
--   RH height 14–100 — ordinary mathematical moment-certificate data
-- statement:
--   The original proposed moment records, sequence caches, exact rounding data and dependent certificate schemas for the height-14–100 pilot. All numerical definitions are explicitly declared noncomputable to avoid unnecessary executable code generation. They remain transparent ordinary Lean definitions and their validity fields remain checked by the Lean kernel. This interface asserts no analytic enclosure.
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
noncomputable section
namespace RH14MomentEnclosureProof
section Height100Module0

open Finset
namespace CertifiedPackedConvolution
open _root_.CertifiedPackedConvolution

end CertifiedPackedConvolution

end Height100Module0

section Height100Module1

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution
open _root_.CertifiedMomentConvolution

end CertifiedMomentConvolution

end Height100Module1

section Height100Module2

open Finset

namespace CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

end CertifiedTaylorQuadrature

end Height100Module2

section Height100Module3

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution
open _root_.CertifiedMomentConvolution
open CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module3

section Height100Module4

open Finset
namespace CertifiedExponentialJets
open _root_.CertifiedExponentialJets
open CertifiedTaylorQuadrature CertifiedMomentConvolution
open _root_.CertifiedTaylorQuadrature _root_.CertifiedMomentConvolution

end CertifiedExponentialJets

end Height100Module4

section Height100Module5

open Finset
namespace CertifiedIntegerExponentialJets
open _root_.CertifiedIntegerExponentialJets
open CertifiedMomentConvolution CertifiedExponentialJets
open _root_.CertifiedMomentConvolution _root_.CertifiedExponentialJets

end CertifiedIntegerExponentialJets

end Height100Module5

section Height100Module6

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedSignedODEConvolution
open _root_.CertifiedSignedODEConvolution
open CertifiedIntegerExponentialJets
open _root_.CertifiedIntegerExponentialJets

end CertifiedSignedODEConvolution

end Height100Module6

section Height100Module7

set_option autoImplicit false
namespace CertifiedListODEVectors
open _root_.CertifiedListODEVectors
open CertifiedSignedODEConvolution
open _root_.CertifiedSignedODEConvolution
open Finset
open scoped BigOperators

end CertifiedListODEVectors

end Height100Module7

section Height100Module8

set_option autoImplicit false
open Finset
namespace CertifiedPackedHorner
open _root_.CertifiedPackedHorner
open CertifiedPackedConvolution
open _root_.CertifiedPackedConvolution

end CertifiedPackedHorner

namespace CertifiedPackedHorner
open _root_.CertifiedPackedHorner

end CertifiedPackedHorner

end Height100Module8

section Height100Module9

namespace ZetaSix

end ZetaSix

end Height100Module9

section Height100Module10

namespace TaoZetaBounds

end TaoZetaBounds

end Height100Module10

section Height100Module11

namespace TaoZetaBounds

end TaoZetaBounds

end Height100Module11

section Height100Module12

open Finset

namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module12

section Height100Module13

open Finset

namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module13

section Height100Module14

namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module14

section Height100Module15

open Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module15

section Height100Module16

open Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module16

section Height100Module17

set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxRecDepth 10000

namespace TaoZetaWide256

end TaoZetaWide256

end Height100Module17

section Height100Module18

open Finset
open scoped BigOperators
set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace TaoZetaGlobal

end TaoZetaGlobal

end Height100Module18

section Height100Module19

set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module19

section Height100Module20

set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module20

section Height100Module21

set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module21

section Height100Module22

open Finset
namespace CertifiedComplexTaylor
open _root_.CertifiedComplexTaylor
open CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

end CertifiedComplexTaylor

end Height100Module22

section Height100Module23

set_option autoImplicit false

namespace TaoZetaWide

end TaoZetaWide

end Height100Module23

section Height100Module24

namespace CertifiedLocalXi
open _root_.CertifiedLocalXi

end CertifiedLocalXi

end Height100Module24

section Height100Module25

open Finset
namespace CertifiedGlobalMoments
open _root_.CertifiedGlobalMoments
open CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedGlobalMoments

end Height100Module25

section Height100Module26

open Finset
namespace CertifiedEvenPolynomial
open _root_.CertifiedEvenPolynomial

end CertifiedEvenPolynomial

end Height100Module26

section Height100Module27

namespace CertifiedLocalXi
open _root_.CertifiedLocalXi

end CertifiedLocalXi

end Height100Module27

section Height100Module28

namespace CertifiedLocalXi
open _root_.CertifiedLocalXi

end CertifiedLocalXi

end Height100Module28

section Height100Module29

open Finset
namespace CertifiedLocalXi
open _root_.CertifiedLocalXi

end CertifiedLocalXi

end Height100Module29

section Height100Module30

open Finset
namespace CertifiedLocalXi
open _root_.CertifiedLocalXi

end CertifiedLocalXi

end Height100Module30

section Height100Module31

open Finset
namespace CertifiedPolynomialTranslation
open _root_.CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

end CertifiedPolynomialTranslation

end Height100Module31

section Height100Module32

open Finset
namespace CertifiedPolynomialTranslation
open _root_.CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature CertifiedGlobalMoments
open _root_.CertifiedTaylorQuadrature _root_.CertifiedGlobalMoments

end CertifiedPolynomialTranslation

end Height100Module32

section Height100Module33

set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

namespace CertifiedDenseGlobalPolynomial
open _root_.CertifiedDenseGlobalPolynomial
open Finset CertifiedPolynomialTranslation
open _root_.CertifiedPolynomialTranslation

end CertifiedDenseGlobalPolynomial

end Height100Module33

section Height100Module34

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedFixedPoint
open _root_.CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module34

section Height100Module35

set_option autoImplicit false
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
namespace CertifiedFixedPoint
open _root_.CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module35

section Height100Module36

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open _root_.CertifiedThetaPoints
open CertifiedFixedPoint
open _root_.CertifiedFixedPoint

end CertifiedThetaPoints

end Height100Module36

section Height100Module37

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators

namespace CertifiedHighPrecisionPi
open _root_.CertifiedHighPrecisionPi

end CertifiedHighPrecisionPi

end Height100Module37

section Height100Module38

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option Elab.async false

namespace CertifiedHighPrecisionPi
open _root_.CertifiedHighPrecisionPi

end CertifiedHighPrecisionPi

end Height100Module38

section Height100Module39

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedFixedPoint
open _root_.CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module39

section Height100Module40

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace CertifiedThetaPoints
open _root_.CertifiedThetaPoints
open CertifiedFixedPoint CertifiedHighPrecisionPi
open _root_.CertifiedFixedPoint _root_.CertifiedHighPrecisionPi

end CertifiedThetaPoints

end Height100Module40

section Height100Module41

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open _root_.CertifiedThetaPoints
open CertifiedFixedPoint
open _root_.CertifiedFixedPoint

end CertifiedThetaPoints

end Height100Module41

section Height100Module42

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CertifiedThetaCandidates
open _root_.CertifiedThetaCandidates
open CertifiedThetaPoints CertifiedFixedPoint
open _root_.CertifiedThetaPoints _root_.CertifiedFixedPoint

end CertifiedThetaCandidates

end Height100Module42

section Height100Module43

namespace CertifiedStreamingODE
open _root_.CertifiedStreamingODE
open CertifiedSignedODEConvolution
open _root_.CertifiedSignedODEConvolution

end CertifiedStreamingODE

end Height100Module43

section Height100Module44

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedJetRecords
open _root_.CertifiedJetRecords
open CertifiedThetaCandidates CertifiedThetaPoints CertifiedFixedPoint
open _root_.CertifiedThetaCandidates _root_.CertifiedThetaPoints _root_.CertifiedFixedPoint
open CertifiedListODEVectors CertifiedPackedConvolution CertifiedStreamingODE
open _root_.CertifiedListODEVectors _root_.CertifiedPackedConvolution _root_.CertifiedStreamingODE

end CertifiedJetRecords

end Height100Module44

section Height100Module45
namespace CertifiedJetRecords
open _root_.CertifiedJetRecords
open _root_.CertifiedJetRecords
end CertifiedJetRecords
end Height100Module45

section Height100Module46

end Height100Module46

section Height100Module47

namespace CertifiedJetRecords
open _root_.CertifiedJetRecords

end CertifiedJetRecords

end Height100Module47

section Height100Module48

set_option autoImplicit false
namespace CertifiedJetRecords
open _root_.CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedSignedODEConvolution
open _root_.CertifiedFixedPoint _root_.CertifiedThetaPoints _root_.CertifiedSignedODEConvolution
open CertifiedListODEVectors CertifiedStreamingODE CertifiedIntegerExponentialJets
open _root_.CertifiedListODEVectors _root_.CertifiedStreamingODE _root_.CertifiedIntegerExponentialJets

end CertifiedJetRecords

end Height100Module48

section Height100Module49

set_option autoImplicit false
namespace CertifiedFixedPoint
open _root_.CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module49

section Height100Module50

namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module50

section Height100Module51

open Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
set_option exponentiation.threshold 512
open CertifiedTaylorQuadrature CertifiedMomentConvolution
open _root_.CertifiedTaylorQuadrature _root_.CertifiedMomentConvolution

end CertifiedZetaQuadrature

end Height100Module51

section Height100Module52

open Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution CertifiedExponentialJets
open _root_.CertifiedTaylorQuadrature _root_.CertifiedMomentConvolution _root_.CertifiedExponentialJets

end CertifiedZetaQuadrature

end Height100Module52

section Height100Module53

open Finset
namespace CertifiedJetRecords
open _root_.CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedIntegerExponentialJets
open _root_.CertifiedFixedPoint _root_.CertifiedThetaPoints _root_.CertifiedIntegerExponentialJets
open CertifiedZetaQuadrature CertifiedMomentConvolution CertifiedTaylorQuadrature
open _root_.CertifiedZetaQuadrature _root_.CertifiedMomentConvolution _root_.CertifiedTaylorQuadrature

end CertifiedJetRecords

end Height100Module53

section Height100Module54

open Finset
namespace CertifiedMomentConvolution
open _root_.CertifiedMomentConvolution
open CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module54

section Height100Module55

open Finset
namespace CertifiedMomentConvolution
open _root_.CertifiedMomentConvolution
open CertifiedTaylorQuadrature
open _root_.CertifiedTaylorQuadrature

set_option exponentiation.threshold 512

end CertifiedMomentConvolution

end Height100Module55

section Height100Module56

open Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module56

section Height100Module57

open Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module57

section Height100Module58
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
end CertifiedZetaQuadrature

end Height100Module58

section Height100Module59

open Finset
namespace CertifiedGlobalQuadrature
open _root_.CertifiedGlobalQuadrature
open CertifiedZetaQuadrature CertifiedTaylorQuadrature
open _root_.CertifiedZetaQuadrature _root_.CertifiedTaylorQuadrature

end CertifiedGlobalQuadrature

end Height100Module59

section Height100Module60

open Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
open CertifiedMomentConvolution CertifiedTaylorQuadrature
open _root_.CertifiedMomentConvolution _root_.CertifiedTaylorQuadrature

end CertifiedZetaQuadrature

end Height100Module60

section Height100Module61

open Finset
namespace CertifiedZetaQuadrature
open _root_.CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution
open _root_.CertifiedTaylorQuadrature _root_.CertifiedMomentConvolution
set_option exponentiation.threshold 1024

end CertifiedZetaQuadrature

end Height100Module61

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

noncomputable def addLists : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x::xs,y::ys => (x+y)::addLists xs ys

noncomputable def sumLists : List (List ℤ) → List ℤ
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

noncomputable def denominator : ℕ := 233398525209048950364126761403658816544333459669051688264166752003070906265328000

noncomputable def weight (j : ℕ) : ℕ := if j%2=0 then 2*(denominator/(j+1)) else 0
noncomputable def weights : List ℕ := List.ofFn (fun j : Fin 184 => weight j.val)

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

noncomputable def qSequence : List ℕ := expSeq 12 184 0 (Nat.factorial 184)
noncomputable def centerSequence (p : ℕ) : List ℕ := expSeq p 512 0 (Nat.factorial 512)
noncomputable def scaledCorrelations (B : List ℤ) : List ℤ :=
  List.zipWith (fun b e => b*(e:ℤ)) B qSequence

noncomputable def momentDenominator : ℕ :=
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

noncomputable def correlationBits : ℕ := 1536
noncomputable def momentBits : ℕ := 7168

noncomputable def correlationProduct (h : List ℕ) : ℕ :=
  encode correlationBits h.reverse * encode correlationBits CertifiedMomentWeights.weights

noncomputable def panelParameter (i : Fin 16) : ℕ := 12*(2*i.val+1)

noncomputable def momentProduct (c : List ℕ) (p : ℕ) : ℕ :=
  (encode momentBits c*encode momentBits (centerSequence p)) %
    Nat.shiftLeft 1 (momentBits*512)

noncomputable def initialCondition (d : Record) : Prop :=
  d.h.length=184 ∧ d.b.length=184 ∧ d.z.length=256
noncomputable instance (d : Record) : Decidable (initialCondition d) := inferInstanceAs (Decidable (_∧_∧_))

noncomputable def correlationCarry (d : Record) : Prop :=
  (positiveList d.h).reverse.sum*CertifiedMomentWeights.weights.sum<2^correlationBits ∧
  (negativeList d.h).reverse.sum*CertifiedMomentWeights.weights.sum<2^correlationBits
noncomputable instance (d : Record) : Decidable (correlationCarry d) := inferInstanceAs (Decidable (_∧_))

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

section Height100Module74

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedMomentRecords
open _root_.CertifiedMomentRecords

noncomputable def cacheChunks : ℕ → List ℕ → List ℕ
  | 0,_ => []
  | n+1,xs => CertifiedPackedConvolution.encode momentBits (xs.take 32)::cacheChunks n (xs.drop 32)

open CertifiedListODEVectors CertifiedPackedExtraction CertifiedMomentArithmetic
open _root_.CertifiedListODEVectors _root_.CertifiedPackedExtraction _root_.CertifiedMomentArithmetic

noncomputable def compactMomentRecord (i : Fin 16) : Record :=
  let h := CertifiedGlobalJetCenters.centerNumerators i
  let cp := correlationProduct (positiveList h)
  let cm := correlationProduct (negativeList h)
  let b := extract correlationBits 1 184
    (cp >>> (correlationBits*183)) (cm >>> (correlationBits*183))
  let c := scaledCorrelations b
  let pp := momentProduct (positiveList c) (panelParameter i)
  let pm := momentProduct (negativeList c) (panelParameter i)
  let z := extract momentBits 2 256 pp pm
  ⟨h,b,z,cp,cm,pp,pm⟩
@[noinline] noncomputable def pointRecord.«0» : Record := compactMomentRecord (0 : Fin 16)
@[noinline] noncomputable def sequenceCache.«0» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (0 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«0».b⟩
@[noinline] noncomputable def pointRecord.«1» : Record := compactMomentRecord (1 : Fin 16)
@[noinline] noncomputable def sequenceCache.«1» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (1 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«1».b⟩
@[noinline] noncomputable def pointRecord.«2» : Record := compactMomentRecord (2 : Fin 16)
@[noinline] noncomputable def sequenceCache.«2» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (2 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«2».b⟩
@[noinline] noncomputable def pointRecord.«3» : Record := compactMomentRecord (3 : Fin 16)
@[noinline] noncomputable def sequenceCache.«3» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (3 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«3».b⟩
@[noinline] noncomputable def pointRecord.«4» : Record := compactMomentRecord (4 : Fin 16)
@[noinline] noncomputable def sequenceCache.«4» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (4 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«4».b⟩
@[noinline] noncomputable def pointRecord.«5» : Record := compactMomentRecord (5 : Fin 16)
@[noinline] noncomputable def sequenceCache.«5» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (5 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«5».b⟩
@[noinline] noncomputable def pointRecord.«6» : Record := compactMomentRecord (6 : Fin 16)
@[noinline] noncomputable def sequenceCache.«6» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (6 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«6».b⟩
@[noinline] noncomputable def pointRecord.«7» : Record := compactMomentRecord (7 : Fin 16)
@[noinline] noncomputable def sequenceCache.«7» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (7 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«7».b⟩
@[noinline] noncomputable def pointRecord.«8» : Record := compactMomentRecord (8 : Fin 16)
@[noinline] noncomputable def sequenceCache.«8» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (8 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«8».b⟩
@[noinline] noncomputable def pointRecord.«9» : Record := compactMomentRecord (9 : Fin 16)
@[noinline] noncomputable def sequenceCache.«9» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (9 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«9».b⟩
@[noinline] noncomputable def pointRecord.«10» : Record := compactMomentRecord (10 : Fin 16)
@[noinline] noncomputable def sequenceCache.«10» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (10 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«10».b⟩
@[noinline] noncomputable def pointRecord.«11» : Record := compactMomentRecord (11 : Fin 16)
@[noinline] noncomputable def sequenceCache.«11» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (11 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«11».b⟩
@[noinline] noncomputable def pointRecord.«12» : Record := compactMomentRecord (12 : Fin 16)
@[noinline] noncomputable def sequenceCache.«12» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (12 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«12».b⟩
@[noinline] noncomputable def pointRecord.«13» : Record := compactMomentRecord (13 : Fin 16)
@[noinline] noncomputable def sequenceCache.«13» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (13 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«13».b⟩
@[noinline] noncomputable def pointRecord.«14» : Record := compactMomentRecord (14 : Fin 16)
@[noinline] noncomputable def sequenceCache.«14» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (14 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«14».b⟩
@[noinline] noncomputable def pointRecord.«15» : Record := compactMomentRecord (15 : Fin 16)
@[noinline] noncomputable def sequenceCache.«15» : CertifiedMomentSequenceCache.Aux :=
  let e := CertifiedMomentArithmetic.centerSequence (panelParameter (15 : Fin 16))
  ⟨e,cacheChunks 16 e,CertifiedMomentArithmetic.scaledCorrelations pointRecord.«15».b⟩
@[noinline] noncomputable def _root_.RH14MomentEnclosureProof.CertifiedMomentRecords.panelBank : (@_root_.List (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)) :=
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«0»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«1»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«2»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«3»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«4»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«5»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«6»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«7»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«8»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«9»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«10»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«11»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«12»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«13»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«14»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.pointRecord.«15»)
  (@_root_.List.nil
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.Record))))))))))))))))))

@[noinline] noncomputable def _root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCacheBank : (@_root_.List (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)) :=
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«0»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«1»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«2»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«3»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«4»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«5»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«6»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«7»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«8»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«9»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«10»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«11»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«12»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«13»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«14»)
  (@_root_.List.cons
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux)
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentRecords.sequenceCache.«15»)
  (@_root_.List.nil
  (@_root_.RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux))))))))))))))))))

@[noinline] noncomputable def sumRow.«16» : List ℤ := []
@[noinline] noncomputable def sumRow.«15» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«15».z sumRow.«16»
@[noinline] noncomputable def sumRow.«14» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«14».z sumRow.«15»
@[noinline] noncomputable def sumRow.«13» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«13».z sumRow.«14»
@[noinline] noncomputable def sumRow.«12» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«12».z sumRow.«13»
@[noinline] noncomputable def sumRow.«11» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«11».z sumRow.«12»
@[noinline] noncomputable def sumRow.«10» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«10».z sumRow.«11»
@[noinline] noncomputable def sumRow.«9» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«9».z sumRow.«10»
@[noinline] noncomputable def sumRow.«8» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«8».z sumRow.«9»
@[noinline] noncomputable def sumRow.«7» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«7».z sumRow.«8»
@[noinline] noncomputable def sumRow.«6» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«6».z sumRow.«7»
@[noinline] noncomputable def sumRow.«5» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«5».z sumRow.«6»
@[noinline] noncomputable def sumRow.«4» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«4».z sumRow.«5»
@[noinline] noncomputable def sumRow.«3» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«3».z sumRow.«4»
@[noinline] noncomputable def sumRow.«2» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«2».z sumRow.«3»
@[noinline] noncomputable def sumRow.«1» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«1».z sumRow.«2»
@[noinline] noncomputable def sumRow.«0» : List ℤ := CertifiedGlobalJetCenters.addLists pointRecord.«0».z sumRow.«1»

@[noinline] noncomputable def _root_.RH14MomentEnclosureProof.CertifiedMomentRecords.roundedNumerators : (@_root_.List (@_root_.Int)) :=
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  230337744934871206978100825168182415416511235383585125341261280)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  40521025678005477415456616733783672132802773496266119565479671793)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4474037647682628329675671257143783483010223849002749953812275576994)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  351481606056109814371215101276232647382890680092901678739777715030727)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21079322957780478348614085877194415708902446857461078509372025895219048)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1009906114954808594635649856423182566693468066012802252484490411697737673)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  39903750943173106741665468822383755693987872165751985529597445144845680539)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1331470276361406723382990211054507272438448335323970548523937999689088179798)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  38210603612544347746315297629478780370009798584563038472487139984253116180534)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  957002659355094357051996352730687697044637763073824082397908009095374325090813)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21169112240876900122895473916783501561578580865741024483646570063992924488197112)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  417707216394437395069182164041149338016821602508332594906122329231102621263511994)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  7414448651866805443080890666142606697008549203242062339680258167052349871440493647)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  119251079574613808442263180612819754528069143272698342764324606930311890518183788945)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1748827836515974891785470840690180915227738473359199733984814329944979037706203206215)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  23513723985769920939217262691957387645837874121950613396068533358212430466909663734953)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  291270693313355443376206815370169006340788048154649240517879787074749061828146378513085)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3338518131038545549138164387804051538738418214480060569168393458696955129363494882040444)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  35544985229591172625684774299524936842802041283057434755286810486152610397600730676270022)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  352769653373032509609294502733122625725691175349819236585001236636052871362825144240626591)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3273942665769892066201192175725157345610380961494525744239269899064956498739987174598171564)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  28495341128344223264466382890880235996054876098944147947017153717987076374357885201505864504)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  233210830796486179752541507992613355223459727378496691445694279470086198699800967116313064979)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1799082808553918074328921290271516627531882269244807441711139435166392296396227287227260877117)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  13111555063527463899658137982623050846424460849761654802608628406121496667428135423995979666172)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  90460258395567983297826010561080796586035155156165822644366792665546611035938819704943792696021)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  591966227421235819961939370242284921900605584099330505613232297216647356213622414218353866061424)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3680851328381476238093626711503856449769026470186667050464951856397664754592000951305749289737319)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21783938234617465080465127501663179183803511947053137835933650329491848105998827901501454613760898)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  122896286345298928202889691868195211018389050672765997938259510159468210422008747289629807082647581)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  661896764059095544418944509051882905440391939571062170853784862967738469690496177016535758832757507)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3407902375649385423255931472837615584956129100135229867353169374123845800389531134558494071019059342)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  16795405641116791769934676225690695569672686211415590869989697594699871268080253179556179036897751009)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  79328504834735992797961735483857995183186360903777911376594540590744634700654477288783620592366924670)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  359503402400251072302632420442272446033649605800195348037908812570660365117829316867924629309956614099)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1564891578809607683837439345958753793693489138324228564605133413470409915656456978041071303134103249258)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6549689607050495289748831679864012911033094229985282350613899131183797739851433544424314683038868332273)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  26383790673483976500802973951375480799101840989213513544639973606510202222807435321190830414439171669686)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  102385224069815496424048117347336775593083111413716788412394968958275130923522935816824924157860649531804)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  383093681304377101691157527548427416104242535409492481225575791167407445709517213576338822897395161226712)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1383267233012268096728763043982505147210531055195534803842484055609078069845426765276971794093832361387402)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4823801669256233717509961639779626798180498814081390138875458993263767919832791832099673248596818563159920)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  16258786912812242851070023368221738286650130503766421712302217438297804186103604983098180301577585905467889)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  53005453321238144063475135375553213102108249789666361835289818298916112267130272552203426619277441277344180)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  167259699739909746586097975739608894466640887421980309589859051356015158300103430632898041582321425576128576)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  511201569199618328388682035642015183716223428657078761898530422970635251622387085480862514343916963521077446)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1514268360033576699239629210702377404203157316318801040737917153348240908029663237214898033548070250584733811)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4350024466032531736137485651158028549124851735541798791494414684336922034796622944044073832763356867556942868)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  12125969447371700538144145523858465768072390111850709665141931270113182005634337628419551349269330031662963366)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  32818965027713334774607672466550353878562293347435903669565112216134936692058699526343165169275653890933439669)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  86288957294445055453723896102565961035526299123475221068609509920240769688194119818758828575657862598883674965)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  220514359448124013124360309693042963618313305251717885468867657801667275549776073439190573376017655961643565449)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  548012950584713318471240374180930833187282403868929268726136061469816186554298556635017901922413077283474191585)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1325043362697313661267273124401190889083615877032306762592870194947488991977360359051896126781680612887009017353)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3118603695531478887931894731224078196241574803072467660459290885064421736913864638145833839019274111024284178871)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  7147916901257877142451613994534244498891099975609559706458204629373123562644743662953505755920004710191712756016)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  15961717749099447270220922223775485461823794648968745871376060444538355296492143824801841686549146792872238636673)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  34741277717018998441055817119538311887331505553002022821256599645183350195301304725940839221873166398824406255724)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  73732180885805818997195033400198578417488576000375397042723824904020656267752346541585961063534657631169786041169)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  152646486618753505797712642726787604838126950708161968694527464265762385133015854388207189859135513562504335527355)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  308391766521426586150620190528414116333451354928206260327662435502671379948002469750059156354308268726793350292723)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  608229524880516581095696726084999815537489900506554426024281557583402842240547443625026397508703078707024412270470)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1171489780547940326466838979833870263082176599874865247882354536210955207753067997058796643245282944398760353931680)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2204289008369331614211393192734969310993912795935596010424838156469634079887456127982902722961703777789873768480800)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4053272171115841125896038746079161026203787208888575616201569194886653253250115135638516581780654873154752919733383)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  7286081356399804410160825762798926719343870265243834117930823813855264120555140941345143137203971444012418987732555)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  12807752599681632682594465631968923341882774085929257005367947208425015821862785875704479277157417194951509064851554)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  22023085559476589648315906949873989177570956203642298778304535176403880895601429389498726489101536252388787443069479)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  37054551713705799431963597350577060771485155049770234531134872484328507438646736753642822364035197057628436606185227)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  61022683659403032432002100378529671339726819561070662378704454026256648512252694334542358434747243494807425892910799)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  98390248774068934267818496253608159345669527825577705641147623001679881612399922307052470703199684162013657401011607)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  155362120504156392253006756819371502102861726633411812665843332583965484456445617692055288014314955685357000879132586)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  240319288647697787465250087363441510160595712827731040046055083334949488764089353082400005936884487491991342670001249)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  364248280011243983928797243522795257841133934717581745518237469613634674608997694881711842161524294553001711362349831)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  541107787007418697784410183201362294013501196179903694285905223858669966419416449768821043307339417314748895183543560)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  788055116748299936781383114393733450895207237085888709262836318213897820100190754347406783931034451016357600308195398)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1125439944043561652792779094446107559017022660671637247540184756636004062239697789015159637919979694881578422773395940)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1576466392591880596347199661982691471137965810011608752063057918239854687430762539239506937852725634307541914456967142)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2166431465244016535258128801836656334132133849122055142594873758332598963983219213131361100894413176725852844603534717)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2921472264772708457662769876573055850874158803435613538737788515162063294914296659613122157034663860123284769475102159)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3866798274909779750378055930680577087707182518092710812078820332062061610144690701018715392851875319483457861788565354)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5024447094416485861170639375149215236523823673073569482122014224502665642438287774083100379864705927284553385868245589)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6410677462716058256830386674163337664583441535138435840987126266048393328101290064509314879101735491193198555649041922)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  8033193236813446749855158340740884468890791939824631423641032097492682601375716611501805580601185352745911567540370250)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  9888463992892261026294399053302050353315475755986770043146024921981751181573528907016258458696004950479378982133934344)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  11959458355805667432840357083911271779243644253904285353297505408346295891788543248174284203189065026354757519898461126)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  14214122009168935492411437611278131328892767265799177436345601839295380919886842683727210518722209651174934101709415441)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  16604904102785954468612350603108138951522203916254430092706955436179017489435843836894531335025626336091447025454085867)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  19069559934555604974272203556854497191679987078795605860357947493854713111245860525506225114474583435991010916615538655)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21533338488066587164394371988267857042086587760873074203424439347967880800321413106237897063512771708831624360098066115)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  23912512827567368520471245946349022060662646536742222538662198688126551288707656235987546918074812350659353424398720060)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  26119048469582367014988263488255144442775100970635030486929259871895764787873083662704672194888052583349584279025495951)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  28066052736065570155910996473431311562695168169936040290420597647273733027223147204134799510380805402299634636973088997)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  29673530122311393504673243590584568917775152462440663883020155148884218775544068780749032414317681680851346014662324924)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  30873904418246021375508235302891495972536309292439648952355343855120366032945067167079339323237329862993950325768156985)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  31616769736638708498485330717603240395631976551395580032763282800241942160595581701264757530264366886817991084104754222)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  31872401853628104556682396338515436084415629360127184333764883027551715987188171490159605085528753830484618024383083395)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  31633689961338423795524837129142484707100960356733319867405068202285497053189176103942739918717739211535212223311035615)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  30916319474063644929093298891980903097400265550750296554278385658800961810071064937323249376826867178222643985715472643)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  29757225120046884352371459059332046256328854231758780953161282104759368970069694311566051451638609037760381035606472228)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  28211514250876815925070829636244409132019321224818761063927215945801499961477186047300747881032585585197972117238257682)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  26348209340089073455502688921264956471113530343208911202852767530395999551093900924914267382432742076796253308723124053)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  24245258146092610141417955823902796228146542823828446491405190889214568825838575574944571757921313966461982947712186691)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21984300471538932719014158205683329480515331440037348623648165494525900336376354971565810031874668106204673722403591305)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  19645661563473902849622212119234762090192892736824460045757115798855759825972767722205302170999291058154928294410808391)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  17303972086882990323347546994630570986381389383150177448531080322087827998216413415331616626748808246991738244020703427)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  15024707681771443125228122817061082970304835954624598181834779529296532559599966890044946529984599157163083972762964315)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  12861815158134630571814639260113417124123533051006205795871069473099645877468926637509083386436492322031698224795879472)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  10856465426923995844148268577020183218910516313331689568430848289913452548213222422114343357044101462560043691928382155)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  9036860879065487806368715471363029470570340033033666499983088167548642203675725409729224351270421962103748712506200999)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  7418938305539314973164751917034906166089750341845617578379201791312644816269906264863651249751131508729451077711335286)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6007753516400793449864977883785246682598153650004064162729661575917763140706103782026762892886531136508243760980395238)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4799311283444681351323325635120794438156327909124966865128343046689550714342820801947252457868227820991338080957981657)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3782610492737314363585041922809291142303162768195030715034604995776496649488237622638069013662080912617744810433363740)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2941702883719540247753618494519485391372258014759462620867620811061959885937975917230257685345598793502195846336844532)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2257606480431147015634527243756413241092724517247810393168459660617037098489921245838683690770426137041152705415001897)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1709963786594029934198148238161219942785634838863411701208172989743005906745803797948514281033620633312478943475591334)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1278383102108132602914421361878262378158352979339386496251673552331256302548278850874604727649696315422970207826971988)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  943443763558944612318017707610808411273887314735250432224416427802887561567347223675471118089514646927394817877515471)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  687379563251394684755067780715941995323445651468136693575339997585136956681214036120488521458135739594657030439537169)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  494477812054412051850217461144623224737510897609951119568730385848780066648952390895154674654194847261363653201510939)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  351244789036113620270913445498910441870570534242033732902968911487802793610087389836905272625600865367917833372786896)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  246393057296385527927625321801261584958429554665349433629837825203149306004573134099703916107541845397820854118182731)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  170704306511498144832131365133348094690576538087043079584676446264136204386565688161873242797837624176850679225618006)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  116815160441825511579597983372462433697761608772487210730254955409765946275095566513344232870818847525772280647190139)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  78964758551213488567191741501448918974074810491770403187942454495016129340408120865933118055438818901596375352400124)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  52733525787778959850093870273125969060751345987106333399282340713222661814000048079714128034946992652815449139207094)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  34793580278346091081561925170229068398788469309261747585284095701998834829406913551667770423511983416414489431588675)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  22683447823210819510840556670341483911283287054625912140906130879751010151406524119083066874989610438225058271674139)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  14613521773999908153576242585867167705748049021504075955887079974772880637663896698379791832865959290753102610359217)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  9304097786168062233919889702895019864127394590317242394183882927491824365101373899113482989434491834341249875394142)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5854695471590296594889268485516069710624502931626792698643369273633070248946396071107965676660081652159775479677374)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3641510768964107417180507143758806896272182343659176857733024908494371024894190125898556739215964365407358287805250)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2238938551548087204043180353426761744867432305741688037386512686964575599373813756749606195915481205729546298344035)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1360885421330486093682026502271488948212604237540682412072580849542756178111097563063528042102124898118787448570536)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  817814442757512222191498690548480755255908110387124058086076137406343528204424030574211684453019871896896485385327)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  485932935304902485532170910497585908805188414244843874851724444621448721353524033401848093861107235095246531882998)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  285509307783714983951466760154658945128542251471548036259267581372277817257527323122444062964170876560291183093961)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  165889973386589654877158296650175768336046352771272056895425710234530369314682757151126263140977580729158438175944)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  95325484777461657595177313088853274881009194580162690699427886083499598193650976792720736744279178530089542077821)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  54177574428624942806329572906961615291850676073509562539302795042159473769008174255146586362645538606613036575596)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  30456775763927113466073714225469630453135090212335782121720343984871294520034649202655590328680543320866097004887)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  16936898050875261249102959812866180441801909978744473925308521906586332475592442117343579794686059022012701588370)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  9317528210135331745884269504579959252549755746191899203994783915592278645937426361319676857122436776526076593905)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5071253851409451194529197009000903828500390748571667978434131758119884995335124312752267541980288874352600902642)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2730915483896227844291346380728564275966996781699100837078740352126306404706831244432968819696621582179789353986)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1455155899101426667562329508852122212401563629446993923938819029776785019679114132599142345164519453291371396850)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  767271078112243542872014583274611064826529388547039749236929573309609013846595080955271359518759363838254688122)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  400364412855510914705351579923493252269719224169127031331058385937738738722804181457111247525881769265725012549)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  206756112848320950299126263066873832337706173026969870983750191987947494592287962740177768376060718343683745802)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  105678355003605692066794025514549455806012201220062138851900921351412831646318793911879824061609488473686071150)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  53464646831642376647760878621640675417407056521717965017467225622273550580502346884310850968099206718651731163)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  26774918106615866193036307190810755244898150238624382293098356671627280189477945355937315554942734635720191340)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  13273879099850554908931965571781108787668622397939498185378583368143511526558818357815268334652659122428222404)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6514827842479392165031781418775183687880260186024336708113265137112123439289265245887832825786622276993332118)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3165703179774824618086768989640998123745923155894566626852580956614691239826936451631752133053985423195554778)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1523091711261223364068703398571961436126544028045975800154231033484571374940418360436581853832763232946509370)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  725598966115632643891052880061095851796853223215076616625309797677360375538038964581349381103467892646913777)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  342300709155401550254929486278323892647613868640702992553576620034732212487899071298259805629037777553886196)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  159913443840765758647254087712649319839494340822775911838391191982702433349259917353376849153848601404280854)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  73986650981835381262877710348956892281457683674913100289706824914159828407701304084401946042543369618586808)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  33902978772603085559596380624168863702614844091091365457344330328324635085280554632014188452404079317475776)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  15387321335580810055720039958490666664152019075782669011076303451419272284438251729996094032758834944962391)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6917563526809352821660728922599506854507371885081832380572043324121401129842343124659841649268636865448261)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3080578353422031391087923828966453956408314324983125302078899635582350534130147055876842329965119154660134)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1359014387758804552797279302384167444186322963556937131272306014488640427451808723143888038531316477116082)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  593952871734669351352614675366201680438326404109783533863605871378540181710918909004191933764580691660237)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  257181205609381363445474742255526888919011444656487668987937061184880954029124176110164821981500675200467)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  110333827571476178283805974572422078241923994869405228823571824976813835443464159149617092454601443846856)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  46901096849359548598030680892988600441945956833899401006836693275901420201442377073625181036969722002401)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  19755342244704333562853842753561747862367681632745902144886839983216306792444025802084499395764742337696)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  8245851158358469345831580273399339388878368624409501035288102986958210435536871351748583632669473652001)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3410811212489669455387005762578972016401218506714583352046524601265310812167666205970074317356767488210)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1398211169295878244953717693619777455700273627219000854373461124757180789801012323138332582661781135955)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  568070376924269854258908334669388668339020728965513199837951168077962876904314029570652046087170143636)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  228753089573969858797539365414537630455718843484395797755581041643323701890505222030291484736930509413)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  91303656490973206429870244988201108681940160409246801292555423368916752806781704737771709294173274326)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  36123219135367658635354255660358276393724511694550236673574519457168694368623170425579131030450443032)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  14167142634018493661728131641245212439054101759777379865676285226039498762611842360757890130796016317)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5508024743594246970220057476792118666813498790747765443471363665982435928922200540054110167403127826)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2122986958788415678036076216755721467920224495089087434457396677308891001315768419817478101313173333)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  811253185948006252156337030880053540675415404880160201386596766203745964611164179453393158826618382)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  307356750554571663111671953857747333623712185976516135243833759786556378019769281026411291637668679)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  115458456482844912278364916051942933587315365338516480858036415783544939131370493459272978994569008)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  43005557640193437513758370485790451828343922428909937834340925228009171326936765425702338164717394)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  15883940722434315555583526513098283513428158550630296853696526294727739372165299661373887480197655)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5817622880100087289706471368268897823925865461094279778685530167794735633184587586512605554094139)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2113027292388215383384902730748577800965869698254445976104928225671717828483657681964463901815814)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  761123778402704116290219071467663639037645253999010817405412392379819402620129089770796174579985)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  271903210325061929562216655058598158652380701216334257562881898232453000901024256602841866154467)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  96338587819901656764277777811343395898370623624615114974481554932817621444371573457547156043027)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  33855634887481753601934627470482488249490093978944039022978218200323715028386602618333004613559)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  11801142784660292186534810895891576637620037023985003722554303488879101684409685068181512409756)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  4080346797004230778284237670592229353363951694847475434032435654359930307364639214392562719754)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1399481989559843430660920757181499912956361150288886898083540907610469273025768568401200092913)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  476158918311473346377755538381091878761081950130130398354706346638323919655542280116848758666)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  160719243492927760573229511524478280117459965816923882158044386161166424281530519837520022895)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  53818549913498936685516959468622130449770070432897552830458261816568092357816117751735593512)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  17879727850704803165154005146105716568141667156875353452403019822385690549854063241717431229)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5893470274131850050455164699819786557069644888091093665784854499907028684197178150140971172)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1927431238333024601928975790464443931942664671629763405595811934073370469604414666977622512)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  625461318901260630002780142214188309568333154119687878014743394258733320466146951484989487)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  201396442462929629780557831201350302328678907688739924332273516443432730099118970359446013)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  64350031595480698195187632786846164018625605752032864882432663738108508088856005377758103)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  20403612659279058811629855164303095980734681564212864555437616704918751116012388731887185)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  6420107032673464067478586260827535025706505865952476985262515704982045321421165234013162)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2004794067396725613361889452711807529277381113755822137760056210265476119880015404391831)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  621304981178716779407428360038480251682997731531771054440456066314969110343334819320524)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  191100838271598461840789183587450734318889830718539672128266077179380698983292398735863)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  58338871041528099446932901933760742666997727692004285454098931991285546534192575253936)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  17676894272764358334185761536639304230478036761916155469457036277860228943145444805485)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5316442618057808921118398829027243898708000398300859133430232367136929134823185601661)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1587150433662812134344451743489804325493537934508286475132215825087676638419440387552)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  470339321087277591251779861881261768728636751086183134497247586403883568139259036115)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  138361425199269938520982181645980820222504917244541730707410310752765026122598399639)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  40405779369493323177137705013206813864205895197663672005725192975235532378489814027)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  11714148454305351304191858180993050318476430519134695562887480798295624085425732765)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  3371558188074921700297922131675114341827848694791383519806308740969539028810304320)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  963423193803261889964685815714152664253103249045141373192704022569284709107148512)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  273327744485321878291024431974313056605948782996938525567546754792227199366933444)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  76991730027329504458982487871966581527445582610250072824890164569643179984196778)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  21533351016136120329387220052748946269276628929434789521261721162634530079868402)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5979979070509533048027262821970493939428762559133625902558835247014974159029670)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1649002889983821557129845325778487549188142351077220989216756344679693659455306)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  451533492660709838490739461029255520118855101183326720183669979697827493940374)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  122777363042472423826084446518287987115484367901030976983025887857476007241166)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  33152728650116463955828458361552583058210906932268057411888423622642813614057)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  8890079792316428993241760103418812617948744664767479591869701656345062229588)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2367500555302219402185818776098054525625249822058751604606595557624219621297)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  626159698251605642668385708271183572281544077736147167710314788759171553110)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  164476236405621721362112883438033227096563530243274144786589079769382128734)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  42909807333401513096470074960289146104365468314301453696369014344470201044)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  11118790639712553134222831610813443944024426202288570094142463800943945858)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2861661426727762745451724033243470304714019204925753100645534500993743574)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  731561226051720630884607364036597580679771404906355180620191204655841534)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  185766229493032334041489795924184659589824975660773452165571304662300350)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  46857416268228191555039384647565203313294710460675863181564794322218593)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  11740784677081729058657595546216437665062844022753008790870201803910499)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2922367010278589810234328714192591214787659798010120363397893230811162)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  722608019498618097701432100076492212567464681928526784019444539472502)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  177505833604297376144512225956684151282906999547666033753469454064308)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  43318725458201218833627979739151936843150513501542850079746761125724)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  10502753157728905916634305693036038530276826035185762025063070003612)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  2529916967615284321400157210514678263046911751565233817624981825749)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  605474811966852462774833090487881352146598353546103511944758143083)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  143973841767317043597185403333825897348073231886751391407822883105)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  34015723555222151979559668184750159455109614228037050647815289054)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  7985374033618188486601203600617152286198413367844692610875450818)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1862691705350919262500260844422122112753419971266193632064575628)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  431745201371402506008809968055918255176220123123484430029717402)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  99440992463567904872281968953405115938970789177988452222455195)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  22759633378880396049095860353839022177629066086599119650132626)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  5176513643619638944048951873943423628269559975807630345639002)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  1170016755389539788380436228117947796418712408852049646995106)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  262808656082222555837306081210618205835764028970434795591968)
  (@_root_.List.cons
  (@_root_.Int)
  (@_root_.Int.ofNat
  58666514479806482326929441881640849167599909289675930492757)
  (@_root_.List.nil
  (@_root_.Int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

noncomputable def panelAt (i : Fin 16) : Record := panelBank.getD i.val ⟨[],[],[],0,0,0,0⟩

noncomputable def sequenceCacheAt (i : Fin 16) : CertifiedMomentSequenceCache.Aux :=
  sequenceCacheBank.getD i.val ⟨[],[],[]⟩

noncomputable def totalNumerators : List ℤ :=
  CertifiedGlobalJetCenters.sumLists (List.ofFn (fun i : Fin 16 => (panelAt i).z))

end CertifiedMomentRecords

end Height100Module74

section Height100Module75
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CertifiedMomentRecords
open _root_.CertifiedMomentRecords

end CertifiedMomentRecords

end Height100Module75

section Height100Module76

end Height100Module76

section Height100Module77
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedLocalCandidates
open _root_.CertifiedLocalCandidates

end CertifiedLocalCandidates

end Height100Module77

section Height100Module84

namespace CertifiedExponentialSequenceBound
open _root_.CertifiedExponentialSequenceBound
open CertifiedExponentialSequenceCheck CertifiedPackedExponentialSequence
open _root_.CertifiedExponentialSequenceCheck _root_.CertifiedPackedExponentialSequence
open CertifiedPackedConvolution
open _root_.CertifiedPackedConvolution
set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

end CertifiedExponentialSequenceBound

end Height100Module84

section Height100Module87

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
namespace CertifiedMomentRecords
open _root_.CertifiedMomentRecords
open CertifiedPackedCorrelation CertifiedMomentArithmetic CertifiedMomentConvolution
open _root_.CertifiedPackedCorrelation _root_.CertifiedMomentArithmetic _root_.CertifiedMomentConvolution
open CertifiedListODEVectors CertifiedPackedExtraction CertifiedSignedODEConvolution
open _root_.CertifiedListODEVectors _root_.CertifiedPackedExtraction _root_.CertifiedSignedODEConvolution
open CertifiedGlobalJetCenters CertifiedFixedPoint CertifiedPackedConvolution
open _root_.CertifiedGlobalJetCenters _root_.CertifiedFixedPoint _root_.CertifiedPackedConvolution

end CertifiedMomentRecords

end Height100Module87

section Height100Module88

set_option autoImplicit false
namespace CertifiedIntegerRounding
open _root_.CertifiedIntegerRounding

end CertifiedIntegerRounding

end Height100Module88

section Height100Module89

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Finset
open scoped BigOperators

namespace CertifiedGlobalMomentEnclosure
open _root_.CertifiedGlobalMomentEnclosure
open CertifiedMomentRecords CertifiedMomentArithmetic CertifiedGlobalJetCenters
open _root_.CertifiedMomentRecords _root_.CertifiedMomentArithmetic _root_.CertifiedGlobalJetCenters
open CertifiedZetaQuadrature CertifiedIntegerRounding
open _root_.CertifiedZetaQuadrature _root_.CertifiedIntegerRounding

end CertifiedGlobalMomentEnclosure

end Height100Module89

end RH14MomentEnclosureProof


namespace RH14MomentCertificateData
open RH14MomentEnclosureProof.CertifiedMomentRecords
structure CheckedPanel (i : Fin 16) where
  record : Record
  cache : RH14MomentEnclosureProof.CertifiedMomentSequenceCache.Aux
  valid : RH14MomentEnclosureProof.CertifiedMomentSequenceCache.checkCached i record cache=true
structure CheckedRounding where
  numerators : List Int
  valid : numerators = totalNumerators.map
    (fun z => (3*z*(10^64:Int))/(RH14MomentEnclosureProof.CertifiedMomentArithmetic.momentDenominator:Int))
end RH14MomentCertificateData
noncomputable def TaoFivePrimes_RH14To100MomentCertificateDataNC : Nat := 14
end


