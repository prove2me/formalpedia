-- Prove2me | Definitions.Def_TaoFivePrimes_RH14To100TranslationInterface
-- name    : TaoFivePrimes_RH14To100TranslationInterface
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T00:08:05.381072+00:00
-- url     : https://prove2.me/theorems/5fae3f97-af5c-4854-97fc-ae439cc4f513
-- title:
--   RH height 14–100 — translation arithmetic interface
-- statement:
--   The translation arithmetic interface for the existing height-14–100 finite certificate. This module defines the proposed data structures and exact integer validators, without asserting numerical correctness or a Riemann-hypothesis conclusion. It extracts the ordinary definitions from sometik179’s publicly submitted certificate, with the theta/Mellin attribution to Gabewhigham retained.
-- source:
--   sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03), https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a. Original theta/Mellin attribution: Gabewhigham. These definitions already occur in public pilot 9fe11bf7-b735-43df-b4a3-f64c598366d3 and the published finite arithmetic interface 9b37fd72-f28f-4143-ba7e-0c2e92b04787; only dependency partitioning is changed.

/- Ordinary finite arithmetic definitions extracted from sometik179's
height-14–100 certificate, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a.
Theta/Mellin attribution to Gabewhigham is retained. No certificate assertion
or RH theorem is supplied in this definition interface. -/
import Definitions.Def_TaoFivePrimes_RH14To100ArithmeticCore
import Definitions.Def_TaoFivePrimes_RH14To100FactorialWeightValues
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

section Height100Module0

open Finset
namespace CertifiedPackedConvolution

end CertifiedPackedConvolution

end Height100Module0

section Height100Module1

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution

end CertifiedMomentConvolution

end Height100Module1

section Height100Module2

open Finset

namespace CertifiedTaylorQuadrature

end CertifiedTaylorQuadrature

end Height100Module2

section Height100Module3

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module3

section Height100Module4

open Finset
namespace CertifiedExponentialJets
open CertifiedTaylorQuadrature CertifiedMomentConvolution

end CertifiedExponentialJets

end Height100Module4

section Height100Module5

open Finset
namespace CertifiedIntegerExponentialJets
open CertifiedMomentConvolution CertifiedExponentialJets

end CertifiedIntegerExponentialJets

end Height100Module5

section Height100Module6

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedSignedODEConvolution
open CertifiedIntegerExponentialJets

end CertifiedSignedODEConvolution

end Height100Module6

section Height100Module7

set_option autoImplicit false
namespace CertifiedListODEVectors
open CertifiedSignedODEConvolution
open Finset
open scoped BigOperators

end CertifiedListODEVectors

end Height100Module7

section Height100Module8

set_option autoImplicit false
open Finset
namespace CertifiedPackedHorner
open CertifiedPackedConvolution

end CertifiedPackedHorner

namespace CertifiedPackedHorner

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

end CertifiedZetaQuadrature

end Height100Module12

section Height100Module13

open Finset

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module13

section Height100Module14

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module14

section Height100Module15

open Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module15

section Height100Module16

open Finset
namespace CertifiedZetaQuadrature

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
open CertifiedTaylorQuadrature

end CertifiedComplexTaylor

end Height100Module22

section Height100Module23

set_option autoImplicit false

namespace TaoZetaWide

end TaoZetaWide

end Height100Module23

section Height100Module24

namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module24

section Height100Module25

open Finset
namespace CertifiedGlobalMoments
open CertifiedZetaQuadrature

end CertifiedGlobalMoments

end Height100Module25

section Height100Module26

open Finset
namespace CertifiedEvenPolynomial

end CertifiedEvenPolynomial

end Height100Module26

section Height100Module27

namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module27

section Height100Module28

namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module28

section Height100Module29

open Finset
namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module29

section Height100Module30

open Finset
namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module30

section Height100Module31

open Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature

end CertifiedPolynomialTranslation

end Height100Module31

section Height100Module32

open Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature CertifiedGlobalMoments

end CertifiedPolynomialTranslation

end Height100Module32

section Height100Module33

set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

namespace CertifiedDenseGlobalPolynomial
open Finset CertifiedPolynomialTranslation

def momentScale : ℕ := 10^64
def denominator : ℕ := 8*momentScale*128^510

end CertifiedDenseGlobalPolynomial

end Height100Module33

section Height100Module34

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module34

section Height100Module35

set_option autoImplicit false
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module35

section Height100Module36

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

end CertifiedThetaPoints

end Height100Module36

section Height100Module37

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators

namespace CertifiedHighPrecisionPi

end CertifiedHighPrecisionPi

end Height100Module37

section Height100Module38

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option Elab.async false

namespace CertifiedHighPrecisionPi

end CertifiedHighPrecisionPi

end Height100Module38

section Height100Module39

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module39

section Height100Module40

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace CertifiedThetaPoints
open CertifiedFixedPoint CertifiedHighPrecisionPi

end CertifiedThetaPoints

end Height100Module40

section Height100Module41

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

end CertifiedThetaPoints

end Height100Module41

section Height100Module42

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CertifiedThetaCandidates
open CertifiedThetaPoints CertifiedFixedPoint

end CertifiedThetaCandidates

end Height100Module42

section Height100Module43

namespace CertifiedStreamingODE
open CertifiedSignedODEConvolution

end CertifiedStreamingODE

end Height100Module43

section Height100Module44

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedJetRecords
open CertifiedThetaCandidates CertifiedThetaPoints CertifiedFixedPoint
open CertifiedListODEVectors CertifiedPackedConvolution CertifiedStreamingODE

end CertifiedJetRecords

end Height100Module44

section Height100Module45

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedJetRecords
open CertifiedThetaPoints

end CertifiedJetRecords

end Height100Module45

section Height100Module46

end Height100Module46

section Height100Module47

namespace CertifiedJetRecords

end CertifiedJetRecords

end Height100Module47

section Height100Module48

set_option autoImplicit false
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedSignedODEConvolution
open CertifiedListODEVectors CertifiedStreamingODE CertifiedIntegerExponentialJets

end CertifiedJetRecords

end Height100Module48

section Height100Module49

set_option autoImplicit false
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module49

section Height100Module50

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module50

section Height100Module51

open Finset
namespace CertifiedZetaQuadrature
set_option exponentiation.threshold 512
open CertifiedTaylorQuadrature CertifiedMomentConvolution

end CertifiedZetaQuadrature

end Height100Module51

section Height100Module52

open Finset
namespace CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution CertifiedExponentialJets

end CertifiedZetaQuadrature

end Height100Module52

section Height100Module53

open Finset
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedIntegerExponentialJets
open CertifiedZetaQuadrature CertifiedMomentConvolution CertifiedTaylorQuadrature

end CertifiedJetRecords

end Height100Module53

section Height100Module54

open Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module54

section Height100Module55

open Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

set_option exponentiation.threshold 512

end CertifiedMomentConvolution

end Height100Module55

section Height100Module56

open Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module56

section Height100Module57

open Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module57

section Height100Module58
namespace CertifiedZetaQuadrature
end CertifiedZetaQuadrature

end Height100Module58

section Height100Module59

open Finset
namespace CertifiedGlobalQuadrature
open CertifiedZetaQuadrature CertifiedTaylorQuadrature

end CertifiedGlobalQuadrature

end Height100Module59

section Height100Module60

open Finset
namespace CertifiedZetaQuadrature
open CertifiedMomentConvolution CertifiedTaylorQuadrature

end CertifiedZetaQuadrature

end Height100Module60

section Height100Module61

open Finset
namespace CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution
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
open CertifiedJetRecords CertifiedThetaPoints CertifiedFixedPoint
open CertifiedMomentConvolution CertifiedZetaQuadrature

end CertifiedGlobalJetCenters

end Height100Module62

section Height100Module63

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedPackedCorrelation
open CertifiedSignedODEConvolution CertifiedListODEVectors CertifiedPackedConvolution

end CertifiedPackedCorrelation

end Height100Module63

section Height100Module64

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CertifiedMomentWeights
open CertifiedMomentConvolution

end CertifiedMomentWeights

end Height100Module64

section Height100Module65

namespace CertifiedExponentialIntegerSequence

end CertifiedExponentialIntegerSequence

end Height100Module65

section Height100Module66

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators
namespace CertifiedMomentArithmetic
open CertifiedFixedPoint CertifiedExponentialIntegerSequence
open CertifiedMomentConvolution

end CertifiedMomentArithmetic

end Height100Module66

section Height100Module67

set_option autoImplicit false
namespace CertifiedPackedExtraction
open CertifiedSignedODEConvolution

end CertifiedPackedExtraction

end Height100Module67

section Height100Module68

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentRecords
open CertifiedGlobalJetCenters CertifiedThetaCandidates CertifiedThetaPoints
open CertifiedJetRecords CertifiedFixedPoint CertifiedPackedConvolution
open CertifiedMomentArithmetic CertifiedListODEVectors CertifiedPackedExtraction

end CertifiedMomentRecords

end Height100Module68

section Height100Module69

namespace CertifiedExponentialSequenceCheck
open CertifiedExponentialIntegerSequence

end CertifiedExponentialSequenceCheck

end Height100Module69

section Height100Module70

namespace CertifiedPackedExponentialSequence
open CertifiedPackedConvolution CertifiedExponentialSequenceCheck

end CertifiedPackedExponentialSequence

end Height100Module70

section Height100Module71

namespace CertifiedChunkedExponentialSequence
open CertifiedPackedConvolution CertifiedPackedExponentialSequence

end CertifiedChunkedExponentialSequence

end Height100Module71

section Height100Module72

namespace CertifiedChunkedEncoding
open CertifiedPackedConvolution CertifiedPackedExponentialSequence
open CertifiedChunkedExponentialSequence

end CertifiedChunkedEncoding

end Height100Module72

section Height100Module73

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentSequenceCache
open CertifiedMomentRecords CertifiedMomentArithmetic CertifiedPackedConvolution
open CertifiedExponentialIntegerSequence CertifiedExponentialSequenceCheck
open CertifiedChunkedEncoding CertifiedListODEVectors CertifiedPackedExtraction

end CertifiedMomentSequenceCache

end Height100Module73

section Height100Module74

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedMomentRecords

open CertifiedListODEVectors CertifiedPackedExtraction CertifiedMomentArithmetic

end CertifiedMomentRecords

end Height100Module74

section Height100Module75
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CertifiedMomentRecords

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

end CertifiedLocalCandidates

end Height100Module77

section Height100Module78

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedGlobalTranslation
open CertifiedMomentRecords CertifiedPackedHorner CertifiedSignedODEConvolution
open CertifiedPackedExtraction CertifiedListODEVectors

def parameter (i : Fin 86) : ℕ := 29+2*i.val
def denominator : ℕ := Nat.shiftLeft CertifiedDenseGlobalPolynomial.denominator 512
def normalization (i : Fin 86) : ℕ := 10^((14+i.val)/3)

end CertifiedGlobalTranslation

end Height100Module78

section Height100Module79

open Finset
namespace CertifiedPolynomialTranslation

end CertifiedPolynomialTranslation

end Height100Module79

section Height100Module80

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000
namespace CertifiedTranslationConvolution
open CertifiedGlobalTranslation CertifiedPackedConvolution CertifiedListODEVectors
open CertifiedExponentialIntegerSequence CertifiedPackedExtraction

def bits : ℕ := 8192
def commonFactor : ℕ := Nat.shiftLeft 1 496

@[noinline] def encodedPlus : ℕ := encode bits (positiveList weights).reverse
@[noinline] def encodedMinus : ℕ := encode bits (negativeList weights).reverse

end CertifiedTranslationConvolution

end Height100Module80

section Height100Module81

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction CertifiedExponentialIntegerSequence

abbrev bits : ℕ := CertifiedTranslationConvolution.bits

def scaleDenominator : ℕ := CertifiedGlobalTranslation.denominator*(512).factorial

def productWindow (a b : ℕ) : ℕ :=
  ((a*b) >>> (bits*481)) &&& ((1 <<< (bits*32))-1)

structure Record where
  ep : ℕ
  wp : ℕ
  wm : ℕ
  z : List ℤ
  deriving Repr

def checkErrors (ν : ℕ) : ℕ → ℕ → ℕ → List ℤ → List ℤ → Bool
  | _,_,0,_,_ => true
  | j,f,n+1,z::zs,c::cs =>
      decide (|(ν:ℤ)*(Nat.shiftLeft 1 j:ℕ)*commonFactor*z*100000000-
        c*scaleDenominator*f|≤ 10*(scaleDenominator:ℤ)*f) &&
        checkErrors ν (j+1) (f*(j+1)) n zs cs
  | j,f,n+1,z::zs,[] =>
      decide (|(ν:ℤ)*(Nat.shiftLeft 1 j:ℕ)*commonFactor*z*100000000|≤ 
        10*(scaleDenominator:ℤ)*f) && checkErrors ν (j+1) (f*(j+1)) n zs []
  | _,_,_+1,[],_ => false

end CertifiedPackedTranslation

end Height100Module81

section Height100Module82

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedLiteralTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction CertifiedExponentialIntegerSequence

abbrev bits : ℕ := CertifiedPackedTranslation.bits

def makeChunks : ℕ → List ℕ → List ℕ
  | 0,_ => []
  | n+1,xs => encode bits (xs.take 32)::makeChunks n (xs.drop 32)

structure Record where
  e : List ℕ
  chunks : List ℕ
  wp : ℕ
  wm : ℕ
  z : List ℤ
  deriving Repr

def toOriginal (r : Record) : CertifiedPackedTranslation.Record :=
  ⟨encode (bits*32) r.chunks,r.wp,r.wm,r.z⟩

def makeRecord (i : Fin 86) : Record :=
  let e := expSeq (parameter i) 513 0 (512).factorial
  let chunks := makeChunks 17 e
  let ep := encode (bits*32) chunks
  let wp := CertifiedPackedTranslation.productWindow encodedPlus ep
  let wm := CertifiedPackedTranslation.productWindow encodedMinus ep
  ⟨e,chunks,wp,wm,(extract bits 1 32 wp wm).reverse⟩

def checkRecord (i : Fin 86) (r : Record) : Bool :=
  decide (r.e.length=513) && decide (r.e.headD 0=(512).factorial) &&
  CertifiedExponentialSequenceCheck.checkSteps (parameter i) 0 r.e &&
  CertifiedChunkedEncoding.checkChunks bits 32 r.e r.chunks &&
  decide (r.wp=CertifiedPackedTranslation.productWindow encodedPlus (toOriginal r).ep) &&
  decide (r.wm=CertifiedPackedTranslation.productWindow encodedMinus (toOriginal r).ep) &&
  decide (r.z=(extract bits 1 32 r.wp r.wm).reverse) &&
  CertifiedPackedTranslation.checkErrors (normalization i) 0 1 32 r.z
    (CertifiedLocalCandidates.coefficientNumerators.getD i.val [])
end CertifiedLiteralTranslation

end Height100Module82

section Height100Module83
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedLiteralTranslation
@[noinline] def pointRecord.«0» : Record := makeRecord (0 : Fin 86)
@[noinline] def pointRecord.«1» : Record := makeRecord (1 : Fin 86)
@[noinline] def pointRecord.«2» : Record := makeRecord (2 : Fin 86)
@[noinline] def pointRecord.«3» : Record := makeRecord (3 : Fin 86)
@[noinline] def pointRecord.«4» : Record := makeRecord (4 : Fin 86)
@[noinline] def pointRecord.«5» : Record := makeRecord (5 : Fin 86)
@[noinline] def pointRecord.«6» : Record := makeRecord (6 : Fin 86)
@[noinline] def pointRecord.«7» : Record := makeRecord (7 : Fin 86)
@[noinline] def pointRecord.«8» : Record := makeRecord (8 : Fin 86)
@[noinline] def pointRecord.«9» : Record := makeRecord (9 : Fin 86)
@[noinline] def pointRecord.«10» : Record := makeRecord (10 : Fin 86)
@[noinline] def pointRecord.«11» : Record := makeRecord (11 : Fin 86)
@[noinline] def pointRecord.«12» : Record := makeRecord (12 : Fin 86)
@[noinline] def pointRecord.«13» : Record := makeRecord (13 : Fin 86)
@[noinline] def pointRecord.«14» : Record := makeRecord (14 : Fin 86)
@[noinline] def pointRecord.«15» : Record := makeRecord (15 : Fin 86)
@[noinline] def pointRecord.«16» : Record := makeRecord (16 : Fin 86)
@[noinline] def pointRecord.«17» : Record := makeRecord (17 : Fin 86)
@[noinline] def pointRecord.«18» : Record := makeRecord (18 : Fin 86)
@[noinline] def pointRecord.«19» : Record := makeRecord (19 : Fin 86)
@[noinline] def pointRecord.«20» : Record := makeRecord (20 : Fin 86)
@[noinline] def pointRecord.«21» : Record := makeRecord (21 : Fin 86)
@[noinline] def pointRecord.«22» : Record := makeRecord (22 : Fin 86)
@[noinline] def pointRecord.«23» : Record := makeRecord (23 : Fin 86)
@[noinline] def pointRecord.«24» : Record := makeRecord (24 : Fin 86)
@[noinline] def pointRecord.«25» : Record := makeRecord (25 : Fin 86)
@[noinline] def pointRecord.«26» : Record := makeRecord (26 : Fin 86)
@[noinline] def pointRecord.«27» : Record := makeRecord (27 : Fin 86)
@[noinline] def pointRecord.«28» : Record := makeRecord (28 : Fin 86)
@[noinline] def pointRecord.«29» : Record := makeRecord (29 : Fin 86)
@[noinline] def pointRecord.«30» : Record := makeRecord (30 : Fin 86)
@[noinline] def pointRecord.«31» : Record := makeRecord (31 : Fin 86)
@[noinline] def pointRecord.«32» : Record := makeRecord (32 : Fin 86)
@[noinline] def pointRecord.«33» : Record := makeRecord (33 : Fin 86)
@[noinline] def pointRecord.«34» : Record := makeRecord (34 : Fin 86)
@[noinline] def pointRecord.«35» : Record := makeRecord (35 : Fin 86)
@[noinline] def pointRecord.«36» : Record := makeRecord (36 : Fin 86)
@[noinline] def pointRecord.«37» : Record := makeRecord (37 : Fin 86)
@[noinline] def pointRecord.«38» : Record := makeRecord (38 : Fin 86)
@[noinline] def pointRecord.«39» : Record := makeRecord (39 : Fin 86)
@[noinline] def pointRecord.«40» : Record := makeRecord (40 : Fin 86)
@[noinline] def pointRecord.«41» : Record := makeRecord (41 : Fin 86)
@[noinline] def pointRecord.«42» : Record := makeRecord (42 : Fin 86)
@[noinline] def pointRecord.«43» : Record := makeRecord (43 : Fin 86)
@[noinline] def pointRecord.«44» : Record := makeRecord (44 : Fin 86)
@[noinline] def pointRecord.«45» : Record := makeRecord (45 : Fin 86)
@[noinline] def pointRecord.«46» : Record := makeRecord (46 : Fin 86)
@[noinline] def pointRecord.«47» : Record := makeRecord (47 : Fin 86)
@[noinline] def pointRecord.«48» : Record := makeRecord (48 : Fin 86)
@[noinline] def pointRecord.«49» : Record := makeRecord (49 : Fin 86)
@[noinline] def pointRecord.«50» : Record := makeRecord (50 : Fin 86)
@[noinline] def pointRecord.«51» : Record := makeRecord (51 : Fin 86)
@[noinline] def pointRecord.«52» : Record := makeRecord (52 : Fin 86)
@[noinline] def pointRecord.«53» : Record := makeRecord (53 : Fin 86)
@[noinline] def pointRecord.«54» : Record := makeRecord (54 : Fin 86)
@[noinline] def pointRecord.«55» : Record := makeRecord (55 : Fin 86)
@[noinline] def pointRecord.«56» : Record := makeRecord (56 : Fin 86)
@[noinline] def pointRecord.«57» : Record := makeRecord (57 : Fin 86)
@[noinline] def pointRecord.«58» : Record := makeRecord (58 : Fin 86)
@[noinline] def pointRecord.«59» : Record := makeRecord (59 : Fin 86)
@[noinline] def pointRecord.«60» : Record := makeRecord (60 : Fin 86)
@[noinline] def pointRecord.«61» : Record := makeRecord (61 : Fin 86)
@[noinline] def pointRecord.«62» : Record := makeRecord (62 : Fin 86)
@[noinline] def pointRecord.«63» : Record := makeRecord (63 : Fin 86)
@[noinline] def pointRecord.«64» : Record := makeRecord (64 : Fin 86)
@[noinline] def pointRecord.«65» : Record := makeRecord (65 : Fin 86)
@[noinline] def pointRecord.«66» : Record := makeRecord (66 : Fin 86)
@[noinline] def pointRecord.«67» : Record := makeRecord (67 : Fin 86)
@[noinline] def pointRecord.«68» : Record := makeRecord (68 : Fin 86)
@[noinline] def pointRecord.«69» : Record := makeRecord (69 : Fin 86)
@[noinline] def pointRecord.«70» : Record := makeRecord (70 : Fin 86)
@[noinline] def pointRecord.«71» : Record := makeRecord (71 : Fin 86)
@[noinline] def pointRecord.«72» : Record := makeRecord (72 : Fin 86)
@[noinline] def pointRecord.«73» : Record := makeRecord (73 : Fin 86)
@[noinline] def pointRecord.«74» : Record := makeRecord (74 : Fin 86)
@[noinline] def pointRecord.«75» : Record := makeRecord (75 : Fin 86)
@[noinline] def pointRecord.«76» : Record := makeRecord (76 : Fin 86)
@[noinline] def pointRecord.«77» : Record := makeRecord (77 : Fin 86)
@[noinline] def pointRecord.«78» : Record := makeRecord (78 : Fin 86)
@[noinline] def pointRecord.«79» : Record := makeRecord (79 : Fin 86)
@[noinline] def pointRecord.«80» : Record := makeRecord (80 : Fin 86)
@[noinline] def pointRecord.«81» : Record := makeRecord (81 : Fin 86)
@[noinline] def pointRecord.«82» : Record := makeRecord (82 : Fin 86)
@[noinline] def pointRecord.«83» : Record := makeRecord (83 : Fin 86)
@[noinline] def pointRecord.«84» : Record := makeRecord (84 : Fin 86)
@[noinline] def pointRecord.«85» : Record := makeRecord (85 : Fin 86)
@[noinline] def _root_.CertifiedLiteralTranslation.recordBank : (@_root_.List (@_root_.CertifiedLiteralTranslation.Record)) :=
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«0»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«1»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«2»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«3»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«4»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«5»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«6»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«7»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«8»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«9»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«10»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«11»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«12»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«13»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«14»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«15»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«16»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«17»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«18»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«19»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«20»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«21»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«22»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«23»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«24»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«25»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«26»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«27»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«28»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«29»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«30»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«31»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«32»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«33»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«34»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«35»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«36»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«37»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«38»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«39»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«40»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«41»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«42»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«43»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«44»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«45»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«46»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«47»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«48»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«49»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«50»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«51»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«52»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«53»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«54»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«55»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«56»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«57»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«58»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«59»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«60»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«61»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«62»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«63»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«64»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«65»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«66»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«67»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«68»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«69»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«70»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«71»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«72»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«73»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«74»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«75»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«76»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«77»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«78»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«79»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«80»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«81»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«82»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«83»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«84»)
  (@_root_.List.cons
  (@_root_.CertifiedLiteralTranslation.Record)
  (@_root_.CertifiedLiteralTranslation.pointRecord.«85»)
  (@_root_.List.nil
  (@_root_.CertifiedLiteralTranslation.Record))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

noncomputable def recordAt (i : Fin 86) : Record := recordBank.getD i.val ⟨[],[],0,0,[]⟩

end CertifiedLiteralTranslation

end Height100Module83

section Height100Module84

namespace CertifiedExponentialSequenceBound
open CertifiedExponentialSequenceCheck CertifiedPackedExponentialSequence
open CertifiedPackedConvolution
set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

end CertifiedExponentialSequenceBound

end Height100Module84

section Height100Module85

set_option autoImplicit false
open Finset
namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature
end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature
end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedPackedHorner

end Height100Module85

section Height100Module86

set_option autoImplicit false
open Finset
namespace CertifiedTranslationAlgebra
open CertifiedPolynomialTranslation CertifiedPackedHorner CertifiedListODEVectors
open CertifiedPackedCorrelation CertifiedPackedConvolution CertifiedSignedODEConvolution

end CertifiedTranslationAlgebra

namespace CertifiedTranslationAlgebra
open CertifiedPackedConvolution CertifiedSignedODEConvolution

end CertifiedTranslationAlgebra

end Height100Module86

section Height100Module87

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
namespace CertifiedMomentRecords
open CertifiedPackedCorrelation CertifiedMomentArithmetic CertifiedMomentConvolution
open CertifiedListODEVectors CertifiedPackedExtraction CertifiedSignedODEConvolution
open CertifiedGlobalJetCenters CertifiedFixedPoint CertifiedPackedConvolution

end CertifiedMomentRecords

end Height100Module87

section Height100Module88

set_option autoImplicit false
namespace CertifiedIntegerRounding

end CertifiedIntegerRounding

end Height100Module88

section Height100Module89

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Finset
open scoped BigOperators

namespace CertifiedGlobalMomentEnclosure
open CertifiedMomentRecords CertifiedMomentArithmetic CertifiedGlobalJetCenters
open CertifiedZetaQuadrature CertifiedIntegerRounding

end CertifiedGlobalMomentEnclosure

end Height100Module89

section Height100Module90

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Finset
namespace CertifiedGlobalTranslation
open CertifiedPackedHorner CertifiedListODEVectors CertifiedPackedExtraction
open CertifiedSignedODEConvolution CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedGlobalTranslation

end Height100Module90

section Height100Module91

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Finset
namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedListODEVectors CertifiedPackedExtraction
open CertifiedSignedODEConvolution CertifiedTranslationAlgebra CertifiedPackedExponentialSequence

end CertifiedPackedTranslation

end Height100Module91

section Height100Module92

namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation CertifiedPolynomialTranslation

end CertifiedPackedTranslation

end Height100Module92

section Height100Module93

set_option autoImplicit false
set_option exponentiation.threshold 8192
namespace CertifiedLiteralTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction

end CertifiedLiteralTranslation

end Height100Module93

section Height100Module94

set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaPoly

end TaoZetaPoly

end Height100Module94

section Height100Module95

namespace CertifiedLocalPolynomial
open Finset CertifiedLocalXi

end CertifiedLocalPolynomial

end Height100Module95

section Height100Module96

namespace CertifiedIntegerLocalPolynomial
open Finset

end CertifiedIntegerLocalPolynomial

end Height100Module96

section Height100Module97

open Finset
set_option autoImplicit false

namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module97

section Height100Module98

open Finset
set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module98

section Height100Module99

namespace CertifiedLocalPolynomial
open Finset TaoZetaNumerics

end CertifiedLocalPolynomial

end Height100Module99

section Height100Module100

namespace CertifiedLocalPolynomial
open Finset CertifiedLocalXi

end CertifiedLocalPolynomial

end Height100Module100

section Height100Module101

open Finset
set_option autoImplicit false
set_option maxHeartbeats 0
namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module101

section Height100Module102

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial TaoZetaNumerics
open Finset

end CertifiedLocalBoxes

end Height100Module102

section Height100Module103

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedFastLocalBoxes

end Height100Module103

section Height100Module104

namespace CertifiedStreamingBernstein
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedStreamingBernstein

end Height100Module104

section Height100Module105

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein
open TaoZetaNumerics

end CertifiedStreamingLocalBoxes

end Height100Module105

section Height100Module106

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes
open CertifiedLocalPolynomial CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedFastLocalBoxes

end Height100Module106

section Height100Module107

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedLocalBoxes

end Height100Module107

section Height100Module108

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedFastLocalBoxes

end Height100Module108

section Height100Module109

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein

end CertifiedStreamingLocalBoxes

end Height100Module109

section Height100Module110

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes

end CertifiedStreamingLocalBoxes

end Height100Module110

section Height100Module111

namespace CertifiedStreamingLocalBoxes
open CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedStreamingLocalBoxes

end Height100Module111

section Height100Module112

namespace CertifiedHeight100
open CertifiedPolynomialTranslation CertifiedGlobalMoments CertifiedLocalXi

end CertifiedHeight100

end Height100Module112

section Height100Module113

set_option autoImplicit false
namespace TaoFivePrimes

end TaoFivePrimes

end Height100Module113


def TaoFivePrimes_RH14To100TranslationInterface : Nat := 14


