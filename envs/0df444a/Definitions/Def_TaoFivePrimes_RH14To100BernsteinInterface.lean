-- Prove2me | Definitions.Def_TaoFivePrimes_RH14To100BernsteinInterface
-- name    : TaoFivePrimes_RH14To100BernsteinInterface
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T00:08:44.859357+00:00
-- url     : https://prove2.me/theorems/c5a7ebee-214f-4d1c-b10f-cf68bd8d9f6b
-- title:
--   RH height 14–100 — bernstein arithmetic interface
-- statement:
--   The bernstein arithmetic interface for the existing height-14–100 finite certificate. This module defines the proposed data structures and exact integer validators, without asserting numerical correctness or a Riemann-hypothesis conclusion. It extracts the ordinary definitions from sometik179’s publicly submitted certificate, with the theta/Mellin attribution to Gabewhigham retained.
-- source:
--   sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03), https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a. Original theta/Mellin attribution: Gabewhigham. These definitions already occur in public pilot 9fe11bf7-b735-43df-b4a3-f64c598366d3 and the published finite arithmetic interface 9b37fd72-f28f-4143-ba7e-0c2e92b04787; only dependency partitioning is changed.

/- Ordinary finite arithmetic definitions extracted from sometik179's
height-14–100 certificate, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a.
Theta/Mellin attribution to Gabewhigham is retained. No certificate assertion
or RH theorem is supplied in this definition interface. -/
import Definitions.Def_TaoFivePrimes_RH14To100ArithmeticCore
import Definitions.Def_TaoFivePrimes_RH14To100BernsteinData
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

end CertifiedPackedTranslation

end Height100Module81

section Height100Module82

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedLiteralTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction CertifiedExponentialIntegerSequence

end CertifiedLiteralTranslation

end Height100Module82

section Height100Module83
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedLiteralTranslation

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

abbrev Row := List ℤ
abbrev Bi := List Row

def rowAdd : Row → Row → Row
  | [],b => b
  | a,[] => a
  | a::as,b::bs => (a+b)::rowAdd as bs
def biAdd : Bi → Bi → Bi
  | [],b => b
  | a,[] => a
  | a::as,b::bs => rowAdd a b::biAdd as bs
def biScale (q : ℤ) (a : Bi) : Bi := a.map (fun r => r.map (q*·))
def shiftX : Bi → Bi
  | [] => []
  | a::as => []::a::as
def shiftY (a : Bi) : Bi := a.map (0::·)
def biConst (q : ℤ) : Bi := [[q]]

/-- A division-free Horner interpreter for x²=u/4 and y=(a+bv)/2.
Both integer output matrices have the common denominator4^(length cs). -/
def normalizedPair (a b : ℤ) : List ℤ → Bi × Bi
  | [] => ([],[])
  | c::cs =>
    let p := normalizedPair a b cs
    (biAdd (biConst (c*4^(cs.length+1)))
      (biAdd (biScale (2*a) p.1)
        (biAdd (biScale (2*b) (shiftY p.1)) (biScale (-1) (shiftX p.2)))),
     biAdd (biScale 4 p.1)
       (biAdd (biScale (2*a) p.2) (biScale (2*b) (shiftY p.2))))

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

structure Spec where
  imaginary : Bool
  sign : ℤ
  a2 : ℤ
  b2 : ℤ
  deriving DecidableEq, Repr

def defaultSpec : Spec := ⟨false,1,-1,1⟩
def specs : List (List Spec) := [
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨true,-1,-1,0⟩,⟨false,-1,0,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨true,-1,-1,0⟩,⟨false,-1,0,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨true,-1,-1,0⟩,⟨false,-1,0,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,0⟩,⟨false,1,0,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨true,1,-1,0⟩,⟨false,1,0,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,0⟩,⟨false,1,0,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨true,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,0⟩,⟨true,1,0,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨false,1,-1,1⟩],
  [⟨true,-1,-1,1⟩],
  [⟨false,-1,-1,1⟩]]

def rowSpecs (i : Fin 86) : List Spec := specs.getD i.val []
def specAt (i : Fin 86) (j : ℕ) : Spec := (rowSpecs i).getD j defaultSpec

structure Certificate where
  power : List (List ℤ)
  row : List (List ℤ)
  result : List (List ℤ)
  deriving Repr

end CertifiedLocalBoxes

end Height100Module102

section Height100Module103

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

def integerCandidate (i : Fin 86) : List ℤ :=
  CertifiedLocalCandidates.coefficientNumerators.getD i.val []

def powerMatrix (i : Fin 86) (j : ℕ) : Bi :=
  let s := specAt i j
  let p := normalizedPair s.a2 (s.b2-s.a2) (integerCandidate i)
  biScale s.sign (if s.imaginary then p.2 else p.1)

end CertifiedFastLocalBoxes

end Height100Module103

section Height100Module104

namespace CertifiedStreamingBernstein
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

def dot : List ℤ → List ℕ → ℤ
  | [],_ => 0
  | _,[] => 0
  | x::xs,w::ws => x*(w:ℤ)+dot xs ws

def weightedRows : List ℕ → List (List ℤ) → List ℤ
  | [],_ => []
  | _,[] => []
  | w::ws,r::rs => rowAdd (r.map (fun x => x*(w:ℤ))) (weightedRows ws rs)

def transformRow (w : List (List ℕ)) (r : List ℤ) : List ℤ := w.map (dot r)
def transformRows (w : List (List ℕ)) (rows : List (List ℤ)) : List (List ℤ) :=
  rows.map (transformRow w)
def transformColumns (w : List (List ℕ)) (rows : List (List ℤ)) : List (List ℤ) :=
  w.map (fun row => weightedRows row rows)

end CertifiedStreamingBernstein

end Height100Module104

section Height100Module105

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein
open TaoZetaNumerics

def weights7 : List (List ℕ) := [[5040,0,0,0,0,0,0,0],[5040,720,0,0,0,0,0,0],[5040,1440,240,0,0,0,0,0],[5040,2160,720,144,0,0,0,0],[5040,2880,1440,576,144,0,0,0],[5040,3600,2400,1440,720,240,0,0],[5040,4320,3600,2880,2160,1440,720,0],[5040,5040,5040,5040,5040,5040,5040,5040]]

def weights15 : List (List ℕ) := [[1307674368000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[1307674368000,87178291200,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[1307674368000,174356582400,12454041600,0,0,0,0,0,0,0,0,0,0,0,0,0],[1307674368000,261534873600,37362124800,2874009600,0,0,0,0,0,0,0,0,0,0,0,0],[1307674368000,348713164800,74724249600,11496038400,958003200,0,0,0,0,0,0,0,0,0,0,0],[1307674368000,435891456000,124540416000,28740096000,4790016000,435456000,0,0,0,0,0,0,0,0,0,0],[1307674368000,523069747200,186810624000,57480192000,14370048000,2612736000,261273600,0,0,0,0,0,0,0,0,0],[1307674368000,610248038400,261534873600,100590336000,33530112000,9144576000,1828915200,203212800,0,0,0,0,0,0,0,0],[1307674368000,697426329600,348713164800,160944537600,67060224000,24385536000,7315660800,1625702400,203212800,0,0,0,0,0,0,0],[1307674368000,784604620800,448345497600,241416806400,120708403200,54867456000,21946982400,7315660800,1828915200,261273600,0,0,0,0,0,0],[1307674368000,871782912000,560431872000,344881152000,201180672000,109734912000,54867456000,24385536000,9144576000,2612736000,435456000,0,0,0,0,0],[1307674368000,958961203200,684972288000,474211584000,316141056000,201180672000,120708403200,67060224000,33530112000,14370048000,4790016000,958003200,0,0,0,0],[1307674368000,1046139494400,821966745600,632282112000,474211584000,344881152000,241416806400,160944537600,100590336000,57480192000,28740096000,11496038400,2874009600,0,0,0],[1307674368000,1133317785600,971415244800,821966745600,684972288000,560431872000,448345497600,348713164800,261534873600,186810624000,124540416000,74724249600,37362124800,12454041600,0,0],[1307674368000,1220496076800,1133317785600,1046139494400,958961203200,871782912000,784604620800,697426329600,610248038400,523069747200,435891456000,348713164800,261534873600,174356582400,87178291200,0],[1307674368000,1307674368000,1307674368000,1307674368000,1307674368000,1307674368000,1307674368000,1307674368000,1307674368000,1307674368000,1307674368000,1307674368000,1307674368000,1307674368000,1307674368000,1307674368000]]

def threshold : ℤ := 2830674996766244339712000000000000

def positiveRow (row : List ℤ) : Bool :=
  decide (row.length=16) && row.all (fun x => decide (threshold≤ x))

def valid (i : Fin 86) (j : ℕ) (c : Certificate) : Prop :=
  c.power=powerMatrix i j ∧ c.power.length=8 ∧
  c.power.all (fun row => decide (row.length≤ 16))=true ∧
  c.row=transformRows weights15 c.power ∧
  c.result=transformColumns weights7 c.row ∧
  c.result.length=8 ∧ c.result.all positiveRow=true

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

def emptyCertificate : Certificate := ⟨[],[],[]⟩

/-- Native code only proposes literal integer matrices. Each one is subsequently
checked by the complete ordinary-kernel validator below. -/
@[noinline] def boxCertificate.«0».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 0 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«1».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 1 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«2».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 2 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«3».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 3 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«4».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 4 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«5».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 5 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«6».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 6 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«7».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 7 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«8».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 8 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«9».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 9 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«10».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 10 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«11».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 11 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«12».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 12 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«13».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 13 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«14».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 14 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«15».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 15 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«16».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 16 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«17».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 17 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«18».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 18 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«19».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 19 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«20».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 20 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«21».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 21 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«22».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 22 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«23».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 23 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«24».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 24 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«25».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 25 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«26».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 26 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«27».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 27 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«28».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 28 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«29».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 29 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«30».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 30 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«31».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 31 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«32».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 32 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«33».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 33 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«34».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 34 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«34».«1» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 34 []).getD 1 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«35».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 35 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«36».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 36 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«37».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 37 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«38».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 38 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«39».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 39 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«40».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 40 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«41».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 41 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«42».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 42 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«43».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 43 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«44».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 44 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«45».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 45 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«45».«1» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 45 []).getD 1 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«46».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 46 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«47».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 47 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«48».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 48 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«49».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 49 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«50».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 50 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«51».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 51 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«51».«1» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 51 []).getD 1 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«52».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 52 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«53».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 53 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«53».«1» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 53 []).getD 1 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«54».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 54 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«55».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 55 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«56».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 56 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«57».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 57 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«58».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 58 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«59».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 59 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«60».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 60 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«61».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 61 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«62».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 62 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«63».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 63 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«63».«1» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 63 []).getD 1 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«64».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 64 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«65».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 65 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«66».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 66 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«67».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 67 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«68».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 68 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«69».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 69 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«70».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 70 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«71».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 71 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«72».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 72 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«73».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 73 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«73».«1» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 73 []).getD 1 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«74».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 74 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«75».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 75 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«76».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 76 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«77».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 77 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«78».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 78 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«79».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 79 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«80».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 80 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«81».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 81 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«81».«1» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 81 []).getD 1 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«82».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 82 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«83».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 83 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«84».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 84 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def boxCertificate.«85».«0» : CertifiedLocalBoxes.Certificate :=
  let d := (_root_.TaoFivePrimes_RH14To100BernsteinData.getD 85 []).getD 0 ([],[],[])
  ⟨d.1,d.2.1,d.2.2⟩
@[noinline] def _root_.CertifiedStreamingLocalBoxes.certificateBank : (@_root_.List (@_root_.List (@_root_.CertifiedLocalBoxes.Certificate))) :=
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«0».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«1».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«2».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«3».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«4».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«5».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«6».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«7».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«8».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«9».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«10».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«11».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«12».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«13».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«14».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«15».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«16».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«17».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«18».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«19».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«20».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«21».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«22».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«23».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«24».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«25».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«26».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«27».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«28».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«29».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«30».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«31».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«32».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«33».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«34».«0»)
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«34».«1»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate))))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«35».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«36».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«37».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«38».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«39».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«40».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«41».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«42».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«43».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«44».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«45».«0»)
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«45».«1»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate))))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«46».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«47».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«48».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«49».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«50».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«51».«0»)
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«51».«1»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate))))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«52».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«53».«0»)
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«53».«1»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate))))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«54».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«55».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«56».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«57».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«58».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«59».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«60».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«61».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«62».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«63».«0»)
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«63».«1»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate))))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«64».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«65».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«66».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«67».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«68».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«69».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«70».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«71».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«72».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«73».«0»)
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«73».«1»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate))))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«74».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«75».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«76».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«77».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«78».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«79».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«80».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«81».«0»)
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«81».«1»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate))))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«82».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«83».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«84».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.cons
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate))
  (@_root_.List.cons
  (@_root_.CertifiedLocalBoxes.Certificate)
  (@_root_.CertifiedStreamingLocalBoxes.boxCertificate.«85».«0»)
  (@_root_.List.nil
  (@_root_.CertifiedLocalBoxes.Certificate)))
  (@_root_.List.nil
  (@_root_.List
  (@_root_.CertifiedLocalBoxes.Certificate)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

noncomputable def certificateAt (i : Fin 86) (j : ℕ) : Certificate :=
  (certificateBank.getD i.val []).getD j emptyCertificate

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


def TaoFivePrimes_RH14To100BernsteinInterface : Nat := 14


