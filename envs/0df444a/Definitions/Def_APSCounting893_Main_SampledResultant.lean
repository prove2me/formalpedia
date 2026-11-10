-- Prove2me | Definitions.Def_APSCounting893_Main_SampledResultant
-- name    : APSCounting893_Main_SampledResultant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:26:12.016398+00:00
-- url     : https://prove2.me/theorems/9d93bc8a-2d70-42d5-8e5e-a914d1ce974d
-- title:
--   Circuit-derived resultant families and exact sampling parameters
-- statement:
--   A reduced rational circuit has positive input dimension, one more output, and full image dimension. Its formal gate degrees determine homogenizing degrees before parameters are sampled. The resultant is then computed from the actual represented output polynomials, projection, direction and linear form, with no supplied resultant or correct-coefficient oracle.
--
--   Writing $N=n+m$, the source bounds and error allocations are
--
--   $$D_*=(N+1)(2N+1)d^N,\quad M\ge48D_*,\quad M=2^s,\quad 1/12+1/12=1/6.$$
--
--   The recorded grid chooses $M=2^{\lfloor\log_2(48D_*)\rfloor+1}$; grid entries are integers in $\{1,\ldots,M\}$. Coefficient-access tuples range over all integers, including geometrically unsuccessful choices, with a binary encoding of every coordinate. Polynomial bounds on tuple length are fixed before all circuit inputs. Numerator and denominator representations remain outputs of the coefficient-access theorem, never assumptions declaring the actual resultant coefficients accessible.
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), §6, equations (6.3)–(6.4), Remark 6.3, p. 24, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_CoefficientLanguages

set_option autoImplicit false

namespace APSCounting893.Main

/-- Formal degrees are computed from the actual circuit DAG, without expanding its outputs. -/
def gateFormalDegree {n : ℕ} (prior : List ℕ) : ArithmeticGate n → ℕ
  | .variable _ => 1
  | .constant _ => 0
  | .add a b | .sub a b => max (prior[a]?.getD 0) (prior[b]?.getD 0)
  | .mul a b => prior[a]?.getD 0 + prior[b]?.getD 0
  | .div a b => max (prior[a]?.getD 0) (prior[b]?.getD 0)

def formalDegrees {n : ℕ} (C : ArithmeticCircuit n) : List ℕ :=
  C.gates.foldl (fun prior g => prior ++ [gateFormalDegree prior g]) []

def outputFormalDegree {n : ℕ} (C : ArithmeticCircuit n) (j : Fin C.outputs.length) : ℕ :=
  (formalDegrees C)[C.outputs[j]]?.getD 0

noncomputable def rationalComplexPolynomials {n : ℕ} (C : ArithmeticCircuit n) :
    PolynomialMap ℂ n C.outputs.length :=
  fun j => MvPolynomial.map (algebraMap ℚ ℂ) (circuitPolynomials .rational C j)

/-- The circuit after the input-reduction step. No sampled projection, line or form is promised good. -/
structure ReducedCircuit where
  n : ℕ
  positive : 0 < n
  C : ArithmeticCircuit n
  outputCount : C.outputs.length = n + 1
  valid : ValidCircuit .rational C
  divisionFree : ∀ g ∈ C.gates, match g with | .div _ _ => False | _ => True
  dimension : RSCapacity.algDim (imageClosure (rationalComplexPolynomials C)) =
    ((n : ℕ∞) : WithBot ℕ∞)

noncomputable def ReducedCircuit.rawMap (I : ReducedCircuit) : RawMap :=
  { n := I.n
    F := fun j => rationalComplexPolynomials I.C (Fin.cast I.outputCount.symm j)
    d := max 2 (Finset.univ.sup (outputFormalDegree I.C)) }

noncomputable def ReducedCircuit.homogenizingDegrees (I : ReducedCircuit) :
    Fin (I.n + (I.n + 1)) → ℕ :=
  fun i => Fin.addCases
    (fun j => max 1 (outputFormalDegree I.C (Fin.cast I.outputCount.symm j)))
    (fun _ : Fin I.n => 1) (Fin.cast (Nat.add_comm _ _) i)

/-- The exact bound (6.3); no per-input polynomial exponent is chosen. -/
def sourceDStar (n d : ℕ) : ℕ :=
  let N := n + (n + 1)
  (N + 1) * (2 * N + 1) * d ^ N

/-- The first power of two strictly greater than or equal to 48D*, using a harmless larger
power when 48D* itself is a power of two. -/
noncomputable def samplingGridSize (I : ReducedCircuit) : ℕ :=
  2 ^ (Nat.log2 (48 * sourceDStar I.n I.rawMap.d) + 1)

/-- All integer tuples are admitted for coefficient access, including unsuccessful geometric choices.
The sampling grid is only the subset of tuples whose coordinates lie in {1,…,M}. -/
abbrev SampleTuple (I : ReducedCircuit) := Fin (I.n + I.n + (I.n + 1)) → ℤ

noncomputable def sampleCoordinates (I : ReducedCircuit) (theta : SampleTuple I) :
    Affine ℂ I.n × Affine ℂ I.n × Affine ℂ (I.n + 1) :=
  let all : Fin (I.n + I.n + (I.n + 1)) → ℂ := fun i => (theta i : ℂ)
  (fun i => all ((i.castAdd I.n).castAdd (I.n + 1)),
   fun i => all ((i.natAdd I.n).castAdd (I.n + 1)),
   fun i => all (i.natAdd (I.n + I.n)))

noncomputable def sampledResultant (I : ReducedCircuit) (theta : SampleTuple I) : Aux :=
  let s := sampleCoordinates I theta
  resultantFor I.rawMap s.1 s.2.1 s.2.2 I.homogenizingDegrees

noncomputable def encodeSample (I : ReducedCircuit) (theta : SampleTuple I) : Word :=
  I.C.encode ++ encodeList encodeInt (List.ofFn theta)

/-- The numerical error allocation in (6.4) and the final proof. -/
def inputReductionError : ℚ := 1 / 12

def auxiliarySamplingError : ℚ := 1 / 12

noncomputable def SampledCoefficientBitLanguage
    (rho : (I : ReducedCircuit) → SampleTuple I → (Fin 4 →₀ ℕ) → ℤ × ℕ) : Language :=
  fun w => ∃ (I : ReducedCircuit) (theta : SampleTuple I) (e : Fin 4 →₀ ℕ)
    (part : CoefficientPart) (q : ℕ),
      w = coefficientQuery (k := 3) (encodeSample I theta) e part q ∧
      representationBit (rho I theta e) part q = true

end APSCounting893.Main


