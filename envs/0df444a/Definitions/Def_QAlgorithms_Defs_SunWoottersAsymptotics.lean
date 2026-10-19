-- Prove2me | Definitions.Def_QAlgorithms_Defs_SunWoottersAsymptotics
-- name    : QAlgorithms_Defs_SunWoottersAsymptotics
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:39:01.160087+00:00
-- url     : https://prove2.me/theorems/2b66f8e2-8541-4510-851d-54b312770c01
-- title:
--   SunWoottersAsymptotics
-- statement:
--   SunWoottersAsymptotics
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SunWoottersAsymptotics.lean

import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_Defs_DQI
import Definitions.Def_QAlgorithms_Defs_SunWoottersSampling
noncomputable section

attribute [local instance] Classical.propDecidable

open Filter

namespace QAlgorithms.SunWootters

/-- Balanced public sequence indexed independently of blocklength;
2607.16541 p.7, pp.17,21–23. Every member retains its actual prime and points. -/
structure ParameterFamily where
  parameters : ℕ → OPI.PrimePublicData
  limitingRate : ℝ
  rate_range : 0 < limitingRate ∧ limitingRate ≤ 1
  length_grows : Tendsto (fun j => (parameters j).m) atTop atTop
  rate_converges : Tendsto (fun j => ((parameters j).n : ℝ)/(parameters j).m)
    atTop (nhds limitingRate)
  density_converges : Tendsto (fun j => ((parameters j).c : ℝ)/(parameters j).p)
    atTop (nhds (1/2))

/-- Entropy domain preventing all undefined ratios;
2607.16541 p.8 (15)–(16). -/
def ExponentDomain (mu delta lam : ℝ) : Prop :=
  mu+delta ≠ 0 ∧ 1-mu-delta ≠ 0 ∧ 4*mu-1 ≠ 0 ∧ 2-4*mu ≠ 0 ∧
    mu/(mu+delta) ∈ Set.Icc 0 1 ∧ mu/(1-mu-delta) ∈ Set.Icc 0 1 ∧
    2*mu ∈ Set.Icc 0 1 ∧ lam/(4*mu-1) ∈ Set.Icc 0 1 ∧
    (2*mu-lam)/(2-4*mu) ∈ Set.Icc 0 1

/-- Computed natural-log (E,G) exponents, with their genuine domain;
2607.16541 p.8 (15)–(16). Strict E+G<0 belongs to the theorem. -/
def feasibilityExponents (mu delta lam : ℝ) (_domain : ExponentDomain mu delta lam) : ℝ × ℝ :=
  ((mu+delta)*Real.binEntropy (mu/(mu+delta))+
    (1-mu-delta)*Real.binEntropy (mu/(1-mu-delta))-Real.binEntropy (2*mu),
    (1-2*mu)*Real.log 2+Real.binEntropy (2*mu)-
    (4*mu-1)*Real.binEntropy (lam/(4*mu-1))-
    (2-4*mu)*Real.binEntropy ((2*mu-lam)/(2-4*mu))+lam*Real.log (2/Real.pi))

/-- A public sampling/performance request; 2607.16541 pp.7,17,21–23.
Mode 0 samples, mode 1 selects from repeated score-checked samples, and mode 2
uses the endpoint subproblem. Integer accuracy/confidence parameters are public. -/
structure SamplingRequest where
  parameters : OPI.PrimePublicData
  mode : Fin 3
  accuracy : ℕ
  confidence : ℕ

/-- Standard binary public request encoding, including the known common cardinality;
2607.16541 p.7. No hidden membership table enters the constructor. -/
def samplingRequestEncoding (Q : SamplingRequest) : Complexity.Str :=
  LocalHamiltonian.encBin Q.parameters.p ++ LocalHamiltonian.encBin Q.parameters.m ++
  LocalHamiltonian.encBin Q.parameters.n ++ LocalHamiltonian.encBin Q.parameters.c ++
  (List.ofFn fun i => List.ofFn
    (natToBits (Nat.clog 2 Q.parameters.p) (Q.parameters.alpha i).val)).flatten ++
  LocalHamiltonian.encBin Q.mode.val ++ LocalHamiltonian.encBin Q.accuracy ++
  LocalHamiltonian.encBin Q.confidence

/-- Charged public parameter scale; 2607.16541 pp.7,17,21–23. -/
def samplingRequestScale (Q : SamplingRequest) : ℕ :=
  Q.parameters.m + Nat.clog 2 Q.parameters.p + Q.accuracy + Q.confidence + 1

/-- Uniform generated scalar sampler/performance engine; 2607.16541 pp.7,17,21–23.
Interface fields only identify the source oracle and coefficient output format;
no accuracy, score, successful decoding or execution-cost conclusion is assumed. -/
structure UniformPrimeSampler where
  family : OPI.UniformResourceFamily SamplingRequest samplingRequestEncoding samplingRequestScale
  oneOracle : ∀ Q, (family.construct Q).oracles = 1
  arity : ∀ Q k, (family.construct Q).arity k =
    Nat.clog 2 Q.parameters.m + Nat.clog 2 Q.parameters.p + 1
  outputSize : ∀ Q, (family.construct Q).outputBits = Q.parameters.n * Nat.clog 2 Q.parameters.p

/-- Canonical coefficient output decoding; 2607.16541 pp.6–7,22–23.
The n consecutive field registers are read most-significant-bit first. Invalid
field labels are mapped modulo p, a fixed total postprocessing convention. -/
def samplerCoefficients (S : UniformPrimeSampler) (Q : SamplingRequest)
    (z : Fin (S.family.construct Q).outputBits → Bool) : Fin Q.parameters.n → ZMod Q.parameters.p :=
  fun i => (bitsToNat (fun j : Fin (Nat.clog 2 Q.parameters.p) =>
    z (Fin.cast (S.outputSize Q).symm (finProdFinEquiv (i,j)))) : ZMod Q.parameters.p)

/-- Execute the actual generated sampler, including failure-to-zero postprocessing;
2607.16541 pp.16–17,21–23. Hidden sets enter solely through the indexed XOR oracle.
The oracle layout is fixed by public arities; there is no freely supplied output law. -/
def samplerEventLaw (S : UniformPrimeSampler) (Q : SamplingRequest)
    (sets : Fin Q.parameters.m → Finset (ZMod Q.parameters.p))
    (event : (Fin Q.parameters.n → ZMod Q.parameters.p) → Prop) : ℝ :=
  letI : NeZero Q.parameters.p := ⟨Q.parameters.prime.ne_zero⟩
  let oracle := fun k => (OPI.indexedQubitOracle sets).submatrix
    (fun z => z ∘ Fin.cast (S.arity Q k).symm)
    (fun z => z ∘ Fin.cast (S.arity Q k).symm)
  OPI.membershipOutputLaw (S.family.construct Q).program oracle
    (fun result => match result with
      | none => event 0
      | some z => event (samplerCoefficients S Q z))

/-- Actual worst-branch work, including coefficient-output decoding;
2607.16541 pp.7,16–17,21–23. Constructor work is already charged by family.generates. -/
def samplerWork (S : UniformPrimeSampler) (Q : SamplingRequest)
    (sets : Fin Q.parameters.m → Finset (ZMod Q.parameters.p)) : ℕ :=
  letI : NeZero Q.parameters.p := ⟨Q.parameters.prime.ne_zero⟩
  let oracle := fun k => (OPI.indexedQubitOracle sets).submatrix
    (fun z => z ∘ Fin.cast (S.arity Q k).symm)
    (fun z => z ∘ Fin.cast (S.arity Q k).symm)
  OPI.membershipResources (S.family.construct Q).program oracle +
    Q.parameters.n * (Nat.clog 2 Q.parameters.p + 1)^2

/-- Every selected uniform performance clause, on computed execution laws;
2607.16541 pp.21–23, Corollaries 8.6/8.8. The expected positive gap, amplified
high-probability gap and asymptotic perfection retain their source rate domains.
Work polynomials, thresholds, gaps and vanishing sequences precede hidden sets. -/
def UniformPerformance (F : ParameterFamily) (S : UniformPrimeSampler) : Prop :=
  (∃ work : Polynomial ℕ, ∃ j0 : ℕ, ∀ j ≥ j0, ∀ mode accuracy confidence,
    let Q : SamplingRequest := ⟨F.parameters j,mode,accuracy,confidence⟩
    ∀ sets : Fin Q.parameters.m → Finset (ZMod Q.parameters.p),
      (∀ i, (sets i).card = Q.parameters.c) → samplerWork S Q sets ≤ work.eval (samplingRequestScale Q)) ∧
  ((249/400 ≤ F.limitingRate ∧ F.limitingRate < 1) →
    ∃ gap : ℝ, 0 < gap ∧
    (∃ j0 : ℕ, ∀ j ≥ j0,
      let P := F.parameters j
      letI : Fact P.p.Prime := ⟨P.prime⟩
      let Q : SamplingRequest := ⟨P,0,2*Nat.clog 2 P.m,2*Nat.clog 2 P.m⟩
      ∀ sets : Fin P.m → Finset (ZMod P.p), (∀ i, (sets i).card = P.c) →
        (∑ x : Fin P.n → ZMod P.p,
          samplerEventLaw S Q sets (fun y => y = x) *
            OPI.score (by have := P.n_pos; have := P.n_lt; omega) P.alpha sets x) ≥
          semicircleValue (F.limitingRate/2) (1/2)+gap) ∧
    ∀ eps beta : ℝ, 0 < eps → 0 < beta → beta < 1 →
      ∃ accuracy confidence j0 : ℕ, ∀ j ≥ j0,
      let P := F.parameters j
      letI : Fact P.p.Prime := ⟨P.prime⟩
      ∀ sets : Fin P.m → Finset (ZMod P.p), (∀ i, (sets i).card = P.c) →
        samplerEventLaw S ⟨P,1,accuracy,confidence⟩ sets (fun x =>
          semicircleValue (F.limitingRate/2) (1/2)+gap-eps ≤
            OPI.score (by have := P.n_pos; have := P.n_lt; omega) P.alpha sets x) ≥ 1-beta) ∧
  (3/4 ≤ F.limitingRate → ∃ deficit failure : ℕ → ℝ,
    (∀ j, 0 ≤ deficit j ∧ 0 ≤ failure j) ∧
    Tendsto deficit atTop (nhds 0) ∧ Tendsto failure atTop (nhds 0) ∧
    ∃ j0 : ℕ, ∀ j ≥ j0,
      let P := F.parameters j
      letI : Fact P.p.Prime := ⟨P.prime⟩
      ∀ sets : Fin P.m → Finset (ZMod P.p), (∀ i, (sets i).card = P.c) →
        samplerEventLaw S ⟨P,2,2*Nat.clog 2 P.m,2*Nat.clog 2 P.m⟩ sets (fun x =>
          1-deficit j ≤ OPI.score (by have := P.n_pos; have := P.n_lt; omega) P.alpha sets x) ≥
          1-failure j)

/-- Signed ceil-minus-one strict Johnson endpoint, plus reduced dimension;
2607.16541 p.22 (69). The eventual positive domain excludes empty degree bounds. -/
def johnsonEndpoint (m n : ℕ) (hn : 0 < min n (3*m/4) ∧ min n (3*m/4) < m) : ℕ × ℕ :=
  let reduced := min n (3*m/4)
  (reduced,min (m/2)
    (Int.toNat (⌈(m : ℝ)-Real.sqrt (((m : ℝ)-reduced-1)*m)⌉-1)))

example : johnsonEndpoint 4 3 (by omega) = (3,2) := by
  norm_num [johnsonEndpoint]

end QAlgorithms.SunWootters


