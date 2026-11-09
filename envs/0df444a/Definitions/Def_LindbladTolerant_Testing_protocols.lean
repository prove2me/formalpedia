-- Prove2me | Definitions.Def_LindbladTolerant_Testing_protocols
-- name    : LindbladTolerant_Testing_protocols
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:58:37.192003+00:00
-- url     : https://prove2.me/theorems/49669885-1763-4a81-94a4-fa42a4fc2ff6
-- title:
--   Bounded-query adaptive forward-evolution protocols and summed time
-- statement:
--   An oracle protocol has a finite bound on the number of calls, an initial density matrix independent of the generator, and a quantum memory whose finite dimension may depend on the entire classical history. The classical outcome space is an arbitrary measurable space. Every history chooses a real duration $t\ge0$, followed by a known completely positive instrument; the final two-outcome joint measurement acts on the system and all retained memory. All control functions, instrument densities, and dominating measures are measurable in finite history coordinates and independent of the unknown generator.
--
--   For a generator $\mathcal L$, the output probabilities are computed recursively by composing the actual channels $\exp(t\mathcal L)\otimes\mathrm{Id}$ with the instrument densities and integrating the resulting Born probabilities. Unnormalized posteriors are retained throughout, so null histories have zero mass. A protocol uses time at most $T$ exactly when every complete branch obeys
--   $$\sum_j t_j\le T.$$
--   This counts all calls, including failed preparations and the sum of durations of parallel calls. Disjoint-register oracle channels commute even on entangled inputs, which permits sequentializing parallel calls without changing this resource measure.
--
--   The success predicate requires, uniformly over every generator in the source class,
--   $$\Pr(\mathrm{YES})\ge2/3\quad\text{if }\|\mathcal D\|_F\le\varepsilon_1,\qquad
--   \Pr(\mathrm{NO})\ge2/3\quad\text{if }\|\mathcal D\|_F\ge\varepsilon_2.$$
--   No requirement is imposed in the strict promise gap. The type carries no success or lower-bound assumption. A padded zero-duration first call allows arbitrary initial classical randomization, and zero-duration padding permits a fixed call count for a bounded-call procedure.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, §3, pp.16–18, PDF pp.16–18; Theorem 5.2 proof, p.29, PDF p.29 (parallel sequentialization and adaptive histories)

import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladTolerant_Testing_quantum_instruments

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Matrix

namespace LindbladTolerant.Testing

/-- Bounded-query oracle circuit. Memory sizes can vary without a uniform bound
over histories. A free initial randomized operation can be encoded by a padded
zero-duration first call. The instrument and all control data are independent
of the unknown generator. -/
structure Protocol (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  queries : ℕ
  memory : List Ω → ℕ+
  initial : Op (Qubits n × Fin (memory []))
  duration : List Ω → ℝ
  instrument : (h : List Ω) → QuantumInstrument
    (Qubits n × Fin (memory h))
    (fun o => Qubits n × Fin (memory (h ++ [o])))
  effect : (h : List Ω) → Op (Qubits n × Fin (memory h))

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Zero-padding only for expressing measurability of dimension-changing maps. -/
def paddedBranch (p : Protocol n Ω) (h : List Ω) (o : Ω)
    (ij rs : Qubits n × Qubits n) (a b c d : ℕ) : ℂ :=
  if ha : a < (p.memory (h ++ [o]) : ℕ) then
  if hb : b < (p.memory (h ++ [o]) : ℕ) then
  if hc : c < (p.memory h : ℕ) then
  if hd : d < (p.memory h : ℕ) then
    (p.instrument h).branch o ((ij.1,⟨a,ha⟩),(ij.2,⟨b,hb⟩))
      ((rs.1,⟨c,hc⟩),(rs.2,⟨d,hd⟩))
  else 0 else 0 else 0 else 0

def paddedEffect (p : Protocol n Ω) (h : List Ω)
    (i j : Qubits n) (a b : ℕ) : ℂ :=
  if ha : a < (p.memory h : ℕ) then
  if hb : b < (p.memory h : ℕ) then
    p.effect h (i,⟨a,ha⟩) (j,⟨b,hb⟩)
  else 0 else 0

/-- Physical and measurable feedback, not a supplied response kernel or success
assumption. Measurability is tested on every finite history cylinder. -/
structure Admissible (p : Protocol n Ω) : Prop where
  initialDensity : IsDensity p.initial
  forward : ∀ h, 0 ≤ p.duration h
  effectPositive : ∀ h, (p.effect h).PosSemidef
  effectBound : ∀ h, (1 - p.effect h).PosSemidef
  memoryMeasurable : ∀ r : ℕ,
    Measurable (fun h : Fin r → Ω => (p.memory (List.ofFn h) : ℕ))
  durationMeasurable : ∀ r : ℕ,
    Measurable (fun h : Fin r → Ω => p.duration (List.ofFn h))
  baseMeasurable : ∀ (r : ℕ) (a : Set Ω), MeasurableSet a →
    Measurable (fun h : Fin r → Ω => (p.instrument (List.ofFn h)).base a)
  branchMeasurable : ∀ (r : ℕ) (ij rs : Qubits n × Qubits n) (a b c d : ℕ),
    Measurable (fun z : (Fin r → Ω) × Ω =>
      paddedBranch p (List.ofFn z.1) z.2 ij rs a b c d)
  effectMeasurable : ∀ (r : ℕ) (i j : Qubits n) (a b : ℕ),
    Measurable (fun h : Fin r → Ω => paddedEffect p (List.ofFn h) i j a b)

/-- Nested Born integrals compose the actual exp(t*g) channels and the CP
instrument densities. Lintegrals avoid totalized nonintegrable real expectations;
there is no normalization of a zero-mass history. -/
def runOutcome (p : Protocol n Ω) (g : Super (Qubits n) (Qubits n)) (yes : Bool) :
    (q : ℕ) → (h : List Ω) → Op (Qubits n × Fin (p.memory h)) → ℝ≥0∞
  | 0, h, rho => ENNReal.ofReal
      (((if yes then p.effect h else 1 - p.effect h) * rho).trace.re)
  | q+1, h, rho => ∫⁻ o,
      runOutcome p g yes q (h ++ [o])
        (applySuper ((p.instrument h).branch o)
          (tensorId (evolution g (p.duration h)) rho)) ∂(p.instrument h).base

def outputProbability (p : Protocol n Ω) (g : Super (Qubits n) (Qubits n))
    (yes : Bool) : ℝ≥0∞ := runOutcome p g yes p.queries [] p.initial

/-- Every complete classical branch, including zero-probability ones, is charged
for every call. This sums parallel durations after commuting disjoint channels. -/
def TimeAtMost (p : Protocol n Ω) (T : ℝ) : Prop :=
  0 ≤ T ∧ ∀ h : List Ω, h.length = p.queries →
    ∑ j ∈ Finset.range p.queries, p.duration (h.take j) ≤ T

def Solves (p : Protocol n Ω) (k : ℕ) (bound eps1 eps2 : ℝ) : Prop :=
  ∀ g : Super (Qubits n) (Qubits n), SourceClass k bound g →
    (frobenius (canonicalD g) ≤ eps1 →
      (2/3 : ℝ≥0∞) ≤ outputProbability p g true) ∧
    (eps2 ≤ frobenius (canonicalD g) →
      (2/3 : ℝ≥0∞) ≤ outputProbability p g false)

end LindbladTolerant.Testing


