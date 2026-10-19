-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Independent2_P01
-- name    : QAlgorithms_Papers_Independent_Independent2_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:24:37.02898+00:00
-- url     : https://prove2.me/theorems/37b0ea18-d59c-4768-96bb-d4a771db062a
-- title:
--   Definitions for Error mitigation for short-depth quantum circuits
-- statement:
--   The objects the formalized statements of *Error mitigation for short-depth quantum circuits* (arXiv:1612.02058) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `MarkovData`: Finite GKSL data of PDF p.5, (11)--(13); real continuous Pauli controls.
--   - `controlHamiltonian`: Pauli control Hamiltonian, Eq. (12).
--   - `lindbladAction`: Fixed control-independent Lindblad generator, Eq. (13).
--   - `IsMasterRun`: Actual master-equation trajectory, including continuity and the initial value at T=0.
--   - `IsForwardPropagator`: Forward U'=-iKU, U(0)=I. Printed Eq. (17)'s frame conjugation is reversed; the consistently corrected physical interaction picture is U^dagger rho U.
--   - `interactionNoise`: Corrected interaction generator U(t)^dagger L(U(t) X U(t)^dagger) U(t).
--   - `noiseIntegral`: Ordered Duhamel integral, latest insertion on the left.
--   - `noiseWord`: Ordered insertions without integration, for the source's l_k hypothesis.
--   - `HasInsertionBounds`: Uniform trace-norm action bounds on density operators (finite-dimensional regime). Every bounded finite-dimensional generator has bounds of this form. No expansion or remainder inequality is assumed.
--   - `noiseCoefficient`: Physical a_k in Eq. (23), with the forward frame convention.
--   - `noiseRemainder`: Explicit remainder integral (24).
--   - `richardsonMatrix`: Defining Richardson system (4), with k=0 in the first row.
--   - `richardsonWeights`: Weights computed from (4), avoiding the erroneous printed product.
--   - `richardsonOverhead`: Gamma_n from pp.2,9.
--   - `LocalLPFeasible`: Local LP feasibility (43)--(44), on the original one- or two-qubit support.
--   - `signedMass`: l1 mass of a signed expansion.
--   - `coefficientSign`: Total plus or minus1 convention, including zero coefficients of zero probability.
--   - `coefficientLaw`: Normalized absolute coefficients; zero-vector fallback is never used in a valid QPR.
--   - `PlacedMap`: Honest finite Kraus data for a channel at one scheduled location.
--   - `placedAction`: Identity extension of a placed channel to the full register.
--   - `ScheduledDisjoint`: Same-layer locations have disjoint supports, with first listed layer first.
--   - `productChoiceWeight`: Independent local choice probabilities in the product QPR.
--   - `productChoiceSign`: Product of local signs.
--   - `productNoisyChannel`: First listed local operation acts first.
--   - `depolarize`: Replacement depolarization on k qubits, not D_1 tensor D_1.
--   - `depolarizingCoefficient`: Inverse-depolarizing Pauli coefficients in the specified ansatz.
--   - `depolarizingReplacement`: One physical Omega operation: noise after the Pauli-corrected original gate.
--   - `depolarizingMass`: Exact local depolarizing overhead, pp.4,11--12.
--   - `depolarizingChoice`: Independent insertion probability per Pauli.
--   - `alternatingDepolarizingMass`: Product overhead computed from every layer of the alternating schedule.
--   - `groupedWeight`: Grouped fresh readouts, on the numerical section's |+> input. All labels are chosen before their positive, possibly label-dependent shot counts.
--   - `groupedEstimate`: Eq. (46), with equal group weight 1/K rather than M_j/M.
--   - `dampingKraus`: Two amplitude-damping Kraus operators, pp.13--14.
--   - `damping`: Amplitude damping.
--   - `dampingN`: Independent damping on each acted-on qubit.
--   - `prepareMap`: State replacement P_psi(X)=Tr(X)|psi><psi|, (47).
--   - `dampingGateCoefficient`: Eq. (49)'s four coefficients, including negative eta_4.
--   - `dampingGateMap`: Fixed four-map ansatz, with AP_zero=P_zero.
--   - `dampingPlusCoefficient`: Eq. (51)'s linked signs, checked on rendered p.15.
--   - `dampingPlusMap`: Three available noisy preparations in Eq. (51).
--   - `IdealLocation`: Clifford+T gate names in supplemental IV; identity counts as a gate.
--   - `singleGateMatrix`: I,H,S,T in that order.
--   - `locationSupport`: Original support of a source gate.
--   - `locationMatrix`: Source unitary at its placed wires.
--   - `locationCircuitMatrix`: Original time-ordered circuit, first listed gate first.
--   - `HasCnotPadding`: Every CNOT has a next single-qubit gate on both output wires, before any other touch. This is the essential padding requirement of p.11.
--   - `IsLocationSchedule`: The given gate schedule, including padding gates.
--   - `placeOne`: Identity extension of a one-qubit channel at q.
--   - `dampingPhase`: I,S,S inverse, and I for the reset branch of (49).
--   - `dampingCnotMap`: Noisy CNOT part of (50); reset postmaps are carried forward, not implemented here.
--   - `rawDampingGateMap`: Single-gate decomposition for raw (not subtype-wrapped) source matrices.
--   - `dampingCircuitTerms`: Two-stage construction of pp.14--15. First expand CNOT inverse noise, carrying resets to the next gate on the same wire. Then decompose the resulting single gates or plus preparations. Each leaf has one physical operation per original gate. No target equality is a construction field.
--   - `dampingCircuitMass`: Absolute-mass normalizer of the explicit two-stage list.
--   - `IsDampingReplacement`: Membership in the actual noisy basis Omega described on pp.14--15. A state preparation is one operation. No post-reset is added after a CNOT.
--   - `BoundedBathData`: PDF pp.5--6, (12),(14)--(16): a finite system and arbitrary nonempty finite bath. The interaction and bath Hamiltonian are fixed independently of rate and controls. Only the total interaction is required Hermitian; no bath approximation is made.
--   - `BathMatrix`: Joint operator space; b need not be a power of two.
--   - `boundedBathControl`: Eq. (12), lifted as K_S(t) tensor I_B, with system coordinate first.
--   - `boundedBathInteraction`: Eq. (15), including the bath-only Hamiltonian in the fixed noise V.
--   - `boundedBathInitial`: The source's normalized product input, permitting mixed system states.
--   - `boundedBathNoise`: Eq. (14), the coherent noise generator, with the physical factor -i.
--   - `boundedBathNoiseNorm`: The induced trace norm ||L_V||_(1 to 1) from (27). Its supremum set contains zero and is bounded: in finite dimension, the trace-norm unit ball is compact and the fixed commutator is continuous. No junk supremum is used.
--   - `IsBoundedBathRun`: Joint physical trajectory, not a reduced-system Markovian semigroup. At T=0 the initial-value clause still fixes the endpoint.
--   - `IsBoundedBathForward`: Forward propagator for the controlled system Hamiltonian only, tensored with I_B. As in noiseSeries, the printed frame in (17) is corrected to U^dagger rho U.
--   - `boundedBathInteractionNoise`: Consistent interaction-frame coherent noise Ad(U^dagger) L_V Ad(U).
--   - `boundedBathIntegral`: Ordered Duhamel integrals, with latest time on the left and inner path at earliest time.
--   - `boundedBathCoefficient`: Eq. (23)'s real coefficient for A=A_S tensor I_B, independent of noise rate.
--   - `boundedBathRemainder`: Eq. (24)'s actual integral remainder, using the evolved joint density at the inner time.
-- source:
--   Error mitigation for short-depth quantum circuits, arXiv:1612.02058v3, https://arxiv.org/abs/1612.02058v3

import Definitions.Def_QAlgorithms_Defs_CancellationResources
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-! Statements of arXiv:1612.02058v3. New definitions are specific to this paper. -/

noncomputable section

open MeasureTheory
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Independent2.P01

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open ProbabilisticCancellation

/-- Finite GKSL data of PDF p.5, (11)--(13); real continuous Pauli controls. -/
structure MarkovData (q : ℕ) where
  controls : (Fin q → Stabilizer.Pauli) → ℝ → ℝ
  continuous : ∀ a, Continuous (controls a)
  jumpCount : ℕ
  jumps : Fin jumpCount → Matrix (Qubits q) (Qubits q) ℂ
  rhoInitial : Matrix (Qubits q) (Qubits q) ℂ
  density : IsDensityMatrix rhoInitial

/-- Pauli control Hamiltonian, Eq. (12). -/
def controlHamiltonian {q : ℕ} (D : MarkovData q) (t : ℝ) : Matrix (Qubits q) (Qubits q) ℂ :=
  ∑ a, (D.controls a t : ℂ) • pauliOps a

/-- Fixed control-independent Lindblad generator, Eq. (13). -/
def lindbladAction {q : ℕ} (D : MarkovData q) (X : Matrix (Qubits q) (Qubits q) ℂ) :=
  ∑ a, (D.jumps a*X*(D.jumps a)ᴴ -
    (2⁻¹ : ℂ) • ((D.jumps a)ᴴ*D.jumps a*X+X*(D.jumps a)ᴴ*D.jumps a))

/-- Actual master-equation trajectory, including continuity and the initial value at T=0. -/
def IsMasterRun {q : ℕ} (D : MarkovData q) (K : ℝ → Matrix (Qubits q) (Qubits q) ℂ)
    (T rate : ℝ) (rho : ℝ → Matrix (Qubits q) (Qubits q) ℂ) : Prop :=
  0 ≤ T ∧ 0 ≤ rate ∧ rho 0 = D.rhoInitial ∧ ContinuousOn rho (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, IsDensityMatrix (rho t)) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt rho (-Complex.I • (K t*rho t-rho t*K t)+(rate : ℂ) • lindbladAction D (rho t))
        (Set.Icc 0 T) t

/-- Forward U'=-iKU, U(0)=I. Printed Eq. (17)'s frame conjugation is reversed;
the consistently corrected physical interaction picture is U^dagger rho U. -/
def IsForwardPropagator {q : ℕ} (D : MarkovData q) (T : ℝ)
    (U : ℝ → Matrix (Qubits q) (Qubits q) ℂ) : Prop :=
  U 0 = 1 ∧ ContinuousOn U (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, U t ∈ Matrix.unitaryGroup _ ℂ) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt U (-Complex.I • (controlHamiltonian D t*U t)) (Set.Icc 0 T) t

/-- Corrected interaction generator U(t)^dagger L(U(t) X U(t)^dagger) U(t). -/
def interactionNoise {q : ℕ} (D : MarkovData q)
    (U : ℝ → Matrix (Qubits q) (Qubits q) ℂ) (t : ℝ) (X : Matrix (Qubits q) (Qubits q) ℂ) :=
  (U t)ᴴ*lindbladAction D (U t*X*(U t)ᴴ)*U t

/-- Ordered Duhamel integral, latest insertion on the left. -/
def noiseIntegral {q : ℕ} (D : MarkovData q) (U : ℝ → Matrix (Qubits q) (Qubits q) ℂ)
    (initial : ℝ → Matrix (Qubits q) (Qubits q) ℂ) : ℕ → ℝ → Matrix (Qubits q) (Qubits q) ℂ
  | 0, t => initial t
  | k+1, t => ∫ s in (0 : ℝ)..t, interactionNoise D U s (noiseIntegral D U initial k s)

/-- Ordered insertions without integration, for the source's l_k hypothesis. -/
def noiseWord {q : ℕ} (D : MarkovData q) (U : ℝ → Matrix (Qubits q) (Qubits q) ℂ) :
    List ℝ → Matrix (Qubits q) (Qubits q) ℂ → Matrix (Qubits q) (Qubits q) ℂ
  | [], X => X
  | t::rest, X => interactionNoise D U t (noiseWord D U rest X)

/-- Uniform trace-norm action bounds on density operators (finite-dimensional regime).
Every bounded finite-dimensional generator has bounds of this form.
No expansion or remainder inequality is assumed. -/
def HasInsertionBounds {q : ℕ} (D : MarkovData q)
    (U : ℝ → Matrix (Qubits q) (Qubits q) ℂ) (T : ℝ) (ell : ℕ → ℝ) : Prop :=
  ∀ times : List ℝ, (∀ t ∈ times, t ∈ Set.Icc (0 : ℝ) T) →
    times.Pairwise (fun s t => t ≤ s) →
    ∀ X, IsDensityMatrix X → traceNorm (noiseWord D U times X) ≤ ell times.length

/-- Physical a_k in Eq. (23), with the forward frame convention. -/
def noiseCoefficient {q : ℕ} (D : MarkovData q)
    (U : ℝ → Matrix (Qubits q) (Qubits q) ℂ) (A : Matrix (Qubits q) (Qubits q) ℂ)
    (T : ℝ) (k : ℕ) : ℝ :=
  (A*(U T*noiseIntegral D U (fun _ => D.rhoInitial) k T*(U T)ᴴ)).trace.re

/-- Explicit remainder integral (24). -/
def noiseRemainder {q : ℕ} (D : MarkovData q)
    (U rho : ℝ → Matrix (Qubits q) (Qubits q) ℂ)
    (A : Matrix (Qubits q) (Qubits q) ℂ) (T rate : ℝ) (n : ℕ) : ℝ :=
  rate^(n+1)*(A*(U T*noiseIntegral D U (fun t => (U t)ᴴ*rho t*U t) (n+1) T*(U T)ᴴ)).trace.re

/-- Defining Richardson system (4), with k=0 in the first row. -/
def richardsonMatrix {n : ℕ} (c : Fin (n+1) → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.of fun k j => c j^k.val

/-- Weights computed from (4), avoiding the erroneous printed product. -/
def richardsonWeights {n : ℕ} (c : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  (richardsonMatrix c)⁻¹.mulVec (Pi.single 0 1)

/-- Gamma_n from pp.2,9. -/
def richardsonOverhead {n : ℕ} (c : Fin (n+1) → ℝ) : ℝ :=
  ∑ j, |richardsonWeights c j| *c j^(n+1)

/-- Local LP feasibility (43)--(44), on the original one- or two-qubit support. -/
def LocalLPFeasible {I : Type*} [Fintype I] {p : ℕ}
    (target : Superop I I) (operations : Fin p → Superop I I) (mu eta : Fin p → ℝ) : Prop :=
  (∀ i, eta i ≤ mu i ∧ -eta i ≤ mu i) ∧
    ∀ X, target X = ∑ i, (eta i : ℂ) • operations i X

/-- l1 mass of a signed expansion. -/
def signedMass {p : ℕ} (eta : Fin p → ℝ) : ℝ := ∑ i, |eta i|

/-- Total plus or minus1 convention, including zero coefficients of zero probability. -/
def coefficientSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

/-- Normalized absolute coefficients; zero-vector fallback is never used in a valid QPR. -/
def coefficientLaw {p : ℕ} (hp : 0 < p) (eta : Fin p → ℝ) : PMF (Fin p) :=
  if h : 0 < signedMass eta then
    PMF.ofFintype (fun i => ENNReal.ofReal (|eta i| /signedMass eta)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (abs_nonneg _) h.le)]
      rw [← Finset.sum_div]
      change ENNReal.ofReal (signedMass eta/signedMass eta) = 1
      rw [div_self h.ne']; simp)
  else PMF.pure ⟨0,hp⟩

/-- Honest finite Kraus data for a channel at one scheduled location. -/
structure PlacedMap (n : ℕ) where
  arity : ℕ
  localSize : arity = 1 ∨ arity = 2
  wires : Fin arity ↪ Fin n
  multiplicity : ℕ
  kraus : Fin multiplicity → Matrix (Qubits arity) (Qubits arity) ℂ
  complete : IsKrausFamily kraus

/-- Identity extension of a placed channel to the full register. -/
def placedAction {n : ℕ} (M : PlacedMap n) : Superop (Qubits n) (Qubits n) :=
  krausApply (fun j => embedOp (M.kraus j) M.wires)

/-- Same-layer locations have disjoint supports, with first listed layer first. -/
def ScheduledDisjoint {n L : ℕ} (arity : Fin L → ℕ)
    (wires : (j : Fin L) → Fin (arity j) ↪ Fin n) (layer : Fin L → ℕ) : Prop :=
  Monotone layer ∧ ∀ i j, i ≠ j → layer i = layer j →
    Disjoint (Set.range (wires i)) (Set.range (wires j))

/-- Independent local choice probabilities in the product QPR. -/
def productChoiceWeight {L p : ℕ} (P : Fin L → PMF (Fin p)) (a : Fin L → Fin p) : ℝ :=
  ∏ j, (P j (a j)).toReal

/-- Product of local signs. -/
def productChoiceSign {L p : ℕ} (sign : Fin L → Fin p → Bool) (a : Fin L → Fin p) : ℝ :=
  ∏ j, if sign j (a j) then 1 else -1

/-- First listed local operation acts first. -/
def productNoisyChannel {n L p : ℕ} (maps : Fin L → Fin p → PlacedMap n)
    (a : Fin L → Fin p) : Superop (Qubits n) (Qubits n) :=
  fun X => (List.ofFn fun j => maps j (a j)).foldl (fun Y M => placedAction M Y) X

/-- Replacement depolarization on k qubits, not D_1 tensor D_1. -/
def depolarize (k : ℕ) (eps : ℝ) : Superop (Qubits k) (Qubits k) :=
  fun X => ((1-eps : ℝ) : ℂ) • X + ((eps/(2 : ℝ)^k : ℝ) : ℂ) • (X.trace • 1)

/-- Inverse-depolarizing Pauli coefficients in the specified ansatz. -/
def depolarizingCoefficient (k : ℕ) (eps : ℝ) (P : Fin k → Stabilizer.Pauli) : ℝ :=
  if P = fun _ => Stabilizer.Pauli.I then 1+((4 : ℝ)^k-1)*eps/((4 : ℝ)^k*(1-eps))
  else -eps/((4 : ℝ)^k*(1-eps))

/-- One physical Omega operation: noise after the Pauli-corrected original gate. -/
def depolarizingReplacement {k : ℕ} (eps : ℝ) (U : Matrix.unitaryGroup (Qubits k) ℂ)
    (P : Fin k → Stabilizer.Pauli) : Superop (Qubits k) (Qubits k) :=
  depolarize k eps ∘ conjSuperop (pauliOps P) ∘ conjSuperop (U : Matrix _ _ ℂ)

/-- Exact local depolarizing overhead, pp.4,11--12. -/
def depolarizingMass (k : ℕ) (eps : ℝ) : ℝ :=
  (1+(1-2/(4 : ℝ)^k)*eps)/(1-eps)

/-- Independent insertion probability per Pauli. -/
def depolarizingChoice (k : ℕ) (eps : ℝ) (P : Fin k → Stabilizer.Pauli) : ℝ :=
  |depolarizingCoefficient k eps P| /depolarizingMass k eps

/-- Product overhead computed from every layer of the alternating schedule. -/
def alternatingDepolarizingMass (n depth : ℕ) (eps : ℝ) : ℝ :=
  ∏ layer : Fin depth, if layer.val%2 = 0 then (depolarizingMass 1 eps)^n
    else (depolarizingMass 2 eps)^(n/2)

/-- Grouped fresh readouts, on the numerical section's |+> input.
All labels are chosen before their positive, possibly label-dependent shot counts. -/
def groupedWeight {n m L K : ℕ} {B : NoisyCircuits.ChannelBasis n m}
    {ideal : Matrix.unitaryGroup (Qubits n) ℂ} (Q : QPR B L ideal)
    (counts : (Fin K → (Fin L → Fin m)) → Fin K → ℕ)
    (labels : Fin K → (Fin L → Fin m))
    (readouts : (j : Fin K) → Fin (counts labels j) → Qubits n) : ℝ :=
  (∏ j, (Q.words (labels j)).toReal) * ∏ j, ∏ a,
    (NoisyCircuits.executeWord B.operation (List.ofFn (labels j))
      (pureDensity (act (hadamardN n) (zeroKet n))) (readouts j a) (readouts j a)).re

/-- Eq. (46), with equal group weight 1/K rather than M_j/M. -/
def groupedEstimate {n m L K : ℕ} {B : NoisyCircuits.ChannelBasis n m}
    {ideal : Matrix.unitaryGroup (Qubits n) ℂ} (Q : QPR B L ideal)
    (projector : Finset (Qubits n))
    (counts : (Fin K → (Fin L → Fin m)) → Fin K → ℕ)
    (labels : Fin K → (Fin L → Fin m))
    (readouts : (j : Fin K) → Fin (counts labels j) → Qubits n) : ℝ :=
  Q.gamma/(K : ℝ) * ∑ j, (if Q.sign (labels j) then 1 else -1) *
    ((counts labels j : ℝ)⁻¹ * ∑ a, if readouts j a ∈ projector then (1 : ℝ) else 0)

/-- Two amplitude-damping Kraus operators, pp.13--14. -/
def dampingKraus (eps : ℝ) : Bool → Matrix Bool Bool ℂ :=
  fun b => if b then Matrix.of fun y z => if y = false ∧ z = true then (Real.sqrt eps : ℂ) else 0
    else Matrix.diagonal fun z => if z then (Real.sqrt (1-eps) : ℂ) else 1

/-- Amplitude damping. -/
def damping (eps : ℝ) : Superop Bool Bool := krausApply (dampingKraus eps)

/-- Independent damping on each acted-on qubit. -/
def dampingN (k : ℕ) (eps : ℝ) : Superop (Qubits k) (Qubits k) :=
  piSuperop (fun _ => damping eps)

/-- State replacement P_psi(X)=Tr(X)|psi><psi|, (47). -/
def prepareMap (psi : EuclideanSpace ℂ Bool) : Superop Bool Bool :=
  fun X => X.trace • pureDensity psi

/-- Eq. (49)'s four coefficients, including negative eta_4. -/
def dampingGateCoefficient (eps : ℝ) : Fin 4 → ℝ :=
  ![(Real.sqrt (1-eps))⁻¹, (1-Real.sqrt (1-eps))/(2*(1-eps)),
    (1-Real.sqrt (1-eps))/(2*(1-eps)), -eps/(1-eps)]

/-- Fixed four-map ansatz, with AP_zero=P_zero. -/
def dampingGateMap (eps : ℝ) (U : Matrix.unitaryGroup Bool ℂ) : Fin 4 → Superop Bool Bool :=
  ![damping eps ∘ conjSuperop (U : Matrix _ _ ℂ),
    damping eps ∘ conjSuperop phaseS ∘ conjSuperop (U : Matrix _ _ ℂ),
    damping eps ∘ conjSuperop (star phaseS) ∘ conjSuperop (U : Matrix _ _ ℂ),
    prepareMap (ket false)]

/-- Eq. (51)'s linked signs, checked on rendered p.15. -/
def dampingPlusCoefficient (eps : ℝ) : Fin 3 → ℝ :=
  ![((Real.sqrt (1-eps))⁻¹+(1-2*eps)/(1-eps))/2,
    (-(Real.sqrt (1-eps))⁻¹+(1-2*eps)/(1-eps))/2, eps/(1-eps)]

/-- Three available noisy preparations in Eq. (51). -/
def dampingPlusMap (eps : ℝ) : Fin 3 → Superop Bool Bool :=
  ![damping eps ∘ prepareMap (act hadamard (ket false)),
    damping eps ∘ prepareMap (act hadamard (ket true)), damping eps ∘ prepareMap (ket true)]

/-- Sanity check: the zero-order Duhamel integral is its supplied initial path. -/
example (q : ℕ) (D : MarkovData q) (U : ℝ → Matrix (Qubits q) (Qubits q) ℂ)
    (X : ℝ → Matrix (Qubits q) (Qubits q) ℂ) (t : ℝ) : noiseIntegral D U X 0 t = X t := rfl

example (q : ℕ) (D : MarkovData q) (U : ℝ → Matrix (Qubits q) (Qubits q) ℂ)
    (X : ℝ → Matrix (Qubits q) (Qubits q) ℂ) (k : ℕ) : noiseIntegral D U X (k+1) 0 = 0 := by
  simp [noiseIntegral]

example : coefficientSign 0 = 1 := by norm_num [coefficientSign]

example : richardsonWeights (fun _ : Fin 1 => (1 : ℝ)) = fun _ => 1 := by
  have h : richardsonMatrix (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
    ext i j; fin_cases i; fin_cases j; rfl
  funext j
  fin_cases j
  simp [richardsonWeights,h,Matrix.mulVec,Pi.single_apply]

example : dampingGateCoefficient 0 = ![1,0,0,0] := by
  ext j; fin_cases j <;> norm_num [dampingGateCoefficient]

example : dampingPlusCoefficient 0 = ![1,0,0] := by
  ext j; fin_cases j <;> norm_num [dampingPlusCoefficient]

example (k : ℕ) (X : Matrix (Qubits k) (Qubits k) ℂ) : depolarize k 0 X = X := by simp [depolarize]

example (n : ℕ) (eps : ℝ) : alternatingDepolarizingMass n 0 eps = 1 := by
  simp [alternatingDepolarizingMass]

/-- Clifford+T gate names in supplemental IV; identity counts as a gate. -/
inductive IdealLocation (n : ℕ) where
  | single (tag : Fin 4) (wire : Fin n)
  | cnot (control target : Fin n) (different : control ≠ target)

/-- I,H,S,T in that order. -/
def singleGateMatrix (tag : Fin 4) : Matrix Bool Bool ℂ := ![1,hadamard,phaseS,gateT] tag

/-- Original support of a source gate. -/
def locationSupport {n : ℕ} : IdealLocation n → Finset (Fin n)
  | .single _ q => {q}
  | .cnot c t _ => {c,t}

/-- Source unitary at its placed wires. -/
def locationMatrix {n : ℕ} : IdealLocation n → Matrix (Qubits n) (Qubits n) ℂ
  | .single tag q => qubitOp1 (singleGateMatrix tag) q
  | .cnot c t h => embedOp (Gate.ofMatrix2 cnot).mat (Stabilizer.wire2 c t h)

/-- Original time-ordered circuit, first listed gate first. -/
def locationCircuitMatrix {n : ℕ} (gates : List (IdealLocation n)) : Matrix (Qubits n) (Qubits n) ℂ :=
  (gates.map locationMatrix).reverse.prod

/-- Every CNOT has a next single-qubit gate on both output wires, before any other touch.
This is the essential padding requirement of p.11. -/
def HasCnotPadding {n : ℕ} (gates : List (IdealLocation n)) : Prop :=
  ∀ i : Fin gates.length, ∀ c t h, gates.get i = .cnot c t h →
    ∀ q ∈ ({c,t} : Finset (Fin n)), ∃ j : Fin gates.length, i < j ∧
      (∃ tag, gates.get j = .single tag q) ∧
      ∀ k : Fin gates.length, i < k → k < j → q ∉ locationSupport (gates.get k)

/-- The given gate schedule, including padding gates. -/
def IsLocationSchedule {n : ℕ} (gates : List (IdealLocation n))
    (layer : Fin gates.length → ℕ) (depth : ℕ) : Prop :=
  Monotone layer ∧ (∀ j, layer j < depth) ∧ ∀ i j, i ≠ j → layer i = layer j →
    Disjoint (locationSupport (gates.get i)) (locationSupport (gates.get j))

/-- Identity extension of a one-qubit channel at q. -/
def placeOne {n : ℕ} (q : Fin n) (M : Superop Bool Bool) : Superop (Qubits n) (Qubits n) :=
  liftReg (Stabilizer.wire1 q) (fun X =>
    (M (X.submatrix (fun b => fun _ : Fin 1 => b) (fun b => fun _ : Fin 1 => b))).submatrix
      (fun z => z 0) (fun z => z 0))

/-- I,S,S inverse, and I for the reset branch of (49). -/
def dampingPhase (index : Fin 4) : Matrix Bool Bool ℂ := ![1,phaseS,star phaseS,1] index

/-- Noisy CNOT part of (50); reset postmaps are carried forward, not implemented here. -/
def dampingCnotMap {n : ℕ} (eps : ℝ) (c t : Fin n) (h : c ≠ t) (i j : Fin 4) :
    Superop (Qubits n) (Qubits n) :=
  liftReg (Stabilizer.wire2 c t h)
    (dampingN 2 eps ∘ conjSuperop
      (Gate.ofMatrix2 (Matrix.kronecker (dampingPhase i) (dampingPhase j)*cnot)).mat)

/-- Single-gate decomposition for raw (not subtype-wrapped) source matrices. -/
def rawDampingGateMap (eps : ℝ) (U : Matrix Bool Bool ℂ) : Fin 4 → Superop Bool Bool :=
  ![damping eps ∘ conjSuperop U, damping eps ∘ conjSuperop phaseS ∘ conjSuperop U,
    damping eps ∘ conjSuperop (star phaseS) ∘ conjSuperop U,prepareMap (ket false)]

/-- Two-stage construction of pp.14--15.
First expand CNOT inverse noise, carrying resets to the next gate on the same wire.
Then decompose the resulting single gates or plus preparations. Each leaf has one
physical operation per original gate. No target equality is a construction field. -/
def dampingCircuitTerms {n : ℕ} (eps : ℝ) :
    List (IdealLocation n) → (Fin n → Bool) →
      List (ℝ × List (Superop (Qubits n) (Qubits n)))
  | [], _ => [(1,[])]
  | .single tag q :: rest, pending =>
      let cleared := Function.update pending q false
      let choices : List (ℝ × Superop Bool Bool) :=
        if pending q then
          if tag = 1 then (List.finRange 3).map fun i => (dampingPlusCoefficient eps i,dampingPlusMap eps i)
          else [(1,prepareMap (ket false))]
        else (List.finRange 4).map fun i =>
          (dampingGateCoefficient eps i,rawDampingGateMap eps (singleGateMatrix tag) i)
      choices.flatMap fun choice =>
        (dampingCircuitTerms eps rest cleared).map fun tail =>
          (choice.1*tail.1,placeOne q choice.2 :: tail.2)
  | .cnot c t h :: rest, pending =>
      (List.finRange 4).flatMap fun i => (List.finRange 4).flatMap fun j =>
        (dampingCircuitTerms eps rest (Function.update (Function.update pending c (decide (i=3))) t
          (decide (j=3)))).map fun tail =>
            (dampingGateCoefficient eps i*dampingGateCoefficient eps j*tail.1,
              dampingCnotMap eps c t h i j :: tail.2)

/-- Absolute-mass normalizer of the explicit two-stage list. -/
def dampingCircuitMass {n : ℕ} (eps : ℝ) (gates : List (IdealLocation n)) : ℝ :=
  ((dampingCircuitTerms eps gates (fun _ => false)).map fun term => |term.1|).sum

/-- Membership in the actual noisy basis Omega described on pp.14--15.
A state preparation is one operation. No post-reset is added after a CNOT. -/
def IsDampingReplacement {n : ℕ} (eps : ℝ) : IdealLocation n →
    Superop (Qubits n) (Qubits n) → Prop
  | .single tag q, M =>
      (∃ i : Fin 3, M = placeOne q (rawDampingGateMap eps (singleGateMatrix tag) i.castSucc)) ∨
      ∃ psi ∈ ({ket false,ket true,act hadamard (ket false),act hadamard (ket true)} :
        Set (EuclideanSpace ℂ Bool)), M = placeOne q (damping eps ∘ prepareMap psi)
  | .cnot c t h, M => ∃ i j : Fin 3, M = dampingCnotMap eps c t h i.castSucc j.castSucc

example (eps : ℝ) :
    dampingCircuitTerms (n:=0) eps [] (fun _ => false) = [(1,[])] := rfl

example (eps : ℝ) : dampingCircuitMass (n:=0) eps [] = 1 := by
  simp [dampingCircuitMass,dampingCircuitTerms]

example : singleGateMatrix 0 = 1 := rfl

/-- PDF pp.5--6, (12),(14)--(16): a finite system and arbitrary nonempty finite bath.
The interaction and bath Hamiltonian are fixed independently of rate and controls.
Only the total interaction is required Hermitian; no bath approximation is made. -/
structure BoundedBathData (q b : ℕ) where
  bathNonempty : 0 < b
  controls : (Fin q → Stabilizer.Pauli) → ℝ → ℝ
  continuous : ∀ a, Continuous (controls a)
  couplingCount : ℕ
  systemCoupling : Fin couplingCount → Matrix (Qubits q) (Qubits q) ℂ
  bathCoupling : Fin couplingCount → Matrix (Fin b) (Fin b) ℂ
  bathHamiltonian : Matrix (Fin b) (Fin b) ℂ
  bathHermitian : bathHamiltonian.IsHermitian
  interactionHermitian :
    ((∑ a, Matrix.kronecker (systemCoupling a) (bathCoupling a)) +
      Matrix.kronecker (1 : Matrix (Qubits q) (Qubits q) ℂ) bathHamiltonian).IsHermitian
  rhoSystem : Matrix (Qubits q) (Qubits q) ℂ
  systemDensity : IsDensityMatrix rhoSystem
  rhoBath : Matrix (Fin b) (Fin b) ℂ
  bathDensity : IsDensityMatrix rhoBath
  stationary : bathHamiltonian*rhoBath = rhoBath*bathHamiltonian

/-- Joint operator space; b need not be a power of two. -/
abbrev BathMatrix (q b : ℕ) := Matrix (Qubits q × Fin b) (Qubits q × Fin b) ℂ

/-- Eq. (12), lifted as K_S(t) tensor I_B, with system coordinate first. -/
def boundedBathControl {q b : ℕ} (D : BoundedBathData q b) (t : ℝ) : BathMatrix q b :=
  Matrix.kronecker (∑ a, (D.controls a t : ℂ) • pauliOps a)
    (1 : Matrix (Fin b) (Fin b) ℂ)

/-- Eq. (15), including the bath-only Hamiltonian in the fixed noise V. -/
def boundedBathInteraction {q b : ℕ} (D : BoundedBathData q b) : BathMatrix q b :=
  (∑ a, Matrix.kronecker (D.systemCoupling a) (D.bathCoupling a)) +
    Matrix.kronecker (1 : Matrix (Qubits q) (Qubits q) ℂ) D.bathHamiltonian

/-- The source's normalized product input, permitting mixed system states. -/
def boundedBathInitial {q b : ℕ} (D : BoundedBathData q b) : BathMatrix q b :=
  Matrix.kronecker D.rhoSystem D.rhoBath

/-- Eq. (14), the coherent noise generator, with the physical factor -i. -/
def boundedBathNoise {q b : ℕ} (D : BoundedBathData q b) (X : BathMatrix q b) : BathMatrix q b :=
  -Complex.I • (boundedBathInteraction D*X-X*boundedBathInteraction D)

/-- The induced trace norm ||L_V||_(1 to 1) from (27).
Its supremum set contains zero and is bounded: in finite dimension, the trace-norm
unit ball is compact and the fixed commutator is continuous. No junk supremum is used. -/
def boundedBathNoiseNorm {q b : ℕ} (D : BoundedBathData q b) : ℝ :=
  sSup {r : ℝ | ∃ X : BathMatrix q b, traceNorm X ≤ 1 ∧ r = traceNorm (boundedBathNoise D X)}

/-- Joint physical trajectory, not a reduced-system Markovian semigroup.
At T=0 the initial-value clause still fixes the endpoint. -/
def IsBoundedBathRun {q b : ℕ} (D : BoundedBathData q b) (K : ℝ → BathMatrix q b)
    (T rate : ℝ) (rho : ℝ → BathMatrix q b) : Prop :=
  0 ≤ T ∧ 0 ≤ rate ∧ rho 0 = boundedBathInitial D ∧
    ContinuousOn rho (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, IsDensityMatrix (rho t)) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt rho
        (-Complex.I • (K t*rho t-rho t*K t)+(rate : ℂ) • boundedBathNoise D (rho t))
        (Set.Icc 0 T) t

/-- Forward propagator for the controlled system Hamiltonian only, tensored with I_B.
As in noiseSeries, the printed frame in (17) is corrected to U^dagger rho U. -/
def IsBoundedBathForward {q b : ℕ} (D : BoundedBathData q b) (T : ℝ)
    (U : ℝ → BathMatrix q b) : Prop :=
  U 0 = 1 ∧ ContinuousOn U (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, U t ∈ Matrix.unitaryGroup _ ℂ) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt U (-Complex.I • (boundedBathControl D t*U t)) (Set.Icc 0 T) t

/-- Consistent interaction-frame coherent noise Ad(U^dagger) L_V Ad(U). -/
def boundedBathInteractionNoise {q b : ℕ} (D : BoundedBathData q b)
    (U : ℝ → BathMatrix q b) (t : ℝ) (X : BathMatrix q b) : BathMatrix q b :=
  (U t)ᴴ*boundedBathNoise D (U t*X*(U t)ᴴ)*U t

/-- Ordered Duhamel integrals, with latest time on the left and inner path at earliest time. -/
def boundedBathIntegral {q b : ℕ} (D : BoundedBathData q b)
    (U initial : ℝ → BathMatrix q b) : ℕ → ℝ → BathMatrix q b
  | 0, t => initial t
  | k+1, t => ∫ s in (0 : ℝ)..t,
      boundedBathInteractionNoise D U s (boundedBathIntegral D U initial k s)

/-- Eq. (23)'s real coefficient for A=A_S tensor I_B, independent of noise rate. -/
def boundedBathCoefficient {q b : ℕ} (D : BoundedBathData q b)
    (U : ℝ → BathMatrix q b) (A : Matrix (Qubits q) (Qubits q) ℂ) (T : ℝ) (k : ℕ) : ℝ :=
  ((Matrix.kronecker A (1 : Matrix (Fin b) (Fin b) ℂ))*
    (U T*boundedBathIntegral D U (fun _ => boundedBathInitial D) k T*(U T)ᴴ)).trace.re

/-- Eq. (24)'s actual integral remainder, using the evolved joint density at the inner time. -/
def boundedBathRemainder {q b : ℕ} (D : BoundedBathData q b)
    (U rho : ℝ → BathMatrix q b) (A : Matrix (Qubits q) (Qubits q) ℂ)
    (T rate : ℝ) (n : ℕ) : ℝ :=
  rate^(n+1)*((Matrix.kronecker A (1 : Matrix (Fin b) (Fin b) ℂ))*
    (U T*boundedBathIntegral D U (fun t => (U t)ᴴ*rho t*U t) (n+1) T*(U T)ᴴ)).trace.re

/-- Sanity: zero generator at the zero operator, on any allowed system/bath size. -/
example {q b : ℕ} (D : BoundedBathData q b) : boundedBathNoise D 0 = 0 := by
  simp [boundedBathNoise]

example {q b : ℕ} (D : BoundedBathData q b) (hV : boundedBathInteraction D = 0)
    (X : BathMatrix q b) : boundedBathNoise D X = 0 := by
  simp [boundedBathNoise,hV]

example {q b : ℕ} (D : BoundedBathData q b) (U X : ℝ → BathMatrix q b) (t : ℝ) :
    boundedBathIntegral D U X 0 t = X t := rfl

example {q b : ℕ} (D : BoundedBathData q b) (U X : ℝ → BathMatrix q b) (k : ℕ) :
    boundedBathIntegral D U X (k+1) 0 = 0 := by
  simp [boundedBathIntegral]

example {q b : ℕ} (D : BoundedBathData q b) (U rho : ℝ → BathMatrix q b)
    (A : Matrix (Qubits q) (Qubits q) ℂ) (T : ℝ) (n : ℕ) :
    boundedBathRemainder D U rho A T 0 n = 0 := by
  simp [boundedBathRemainder]

example {q b : ℕ} (D : BoundedBathData q b) :
    (0 : ℝ) ∈ {r : ℝ | ∃ X : BathMatrix q b, traceNorm X ≤ 1 ∧
      r = traceNorm (boundedBathNoise D X)} := by
  refine ⟨0, ?_, ?_⟩ <;> simp [boundedBathNoise,traceNorm,cfc_zero]

end QAlgorithms.Papers.Independent.Independent2.P01


