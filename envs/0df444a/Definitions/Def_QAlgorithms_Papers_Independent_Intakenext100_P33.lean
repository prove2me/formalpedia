-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P33
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P33
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:03:22.098994+00:00
-- url     : https://prove2.me/theorems/397b6422-c66b-4b5a-8cd4-7248144b9bea
-- title:
--   Definitions for The Quantum State of a Propagating Laser Field
-- statement:
--   The objects the formalized statements of *The Quantum State of a Propagating Laser Field* (arXiv:quant-ph/0111157) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `phaseLaw`: PDF p.1, Eq.(2): normalized uniform phase law on one period.
--   - `TraceIntegral`: A trace-norm Bochner integral specified without imposing the operator norm on trace class. Finite-range integrable approximants converge in L¹ nuclear norm. Together with the bounded-operator integral identity this is the genuine trace-class integral, rather than an entrywise or merely weak integral. All nuclear norms are guarded by trace-class membership. PDF pp.1,3,5.
--   - `PacketSpace`: PDF p.3: N distinguishable temporal packets, each with unbounded occupation.
--   - `PacketOperator`: Bounded operators on the full N-packet space.
--   - `packetBasis`: PDF p.3: the tensor occupation basis, including the scalar register N=0.
--   - `HasPacketMatrix`: Exact matrix realization on the total orthonormal occupation basis.
--   - `packetOperator`: Many-packet bounded realization. Theorems assert realization, so the zero fallback outside the bounded regime cannot furnish any physical conclusion.
--   - `IsPacketDensity`: Positive, normalized trace-class N-packet density. PDF p.3, Eq.(13).
--   - `packetCoefficients`: PDF p.3, Eqs.(10)–(12): product coherent coefficients in selected modes.
--   - `packetCoherent`: Constructed full-Fock coherent product. Square summability and normalization are conclusions below, never assumptions on these constructed vectors.
--   - `packetProjector`: PDF p.3: projector of the constructed coherent product.
--   - `fullFockTensorPower`: PDF pp.3–5: full-Fock bounded realization of the accepted matrix tensor power. Information100.P63.tensorPower works for arbitrary index types, so it supplies the occupation coefficients at I=Nat. packetOperator additionally realizes them on l²; the theorems conclude realization for density inputs.
--   - `commonPhase`: PDF p.3, Eq.(13): shared-phase finite-window family.
--   - `discardLastPacket`: PDF pp.3–4: full-Fock partial trace discarding the last packet. Unlike Gap48.P33.discardLast, whose discarded register has a Fintype instance, this sums all natural occupations without a cutoff. Summability and bounded realization are explicit conclusions in the beam theorem.
--   - `permutePackets`: PDF p.4: permutation of packet factors, in occupation coordinates.
--   - `packetFunction`: PDF p.3, Eq.(11), with tau=z0/c. Open endpoints have no L² effect.
--   - `cwAmplitude`: PDF pp.2–3: beta=sqrt(kappa)*alpha*exp(i phi), the ideal linear, frequency-independent vacuum-input boundary condition, without phase noise, amplitude noise or dissipation. The high-finesse, near-resonance and long-time approximations specify this model; no quantitative physical error is asserted.
--   - `cwPacketAmplitude`: PDF p.3, Eq.(10): actual mode projection, before simplifying the rectangle.
--   - `idealBeam`: PDF pp.2–3: constructed ideal vacuum-input CW output from the stationary intracavity Poisson law, using its uniform phase ensemble and the computed output projections. Each finite observed window is constructed separately.
--   - `TemporalSpace`: Single-packet rectangular modes in L²(R), restricted to a finite observation window by the finite family used. No constant function on all R is a vector.
--   - `temporalPacket`: Eq.(11) as an L² vector. Membership and the representative identity are concluded below, excluding the total-function fallback.
--   - `temporalField`: The finite-window coherent field's one-particle displacement, Eqs.(6),(10). It is constant beta on the observed packet intervals and zero outside them.
--   - `modeAmplitude`: Eq.(10): projection onto any normalized discrete temporal mode.
--   - `finiteModeVector`: Eq.(6) in a finite set of orthonormal modes: its coherent factor is constructed from the one-particle projections, not from asserted output states.
--   - `FockLocalInstrument`: PDF p.5, Eqs.(22)–(23): an actual local finite-outcome quantum measurement, allowing countably many Kraus operators per outcome. Completeness is strong summation on the full Hilbert space, not an assumed posterior law. Gap20.P09.LocalMeasurement instead requires a finite-dimensional input and stores only POVM effects; it cannot describe this full-Fock Kraus instrument.
--   - `localEffect`: The selected outcome's computed effect, summing the internal Kraus index and the output occupation. The theorem asserts bounded realization.
--   - `packetLikelihood`: Product Born likelihood for the observed string of individual-packet measurements; no classical phase-readout instrument is presumed.
--   - `packetEvidence`: The unconditional probability calculated from the input ensemble.
--   - `eventKraus`: Tensor Kraus operator for the first K packets, identity on the further M. The construction includes the actual local actions and does not touch the unmeasured packets. Realization is asserted below, excluding the fallback.
--   - `eventTerm`: One internal branch of the observed string's actual instrument.
--   - `eventOutput`: Unnormalized quantum state after the selected outcome, before discarding measured packets. Trace-norm summability is a theorem conclusion.
--   - `discardPrefix`: Partial trace of the first K packets, leaving the last M.
--   - `packetResidual`: Unnormalized residual computed from the instrument, not a Bayesian identity assumed as input. PDF p.5.
--   - `posteriorPhaseLaw`: Bayesian phase law with RN derivative L/Z. Only positive-evidence use is asserted below; division at Z=0 cannot supply a posterior density.
--   - `equalSplitter`: PDF p.5: lossless equal N-port splitter; the Fourier unitary's first column is real positive, fixing the compensable output port phases. N>=1 is required by the theorem; the N=0 division fallback is never used.
--   - `splitNumberCoefficients`: First-input-column second quantization of the constructed equal splitter: expand (sum_j a_j†/sqrt(N))^m/sqrt(m!). No photon cutoff. PDF p.5, Eq.(25).
--   - `splitNumber`: The finite-photon input is sent to its explicitly expanded output vector.
--   - `splitCoherent`: Equal splitting of a coherent input is constructed by linearity on its number expansion, rather than defined to be the desired coherent product.
--   - `spatialBeam`: Phase-averaged fixed-total-energy spatial beam. PDF p.5, §IIE.
--   - `DownCore`: PDF p.7, Eq.(32): finite occupation core for the pump and signal.
--   - `weightedNumber`: The conserved weighted number on the common finite-occupation core.
--   - `downHamiltonian`: Exact cubic Hamiltonian on the core. Both lowering boundaries are guarded; this is not a bounded annihilation operator on the full Fock space.
--   - `downBlock`: The invariant weighted-number-w block, indexed by pump occupation j and signal occupation w-2j. PDF p.7, following Eq.(32).
--   - `downBlockEvolution`: Exact Schroedinger evolution in each finite invariant block, hbar=1.
--   - `downCoefficients`: Direct-sum evolution coefficients, a finite sum at every output occupation. This constructs dynamics on arbitrary full two-mode vectors.
--   - `downEvolution`: Full-space evolution. Its coefficient realization and unitary extension are conclusions, so square summability is never assumed as output data.
--   - `evolvedPumpNumber`: Evolved |m,0>, with vacuum in the signal input.
--   - `signalMatrix`: Computed signal matrix after tracing out the pump, for an arbitrary initial pump probability law p. The theorem guards p's normalization and all series.
--   - `signalOutput`: Reduced signal operator built from the dynamics and the partial trace.
-- source:
--   The Quantum State of a Propagating Laser Field, arXiv:quant-ph/0111157v1, https://arxiv.org/abs/quant-ph/0111157v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

/-!
Exact ideal-model statements from arXiv:quant-ph/0111157v1.
All oscillator registers are full l² spaces. A continuous CW beam is a family
of finite-window states; no constant-amplitude vector on the whole real line is
postulated. Source-ambiguous operational claims are listed in the unit's
HARD.md and GAPS.json. The finite-data measurement instrument is constructed here.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P33

open Filter MeasureTheory
open scoped Topology Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P39

-- Accepted scalar phase; positive exponential, differing only by commuting scalars.
open QAlgorithms.Papers.Independent.Information100.P75 (phase)

/-- PDF p.1, Eq.(2): normalized uniform phase law on one period. -/
def phaseLaw : Measure ℝ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) • volume.restrict (Set.Ico 0 (2 * Real.pi))

/-- A trace-norm Bochner integral specified without imposing the operator norm
on trace class. Finite-range integrable approximants converge in L¹ nuclear
norm. Together with the bounded-operator integral identity this is the genuine
trace-class integral, rather than an entrywise or merely weak integral.
All nuclear norms are guarded by trace-class membership. PDF pp.1,3,5. -/
def TraceIntegral {A H : Type*} [MeasurableSpace A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (mu : Measure A) (f : A → (H →L[ℂ] H)) (X : H →L[ℂ] H) : Prop :=
  Integrable f mu ∧ (∫ x, f x ∂mu) = X ∧ IsTraceClass X ∧
    (∀ᵐ x ∂mu, IsTraceClass (f x)) ∧
    ∃ s : ℕ → A → (H →L[ℂ] H),
      (∀ n, (Set.range (s n)).Finite ∧ Integrable (s n) mu ∧
        (∀ᵐ x ∂mu, IsTraceClass (s n x) ∧ IsTraceClass (f x - s n x)) ∧
        Integrable (fun x => nuclearTraceNorm (f x - s n x)) mu) ∧
      Tendsto (fun n => ∫ x, nuclearTraceNorm (f x - s n x) ∂mu) atTop (nhds 0)

/-- PDF p.3: N distinguishable temporal packets, each with unbounded occupation. -/
abbrev PacketSpace (N : ℕ) := QAlgorithms.RealRegisters.Hilbert (Fin N → ℕ)

/-- Bounded operators on the full N-packet space. -/
abbrev PacketOperator (N : ℕ) := PacketSpace N →L[ℂ] PacketSpace N

/-- PDF p.3: the tensor occupation basis, including the scalar register N=0. -/
def packetBasis {N : ℕ} (m : Fin N → ℕ) : PacketSpace N := lp.single 2 m 1

/-- Exact matrix realization on the total orthonormal occupation basis. -/
def HasPacketMatrix {N : ℕ} (X : PacketOperator N)
    (c : (Fin N → ℕ) → (Fin N → ℕ) → ℂ) : Prop :=
  ∀ m n, X (packetBasis n) m = c m n

/-- Many-packet bounded realization. Theorems assert realization, so the zero
fallback outside the bounded regime cannot furnish any physical conclusion. -/
def packetOperator {N : ℕ}
    (c : (Fin N → ℕ) → (Fin N → ℕ) → ℂ) : PacketOperator N :=
  if h : ∃ X : PacketOperator N, HasPacketMatrix X c then Classical.choose h else 0

/-- Positive, normalized trace-class N-packet density. PDF p.3, Eq.(13). -/
def IsPacketDensity {N : ℕ} (X : PacketOperator N) : Prop :=
  IsTraceClass X ∧ ContinuousLinearMap.adjoint X = X ∧
    (∀ v, 0 ≤ (inner (𝕜 := ℂ) v (X v)).re) ∧
    Summable (fun n => X (packetBasis n) n) ∧ (∑' n, X (packetBasis n) n) = 1

/-- PDF p.3, Eqs.(10)–(12): product coherent coefficients in selected modes. -/
def packetCoefficients {N : ℕ} (z : Fin N → ℂ) (m : Fin N → ℕ) : ℂ :=
  ∏ i, coherentCoefficient (z i) (m i)

/-- Constructed full-Fock coherent product. Square summability and normalization
are conclusions below, never assumptions on these constructed vectors. -/
def packetCoherent {N : ℕ} (z : Fin N → ℂ) : PacketSpace N :=
  if h : Memℓp (packetCoefficients z) 2 then ⟨packetCoefficients z, h⟩ else 0

/-- PDF p.3: projector of the constructed coherent product. -/
def packetProjector {N : ℕ} (z : Fin N → ℂ) : PacketOperator N :=
  InnerProductSpace.rankOne ℂ (packetCoherent z) (packetCoherent z)

/-- PDF pp.3–5: full-Fock bounded realization of the accepted matrix tensor
power. Information100.P63.tensorPower works for arbitrary index types, so it
supplies the occupation coefficients at I=Nat. packetOperator additionally
realizes them on l²; the theorems conclude realization for density inputs. -/
def fullFockTensorPower (X : FockOperator) (N : ℕ) : PacketOperator N :=
  packetOperator (QAlgorithms.Papers.Independent.Information100.P63.tensorPower N
    (fun m n : ℕ => X (fockKet n) m))

/-- PDF p.3, Eq.(13): shared-phase finite-window family. -/
def commonPhase (a : ℝ) (N : ℕ) : PacketOperator N :=
  ∫ theta, packetProjector (fun _ : Fin N => (a : ℂ) * phase theta) ∂phaseLaw

/-- PDF pp.3–4: full-Fock partial trace discarding the last packet.
Unlike Gap48.P33.discardLast, whose discarded register has a Fintype instance,
this sums all natural occupations without a cutoff. Summability and bounded
realization are explicit conclusions in the beam theorem. -/
def discardLastPacket {N : ℕ} (X : PacketOperator (N + 1)) : PacketOperator N :=
  packetOperator (fun m n => ∑' k : ℕ,
    X (packetBasis (Fin.snoc n k)) (Fin.snoc m k))

/-- PDF p.4: permutation of packet factors, in occupation coordinates. -/
def permutePackets {N : ℕ} (s : Equiv.Perm (Fin N)) (X : PacketOperator N) :
    PacketOperator N :=
  packetOperator (fun m n => X (packetBasis (n ∘ s)) (m ∘ s))

/-- PDF p.3, Eq.(11), with tau=z0/c. Open endpoints have no L² effect. -/
def packetFunction (T tau : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  if |t - tau - (n : ℝ) * T| < T / 2 then ((Real.sqrt T)⁻¹ : ℝ) else 0

/-- PDF pp.2–3: beta=sqrt(kappa)*alpha*exp(i phi), the ideal linear,
frequency-independent vacuum-input boundary condition, without phase noise,
amplitude noise or dissipation. The high-finesse, near-resonance and long-time
approximations specify this model; no quantitative physical error is asserted. -/
def cwAmplitude (kappa : ℝ) (alpha : ℂ) (phi : ℝ) : ℂ :=
  (Real.sqrt kappa : ℂ) * alpha * phase phi

/-- PDF p.3, Eq.(10): actual mode projection, before simplifying the rectangle. -/
def cwPacketAmplitude (kappa T tau : ℝ) (alpha : ℂ) (phi : ℝ) (n : ℕ) : ℂ :=
  ∫ t in Set.Ioo (tau + (n : ℝ) * T - T / 2) (tau + (n : ℝ) * T + T / 2),
    star (packetFunction T tau n t) * cwAmplitude kappa alpha phi

/-- PDF pp.2–3: constructed ideal vacuum-input CW output from the stationary
intracavity Poisson law, using its uniform phase ensemble and the computed
output projections. Each finite observed window is constructed separately. -/
def idealBeam (kappa T tau alpha : ℝ) (N : ℕ) : PacketOperator N :=
  ∫ phi, packetProjector (fun i : Fin N =>
    cwPacketAmplitude kappa T tau (alpha : ℂ) phi i.val) ∂phaseLaw

/-- Single-packet rectangular modes in L²(R), restricted to a finite observation
window by the finite family used. No constant function on all R is a vector. -/
abbrev TemporalSpace := Lp ℂ 2 (volume : Measure ℝ)

/-- Eq.(11) as an L² vector. Membership and the representative identity are
concluded below, excluding the total-function fallback. -/
def temporalPacket (T tau : ℝ) (n : ℕ) : TemporalSpace :=
  if h : MemLp (packetFunction T tau n) 2 volume then h.toLp _ else 0

/-- The finite-window coherent field's one-particle displacement, Eqs.(6),(10).
It is constant beta on the observed packet intervals and zero outside them. -/
def temporalField (kappa T tau : ℝ) (alpha : ℂ) (phi : ℝ) (N : ℕ) : TemporalSpace :=
  ∑ i : Fin N, ((Real.sqrt T : ℂ) * cwAmplitude kappa alpha phi) •
    temporalPacket T tau i.val

/-- Eq.(10): projection onto any normalized discrete temporal mode. -/
def modeAmplitude (f g : TemporalSpace) : ℂ := inner (𝕜 := ℂ) f g

/-- Eq.(6) in a finite set of orthonormal modes: its coherent factor is
constructed from the one-particle projections, not from asserted output states. -/
def finiteModeVector {D : ℕ} (f : TemporalSpace) (modes : Fin D → TemporalSpace) :
    PacketSpace D := packetCoherent (fun i => modeAmplitude (modes i) f)

/-- PDF p.5, Eqs.(22)–(23): an actual local finite-outcome quantum
measurement, allowing countably many Kraus operators per outcome. Completeness
is strong summation on the full Hilbert space, not an assumed posterior law.
Gap20.P09.LocalMeasurement instead requires a finite-dimensional input and
stores only POVM effects; it cannot describe this full-Fock Kraus instrument. -/
structure FockLocalInstrument (O : ℕ) where
  kraus : Fin O → ℕ → FockOperator
  complete : ∀ v : Fock, HasSum (fun j : Fin O × ℕ =>
    (ContinuousLinearMap.adjoint (kraus j.1 j.2)) (kraus j.1 j.2 v)) v

/-- The selected outcome's computed effect, summing the internal Kraus index
and the output occupation. The theorem asserts bounded realization. -/
def localEffect {O : ℕ} (A : FockLocalInstrument O) (d : Fin O) : FockOperator :=
  operatorOfMatrix (fun m n => ∑' k : ℕ × ℕ,
    star (A.kraus d k.1 (fockKet m) k.2) * A.kraus d k.1 (fockKet n) k.2)

/-- Product Born likelihood for the observed string of individual-packet
measurements; no classical phase-readout instrument is presumed. -/
def packetLikelihood {K O : ℕ} (A : Fin K → FockLocalInstrument O)
    (d : Fin K → Fin O) (a theta : ℝ) : ℝ :=
  ∏ i, (inner (𝕜 := ℂ) (coherentKet ((a : ℂ) * phase theta))
    (localEffect (A i) (d i) (coherentKet ((a : ℂ) * phase theta)))).re

/-- The unconditional probability calculated from the input ensemble. -/
def packetEvidence {K O : ℕ} (A : Fin K → FockLocalInstrument O)
    (d : Fin K → Fin O) (a : ℝ) : ℝ :=
  ∫ theta, packetLikelihood A d a theta ∂phaseLaw

/-- Tensor Kraus operator for the first K packets, identity on the further M.
The construction includes the actual local actions and does not touch the
unmeasured packets. Realization is asserted below, excluding the fallback. -/
def eventKraus {K O : ℕ} (M : ℕ) (A : Fin K → FockLocalInstrument O)
    (d : Fin K → Fin O) (r : Fin K → ℕ) : PacketOperator (K + M) :=
  packetOperator (fun m n =>
    if (m ∘ Fin.natAdd K) = (n ∘ Fin.natAdd K) then
      ∏ i : Fin K, (A i).kraus (d i) (r i)
        (fockKet (n (Fin.castAdd M i))) (m (Fin.castAdd M i)) else 0)

/-- One internal branch of the observed string's actual instrument. -/
def eventTerm {K O : ℕ} (M : ℕ) (A : Fin K → FockLocalInstrument O)
    (d : Fin K → Fin O) (a : ℝ) (r : Fin K → ℕ) : PacketOperator (K + M) :=
  ((eventKraus M A d r).comp (commonPhase a (K + M))).comp
    (ContinuousLinearMap.adjoint (eventKraus M A d r))

/-- Unnormalized quantum state after the selected outcome, before discarding
measured packets. Trace-norm summability is a theorem conclusion. -/
def eventOutput {K O : ℕ} (M : ℕ) (A : Fin K → FockLocalInstrument O)
    (d : Fin K → Fin O) (a : ℝ) : PacketOperator (K + M) :=
  ∑' r : Fin K → ℕ, eventTerm M A d a r

/-- Partial trace of the first K packets, leaving the last M. -/
def discardPrefix (K M : ℕ) (X : PacketOperator (K + M)) : PacketOperator M :=
  packetOperator (fun m n => ∑' q : Fin K → ℕ,
    X (packetBasis (Fin.append q n)) (Fin.append q m))

/-- Unnormalized residual computed from the instrument, not a Bayesian
identity assumed as input. PDF p.5. -/
def packetResidual {K O : ℕ} (M : ℕ) (A : Fin K → FockLocalInstrument O)
    (d : Fin K → Fin O) (a : ℝ) : PacketOperator M :=
  discardPrefix K M (eventOutput M A d a)

/-- Bayesian phase law with RN derivative L/Z. Only positive-evidence use is
asserted below; division at Z=0 cannot supply a posterior density. -/
def posteriorPhaseLaw {K O : ℕ} (A : Fin K → FockLocalInstrument O)
    (d : Fin K → Fin O) (a : ℝ) : Measure ℝ :=
  phaseLaw.withDensity (fun theta =>
    ENNReal.ofReal (packetLikelihood A d a theta / packetEvidence A d a))

/-- PDF p.5: lossless equal N-port splitter; the Fourier unitary's first column
is real positive, fixing the compensable output port phases. N>=1 is required
by the theorem; the N=0 division fallback is never used. -/
def equalSplitter (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => ((Real.sqrt (N : ℝ))⁻¹ : ℝ) *
    phase (2 * Real.pi * (j.val : ℝ) * (k.val : ℝ) / (N : ℝ))

/-- First-input-column second quantization of the constructed equal splitter:
expand (sum_j a_j†/sqrt(N))^m/sqrt(m!). No photon cutoff. PDF p.5, Eq.(25). -/
def splitNumberCoefficients (N m : ℕ) (q : Fin N → ℕ) : ℂ :=
  if ∑ j, q j = m then
    (Real.sqrt (Nat.factorial m : ℝ) /
      (Real.sqrt (∏ j, (Nat.factorial (q j) : ℝ)) * Real.sqrt (N : ℝ) ^ m) : ℝ)
  else 0

/-- The finite-photon input is sent to its explicitly expanded output vector. -/
def splitNumber (N m : ℕ) : PacketSpace N :=
  if h : Memℓp (splitNumberCoefficients N m) 2 then ⟨splitNumberCoefficients N m, h⟩ else 0

/-- Equal splitting of a coherent input is constructed by linearity on its
number expansion, rather than defined to be the desired coherent product. -/
def splitCoherent (N : ℕ) (alpha : ℂ) : PacketSpace N :=
  ∑' m : ℕ, coherentCoefficient alpha m • splitNumber N m

/-- Phase-averaged fixed-total-energy spatial beam. PDF p.5, §IIE. -/
def spatialBeam (alpha : ℝ) (N : ℕ) : PacketOperator N :=
  ∫ theta, InnerProductSpace.rankOne ℂ
    (splitCoherent N ((alpha : ℂ) * phase theta))
    (splitCoherent N ((alpha : ℂ) * phase theta)) ∂phaseLaw

/-- PDF p.7, Eq.(32): finite occupation core for the pump and signal. -/
abbrev DownCore := (ℕ × ℕ) →₀ ℂ

/-- The conserved weighted number on the common finite-occupation core. -/
def weightedNumber (v : DownCore) : DownCore :=
  v.sum (fun q c => Finsupp.single q (((2 * q.1 + q.2 : ℕ) : ℂ) * c))

/-- Exact cubic Hamiltonian on the core. Both lowering boundaries are guarded;
this is not a bounded annihilation operator on the full Fock space. -/
def downHamiltonian (chi : ℝ) (v : DownCore) : DownCore :=
  v.sum (fun q c =>
    (if 2 ≤ q.2 then Finsupp.single (q.1 + 1, q.2 - 2)
      (c * (chi : ℂ) * (Real.sqrt
        (((q.1 + 1) : ℝ) * (q.2 : ℝ) * ((q.2 - 1 : ℕ) : ℝ)) : ℂ)) else 0) +
    (if 1 ≤ q.1 then Finsupp.single (q.1 - 1, q.2 + 2)
      (c * (chi : ℂ) * (Real.sqrt
        ((q.1 : ℝ) * ((q.2 + 1) : ℝ) * ((q.2 + 2) : ℝ)) : ℂ)) else 0))

/-- The invariant weighted-number-w block, indexed by pump occupation j and
signal occupation w-2j. PDF p.7, following Eq.(32). -/
def downBlock (chi : ℝ) (w : ℕ) : Matrix (Fin (w / 2 + 1)) (Fin (w / 2 + 1)) ℂ :=
  fun i j =>
    if i.val = j.val + 1 then
      ((chi * Real.sqrt (((j.val + 1 : ℕ) : ℝ) * ((w - 2 * j.val : ℕ) : ℝ) *
        ((w - 2 * j.val - 1 : ℕ) : ℝ))) : ℝ)
    else if j.val = i.val + 1 then
      ((chi * Real.sqrt (((i.val + 1 : ℕ) : ℝ) * ((w - 2 * i.val : ℕ) : ℝ) *
        ((w - 2 * i.val - 1 : ℕ) : ℝ))) : ℝ)
    else 0

/-- Exact Schroedinger evolution in each finite invariant block, hbar=1. -/
def downBlockEvolution (chi t : ℝ) (w : ℕ) :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • downBlock chi w)

/-- Direct-sum evolution coefficients, a finite sum at every output occupation.
This constructs dynamics on arbitrary full two-mode vectors. -/
def downCoefficients (chi t : ℝ) (v : BipartiteFock) (q : ℕ × ℕ) : ℂ :=
  let w := 2 * q.1 + q.2
  ∑ j : Fin (w / 2 + 1),
    downBlockEvolution chi t w ⟨q.1, by dsimp [w]; omega⟩ j *
      v (j.val, w - 2 * j.val)

/-- Full-space evolution. Its coefficient realization and unitary extension
are conclusions, so square summability is never assumed as output data. -/
def downEvolution (chi t : ℝ) (v : BipartiteFock) : BipartiteFock :=
  if h : Memℓp (downCoefficients chi t v) 2 then ⟨downCoefficients chi t v, h⟩ else 0

/-- Evolved |m,0>, with vacuum in the signal input. -/
def evolvedPumpNumber (chi t : ℝ) (m : ℕ) : BipartiteFock :=
  downEvolution chi t (bipartiteKet (m, 0))

/-- Computed signal matrix after tracing out the pump, for an arbitrary initial
pump probability law p. The theorem guards p's normalization and all series. -/
def signalMatrix (p : ℕ → ℝ) (chi t : ℝ) (n l : ℕ) : ℂ :=
  ∑' k : ℕ × ℕ, (p k.1 : ℂ) * evolvedPumpNumber chi t k.1 (k.2, n) *
    star (evolvedPumpNumber chi t k.1 (k.2, l))

/-- Reduced signal operator built from the dynamics and the partial trace. -/
def signalOutput (p : ℕ → ℝ) (chi t : ℝ) : FockOperator :=
  operatorOfMatrix (signalMatrix p chi t)

/-! Sanity checks of local constructions; none is an admitted normalization proof. -/

example : phase 0 = 1 := by simp [phase]

-- Zero packets have the same scalar tensor power for every one-mode input.
example (X Y : FockOperator) : fullFockTensorPower X 0 = fullFockTensorPower Y 0 := by
  unfold fullFockTensorPower
  apply congrArg (packetOperator (N := 0))
  funext m n
  simp [QAlgorithms.Papers.Independent.Information100.P63.tensorPower]

example (m : Fin 0 → ℕ) : packetCoefficients (fun _ : Fin 0 => (0 : ℂ)) m = 1 := by
  simp [packetCoefficients]

example (T tau : ℝ) (hT : 0 < T) (n : ℕ) :
    packetFunction T tau n (tau + (n : ℝ) * T) = ((Real.sqrt T)⁻¹ : ℝ) := by
  simp [packetFunction, show (0 : ℝ) < T / 2 by linarith]

example (kappa T tau : ℝ) (alpha : ℂ) (phi : ℝ) :
    temporalField kappa T tau alpha phi 0 = 0 := by simp [temporalField]

example : splitNumberCoefficients 1 0 (fun _ => 0) = 1 := by
  simp [splitNumberCoefficients]

example {O : ℕ} (A : Fin 0 → FockLocalInstrument O) (d : Fin 0 → Fin O)
    (a theta : ℝ) : packetLikelihood A d a theta = 1 := by
  simp [packetLikelihood]

example : weightedNumber 0 = 0 := by simp [weightedNumber]

example (chi : ℝ) : downHamiltonian chi 0 = 0 := by simp [downHamiltonian]

example (chi : ℝ) : downBlock chi 0 = 0 := by
  ext i j
  have hi : i.val = 0 := by
    have := i.isLt
    omega
  have hj : j.val = 0 := by
    have := j.isLt
    omega
  simp [downBlock, hi, hj]

end QAlgorithms.Papers.Independent.Intakenext100.P33


