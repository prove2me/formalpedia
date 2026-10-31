-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67
-- name    : QAlgorithms_Papers_Independent_Intake100_P67
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T14:19:07.790271+00:00
-- url     : https://prove2.me/theorems/d9695b56-78aa-45fc-98b6-6268f0465902
-- title:
--   Definitions for Quantum teleportation scheme by selecting one of multiple output ports
-- statement:
--   The objects the formalized statements of *Quantum teleportation scheme by selecting one of multiple output ports* (arXiv:0901.2975) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AC`: PDF pp.1–3: the ordered Alice register and the extra input/reference qubit.
--   - `singletAmp`: PDF p.2: the normalized singlet amplitude, with |0> = spin down.
--   - `resource`: PDF p.2: normalized resource (O tensor I)|singlet>^N, allowing rectangular O.
--   - `ResourceNormalized`: PDF p.3, Eq.(5): exactly the normalization required of O, including singular O.
--   - `transformed`: PDF p.3, Eq.(3): transformed effects, with C relabelled B.
--   - `portSignal`: PDF p.2, Eq.(2): signal sigma(i), including the maximally mixed unused A qubits.
--   - `portRho`: PDF p.3, Eq.(6): the sum of the physical signal matrices.
--   - `entFidelity`: PDF p.3, Eq.(3): singlet entanglement fidelity of the recovered qubit.
--   - `portAverageFidelity`: PDF pp.2–3: normalized Haar average, f=(2F+1)/3, for deterministic protocols.
--   - `IsDeterministicPortProtocol`: PDF pp.2–3: input-independent resource and a full N-outcome Alice POVM. Bob's only operation is selection of the reported port.
--   - `portRetainedOutput`: PDF p.2, Eq.(1): one retained-port branch, written in matrix entries. Tracing out Alice makes the square-root instrument equal to contraction with its effect. No operation on the output qudit occurs.
--   - `SubPOVM`: PDF p.7: a sub-POVM with the positive omitted effect as failure outcome 0.
--   - `IsFaithfulPortProtocol`: PDF p.7: every successful branch returns every normalized unknown pure input exactly. Zero-probability branches are allowed; failure is unconstrained.
--   - `IsProbabilisticPortProtocol`: PDF pp.7–8: physical faithful probabilistic protocols with an input-independent resource.
--   - `portSuccessProbability`: PDF p.7, Eq.(44): success averaged over normalized Haar inputs, not conditional fidelity.
--   - `Other`: PDF pp.3–5: the actual residual wires; no fictitious negative-spin subsystem.
--   - `embedTheta`: PDF p.7, Eq.(45): P^-_{AiC} tensor Theta_i on the remaining A wires.
--   - `PortSuccessFeasible`: PDF p.7, Eqs.(5),(46): the complete success SDP feasibility constraints.
--   - `successObjective`: PDF p.7, Eq.(47): the success SDP objective.
--   - `spins`: PDF pp.3–5: legal doubled spins k=2j. Factorial arguments below are integers.
--   - `spinSquare`: PDF p.3: Casimir J^2 of spin-half wires, from S_i.S_j=(Swap_ij-I/2)/2. The scalar arithmetic is real, so n=0 never causes natural subtraction underflow.
--   - `qubitSpinProjector`: PDF pp.3–5: the spin-j projector, defined intrinsically by spectral calculus of J^2. This is the identity 11(j) on the span of all source |Phi(j,m,alpha)> vectors. Finite spectra make the indicator continuous on the spectrum. Illegal sectors are zero.
--   - `totalProjector`: PDF p.4: the total-spin projector on AC, the extra qubit indexed by none.
--   - `lambdaMinus`: PDF p.3, Eq.(7): lambda^-_j with j=k/2. Real subtraction is intentional.
--   - `lambdaPlus`: PDF p.3, Eq.(7): lambda^+_j with j=k/2.
--   - `minusSector`: PDF pp.3–4, Eqs.(8),(17): the whole eigenspace obtained by coupling j to j+1/2.
--   - `plusSector`: PDF pp.3–4, Eqs.(8),(17): coupling j to j-1/2; absent when j=0.
--   - `rhoBlock`: PDF p.4: rho(s), on the full space with zero on other total-spin sectors.
--   - `xiProjector`: PDF p.5, Eq.(24): projector onto singlet_{AiC} tensor the residual spin-s sector.
--   - `signalBlock`: PDF p.5: sigma(i)(s), including the normalization 2^{-(N-1)}.
--   - `compressedScalar`: PDF p.5, Eq.(26): scalar compressed moment; k=2s and y is nonzero. At s=0 the nonexistent j=-1/2 term is omitted.
--   - `completedSRM`: PDF p.5, Eqs.(27),(28): SRM completed uniformly on its kernel.
--   - `fixedFidelity`: PDF p.5, Eq.(29): exact fixed-resource entanglement fidelity.
--   - `deterministicOptimumFidelity`: PDF p.7, Eq.(41): the optimum singlet entanglement fidelity.
--   - `deterministicOptimumAverage`: PDF p.7, Eq.(42): the optimum Haar average recovered-qubit fidelity.
--   - `deterministicGamma`: PDF p.6, Eq.(35): gamma(j) on the legal doubled-spin range.
--   - `deterministicX`: PDF p.6, Eq.(34): the explicitly optimized deterministic resource X.
--   - `generalizedFilter`: PDF p.6, Eqs.(32)–(37): sqrt(z)rho(s)^(-1/y), after cancellation. Its branch factors are sqrt(gamma(j)/lambda_j). This agrees with the generalized SRM on nonzero sectors and defines its nonsingular s=0 endpoint without inventing y(0).
--   - `generalizedCore`: PDF p.6, Eq.(32): transformed generalized SRM before the excess term.
--   - `generalizedEffects`: PDF p.6, Eqs.(32),(39): transformed effects, including the uniform positive remainder.
--   - `resourceOperator`: PDF pp.3,6–8: O=sqrt(X), the positive representative of the pure resource.
--   - `physicalEffects`: PDF pp.3,6–8: physical measurement on the range of O, completed on its complement. For sub-POVMs use complete=false so the omitted complement is part of failure.
--   - `deterministicMeasurement`: PDF pp.6–7: the actual optimized deterministic POVM.
--   - `fixedSuccess`: PDF p.8, Eq.(50): the exact fixed-resource success probability, k=2s.
--   - `probabilisticOptimumSuccess`: PDF p.8, Eq.(56): fully optimized faithful qubit success probability.
--   - `fixedTheta`: PDF pp.7–8, Eq.(48): fixed-resource attaining Theta_i.
--   - `optimalTheta`: PDF p.8, Eqs.(52),(53): optimized attaining Theta_i.
--   - `probabilisticX`: PDF p.8, Eq.(54): optimized probabilistic resource X.
--   - `probabilisticMeasurement`: PDF pp.8–9: optimized physical successful effects; failure is I minus their sum.
--   - `quditResource`: PDF pp.5–6: the normalized positive maximally entangled qudit resource.
--   - `quditSignal`: PDF p.5: qudit sigma(i), with the positive maximally entangled reference.
--   - `quditChannel`: PDF pp.5–6: the completed qudit SRM channel, applied to arbitrary operators.
--   - `bobDensity`: PDF p.9: Bob's full reduced density of a pure resource.
--   - `bobPortDensity`: PDF p.9: Bob's one-port marginal, tracing all A and all other ports.
--   - `restorePort`: PDF pp.9–10: insert the selected port into a configuration of the remaining ports.
--   - `postAmplitude`: PDF p.2, Eq.(1), pp.9–10: the single-Kraus square-root postmeasurement vector. All Alice registers, including C, are retained.
--   - `postBranchProbability`: PDF pp.9–10: branch probability, the squared norm of the unnormalized postmeasurement vector.
--   - `residualDensity`: PDF pp.9–10: normalized density of the unused Bob ports on a successful branch. Its entropy is that of the pure residual state in the (all Alice):(unused Bob) cut. Theorems ensure a positive branch probability before using this quotient.
--   - `plusAmp`: PDF p.9: the two-qubit |psi^+> amplitude.
--   - `twoPortResource`: PDF p.9, Eq.(57): the explicit optimized two-port pure resource.
--   - `xAmplitude`: PDF p.9: x^+ and x^-; these are Alice states, not the unknown input.
--   - `twoPortEta`: PDF p.9, Eq.(58): the two orthogonal unit vectors eta^- and eta^+.
--   - `swapTwo`: PDF p.9: A1 <-> A2.
--   - `twoPortMeasurement`: PDF p.9, Eq.(58) and its exchanged branch: the two projective successful effects.
--   - `twoPortResidual`: PDF p.9, Eq.(59): the normalized residual vector for port 1; t labels the unused port.
--   - `twoPortResidualExpanded`: PDF p.9, Eq.(59), second line: the same residual expanded in Bell states.
--   - `twoPortInitialEntropy`: PDF pp.9–10: the exact entropy of Eq.(57), replacing the rounded printed 1.90.
--   - `klmCurve`: PDF p.8: the KLM success curve quoted from [17], only for the numerical comparison.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, https://arxiv.org/abs/0901.2975v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P49

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF pp.1–3: the ordered Alice register and the extra input/reference qubit. -/
abbrev AC (N : ℕ) := Qubits N × Bool

/-- PDF p.2: the normalized singlet amplitude, with |0> = spin down. -/
def singletAmp (a b : Bool) : ℂ :=
  if a = false ∧ b = true then (Real.sqrt 2 : ℂ)⁻¹
  else if a = true ∧ b = false then -(Real.sqrt 2 : ℂ)⁻¹ else 0

/-- PDF p.2: normalized resource (O tensor I)|singlet>^N, allowing rectangular O. -/
def resource {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (a : Qubits NA) (b : Qubits N) : ℂ :=
  ∑ x : Qubits N, O a x * ∏ i, singletAmp (x i) (b i)

/-- PDF p.3, Eq.(5): exactly the normalization required of O, including singular O. -/
def ResourceNormalized {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ) : Prop :=
  (Oᴴ * O).trace = (2 : ℂ) ^ N

/-- PDF p.3, Eq.(3): transformed effects, with C relabelled B. -/
def transformed {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Matrix (AC NA) (AC NA) ℂ) : Matrix (AC N) (AC N) ℂ :=
  (Oᴴ ⊗ₖ (1 : Matrix Bool Bool ℂ)) * M * (O ⊗ₖ (1 : Matrix Bool Bool ℂ))

/-- PDF p.2, Eq.(2): signal sigma(i), including the maximally mixed unused A qubits. -/
def portSignal (N : ℕ) (i : Fin N) : Matrix (AC N) (AC N) ℂ :=
  fun p q => if ∀ k, k ≠ i → p.1 k = q.1 k then
    singletAmp (p.1 i) p.2 * conj (singletAmp (q.1 i) q.2) / (2 : ℂ) ^ (N - 1)
  else 0

/-- PDF p.3, Eq.(6): the sum of the physical signal matrices. -/
def portRho (N : ℕ) : Matrix (AC N) (AC N) ℂ := ∑ i, portSignal N i

/-- PDF p.3, Eq.(3): singlet entanglement fidelity of the recovered qubit. -/
def entFidelity {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Fin N → Matrix (AC NA) (AC NA) ℂ) : ℝ :=
  (∑ i, (transformed O (M i) * portSignal N i).trace.re) / 4

/-- PDF pp.2–3: normalized Haar average, f=(2F+1)/3, for deterministic protocols. -/
def portAverageFidelity {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Fin N → Matrix (AC NA) (AC NA) ℂ) : ℝ := (2 * entFidelity O M + 1) / 3

/-- PDF pp.2–3: input-independent resource and a full N-outcome Alice POVM.
Bob's only operation is selection of the reported port. -/
def IsDeterministicPortProtocol {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Fin N → Matrix (AC NA) (AC NA) ℂ) : Prop :=
  ResourceNormalized O ∧ (∀ i, (M i).PosSemidef) ∧ ∑ i, M i = 1

/-- PDF p.2, Eq.(1): one retained-port branch, written in matrix entries.
Tracing out Alice makes the square-root instrument equal to contraction with its effect.
No operation on the output qudit occurs. -/
def portRetainedOutput {K A : Type*} [Fintype K] [Fintype A] {N : ℕ}
    (R : A → (Fin N → K) → ℂ) (M : Matrix (A × K) (A × K) ℂ)
    (i : Fin N) (T : Matrix K K ℂ) : Matrix K K ℂ :=
  fun u v => ∑ b : Fin N → K, ∑ b' : Fin N → K,
    if b i = u ∧ b' i = v ∧ (∀ k, k ≠ i → b k = b' k) then
      ∑ a : A, ∑ a' : A, ∑ c : K, ∑ c' : K,
        R a b * conj (R a' b') * T c c' * M (a', c') (a, c)
    else 0

/-- PDF p.7: a sub-POVM with the positive omitted effect as failure outcome 0. -/
def SubPOVM {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Fin N → Matrix (AC NA) (AC NA) ℂ) : Prop :=
  ResourceNormalized O ∧ (∀ i, (M i).PosSemidef) ∧ (1 - ∑ i, M i).PosSemidef

/-- PDF p.7: every successful branch returns every normalized unknown pure input exactly.
Zero-probability branches are allowed; failure is unconstrained. -/
def IsFaithfulPortProtocol {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Fin N → Matrix (AC NA) (AC NA) ℂ) : Prop :=
  ∀ (v : EuclideanSpace ℂ Bool), IsState v → ∀ i,
    ∃ q : ℝ, 0 ≤ q ∧ portRetainedOutput (resource O) (M i) i (pureDensity v) =
      (q : ℂ) • pureDensity v

/-- PDF pp.7–8: physical faithful probabilistic protocols with an input-independent resource. -/
def IsProbabilisticPortProtocol {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Fin N → Matrix (AC NA) (AC NA) ℂ) : Prop := SubPOVM O M ∧ IsFaithfulPortProtocol O M

/-- PDF p.7, Eq.(44): success averaged over normalized Haar inputs, not conditional fidelity. -/
def portSuccessProbability {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Fin N → Matrix (AC NA) (AC NA) ℂ) : ℝ :=
  (∑ i, (transformed O (M i)).trace.re) / (2 : ℝ) ^ (N + 1)

/-- PDF pp.3–5: the actual residual wires; no fictitious negative-spin subsystem. -/
abbrev Other (N : ℕ) (i : Fin N) := {k : Fin N // k ≠ i}

/-- PDF p.7, Eq.(45): P^-_{AiC} tensor Theta_i on the remaining A wires. -/
def embedTheta {N : ℕ} (i : Fin N)
    (T : Matrix (Other N i → Bool) (Other N i → Bool) ℂ) : Matrix (AC N) (AC N) ℂ :=
  fun p q => singletAmp (p.1 i) p.2 * conj (singletAmp (q.1 i) q.2) *
    T (fun k => p.1 k.1) (fun k => q.1 k.1)

/-- PDF p.7, Eqs.(5),(46): the complete success SDP feasibility constraints. -/
def PortSuccessFeasible (N : ℕ) (X : Matrix (Qubits N) (Qubits N) ℂ)
    (T : (i : Fin N) → Matrix (Other N i → Bool) (Other N i → Bool) ℂ) : Prop :=
  X.PosSemidef ∧ X.trace = (2 : ℂ) ^ N ∧ (∀ i, (T i).PosSemidef) ∧
    (X ⊗ₖ (1 : Matrix Bool Bool ℂ) - ∑ i, embedTheta i (T i)).PosSemidef

/-- PDF p.7, Eq.(47): the success SDP objective. -/
def successObjective {N : ℕ}
    (T : (i : Fin N) → Matrix (Other N i → Bool) (Other N i → Bool) ℂ) : ℝ :=
  (∑ i, (T i).trace.re) / (2 : ℝ) ^ (N + 1)

/-- PDF pp.3–5: legal doubled spins k=2j. Factorial arguments below are integers. -/
def spins (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter fun k => k % 2 = n % 2

/-- PDF p.3: Casimir J^2 of spin-half wires, from S_i.S_j=(Swap_ij-I/2)/2.
The scalar arithmetic is real, so n=0 never causes natural subtraction underflow. -/
def spinSquare (W : Type*) [Fintype W] : Matrix (W → Bool) (W → Bool) ℂ :=
  (((Fintype.card W : ℝ) * (4 - Fintype.card W) / 4 : ℝ) : ℂ) • 1 +
    (1 / 2 : ℂ) • ∑ i : W, ∑ j : W,
      if i = j then 0 else
        (fun a b => if a = b ∘ Equiv.swap i j then (1 : ℂ) else 0)

/-- PDF pp.3–5: the spin-j projector, defined intrinsically by spectral calculus of J^2.
This is the identity 11(j) on the span of all source |Phi(j,m,alpha)> vectors.
Finite spectra make the indicator continuous on the spectrum. Illegal sectors are zero. -/
def qubitSpinProjector (W : Type*) [Fintype W] (k : ℕ) : Matrix (W → Bool) (W → Bool) ℂ :=
  if k ∈ spins (Fintype.card W) then
    cfc (fun x : ℝ => if x = (k : ℝ) * (k + 2) / 4 then (1 : ℝ) else 0) (spinSquare W)
  else 0

/-- PDF p.4: the total-spin projector on AC, the extra qubit indexed by none. -/
def totalProjector (N k : ℕ) : Matrix (AC N) (AC N) ℂ :=
  fun p q => qubitSpinProjector (Option (Fin N)) k (fun w => w.elim p.2 p.1)
    (fun w => w.elim q.2 q.1)

/-- PDF p.3, Eq.(7): lambda^-_j with j=k/2. Real subtraction is intentional. -/
def lambdaMinus (N k : ℕ) : ℝ := ((N : ℝ) / 2 - (k : ℝ) / 2) / (2 : ℝ) ^ N

/-- PDF p.3, Eq.(7): lambda^+_j with j=k/2. -/
def lambdaPlus (N k : ℕ) : ℝ := ((N : ℝ) / 2 + (k : ℝ) / 2 + 1) / (2 : ℝ) ^ N

/-- PDF pp.3–4, Eqs.(8),(17): the whole eigenspace obtained by coupling j to j+1/2. -/
def minusSector (N k : ℕ) : Matrix (AC N) (AC N) ℂ :=
  (qubitSpinProjector (Fin N) k ⊗ₖ (1 : Matrix Bool Bool ℂ)) * totalProjector N (k + 1)

/-- PDF pp.3–4, Eqs.(8),(17): coupling j to j-1/2; absent when j=0. -/
def plusSector (N k : ℕ) : Matrix (AC N) (AC N) ℂ :=
  if k = 0 then 0 else
    (qubitSpinProjector (Fin N) k ⊗ₖ (1 : Matrix Bool Bool ℂ)) * totalProjector N (k - 1)

/-- PDF p.4: rho(s), on the full space with zero on other total-spin sectors. -/
def rhoBlock (N k : ℕ) : Matrix (AC N) (AC N) ℂ := totalProjector N k * portRho N

/-- PDF p.5, Eq.(24): projector onto singlet_{AiC} tensor the residual spin-s sector. -/
def xiProjector {N : ℕ} (i : Fin N) (k : ℕ) : Matrix (AC N) (AC N) ℂ :=
  embedTheta i (qubitSpinProjector (Other N i) k)

/-- PDF p.5: sigma(i)(s), including the normalization 2^{-(N-1)}. -/
def signalBlock {N : ℕ} (i : Fin N) (k : ℕ) : Matrix (AC N) (AC N) ℂ :=
  ((2 : ℂ) ^ (N - 1))⁻¹ • xiProjector i k

/-- PDF p.5, Eq.(26): scalar compressed moment; k=2s and y is nonzero.
At s=0 the nonexistent j=-1/2 term is omitted. -/
def compressedScalar (N k : ℕ) (y : ℝ) : ℝ :=
  (if k = 0 then 0 else (k : ℝ) / (2 * (k + 1)) *
    Real.rpow (lambdaMinus N (k - 1)) (-1 / y)) +
  ((k : ℝ) + 2) / (2 * (k + 1)) * Real.rpow (lambdaPlus N (k + 1)) (-1 / y)

/-- PDF p.5, Eqs.(27),(28): SRM completed uniformly on its kernel. -/
def completedSRM {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}
    (S : Fin N → Matrix I I ℂ) (i : Fin N) : Matrix I I ℂ :=
  let H := supportPower (∑ j, S j) (-1 / 2)
  H * S i * H + (N : ℂ)⁻¹ • (1 - ∑ j, H * S j * H)

/-- PDF p.5, Eq.(29): exact fixed-resource entanglement fidelity. -/
def fixedFidelity (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (N + 1),
    (((N : ℝ) - 2 * k - 1) / Real.sqrt (k + 1) +
      ((N : ℝ) - 2 * k + 1) / Real.sqrt ((N : ℝ) - k + 1)) ^ 2 *
      (N.choose k : ℝ)) / (2 : ℝ) ^ (N + 3)

/-- PDF p.7, Eq.(41): the optimum singlet entanglement fidelity. -/
def deterministicOptimumFidelity (N : ℕ) : ℝ := Real.cos (Real.pi / (N + 2)) ^ 2

/-- PDF p.7, Eq.(42): the optimum Haar average recovered-qubit fidelity. -/
def deterministicOptimumAverage (N : ℕ) : ℝ := 2 / 3 + Real.cos (2 * Real.pi / (N + 2)) / 3

/-- PDF p.6, Eq.(35): gamma(j) on the legal doubled-spin range. -/
def deterministicGamma (N k : ℕ) : ℝ :=
  (2 : ℝ) ^ (N + 2) / ((N + 2) * (k + 1) * spinMultiplicity N k) *
    Real.sin (Real.pi * (k + 1) / (N + 2)) ^ 2

/-- PDF p.6, Eq.(34): the explicitly optimized deterministic resource X. -/
def deterministicX (N : ℕ) : Matrix (Qubits N) (Qubits N) ℂ :=
  ∑ k ∈ spins N, (deterministicGamma N k : ℂ) • qubitSpinProjector (Fin N) k

/-- PDF p.6, Eqs.(32)–(37): sqrt(z)rho(s)^(-1/y), after cancellation.
Its branch factors are sqrt(gamma(j)/lambda_j). This agrees with the generalized SRM
on nonzero sectors and defines its nonsingular s=0 endpoint without inventing y(0). -/
def generalizedFilter (N k : ℕ) : Matrix (AC N) (AC N) ℂ :=
  (if k = 0 then 0 else
    (Real.sqrt (deterministicGamma N (k - 1) / lambdaMinus N (k - 1)) : ℂ) • minusSector N (k - 1)) +
  (Real.sqrt (deterministicGamma N (k + 1) / lambdaPlus N (k + 1)) : ℂ) • plusSector N (k + 1)

/-- PDF p.6, Eq.(32): transformed generalized SRM before the excess term. -/
def generalizedCore (N : ℕ) (i : Fin N) : Matrix (AC N) (AC N) ℂ :=
  ∑ k ∈ spins (N - 1), generalizedFilter N k * signalBlock i k * generalizedFilter N k

/-- PDF p.6, Eqs.(32),(39): transformed effects, including the uniform positive remainder. -/
def generalizedEffects (N : ℕ) (i : Fin N) : Matrix (AC N) (AC N) ℂ :=
  generalizedCore N i + (N : ℂ)⁻¹ •
    (deterministicX N ⊗ₖ (1 : Matrix Bool Bool ℂ) - ∑ j, generalizedCore N j)

/-- PDF pp.3,6–8: O=sqrt(X), the positive representative of the pure resource. -/
def resourceOperator {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : Matrix I I ℂ := cfc Real.sqrt X

/-- PDF pp.3,6–8: physical measurement on the range of O, completed on its complement.
For sub-POVMs use complete=false so the omitted complement is part of failure. -/
def physicalEffects {N : ℕ} (X : Matrix (Qubits N) (Qubits N) ℂ)
    (E : Fin N → Matrix (AC N) (AC N) ℂ) (complete : Bool) (i : Fin N) :
    Matrix (AC N) (AC N) ℂ :=
  let H := supportPower X (-1 / 2) ⊗ₖ (1 : Matrix Bool Bool ℂ)
  H * E i * H + if complete then
    (N : ℂ)⁻¹ • (1 - (supportPower X 0 ⊗ₖ (1 : Matrix Bool Bool ℂ))) else 0

/-- PDF pp.6–7: the actual optimized deterministic POVM. -/
def deterministicMeasurement (N : ℕ) : Fin N → Matrix (AC N) (AC N) ℂ :=
  physicalEffects (deterministicX N) (generalizedEffects N) true

/-- PDF p.8, Eq.(50): the exact fixed-resource success probability, k=2s. -/
def fixedSuccess (N : ℕ) : ℝ :=
  (∑ k ∈ spins (N - 1), ((k + 1 : ℕ) : ℝ) ^ 2 * (N.factorial : ℝ) /
    ((((N - 1 - k) / 2).factorial : ℝ) * (((N + 3 + k) / 2).factorial : ℝ))) /
      (2 : ℝ) ^ N

/-- PDF p.8, Eq.(56): fully optimized faithful qubit success probability. -/
def probabilisticOptimumSuccess (N : ℕ) : ℝ := (N : ℝ) / (N + 3)

/-- PDF pp.7–8, Eq.(48): fixed-resource attaining Theta_i. -/
def fixedTheta (N : ℕ) (i : Fin N) :
    Matrix (Other N i → Bool) (Other N i → Bool) ℂ :=
  ∑ k ∈ spins (N - 1),
    (((2 : ℝ) ^ (N - 1) * lambdaPlus N (k + 1))⁻¹ : ℂ) • qubitSpinProjector (Other N i) k

/-- PDF p.8, Eqs.(52),(53): optimized attaining Theta_i. -/
def optimalTheta (N : ℕ) (i : Fin N) :
    Matrix (Other N i → Bool) (Other N i → Bool) ℂ :=
  ∑ k ∈ spins (N - 1),
    ((2 ^ (N + 1) * (6 / ((N + 1) * (N + 2) * (N + 3))) * (k + 1) /
      ((N : ℝ) * spinMultiplicity (N - 1) k) : ℝ) : ℂ) • qubitSpinProjector (Other N i) k

/-- PDF p.8, Eq.(54): optimized probabilistic resource X. -/
def probabilisticX (N : ℕ) : Matrix (Qubits N) (Qubits N) ℂ :=
  ∑ k ∈ spins N,
    ((2 ^ N * (6 / ((N + 1) * (N + 2) * (N + 3))) * (k + 1) /
      (spinMultiplicity N k : ℝ) : ℝ) : ℂ) • qubitSpinProjector (Fin N) k

/-- PDF pp.8–9: optimized physical successful effects; failure is I minus their sum. -/
def probabilisticMeasurement (N : ℕ) : Fin N → Matrix (AC N) (AC N) ℂ :=
  physicalEffects (probabilisticX N) (fun i => embedTheta i (optimalTheta N i)) false

/-- Sanity: the two nonzero singlet amplitudes have opposite signs (PDF p.2). -/
example : singletAmp true false = -singletAmp false true := by
  simp [singletAmp]

/-- Sanity: the only legal spin of zero residual wires is zero (PDF pp.3–5). -/
example : spins 0 = {0} := by
  ext k
  simp [spins]
  omega

/-- Sanity: support powers kill the zero operator, including the support projector r=0. -/
example (r : ℝ) : supportPower (0 : Matrix Bool Bool ℂ) r = 0 := by
  simp [supportPower, cfc_zero]

/-- PDF pp.5–6: the normalized positive maximally entangled qudit resource. -/
def quditResource (N d : ℕ) (a b : Fin N → Fin d) : ℂ :=
  if a = b then (Real.sqrt ((d : ℝ) ^ N) : ℂ)⁻¹ else 0

/-- PDF p.5: qudit sigma(i), with the positive maximally entangled reference. -/
def quditSignal (N d : ℕ) (i : Fin N) :
    Matrix ((Fin N → Fin d) × Fin d) ((Fin N → Fin d) × Fin d) ℂ :=
  fun p q => if p.1 i = p.2 ∧ q.1 i = q.2 ∧
    (∀ k, k ≠ i → p.1 k = q.1 k) then ((d : ℂ) ^ N)⁻¹ else 0

/-- PDF pp.5–6: the completed qudit SRM channel, applied to arbitrary operators. -/
def quditChannel (N d : ℕ) : Superop (Fin d) (Fin d) :=
  fun T => ∑ i, portRetainedOutput (quditResource N d) (completedSRM (quditSignal N d) i) i T

/-- PDF p.9: Bob's full reduced density of a pure resource. -/
def bobDensity {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  fun b b' => ∑ a, resource O a b * conj (resource O a b')

/-- PDF p.9: Bob's one-port marginal, tracing all A and all other ports. -/
def bobPortDensity {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (i : Fin N) : Matrix Bool Bool ℂ :=
  fun u v => ∑ b : Qubits N, ∑ b' : Qubits N,
    if b i = u ∧ b' i = v ∧ (∀ k, k ≠ i → b k = b' k) then bobDensity O b b' else 0

/-- PDF pp.9–10: insert the selected port into a configuration of the remaining ports. -/
def restorePort {N : ℕ} (i : Fin N) (r : Other N i → Bool) (t : Bool) : Qubits N :=
  fun k => if h : k = i then t else r ⟨k, h⟩

/-- PDF p.2, Eq.(1), pp.9–10: the single-Kraus square-root postmeasurement vector.
All Alice registers, including C, are retained. -/
def postAmplitude {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Matrix (AC NA) (AC NA) ℂ) (v : EuclideanSpace ℂ Bool)
    (a : Qubits NA) (c : Bool) (b : Qubits N) : ℂ :=
  ∑ a', ∑ c', resourceOperator M (a, c) (a', c') * resource O a' b * v c'

/-- PDF pp.9–10: branch probability, the squared norm of the unnormalized postmeasurement vector. -/
def postBranchProbability {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Matrix (AC NA) (AC NA) ℂ) (v : EuclideanSpace ℂ Bool) : ℝ :=
  ∑ a, ∑ c, ∑ b, Complex.normSq (postAmplitude O M v a c b)

/-- PDF pp.9–10: normalized density of the unused Bob ports on a successful branch.
Its entropy is that of the pure residual state in the (all Alice):(unused Bob) cut.
Theorems ensure a positive branch probability before using this quotient. -/
def residualDensity {N NA : ℕ} (O : Matrix (Qubits NA) (Qubits N) ℂ)
    (M : Matrix (AC NA) (AC NA) ℂ) (v : EuclideanSpace ℂ Bool) (i : Fin N) :
    Matrix (Other N i → Bool) (Other N i → Bool) ℂ :=
  fun r r' => (∑ a, ∑ c, ∑ t : Bool,
    postAmplitude O M v a c (restorePort i r t) *
      conj (postAmplitude O M v a c (restorePort i r' t))) /
    (postBranchProbability O M v : ℂ)

/-- PDF p.9: the two-qubit |psi^+> amplitude. -/
def plusAmp (a b : Bool) : ℂ := if a ≠ b then (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- PDF p.9, Eq.(57): the explicit optimized two-port pure resource. -/
def twoPortResource (a b : Qubits 2) : ℂ :=
  (Real.sqrt (1 / 10) : ℂ) * singletAmp (a 0) (a 1) * singletAmp (b 0) (b 1) +
  (Real.sqrt (3 / 10) : ℂ) *
    ((if a 0 = false ∧ a 1 = false ∧ b 0 = true ∧ b 1 = true then 1 else 0) +
     (if a 0 = true ∧ a 1 = true ∧ b 0 = false ∧ b 1 = false then 1 else 0) -
     plusAmp (a 0) (a 1) * plusAmp (b 0) (b 1))

/-- PDF p.9: x^+ and x^-; these are Alice states, not the unknown input. -/
def xAmplitude (plus : Bool) (a : Qubits 2) : ℂ :=
  ((if plus then 1 else -1) * plusAmp (a 0) (a 1) +
    (Real.sqrt 3 : ℂ) * singletAmp (a 0) (a 1)) / 2

/-- PDF p.9, Eq.(58): the two orthogonal unit vectors eta^- and eta^+. -/
def twoPortEta (plus : Bool) : EuclideanSpace ℂ (AC 2) :=
  WithLp.toLp 2 fun p => if plus then
    (Real.sqrt (2 / 3) : ℂ) * xAmplitude true p.1 * (if p.2 then 1 else 0) -
      (Real.sqrt (1 / 3) : ℂ) *
        (if p.1 0 = true ∧ p.1 1 = true ∧ p.2 = false then 1 else 0)
  else
    (Real.sqrt (2 / 3) : ℂ) * xAmplitude false p.1 * (if p.2 then 0 else 1) +
      (Real.sqrt (1 / 3) : ℂ) *
        (if p.1 0 = false ∧ p.1 1 = false ∧ p.2 = true then 1 else 0)

/-- PDF p.9: A1 <-> A2. -/
def swapTwo (a : Qubits 2) : Qubits 2 := a ∘ Equiv.swap 0 1

/-- PDF p.9, Eq.(58) and its exchanged branch: the two projective successful effects. -/
def twoPortMeasurement (i : Fin 2) : Matrix (AC 2) (AC 2) ℂ :=
  let P := pureDensity (twoPortEta false) + pureDensity (twoPortEta true)
  if i = 0 then P else fun p q => P (swapTwo p.1, p.2) (swapTwo q.1, q.2)

/-- PDF p.9, Eq.(59): the normalized residual vector for port 1; t labels the unused port. -/
def twoPortResidual (a : Qubits 2) (c t : Bool) : ℂ :=
  ((twoPortEta false (a, c)) * (if t then 1 else 0) -
    (twoPortEta true (a, c)) * (if t then 0 else 1)) / (Real.sqrt 2 : ℂ)

/-- PDF p.9, Eq.(59), second line: the same residual expanded in Bell states. -/
def twoPortResidualExpanded (a : Qubits 2) (c t : Bool) : ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ * singletAmp (a 0) (a 1) * singletAmp c t +
  (Real.sqrt 6 : ℂ)⁻¹ *
    ((if a 0 = false ∧ a 1 = false ∧ c = true ∧ t = true then 1 else 0) +
     (if a 0 = true ∧ a 1 = true ∧ c = false ∧ t = false then 1 else 0) -
     plusAmp (a 0) (a 1) * plusAmp c t)

/-- PDF pp.9–10: the exact entropy of Eq.(57), replacing the rounded printed 1.90. -/
def twoPortInitialEntropy : ℝ :=
  -(1 / 10 : ℝ) * Real.logb 2 (1 / 10) - (9 / 10 : ℝ) * Real.logb 2 (3 / 10)

/-- PDF p.8: the KLM success curve quoted from [17], only for the numerical comparison. -/
def klmCurve (m : ℕ) : ℝ := 1 - 1 / ((m : ℝ) + 1)

/-- Sanity: N=1 is postselected singlet teleportation with success 1/4 (PDF p.8). -/
example : probabilisticOptimumSuccess 1 = 1 / 4 := by norm_num [probabilisticOptimumSuccess]

/-- Sanity: restoring a port puts the specified bit in that port. -/
example {N : ℕ} (i : Fin N) (r : Other N i → Bool) (t : Bool) :
    restorePort i r t i = t := by simp [restorePort]

end QAlgorithms.Papers.Independent.Intake100.P67


