-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P41
-- name    : QAlgorithms_Papers_Independent_Renew46_P41
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:18:44.552138+00:00
-- url     : https://prove2.me/theorems/01a3a69f-b648-408a-9318-85c51782a40d
-- title:
--   Definitions for Optimal cloning of coherent states with a linear amplifier and beam splitters
-- statement:
--   The objects the formalized statements of *Optimal cloning of coherent states with a linear amplifier and beam splitters* (arXiv:quant-ph/0012046) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ModeUnitary`: PDF pp.1--2: a genuine unitary on the full multimode Fock space.
--   - `coherentProductCoefficient`: PDF p.1: coefficients of the independent coherent inputs and vacuum auxiliaries. Vacuum is coherent amplitude zero.
--   - `coherentProduct`: PDF p.1: the actual coherent product vector. Every use below concludes convergence, the specified coefficients, and normalization, so no default tsum is used.
--   - `NormalizedCoherent`: PDF p.1: explicit convergence and unit norm of a coherent product.
--   - `PhysicalGaussian`: PDF pp.1--2, hbar=1: Gaussianity of an actual density. The factor 2 converts the accepted hbar=2 covariance to the physical covariance V here.
--   - `coherentMean`: PDF p.2, Eq.(3): the coherent state's physical first moments.
--   - `cloneNoise`: PDF p.1, Eq.(1): optimal isotropic added noise in physical quadrature units.
--   - `cloneFidelity`: PDF pp.1,4: single-clone squared-overlap fidelity, not joint fidelity.
--   - `displacedThermal`: PDF pp.1--3: D(alpha) rho D(alpha)^dagger, with the displacement fixed by its actual Fock Weyl coefficients. The accepted Weyl parameter is -q_p+i q_x.
--   - `insertOccupation`: PDF pp.1--2: insert the kept occupation r among the other modes.
--   - `IsReducedDensity`: PDF pp.1--2: actual partial trace on the full number basis. HasSum guards every environment sum. The kept mode is identified with the one-mode Fock space.
--   - `pureDensity`: PDF pp.1--2: the joint output density of a pure normalized input.
--   - `FockCanonicalAction`: PDF pp.1--3, Eq.(2): bounded Weyl form of the Heisenberg operator identity. It fixes U^dagger W(q) U = W(S^T q) for ALL q, not just coherent inputs. Uniform rescaling of all quadratures leaves S unchanged. The accepted Frontier30.P07.Implements has a one-mode WeylRepresentation and a phase-space linear equivalence, so cannot express this n-mode Fock-coordinate action.
--   - `modeMixingQuadratures`: PDF p.3, Eq.(10): reuse the accepted grouped realification with X=Re(A), Y=-Im(A), then reorder its grouped (all x, all p) coordinates into the interleaved coordinates of the accepted Fock Weyl system.
--   - `embedModes`: PDF p.3: pad an operation on the first k modes by the identity.
--   - `twoModeAmplifierQuadratures`: PDF pp.2--3, Eqs.(8),(11): gain-G two-mode amplifier, including its idler. The minus signs in p encode the creation operators. Other modes are untouched. Dependency50.P39.amplifierMatrix instead denotes one-mode Kraus coefficients; it is not this two-mode quadrature transformation.
--   - `embeddedOpticalBeam`: PDF p.3, Eq.(13): embed the accepted two-port scattering matrix with (tPrime,r,rPrime,t)=(sin(theta),cos(theta),cos(theta),-sin(theta)) on the named oscillator modes; all other modes are untouched.
--   - `OpticalGate`: PDF pp.2--3: optical gates on named oscillator modes, not qubit gates.
--   - `OpticalGate.matrix`: PDF pp.2--3: exact quadrature action of an optical gate.
--   - `circuitMatrix`: PDF p.3, Eqs.(14)--(16): list order is temporal order; the first gate is rightmost in the Heisenberg matrix product.
--   - `circuitUnitary`: PDF p.3: composition of actual oscillator unitaries in temporal order.
--   - `OpticalCircuitRealized`: PDF pp.2--3: every listed optical gate has an actual full-Fock implementer, and the specified U is their composition. A bare gate count is insufficient. Dependency50.P05.Realizes concerns finite Choi supermaps, not oscillator gates.
--   - `splitterGates`: PDF p.3, Eq.(14): adjacent splitters in temporal order. The inverse network is the reversed list, since every real beam block in Eq.(13) is an involution.
--   - `splitterModes`: PDF p.3, Eq.(14): complex mode-mixing matrix of the L-splitter.
--   - `firstModes`: PDF p.3: first k of the M signal/blank modes, leaving the final idler alone.
--   - `cloningAmplitudes`: PDF pp.1,3: N equal coherent originals, M-N independent vacuum blanks, and the independent vacuum idler at index M.
--   - `serialGates`: PDF p.3, Eqs.(15)--(16): inverse N-splitter, gain M/N amplifier, then M-splitter, on the physical oscillator register.
--   - `ClonesCoherently`: PDF pp.1--4: equal actual single-mode densities for all clone slots, correct means, isotropic noise, and the single-clone fidelity. The joint output may be correlated. The displacement is quantified AFTER the implementation.
--   - `duplicatorMatrix`: PDF p.2, Eq.(7): explicit three-mode canonical duplicator (0,1,z). The printed p_o is read as p_0, forced by Eq.(8) and the input convention.
--   - `dftConcentration`: PDF p.3: concentrate with the positive-sign DFT on N physical modes.
--   - `dftDistribution`: PDF p.3: distribute with the positive-sign DFT on M physical modes.
--   - `dftClonerMatrix`: PDF p.3, Eqs.(10)--(12): the complete DFT/amplifier/DFT quadrature matrix.
--   - `addedAmplifierNoise`: PDF pp.2--3, Eq.(9): ADDED amplifier noise from an idler with physical isotropic variance v. This is not the unscaled idler variance itself.
--   - `cloneVariance`: PDF p.3, Eqs.(10)--(12): amplified concentrated input noise, added amplifier noise, and M-1 passive vacuum contributions, divided by M.
--   - `inputMean`: PDF pp.1--3: first moments of the independent originals and zero-mean auxiliaries.
--   - `inputCovariance`: PDF pp.2--3: product coherent/vacuum inputs and an independent isotropic Gaussian idler of physical quadrature variance v. Diagonality encodes independence.
--   - `bankSlot`: PDF pp.3--4, Eqs.(17)--(20): N banks, each with M signal/blank slots followed by its own idler. The standard finite-product equivalence fixes all indices.
--   - `parallelAmplitudes`: PDF pp.3--4: each bank starts in |alpha> on slot zero, with all its blanks and its idler independently in vacuum.
--   - `parallelCloneSlot`: PDF p.4, Eq.(20): the first output of each recombining inverse N-splitter is a clone. The remaining N-1 outputs are waste modes.
--   - `parallelWasteSlot`: PDF p.4: explicit M(N-1) waste output slots, distinct from all idlers.
--   - `parallelGates`: PDF pp.3--4, Eqs.(17)--(20): amplify each original independently, split each amplified mode into M, then recombine each column by an inverse N-splitter.
--   - `splitterNoiseCoefficient`: PDF p.4, Eq.(19): d_(k,l) is the linear combination of the SAME M-1 vacuum modes in bank k. Distinct l are not modeled as independent oscillators.
--   - `parallelCloneRow`: PDF p.4, Eq.(21): expanded clone row. All three terms are inside the bank sum; the idler coefficient denominator is M*N^2. The sign flips on p.
--   - `squeezeBlock`: PDF p.4: a fixed known squeezing amount and axis. The real symplectic matrix is R(theta) diag(exp(-r),exp(r)) R(theta)^T.
--   - `jointSqueeze`: PDF p.4: corresponding controlled squeezing on the joint register. Signal and blank modes use Q; the idler uses Z Q Z, where Z=diag(1,-1), because the amplifier couples to a_z^dagger. On the squeeze axes (theta=0) this is the same squeeze on all modes.
--   - `singleSqueeze`: PDF p.4: one-mode squeezing, acting on a genuine oscillator unitary.
-- source:
--   Optimal cloning of coherent states with a linear amplifier and beam splitters, arXiv:quant-ph/0012046v1, https://arxiv.org/abs/quant-ph/0012046v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P34

/-!
Braunstein et al., arXiv:quant-ph/0012046v1, PDF pp.1--4.
Full oscillator spaces and actual reduced density operators; no photon cutoff.
The accepted Weyl coordinates have hbar=2. PhysicalGaussian explicitly rescales
means by sqrt(2) and covariances by 2, so ALL moments here have hbar=1.
The finite Fourier matrix is used only for scalar mode-mixing coefficients.
Grouped realification and two-port scattering entries are imported from the
accepted library; paper-local adapters only convert coordinates and mode slots.
Optimality means attainment of Eq.(1), within the Gaussian setting of the source.
The seven statements have omitted proofs. Compilation is pending batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P41

open scoped BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator Quadrature PhaseVector numberKet IsModeDensity
   FockWeylSystem GaussianMoments unitaryConjugation thermalTensorDensity Symplectic)
open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1--2: a genuine unitary on the full multimode Fock space. -/
abbrev ModeUnitary (n : ℕ) := ModeHilbert n ≃ₗᵢ[ℂ] ModeHilbert n

/-- PDF p.1: coefficients of the independent coherent inputs and vacuum auxiliaries.
Vacuum is coherent amplitude zero. -/
def coherentProductCoefficient {n : ℕ} (a : Fin n → ℂ) (j : Fin n → ℕ) : ℂ :=
  ∏ k, coherentCoefficient (a k) (j k)

/-- PDF p.1: the actual coherent product vector. Every use below concludes
convergence, the specified coefficients, and normalization, so no default tsum is used. -/
def coherentProduct {n : ℕ} (a : Fin n → ℂ) : ModeHilbert n :=
  ∑' j, coherentProductCoefficient a j • numberKet j

/-- PDF p.1: explicit convergence and unit norm of a coherent product. -/
def NormalizedCoherent {n : ℕ} (a : Fin n → ℂ) : Prop :=
  Summable (fun j => coherentProductCoefficient a j • numberKet j) ∧
    (∀ j, coherentProduct a j = coherentProductCoefficient a j) ∧
    ‖coherentProduct a‖ = 1

/-- PDF pp.1--2, hbar=1: Gaussianity of an actual density. The factor 2
converts the accepted hbar=2 covariance to the physical covariance V here. -/
def PhysicalGaussian {n : ℕ} (W : FockWeylSystem n) (rho : ModeOperator n)
    (m : PhaseVector n) (V : Matrix (Quadrature n) (Quadrature n) ℝ) : Prop :=
  GaussianMoments W rho (fun i => Real.sqrt 2 * m i) (2 • V)

/-- PDF p.2, Eq.(3): the coherent state's physical first moments. -/
def coherentMean (a : ℂ) : PhaseVector 1 :=
  fun i => Real.sqrt 2 * (if i.2 = 0 then a.re else a.im)

/-- PDF p.1, Eq.(1): optimal isotropic added noise in physical quadrature units. -/
def cloneNoise (N M : ℕ) : ℝ := 1 / (N : ℝ) - 1 / (M : ℝ)

/-- PDF pp.1,4: single-clone squared-overlap fidelity, not joint fidelity. -/
def cloneFidelity (N M : ℕ) : ℝ :=
  ((M : ℝ) * N) / ((M : ℝ) * N + M - N)

/-- PDF pp.1--3: D(alpha) rho D(alpha)^dagger, with the displacement fixed by
its actual Fock Weyl coefficients. The accepted Weyl parameter is -q_p+i q_x. -/
def displacedThermal (W : FockWeylSystem 1) (a : ℂ) (t : ℝ) : ModeOperator 1 :=
  let D := W.operator (fun i => if i.2 = 0 then a.im else -a.re)
  D.comp ((thermalTensorDensity (fun _ : Fin 1 => 2 * t + 1)).comp D.adjoint)

/-- PDF pp.1--2: insert the kept occupation r among the other modes. -/
def insertOccupation {n : ℕ} (k : Fin n) (r : ℕ)
    (e : {j : Fin n // j ≠ k} → ℕ) : Fin n → ℕ :=
  fun j => if h : j = k then r else e ⟨j, h⟩

/-- PDF pp.1--2: actual partial trace on the full number basis. HasSum guards
every environment sum. The kept mode is identified with the one-mode Fock space. -/
def IsReducedDensity {n : ℕ} (X : ModeOperator n) (k : Fin n)
    (rho : ModeOperator 1) : Prop :=
  IsModeDensity rho ∧ ∀ a b : Fin 1 → ℕ,
    HasSum (fun e : {j : Fin n // j ≠ k} → ℕ =>
      X (numberKet (insertOccupation k (b 0) e)) (insertOccupation k (a 0) e))
      (rho (numberKet b) a)

/-- PDF pp.1--2: the joint output density of a pure normalized input. -/
def pureDensity {n : ℕ} (psi : ModeHilbert n) : ModeOperator n :=
  InnerProductSpace.rankOne ℂ psi psi

/-- PDF pp.1--3, Eq.(2): bounded Weyl form of the Heisenberg operator identity.
It fixes U^dagger W(q) U = W(S^T q) for ALL q, not just coherent inputs.
Uniform rescaling of all quadratures leaves S unchanged. The accepted
Frontier30.P07.Implements has a one-mode WeylRepresentation and a phase-space
linear equivalence, so cannot express this n-mode Fock-coordinate action. -/
def FockCanonicalAction {n : ℕ} (W : FockWeylSystem n) (U : ModeUnitary n)
    (S : Matrix (Quadrature n) (Quadrature n) ℝ) : Prop :=
  ∀ q, unitaryConjugation U.symm (W.operator q) = W.operator (S.transpose.mulVec q)

/-- PDF p.3, Eq.(10): reuse the accepted grouped realification with
X=Re(A), Y=-Im(A), then reorder its grouped (all x, all p) coordinates
into the interleaved coordinates of the accepted Fock Weyl system. -/
def modeMixingQuadratures {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Quadrature n) (Quadrature n) ℝ :=
  fun i j => QAlgorithms.Papers.Independent.Claimed50.P41.passiveMatrix
    (fun k l => (A k l).re) (fun k l => -(A k l).im)
    (if i.2 = 0 then Sum.inl i.1 else Sum.inr i.1)
    (if j.2 = 0 then Sum.inl j.1 else Sum.inr j.1)

/-- PDF p.3: pad an operation on the first k modes by the identity. -/
def embedModes {k n : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if hi : i.val < k then
    if hj : j.val < k then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
    else if i = j then 1 else 0

/-- PDF pp.2--3, Eqs.(8),(11): gain-G two-mode amplifier, including its idler.
The minus signs in p encode the creation operators. Other modes are untouched.
Dependency50.P39.amplifierMatrix instead denotes one-mode Kraus coefficients;
it is not this two-mode quadrature transformation. -/
def twoModeAmplifierQuadratures {n : ℕ} (signal idler : Fin n) (G : ℝ) :
    Matrix (Quadrature n) (Quadrature n) ℝ :=
  fun i j => if i.2 ≠ j.2 then 0 else
    if (i.1 = signal ∧ j.1 = signal) ∨ (i.1 = idler ∧ j.1 = idler) then Real.sqrt G
    else if (i.1 = signal ∧ j.1 = idler) ∨ (i.1 = idler ∧ j.1 = signal) then
      (if i.2 = 0 then 1 else -1) * Real.sqrt (G - 1)
    else if i.1 = j.1 then 1 else 0

/-- PDF p.3, Eq.(13): embed the accepted two-port scattering matrix with
(tPrime,r,rPrime,t)=(sin(theta),cos(theta),cos(theta),-sin(theta))
on the named oscillator modes; all other modes are untouched. -/
def embeddedOpticalBeam {n : ℕ} (k l : Fin n) (theta : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if (i = k ∨ i = l) ∧ (j = k ∨ j = l) then
    QAlgorithms.Papers.Independent.Dependency50.P34.beamMatrix
      (Real.sin theta : ℂ) (Real.cos theta : ℂ)
      (Real.cos theta : ℂ) (-Real.sin theta : ℂ)
      (if i = k then 0 else 1) (if j = k then 0 else 1)
    else if i = j then 1 else 0

/-- PDF pp.2--3: optical gates on named oscillator modes, not qubit gates. -/
inductive OpticalGate (n : ℕ) where
  | beam (k l : Fin n) (theta : ℝ)
  | amplifier (signal idler : Fin n) (gain : ℝ)

/-- PDF pp.2--3: exact quadrature action of an optical gate. -/
def OpticalGate.matrix {n : ℕ} : OpticalGate n → Matrix (Quadrature n) (Quadrature n) ℝ
  | .beam k l theta => modeMixingQuadratures (embeddedOpticalBeam k l theta)
  | .amplifier k l G => twoModeAmplifierQuadratures k l G

/-- PDF p.3, Eqs.(14)--(16): list order is temporal order; the first gate is
rightmost in the Heisenberg matrix product. -/
def circuitMatrix {n : ℕ} (gs : List (OpticalGate n)) :
    Matrix (Quadrature n) (Quadrature n) ℝ :=
  gs.foldl (fun S g => g.matrix * S) 1

/-- PDF p.3: composition of actual oscillator unitaries in temporal order. -/
def circuitUnitary {n : ℕ} {len : ℕ} (us : Fin len → ModeUnitary n) : ModeUnitary n :=
  (List.ofFn us).foldl (fun U V => U.trans V) (LinearIsometryEquiv.refl ℂ _)

/-- PDF pp.2--3: every listed optical gate has an actual full-Fock implementer,
and the specified U is their composition. A bare gate count is insufficient.
Dependency50.P05.Realizes concerns finite Choi supermaps, not oscillator gates. -/
def OpticalCircuitRealized {n : ℕ} (W : FockWeylSystem n) (gs : List (OpticalGate n))
    (U : ModeUnitary n) : Prop :=
  ∃ us : Fin gs.length → ModeUnitary n,
    (∀ i, FockCanonicalAction W (us i) (gs.get i).matrix) ∧ U = circuitUnitary us

/-- PDF p.3, Eq.(14): adjacent splitters in temporal order. The inverse network
is the reversed list, since every real beam block in Eq.(13) is an involution. -/
def splitterGates {n : ℕ} (L : ℕ) (place : Fin L → Fin n) : List (OpticalGate n) :=
  List.ofFn (fun t : Fin (L - 1) => OpticalGate.beam
    (place ⟨t.val, by omega⟩) (place ⟨t.val + 1, by omega⟩)
    (Real.arcsin (1 / Real.sqrt ((L - t.val : ℕ) : ℝ))))

/-- PDF p.3, Eq.(14): complex mode-mixing matrix of the L-splitter. -/
def splitterModes (L : ℕ) : Matrix (Fin L) (Fin L) ℂ :=
  (List.ofFn (fun t : Fin (L - 1) => embeddedOpticalBeam
    (⟨t.val, by omega⟩ : Fin L) ⟨t.val + 1, by omega⟩
    (Real.arcsin (1 / Real.sqrt ((L - t.val : ℕ) : ℝ))))).foldl
      (fun A B => B * A) 1

/-- PDF p.3: first k of the M signal/blank modes, leaving the final idler alone. -/
def firstModes (M k : ℕ) (hk : k ≤ M) : Fin k → Fin (M + 1) :=
  fun i => ⟨i.val, by omega⟩

/-- PDF pp.1,3: N equal coherent originals, M-N independent vacuum blanks,
and the independent vacuum idler at index M. -/
def cloningAmplitudes (N M : ℕ) (a : ℂ) : Fin (M + 1) → ℂ :=
  fun k => if k.val < N then a else 0

/-- PDF p.3, Eqs.(15)--(16): inverse N-splitter, gain M/N amplifier,
then M-splitter, on the physical oscillator register. -/
def serialGates (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) : List (OpticalGate (M + 1)) :=
  (splitterGates N (firstModes M N hNM)).reverse ++
    [OpticalGate.amplifier ⟨0, by omega⟩ ⟨M, by omega⟩ ((M : ℝ) / N)] ++
    splitterGates M (firstModes M M (by omega))

/-- PDF pp.1--4: equal actual single-mode densities for all clone slots,
correct means, isotropic noise, and the single-clone fidelity. The joint output
may be correlated. The displacement is quantified AFTER the implementation. -/
def ClonesCoherently {n : ℕ} (Wone : FockWeylSystem 1) (N M : ℕ)
    (input : ℂ → Fin n → ℂ) (slots : Fin M → Fin n) (U : ModeUnitary n) : Prop :=
  ∀ a : ℂ, NormalizedCoherent (input a) ∧ NormalizedCoherent (fun _ : Fin 1 => a) ∧
    let rho := displacedThermal Wone a (cloneNoise N M)
    IsModeDensity (pureDensity (U (coherentProduct (input a)))) ∧
    (∀ l, IsReducedDensity (pureDensity (U (coherentProduct (input a)))) (slots l) rho) ∧
    PhysicalGaussian Wone rho (coherentMean a) ((1 / 2 + cloneNoise N M) • 1) ∧
    (inner ℂ (coherentProduct (fun _ : Fin 1 => a))
      (rho (coherentProduct (fun _ : Fin 1 => a)))).re = cloneFidelity N M

/-- PDF p.2, Eq.(7): explicit three-mode canonical duplicator (0,1,z).
The printed p_o is read as p_0, forced by Eq.(8) and the input convention. -/
def duplicatorMatrix : Matrix (Quadrature 3) (Quadrature 3) ℝ :=
  fun i j => if i.2 ≠ j.2 then 0 else if i.2 = 0 then
    (!![1, 1 / Real.sqrt 2, 1 / Real.sqrt 2;
        1, -1 / Real.sqrt 2, 1 / Real.sqrt 2;
        1, 0, Real.sqrt 2] : Matrix (Fin 3) (Fin 3) ℝ) i.1 j.1
    else (!![1, 1 / Real.sqrt 2, -1 / Real.sqrt 2;
             1, -1 / Real.sqrt 2, -1 / Real.sqrt 2;
             -1, 0, Real.sqrt 2] : Matrix (Fin 3) (Fin 3) ℝ) i.1 j.1

/-- PDF p.3: concentrate with the positive-sign DFT on N physical modes. -/
def dftConcentration (N M : ℕ) : Matrix (Quadrature (M + 1)) (Quadrature (M + 1)) ℝ :=
  modeMixingQuadratures (embedModes (n := M + 1) (QAlgorithms.qftMatrix N))

/-- PDF p.3: distribute with the positive-sign DFT on M physical modes. -/
def dftDistribution (M : ℕ) : Matrix (Quadrature (M + 1)) (Quadrature (M + 1)) ℝ :=
  modeMixingQuadratures (embedModes (n := M + 1) (QAlgorithms.qftMatrix M))

/-- PDF p.3, Eqs.(10)--(12): the complete DFT/amplifier/DFT quadrature matrix. -/
def dftClonerMatrix (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    Matrix (Quadrature (M + 1)) (Quadrature (M + 1)) ℝ :=
  dftDistribution M * twoModeAmplifierQuadratures (⟨0, by omega⟩ : Fin (M + 1))
    ⟨M, by omega⟩ ((M : ℝ) / N) * dftConcentration N M

example : coherentProductCoefficient (fun _ : Fin 1 => (0 : ℂ)) (fun _ => 0) = 1 := by
  simp [coherentProductCoefficient, coherentCoefficient]

example : cloneNoise 1 2 = 1 / 2 := by norm_num [cloneNoise]

example : cloneFidelity 1 2 = 2 / 3 := by norm_num [cloneFidelity]

example (N : ℕ) : cloneNoise N N = 0 := by simp [cloneNoise]

example {n : ℕ} (k : Fin n) (r : ℕ) (e : {j : Fin n // j ≠ k} → ℕ) :
    insertOccupation k r e k = r := by simp [insertOccupation]

example {n : ℕ} : circuitMatrix ([] : List (OpticalGate n)) = 1 := rfl

example {n : ℕ} (place : Fin 1 → Fin n) : splitterGates 1 place = [] := by
  simp [splitterGates]

example : duplicatorMatrix ((2 : Fin 3), (1 : Fin 2)) ((0 : Fin 3), (1 : Fin 2)) = -1 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [duplicatorMatrix, ne_eq, eq_self, not_true_eq_false, h10, ite_false] <;> rfl

example : embeddedOpticalBeam (0 : Fin 2) 1 0 0 1 = 1 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [embeddedOpticalBeam, eq_self, h01, h10, true_or, or_true,
    and_self, ite_true, ite_false,
    QAlgorithms.Papers.Independent.Dependency50.P34.beamMatrix,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.sin_zero, Real.cos_zero, Complex.ofReal_zero, Complex.ofReal_one]

example : modeMixingQuadratures (1 : Matrix (Fin 1) (Fin 1) ℂ)
    ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (0 : Fin 2)) = 1 := by
  simp only [modeMixingQuadratures,
    QAlgorithms.Papers.Independent.Claimed50.P41.passiveMatrix,
    eq_self, ite_true]
  change ((1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0).re = 1
  simp only [Matrix.one_apply_eq, Complex.one_re]

/-- PDF pp.2--3, Eq.(9): ADDED amplifier noise from an idler with physical
isotropic variance v. This is not the unscaled idler variance itself. -/
def addedAmplifierNoise (N M : ℕ) (v : ℝ) : ℝ := ((M : ℝ) / N - 1) * v

/-- PDF p.3, Eqs.(10)--(12): amplified concentrated input noise, added amplifier
noise, and M-1 passive vacuum contributions, divided by M. -/
def cloneVariance (N M : ℕ) (s : ℝ) : ℝ :=
  (((M : ℝ) / N) / 2 + s + ((M : ℝ) - 1) / 2) / M

/-- PDF pp.1--3: first moments of the independent originals and zero-mean auxiliaries. -/
def inputMean (N M : ℕ) (a : ℂ) : PhaseVector (M + 1) :=
  fun i => if i.1.val < N then
    Real.sqrt 2 * (if i.2 = 0 then a.re else a.im) else 0

/-- PDF pp.2--3: product coherent/vacuum inputs and an independent isotropic
Gaussian idler of physical quadrature variance v. Diagonality encodes independence. -/
def inputCovariance (M : ℕ) (v : ℝ) :
    Matrix (Quadrature (M + 1)) (Quadrature (M + 1)) ℝ :=
  Matrix.diagonal (fun i => if i.1.val = M then v else 1 / 2)

/-- PDF pp.3--4, Eqs.(17)--(20): N banks, each with M signal/blank slots
followed by its own idler. The standard finite-product equivalence fixes all indices. -/
def bankSlot {N M : ℕ} (k : Fin N) (l : Fin (M + 1)) : Fin (N * (M + 1)) :=
  finProdFinEquiv (k, l)

/-- PDF pp.3--4: each bank starts in |alpha> on slot zero, with all its
blanks and its idler independently in vacuum. -/
def parallelAmplitudes (N M : ℕ) (a : ℂ) : Fin (N * (M + 1)) → ℂ :=
  fun j => if (finProdFinEquiv.symm j).2.val = 0 then a else 0

/-- PDF p.4, Eq.(20): the first output of each recombining inverse N-splitter
is a clone. The remaining N-1 outputs are waste modes. -/
def parallelCloneSlot (N M : ℕ) (hN : 0 < N) (l : Fin M) : Fin (N * (M + 1)) :=
  bankSlot ⟨0, hN⟩ l.castSucc

/-- PDF p.4: explicit M(N-1) waste output slots, distinct from all idlers. -/
def parallelWasteSlot (N M : ℕ) (k : Fin (N - 1)) (l : Fin M) : Fin (N * (M + 1)) :=
  bankSlot (⟨k.val + 1, by omega⟩ : Fin N) l.castSucc

/-- PDF pp.3--4, Eqs.(17)--(20): amplify each original independently, split
each amplified mode into M, then recombine each column by an inverse N-splitter. -/
def parallelGates (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    List (OpticalGate (N * (M + 1))) :=
  (List.finRange N).flatMap (fun k =>
    [OpticalGate.amplifier (bankSlot k (⟨0, by omega⟩ : Fin (M + 1)))
      (bankSlot k ⟨M, by omega⟩) ((M : ℝ) / N)] ++
      splitterGates M (fun l => bankSlot k l.castSucc)) ++
  (List.finRange M).flatMap (fun l =>
    (splitterGates N (fun k => bankSlot k l.castSucc)).reverse)

/-- PDF p.4, Eq.(19): d_(k,l) is the linear combination of the SAME M-1
vacuum modes in bank k. Distinct l are not modeled as independent oscillators. -/
def splitterNoiseCoefficient (M : ℕ) (l : Fin M) (j : Fin (M + 1)) : ℝ :=
  if h : 0 < j.val ∧ j.val < M then (splitterModes M l ⟨j.val, h.2⟩).re else 0

/-- PDF p.4, Eq.(21): expanded clone row. All three terms are inside the bank
sum; the idler coefficient denominator is M*N^2. The sign flips on p. -/
def parallelCloneRow (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (l : Fin M) (p : Fin 2) (j : Quadrature (N * (M + 1))) : ℝ :=
  if p ≠ j.2 then 0 else ∑ k : Fin N, (
    (if j.1 = bankSlot k (⟨0, by omega⟩ : Fin (M + 1)) then 1 / (N : ℝ) else 0) +
    (if j.1 = bankSlot k (⟨M, by omega⟩ : Fin (M + 1)) then
      (if p = 0 then 1 else -1) *
        Real.sqrt (((M : ℝ) - N) / ((M : ℝ) * (N : ℝ) ^ 2)) else 0) +
    (if (finProdFinEquiv.symm j.1).1 = k then
      splitterNoiseCoefficient M l (finProdFinEquiv.symm j.1).2 / Real.sqrt N else 0))

example (k : Fin 1) (l : Fin 1) : splitterNoiseCoefficient 1 k l.castSucc = 0 := by
  have hl : l = 0 := Subsingleton.elim _ _
  subst l
  simp [splitterNoiseCoefficient]

example {N M : ℕ} (k : Fin N) (l : Fin (M + 1)) :
    finProdFinEquiv.symm (bankSlot k l) = (k, l) := by simp [bankSlot]

/-- PDF p.4: a fixed known squeezing amount and axis. The real symplectic
matrix is R(theta) diag(exp(-r),exp(r)) R(theta)^T. -/
def squeezeBlock (r theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let R : Matrix (Fin 2) (Fin 2) ℝ :=
    !![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta]
  R * Matrix.diagonal ![Real.exp (-r), Real.exp r] * R.transpose

/-- PDF p.4: corresponding controlled squeezing on the joint register.
Signal and blank modes use Q; the idler uses Z Q Z, where Z=diag(1,-1),
because the amplifier couples to a_z^dagger. On the squeeze axes (theta=0)
this is the same squeeze on all modes. -/
def jointSqueeze (M : ℕ) (r theta : ℝ) :
    Matrix (Quadrature (M + 1)) (Quadrature (M + 1)) ℝ :=
  fun i j => if i.1 ≠ j.1 then 0 else
    (if i.1.val = M then
      (if i.2 = 0 then 1 else -1) * (if j.2 = 0 then 1 else -1) else 1) *
      squeezeBlock r theta i.2 j.2

/-- PDF p.4: one-mode squeezing, acting on a genuine oscillator unitary. -/
def singleSqueeze (r theta : ℝ) : Matrix (Quadrature 1) (Quadrature 1) ℝ :=
  fun i j => squeezeBlock r theta i.2 j.2

example (M : ℕ) (r theta : ℝ) (i j : Quadrature (M + 1)) (h : i.1 ≠ j.1) :
    jointSqueeze M r theta i j = 0 := by simp [jointSqueeze, h]

example : squeezeBlock 0 0 (0 : Fin 2) (0 : Fin 2) = 1 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [squeezeBlock, Real.cos_zero, Real.sin_zero, neg_zero, Real.exp_zero,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.diagonal_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    eq_self, h01, h10, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one,
    zero_add, add_zero]

end QAlgorithms.Papers.Independent.Renew46.P41


