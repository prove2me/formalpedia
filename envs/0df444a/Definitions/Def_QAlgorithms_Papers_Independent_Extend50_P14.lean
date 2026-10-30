-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14
-- name    : QAlgorithms_Papers_Independent_Extend50_P14
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T22:53:10.013864+00:00
-- url     : https://prove2.me/theorems/6959b71b-61f8-45ad-8ba5-6dbb583fb974
-- title:
--   Definitions for Restrictions on realizable unitary operations imposed by symmetry and locality
-- statement:
--   The objects the formalized statements of *Restrictions on realizable unitary operations imposed by symmetry and locality* (arXiv:2003.05524) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SiteBasis`
--   - `TensorSupported`: PDF pp.1,13: support means an operator on the selected tensor factors, with the identity on every complementary factor.
--   - `SiteLocal`: PDF p.1: a single k-local operator, as opposed to a sum of local terms.
--   - `OnSite`: PDF p.13, A1–A2: on-site unitary representations, allowing heterogeneous sites.
--   - `OnSite.total`: PDF p.13, A2: the specified tensor product representation.
--   - `CommutesWithAction`: PDF pp.1,13: the commutant of a representation.
--   - `localGates`: PDF p.13, A4: the actual generator set.
--   - `symmetricLocalGroup`: PDF p.13, A4: algebraic submonoid closure consists of finite gate products. The generators contain their inverses, so it is the generated group.
--   - `symmetricLocalLie`: PDF p.13, A5: real Lie closure, with the ordinary matrix commutator.
--   - `localTermSpan`: PDF p.2: a sum of local terms need not have individually invariant terms.
--   - `schrodingerEvolution`: PDF p.13: Schrödinger sign convention.
--   - `Propagator`: PDF pp.14–15,31: entrywise integral Schrödinger equation from I. Integrability on the closed interval and the integral equation include finite pulses; unitarity is an invariant of the stipulated physical propagator.
--   - `QMat`
--   - `qubitWeight`: PDF p.23: Hamming weight.
--   - `zString`: PDF p.23, C2: unnormalized Pauli Z string on a bit mask.
--   - `chargeSector`: PDF p.23: full physical charge-sector projector, including the end sectors.
--   - `u1Central`: PDF p.23, C2: sum of all Z strings of weight l, with no normalization.
--   - `phaseWeight`: PDF p.23, C3: integer Krawtchouk coefficient; the s≤l guard prevents natural subtraction from counting spurious terms when s>l.
--   - `totalZ`: PDF p.23, C1: total Z; commuting with it is exactly U(1) invariance.
--   - `U1Invariant`: PDF p.23: this definition is used for Hermitian and skew-Hermitian operators.
--   - `U1Unitary`: PDF p.1: a physical U(1)-invariant unitary.
--   - `rotations`: PDF p.23, C1: all rotations, not one selected group element.
--   - `u1Lie`: PDF p.24, C7.
--   - `u1Group`: PDF p.2: finite local symmetric circuits on the actual qubit register.
--   - `xyExchange`: PDF p.26, C23: R=(XX+YY)/2, for distinct sites.
--   - `exchangeControls`: PDF pp.24,32, C9/D8: all exchange and single-site Z Hamiltonians.
--   - `xyZLie`: PDF p.24, C10: real Lie algebra with the source's factor 1/2.
--   - `controlGenerated`: PDF pp.24,32: finite exchange/Z circuits. All real angles give exactly the same gates as [0,2π), since R and Z have integer spectra.
--   - `xyZGroup`: PDF p.32, D8.
--   - `chargeSectorDet`: PDF pp.31–32: determinant of the full physical sector, by identity extension.
--   - `u1BodyPhase`: PDF p.32, D7: l-body phase in ℝ/(2πℤ), including l=0.
--   - `u1DualCentral`: PDF p.33, D11: dual central element; only l≤n is used in theorems.
--   - `u1FinitePhaseGroup`: PDF p.33, D15: integer powers of the prescribed generators.
--   - `u1PhaseFactor`: PDF p.33, D16: principal representatives are chosen before exponentiation.
--   - `initialString`: PDF p.33, D17: one fixed initial string per weight; l=0 is I.
--   - `stringPhaseFactor`: PDF p.33, D17: includes the displayed factor i missing in the preceding prose.
--   - `lowerBit`: PDF pp.35–36: remove the occupied input bit participating in the Bell pair.
--   - `bellInterference`: PDF p.35, E5: the actual Bell-input/interference-outcome probability.
--   - `restrictedInterference`: PDF p.36, E12: probability from the restricted one-exchange circuit.
--   - `withZero`: PDF pp.5,41: ground-state ancilla embedding, in the fixed wire order.
--   - `Catalyzes`: PDF pp.5,41: exact coherent action with the same returned ancilla for all inputs.
--   - `qubitCatalystControls`: PDF p.41: only the ancilla has a single-site Z control.
--   - `geometricCatalystControls`: PDF p.42: chain system edges, with either all ancilla spokes or one endpoint. The endpoint scheme also has ZZ on every chain edge and the ancilla edge.
--   - `diagonalChainControls`: PDF p.28, C34: diagonal controls and adjacent exchanges, with j<n.
--   - `geometricGroup`: PDF p.2: connected-support k-local gates on a specified graph.
--   - `CompactConnectedMatrixLieGroup`: PDF p.14: finite-dimensional embedded matrix Lie structure can be specified by its local exponential chart: small skew-Hermitian logarithms belong precisely to the indicated real Lie algebra. Ambient matrix exponential is a chart near zero.
--   - `EnergyBasis`
--   - `EMat`
--   - `intrinsicEnergy`: PDF p.43, G8–G9: additive intrinsic energy with a strictly positive gap in every theorem that uses energy conservation.
--   - `lowerLevel`: PDF p.44, G10: local adjacent-level lowering; level index l.val+1≥1.
--   - `energyOnWire`: PDF p.44: insert a local matrix on a named qudit.
--   - `energyExchange`: PDF p.44, G10b: energy transfer with no extraneous factor 1/2.
--   - `ancillaExchange`: PDF p.44, G10a: system/ancilla transfer with the same energy gap.
--   - `ancillaZ`: PDF p.44: the sole single-site ancilla control.
--   - `energyControls`: PDF p.44, G12/G15: chain edges j<n, ancilla couplings to every j≤n.
--   - `energyLie`: PDF p.44, G12: the actual generated real Lie algebra.
--   - `energyDrift`: PDF pp.43–46: additive system-plus-ancilla drift, with no energy shift.
--   - `PulseReachable`: PDF p.45, G17–G18: finite piecewise-constant control pulses, including drift. Nonnegative durations and span coefficients are free. A finite list automatically has compact time support; list order is the matrix product order.
--   - `groundEmbed`: PDF p.44, G13: append the exact ground-state ancillary vector.
--   - `HamiltonianLift`: PDF p.44, G13: one Hamiltonian lift acts correctly on the entire ground slice.
--   - `secondAncillaExchange`: PDF p.46, G25: second-ancilla transfer, identity on ancilla a.
--   - `twoAncillaControls`: PDF p.46, G26 corrected using G22–G23/G27: both local ancilla Z controls, and no direct system/system interaction. Printed G26 repeats an a-exchange in place of Z_b; this correction is subject to independent moderation.
--   - `twoAncillaDrift`: PDF p.46, G27: both ancillas have energy gap gap, retaining the drift.
--   - `energyDiagonalControls`: PDF p.49, G52: arbitrary real diagonal controls and adjacent transfers.
--   - `energyDiagonalMonomial`: PDF pp.47–48, G36–G40: each site is I or a nonzero adjacent-level difference. Option.none is I, while Option.some l denotes Z^(l.val+1), never Z^(0).
--   - `EquispacedLevels`: PDF pp.40,43: heterogeneous, possibly degenerate, equally spaced levels. Every integer level 0,...,last j occurs; eigenvectors sharing a level give degeneracy. The offsets are arbitrary and the common positive gap is supplied in the theorem.
--   - `EquispacedLevels.energy`: PDF pp.5–6,40,43: intrinsic energy is additive before and after the protocol.
--   - `attachEnergy`: PDF p.40: the ancilla has gap ΔE and no system/ancilla interaction at endpoints.
--   - `heterogeneousEnergyGates`: PDF p.40, Theorem 14: all two-local energy-conserving gates on the systems and one ancilla, either system/system or a single system with the ancilla.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, https://arxiv.org/abs/2003.05524v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P49

/-!
Marvian, arXiv:2003.05524v3. PDF pages are used throughout.
Paper-specific definitions are distinguished from unrelated accepted names.
Equivalent accepted matrix, wire-insertion and SWAP definitions are imported. Reachability is finite composition,
without topological closure, ancillary systems, or quotienting out global phases.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius
open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev SiteBasis {n : ℕ} (D : Fin n → Type*) := (j : Fin n) → D j

/-- PDF pp.1,13: support means an operator on the selected tensor factors,
with the identity on every complementary factor. -/
def TensorSupported {n : ℕ} {D : Fin n → Type*} [∀ j, Fintype (D j)]
    [∀ j, DecidableEq (D j)] (s : Finset (Fin n)) (A : Mat (SiteBasis D)) : Prop :=
  ∃ B : Mat ((j : {j // j ∈ s}) → D j.val), ∀ x y,
    A x y = B (fun j => x j.val) (fun j => y j.val) *
      ∏ j ∈ Finset.univ \ s, if x j = y j then 1 else 0

/-- PDF p.1: a single k-local operator, as opposed to a sum of local terms. -/
def SiteLocal {n : ℕ} {D : Fin n → Type*} [∀ j, Fintype (D j)]
    [∀ j, DecidableEq (D j)] (k : ℕ) (A : Mat (SiteBasis D)) : Prop :=
  ∃ s : Finset (Fin n), s.card ≤ k ∧ TensorSupported s A

/-- PDF p.13, A1–A2: on-site unitary representations, allowing heterogeneous sites. -/
structure OnSite (G : Type*) [Group G] {n : ℕ} (D : Fin n → Type*)
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] where
  u : (j : Fin n) → G → Mat (D j)
  unitary : ∀ j g, u j g ∈ Matrix.unitaryGroup (D j) ℂ
  one : ∀ j, u j 1 = 1
  mul : ∀ j g h, u j (g * h) = u j g * u j h

/-- PDF p.13, A2: the specified tensor product representation. -/
def OnSite.total {G : Type*} [Group G] {n : ℕ} {D : Fin n → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] (r : OnSite G D)
    (g : G) : Mat (SiteBasis D) := fun x y => ∏ j, r.u j g (x j) (y j)

/-- PDF pp.1,13: the commutant of a representation. -/
def CommutesWithAction {G I : Type*} [Fintype I] (U : G → Mat I) (A : Mat I) : Prop :=
  ∀ g, A * U g = U g * A

/-- PDF p.13, A4: the actual generator set. -/
def localGates {G : Type*} {n : ℕ} {D : Fin n → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)]
    (U : G → Mat (SiteBasis D)) (k : ℕ) : Set (Mat (SiteBasis D)) :=
  {V | V ∈ Matrix.unitaryGroup (SiteBasis D) ℂ ∧ CommutesWithAction U V ∧ SiteLocal k V}

/-- PDF p.13, A4: algebraic submonoid closure consists of finite gate products.
The generators contain their inverses, so it is the generated group. -/
def symmetricLocalGroup {G : Type*} {n : ℕ} {D : Fin n → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)]
    (U : G → Mat (SiteBasis D)) (k : ℕ) : Submonoid (Mat (SiteBasis D)) :=
  Submonoid.closure (localGates U k)

/-- PDF p.13, A5: real Lie closure, with the ordinary matrix commutator. -/
def symmetricLocalLie {G : Type*} {n : ℕ} {D : Fin n → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)]
    (U : G → Mat (SiteBasis D)) (k : ℕ) : LieSubalgebra ℝ (Mat (SiteBasis D)) :=
  LieSubalgebra.lieSpan ℝ (Mat (SiteBasis D))
    {A | A + Aᴴ = 0 ∧ CommutesWithAction U A ∧ SiteLocal k A}

/-- PDF p.2: a sum of local terms need not have individually invariant terms. -/
def localTermSpan {n : ℕ} {D : Fin n → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] (k : ℕ) : Submodule ℂ (Mat (SiteBasis D)) :=
  Submodule.span ℂ {A | SiteLocal k A}

/-- PDF p.13: Schrödinger sign convention. -/
def schrodingerEvolution {I : Type*} [Fintype I] [DecidableEq I] (H : Mat I) (t : ℝ) : Mat I :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)

/-- PDF pp.14–15,31: entrywise integral Schrödinger equation from I.
Integrability on the closed interval and the integral equation include finite pulses;
unitarity is an invariant of the stipulated physical propagator. -/
def Propagator {I : Type*} [Fintype I] [DecidableEq I]
    (H V : ℝ → Mat I) (T : ℝ) : Prop :=
  0 ≤ T ∧
  (∀ x y, IntegrableOn (fun t => H t x y) (Set.Icc 0 T)) ∧
  (∀ x y, IntegrableOn (fun t => ((-Complex.I) • (H t * V t)) x y) (Set.Icc 0 T)) ∧
  (∀ t ∈ Set.Icc 0 T, (H t).IsHermitian ∧ V t ∈ Matrix.unitaryGroup I ℂ) ∧
  ∀ t ∈ Set.Icc 0 T, ∀ x y,
    V t x y = (1 : Mat I) x y + ∫ s in (0 : ℝ)..t, ((-Complex.I) • (H s * V s)) x y

abbrev QMat (n : ℕ) := Mat (Qubits n)

/-- PDF p.23: Hamming weight. -/
def qubitWeight {n : ℕ} (x : Qubits n) : ℕ :=
  (Finset.univ.filter fun j => x j = true).card

/-- PDF p.23, C2: unnormalized Pauli Z string on a bit mask. -/
def zString {n : ℕ} (b : Qubits n) : QMat n :=
  Matrix.diagonal fun x => ∏ j, if b j ∧ x j then -1 else 1

/-- PDF p.23: full physical charge-sector projector, including the end sectors. -/
def chargeSector (n m : ℕ) : QMat n := Matrix.diagonal fun x => if qubitWeight x = m then 1 else 0

/-- PDF p.23, C2: sum of all Z strings of weight l, with no normalization. -/
def u1Central (n l : ℕ) : QMat n := ∑ b ∈ Finset.univ.filter (fun b => qubitWeight b = l), zString b

/-- PDF p.23, C3: integer Krawtchouk coefficient; the s≤l guard prevents
natural subtraction from counting spurious terms when s>l. -/
def phaseWeight (n l m : ℕ) : ℤ :=
  ∑ s ∈ (Finset.range (m+1)).filter (fun s => s ≤ l),
    (-1 : ℤ)^s * (Nat.choose m s : ℤ) * (Nat.choose (n-m) (l-s) : ℤ)

/-- PDF p.23, C1: total Z; commuting with it is exactly U(1) invariance. -/
def totalZ (n : ℕ) : QMat n := Matrix.diagonal fun x => (n : ℂ) - 2 * (qubitWeight x : ℂ)

/-- PDF p.23: this definition is used for Hermitian and skew-Hermitian operators. -/
def U1Invariant {n : ℕ} (A : QMat n) : Prop := A * totalZ n = totalZ n * A

/-- PDF p.1: a physical U(1)-invariant unitary. -/
def U1Unitary {n : ℕ} (V : QMat n) : Prop :=
  V ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧ U1Invariant V

/-- PDF p.23, C1: all rotations, not one selected group element. -/
def rotations (n : ℕ) (theta : ℝ) : QMat n := schrodingerEvolution (totalZ n) (-theta)

/-- PDF p.24, C7. -/
def u1Lie (n k : ℕ) := symmetricLocalLie (rotations n) k

/-- PDF p.2: finite local symmetric circuits on the actual qubit register. -/
def u1Group (n k : ℕ) := symmetricLocalGroup (rotations n) k

/-- PDF p.26, C23: R=(XX+YY)/2, for distinct sites. -/
def xyExchange {n : ℕ} (a b : Fin n) : QMat n :=
  (1/2 : ℂ) • (onWire a pauliX * onWire b pauliX + onWire a pauliY * onWire b pauliY)

/-- PDF pp.24,32, C9/D8: all exchange and single-site Z Hamiltonians. -/
def exchangeControls (n : ℕ) : Set (QMat n) :=
  {H | (∃ a : Fin n, H = onWire a pauliZ) ∨
    ∃ a b : Fin n, a ≠ b ∧ H = xyExchange a b}

/-- PDF p.24, C10: real Lie algebra with the source's factor 1/2. -/
def xyZLie (n : ℕ) : LieSubalgebra ℝ (QMat n) :=
  LieSubalgebra.lieSpan ℝ (QMat n) ((fun H => Complex.I • H) '' exchangeControls n)

/-- PDF pp.24,32: finite exchange/Z circuits. All real angles give exactly the
same gates as [0,2π), since R and Z have integer spectra. -/
def controlGenerated {I : Type*} [Fintype I] [DecidableEq I] (controls : Set (Mat I)) : Submonoid (Mat I) :=
  Submonoid.closure {V | ∃ H ∈ controls, ∃ theta : ℝ, V = schrodingerEvolution H (-theta)}

/-- PDF p.32, D8. -/
def xyZGroup (n : ℕ) := controlGenerated (exchangeControls n)

/-- PDF pp.31–32: determinant of the full physical sector, by identity extension. -/
def chargeSectorDet {n : ℕ} (V : QMat n) (m : Fin (n+1)) : ℂ :=
  Matrix.det (V * chargeSector n m.val + (1 - chargeSector n m.val))

/-- PDF p.32, D7: l-body phase in ℝ/(2πℤ), including l=0. -/
def u1BodyPhase {n : ℕ} (V : QMat n) (l : ℕ) : Real.Angle :=
  ∑ m : Fin (n+1), phaseWeight n l m.val • ((Complex.arg (chargeSectorDet V m) : ℝ) : Real.Angle)

/-- PDF p.33, D11: dual central element; only l≤n is used in theorems. -/
def u1DualCentral (n l : ℕ) : QMat n :=
  ((2 : ℂ)^n * (Nat.choose n l : ℂ))⁻¹ • u1Central n l

/-- PDF p.33, D15: integer powers of the prescribed generators. -/
def u1FinitePhaseGroup (n : ℕ) : Submonoid (QMat n) :=
  Submonoid.closure {V | ∃ l : Fin (n+1), ∃ z : ℤ,
    V = NormedSpace.exp ((Complex.I * (2*Real.pi : ℝ) * (z : ℂ)) • u1DualCentral n l.val)}

/-- PDF p.33, D16: principal representatives are chosen before exponentiation. -/
def u1PhaseFactor {n : ℕ} (V : QMat n) : QMat n :=
  (List.ofFn fun l : Fin (n+1) =>
    NormedSpace.exp ((Complex.I * ((u1BodyPhase V l.val).toReal : ℂ)) • u1DualCentral n l.val)).prod

/-- PDF p.33, D17: one fixed initial string per weight; l=0 is I. -/
def initialString (n l : ℕ) : QMat n := zString (fun j => decide (j.val < l))

/-- PDF p.33, D17: includes the displayed factor i missing in the preceding prose. -/
def stringPhaseFactor {n : ℕ} (V : QMat n) : QMat n :=
  (List.ofFn fun l : Fin (n+1) => NormedSpace.exp
    ((Complex.I * ((u1BodyPhase V l.val).toReal : ℂ) / (2 : ℂ)^n) • initialString n l.val)).prod

/-- PDF pp.35–36: remove the occupied input bit participating in the Bell pair. -/
def lowerBit {n : ℕ} (x : Qubits n) (r : Fin n) : Qubits n := Function.update x r false

/-- PDF p.35, E5: the actual Bell-input/interference-outcome probability. -/
def bellInterference {n : ℕ} (V : QMat n) (x : Qubits n) (r : Fin n)
    (y z : Qubits n) (theta : ℝ) : ℝ :=
  (1/4 : ℝ) * Complex.normSq (V y x + Complex.exp (-Complex.I * theta) * V z (lowerBit x r))

/-- PDF p.36, E12: probability from the restricted one-exchange circuit. -/
def restrictedInterference (V : QMat 3) (x y : Qubits 3) (r s : Fin 3) (alpha : ℝ) : ℝ :=
  (1/4 : ℝ) * Complex.normSq (V y x + Complex.I * Complex.exp (-2*Complex.I*alpha) *
    V (lowerBit y s) (lowerBit x r))

/-- PDF pp.5,41: ground-state ancilla embedding, in the fixed wire order. -/
def withZero {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) : EuclideanSpace ℂ (Qubits (n+1)) :=
  WithLp.toLp 2 fun x => if x (Fin.last n) then 0 else psi (x ∘ Fin.castSucc)

/-- PDF pp.5,41: exact coherent action with the same returned ancilla for all inputs. -/
def Catalyzes {n : ℕ} (W : QMat (n+1)) (V : QMat n) : Prop :=
  ∀ psi : EuclideanSpace ℂ (Qubits n), act W (withZero psi) = withZero (act V psi)

/-- PDF p.41: only the ancilla has a single-site Z control. -/
def qubitCatalystControls (n : ℕ) : Set (QMat (n+1)) :=
  {H | H = onWire (Fin.last n) pauliZ ∨
    ∃ a b : Fin (n+1), a ≠ b ∧ H = xyExchange a b}

/-- PDF p.42: chain system edges, with either all ancilla spokes or one endpoint.
The endpoint scheme also has ZZ on every chain edge and the ancilla edge. -/
def geometricCatalystControls (n : ℕ) (endpoint : Bool) : Set (QMat (n+1)) :=
  {H | H = onWire (Fin.last n) pauliZ ∨
    ∃ a b : Fin (n+1), a ≠ b ∧
      ((a.val < n ∧ b.val < n ∧ a.val + 1 = b.val) ∨
        (b = Fin.last n ∧ a.val < n ∧ (endpoint = true → a.val = 0))) ∧
      (H = xyExchange a b ∨ (endpoint = true ∧ H = onWire a pauliZ * onWire b pauliZ))}

/-- PDF p.28, C34: diagonal controls and adjacent exchanges, with j<n. -/
def diagonalChainControls (n : ℕ) : Set (QMat n) :=
  {H | (H.IsHermitian ∧ Matrix.IsDiag H) ∨
    ∃ a b : Fin n, a.val + 1 = b.val ∧ H = xyExchange a b}

/-- A sanity check on the physical one-qubit conventions. -/
example : zString (fun _ : Fin 1 => true) (fun _ => true) (fun _ => true) = -1 := by
  simp [zString, Matrix.diagonal, Matrix.of_apply]

/-- The binomial sign and the guarded natural subtraction agree at l=0. -/
example : phaseWeight 1 0 1 = 1 := by
  norm_num [phaseWeight, Finset.sum_filter, Finset.sum_range_succ]

/-- The two one-qubit charge weights for Φ₁ have opposite signs. -/
example : phaseWeight 1 1 0 = 1 ∧ phaseWeight 1 1 1 = -1 := by
  norm_num [phaseWeight, Finset.sum_filter, Finset.sum_range_succ]

section General

variable {G : Type*} [Group G] {n : ℕ} {D : Fin n → Type*}
variable [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [hD : ∀ j, Nonempty (D j)]

-- Positive local dimensions are a physical standing assumption even when unused
-- in the displayed formula; include it in each theorem's elaborated binders.
include hD

end General

/-- PDF p.2: connected-support k-local gates on a specified graph. -/
def geometricGroup {G A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
    (U : G → Mat (Fin n → A)) (graph : SimpleGraph (Fin n)) (k : ℕ) : Submonoid (Mat (Fin n → A)) :=
  Submonoid.closure {V | V ∈ localGates U k ∧ ∃ s : Finset (Fin n),
    s.card ≤ k ∧ TensorSupported s V ∧ (graph.induce (s : Set (Fin n))).Connected}

/-- PDF p.14: finite-dimensional embedded matrix Lie structure can be specified
by its local exponential chart: small skew-Hermitian logarithms belong precisely
to the indicated real Lie algebra. Ambient matrix exponential is a chart near zero. -/
def CompactConnectedMatrixLieGroup {I : Type*} [Fintype I] [DecidableEq I]
    (S : Submonoid (Mat I)) (L : LieSubalgebra ℝ (Mat I)) : Prop :=
  IsCompact (S : Set (Mat I)) ∧ IsConnected (S : Set (Mat I)) ∧
  (∀ V ∈ S, V ∈ Matrix.unitaryGroup I ℂ ∧ Vᴴ ∈ S) ∧
  ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ C : Mat I,
    C + Cᴴ = 0 → ‖C‖ < epsilon → (NormedSpace.exp C ∈ S ↔ C ∈ L)

abbrev EnergyBasis (n d : ℕ) := Fin n → Fin d

abbrev EMat (n d : ℕ) := Mat (EnergyBasis n d)

/-- PDF p.43, G8–G9: additive intrinsic energy with a strictly positive gap
in every theorem that uses energy conservation. -/
def intrinsicEnergy (n d : ℕ) (gap : ℝ) : EMat n d :=
  Matrix.diagonal fun x => ((gap * ∑ j : Fin n, (x j).val : ℝ) : ℂ)

/-- PDF p.44, G10: local adjacent-level lowering; level index l.val+1≥1. -/
def lowerLevel (d : ℕ) (l : Fin (d-1)) : Mat (Fin d) :=
  Matrix.single ⟨l.val, by omega⟩ ⟨l.val+1, by omega⟩ 1

/-- PDF p.44: insert a local matrix on a named qudit. -/
def energyOnWire {n d : ℕ} (j : Fin n) (A : Mat (Fin d)) : EMat n d :=
  fun x y => A (x j) (y j) * ∏ q ∈ Finset.univ.erase j, if x q = y q then 1 else 0

/-- PDF p.44, G10b: energy transfer with no extraneous factor 1/2. -/
def energyExchange {n d : ℕ} (j q : Fin n) (l m : Fin (d-1)) : EMat n d :=
  let A := energyOnWire j (lowerLevel d l) * energyOnWire q (lowerLevel d m)ᴴ
  A + Aᴴ

/-- PDF p.44, G10a: system/ancilla transfer with the same energy gap. -/
def ancillaExchange {n d : ℕ} (j : Fin n) (l : Fin (d-1)) : Mat (EnergyBasis n d × Bool) :=
  let A := Matrix.kronecker (energyOnWire j (lowerLevel d l)) (Matrix.single true false (1 : ℂ))
  A + Aᴴ

/-- PDF p.44: the sole single-site ancilla control. -/
def ancillaZ (n d : ℕ) : Mat (EnergyBasis n d × Bool) :=
  Matrix.kronecker (1 : EMat n d) pauliZ

/-- PDF p.44, G12/G15: chain edges j<n, ancilla couplings to every j≤n. -/
def energyControls (n d : ℕ) : Set (Mat (EnergyBasis n d × Bool)) :=
  {H | H = ancillaZ n d ∨
    (∃ j : Fin n, ∃ l : Fin (d-1), H = ancillaExchange j l) ∨
    ∃ j q : Fin n, j.val+1 = q.val ∧ ∃ l m : Fin (d-1),
      H = Matrix.kronecker (energyExchange j q l m) (1 : Mat Bool)}

/-- PDF p.44, G12: the actual generated real Lie algebra. -/
def energyLie (n d : ℕ) : LieSubalgebra ℝ (Mat (EnergyBasis n d × Bool)) :=
  LieSubalgebra.lieSpan ℝ _ ((fun H => Complex.I • H) '' energyControls n d)

/-- PDF pp.43–46: additive system-plus-ancilla drift, with no energy shift. -/
def energyDrift (n d : ℕ) (gap : ℝ) : Mat (EnergyBasis n d × Bool) :=
  Matrix.kronecker (intrinsicEnergy n d gap) (1 : Mat Bool) +
    Matrix.kronecker (1 : EMat n d) ((gap : ℂ) • Matrix.single true true 1)

/-- PDF p.45, G17–G18: finite piecewise-constant control pulses, including drift.
Nonnegative durations and span coefficients are free. A finite list automatically
has compact time support; list order is the matrix product order. -/
def PulseReachable {I : Type*} [Fintype I] [DecidableEq I]
    (drift : Mat I) (controls : Set (Mat I)) (V : Mat I) : Prop :=
  ∃ pulses : List (ℝ × Mat I),
    (∀ p ∈ pulses, 0 ≤ p.1 ∧ p.2 - drift ∈ Submodule.span ℝ controls) ∧
    (pulses.map fun p => schrodingerEvolution p.2 p.1).prod = V

/-- PDF p.44, G13: append the exact ground-state ancillary vector. -/
def groundEmbed {I : Type*} (psi : EuclideanSpace ℂ I) : EuclideanSpace ℂ (I × Bool) :=
  WithLp.toLp 2 fun x => if x.2 then 0 else psi x.1

/-- PDF p.44, G13: one Hamiltonian lift acts correctly on the entire ground slice. -/
def HamiltonianLift {I : Type*} [Fintype I] (K : Mat (I × Bool)) (H : Mat I) : Prop :=
  ∀ psi : EuclideanSpace ℂ I, act K (groundEmbed psi) = groundEmbed (act H psi)

/-- PDF p.46, G25: second-ancilla transfer, identity on ancilla a. -/
def secondAncillaExchange {n d : ℕ} (j : Fin n) (l : Fin (d-1)) :
    Mat ((EnergyBasis n d × Bool) × Bool) :=
  let A : Mat ((EnergyBasis n d × Bool) × Bool) := fun x y =>
    energyOnWire j (lowerLevel d l) x.1.1 y.1.1 *
      (if x.1.2 = y.1.2 then 1 else 0) * Matrix.single true false (1 : ℂ) x.2 y.2
  A + Aᴴ

/-- PDF p.46, G26 corrected using G22–G23/G27: both local ancilla Z controls,
and no direct system/system interaction. Printed G26 repeats an a-exchange in
place of Z_b; this correction is subject to independent moderation. -/
def twoAncillaControls (n d : ℕ) : Set (Mat ((EnergyBasis n d × Bool) × Bool)) :=
  {H | H = Matrix.kronecker (ancillaZ n d) (1 : Mat Bool) ∨
    H = Matrix.kronecker (1 : Mat (EnergyBasis n d × Bool)) pauliZ ∨
    (∃ j : Fin n, ∃ l : Fin (d-1), H = Matrix.kronecker (ancillaExchange j l) (1 : Mat Bool)) ∨
    ∃ j : Fin n, ∃ l : Fin (d-1), H = secondAncillaExchange j l}

/-- PDF p.46, G27: both ancillas have energy gap gap, retaining the drift. -/
def twoAncillaDrift (n d : ℕ) (gap : ℝ) : Mat ((EnergyBasis n d × Bool) × Bool) :=
  Matrix.kronecker (energyDrift n d gap) (1 : Mat Bool) +
    Matrix.kronecker (1 : Mat (EnergyBasis n d × Bool)) ((gap : ℂ) • Matrix.single true true 1)

/-- PDF p.49, G52: arbitrary real diagonal controls and adjacent transfers. -/
def energyDiagonalControls (n d : ℕ) : Set (EMat n d) :=
  {H | (H.IsHermitian ∧ Matrix.IsDiag H) ∨
    ∃ j q : Fin n, j.val+1 = q.val ∧ ∃ l m : Fin (d-1), H = energyExchange j q l m}

/-- PDF pp.47–48, G36–G40: each site is I or a nonzero adjacent-level difference.
Option.none is I, while Option.some l denotes Z^(l.val+1), never Z^(0). -/
def energyDiagonalMonomial (n d : ℕ) (a : Fin n → Option (Fin (d-1))) : EMat n d :=
  Matrix.diagonal fun x => ∏ j, match a j with
    | none => 1
    | some l => if (x j).val = l.val then 1 else if (x j).val = l.val+1 then -1 else 0

/-- At d=1 the identity monomial still acts on the full one-dimensional register. -/
example (n d : ℕ) : energyDiagonalMonomial n d (fun _ => none) = 1 := by
  ext x y
  simp [energyDiagonalMonomial, Matrix.one_apply]

/-- The ground embedding suppresses the excited ancilla component exactly. -/
example {I : Type*} (psi : EuclideanSpace ℂ I) (x : I) : groundEmbed psi (x, true) = 0 := by rfl

/-- PDF pp.40,43: heterogeneous, possibly degenerate, equally spaced levels.
Every integer level 0,...,last j occurs; eigenvectors sharing a level give degeneracy.
The offsets are arbitrary and the common positive gap is supplied in the theorem. -/
structure EquispacedLevels {n : ℕ} (D : Fin n → Type*) where
  last : Fin n → ℕ
  level : (j : Fin n) → D j → ℕ
  bounded : ∀ j x, level j x ≤ last j
  complete : ∀ j m, m ≤ last j → ∃ x, level j x = m
  offset : Fin n → ℝ

/-- PDF pp.5–6,40,43: intrinsic energy is additive before and after the protocol. -/
def EquispacedLevels.energy {n : ℕ} {D : Fin n → Type*}
    [∀ j, DecidableEq (D j)] (e : EquispacedLevels D) (gap : ℝ) : Mat (SiteBasis D) :=
  Matrix.diagonal fun x => ((∑ j, (e.offset j + gap * (e.level j (x j) : ℝ)) : ℝ) : ℂ)

/-- PDF p.40: the ancilla has gap ΔE and no system/ancilla interaction at endpoints. -/
def attachEnergy {I : Type*} [DecidableEq I] (H : Mat I) (gap : ℝ) : Mat (I × Bool) :=
  Matrix.kronecker H (1 : Mat Bool) +
    Matrix.kronecker (1 : Mat I) ((gap : ℂ) • Matrix.single true true 1)

/-- PDF p.40, Theorem 14: all two-local energy-conserving gates on the systems
and one ancilla, either system/system or a single system with the ancilla. -/
def heterogeneousEnergyGates {n : ℕ} {D : Fin n → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)]
    (Htot : Mat (SiteBasis D × Bool)) : Set (Mat (SiteBasis D × Bool)) :=
  {V | V ∈ Matrix.unitaryGroup (SiteBasis D × Bool) ℂ ∧ V*Htot = Htot*V ∧
    ((∃ A : Mat (SiteBasis D), SiteLocal 2 A ∧ V = Matrix.kronecker A (1 : Mat Bool)) ∨
      ∃ j : Fin n, ∃ B : Mat (D j × Bool), ∀ x y,
        V x y = B (x.1 j, x.2) (y.1 j, y.2) *
          ∏ q ∈ Finset.univ.erase j, if x.1 q = y.1 q then 1 else 0)}

end QAlgorithms.Papers.Independent.Extend50.P14

end


