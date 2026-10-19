-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39
-- name    : QAlgorithms_Papers_Independent_Information100_P39
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T11:13:44.52599+00:00
-- url     : https://prove2.me/theorems/b0501552-aa04-4258-8505-92add092097b
-- title:
--   Definitions for Hierarchy of Rényi Coherent Information in Stabilizer Codes
-- statement:
--   The objects the formalized statements of *Hierarchy of Rényi Coherent Information in Stabilizer Codes* (arXiv:2609.11930) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `F2`: PDF p.2: the binary field.
--   - `Bits`: PDF p.2: finitely many fault coordinates, including the empty family.
--   - `Order`: PDF p.2: positive integer orders and infinity; theorem guards exclude zero.
--   - `binaryLaw`: PDF p.2: the independent Bernoulli law, including deterministic bits and m=0.
--   - `pushLaw`: PDF p.2: a finite observation has the pushforward of the fault law.
--   - `entropy`: PDF pp.2,8: Shannon, positive-integer Rényi, and min-entropy, in nats. Only orders at least 1 are used. On finite normalized laws the range has a nonempty, bounded maximum; zero masses contribute 0 to Shannon entropy.
--   - `quotientLaw`: PDF p.2, Eq.(1): the quotient-label distribution.
--   - `linearDeficit`: PDF p.2, Eq.(2): fine-minus-coarse entropy.
--   - `DecreasingOrders`: PDF pp.2–4: comparisons include all positive integers and the infinite endpoint.
--   - `supported`: PDF p.2, Eq.(6): patterns supported on the erased coordinates. The displayed set is a subspace; taking its linear span leaves it unchanged.
--   - `kappa`: PDF p.2, Eq.(6): dimension of T_Gamma(ker C_Gamma).
--   - `erasedLaw`: PDF p.2: independent erasures of probability 4p(1-p).
--   - `PauliLabel`: PDF pp.4,8: accepted Pauli labels modulo phase in (x,z) coordinates.
--   - `eventLaw`: PDF p.4, Eq.(33): summing binary event vectors gives the realized Pauli modulo phase.
--   - `HasIndependentEvents`: PDF pp.2,4,8: independent Bernoulli events may act on several qubits.
--   - `HasSmallEvents`: PDF p.8: the reduced representation used after complementing fault bits.
--   - `StabilizerCode`: PDF pp.2,4: an encoding isometry onto the full stabilizer codespace. The frozen stabilizer predicate excludes -I. No CSS or locality restriction is used.
--   - `quantumEntropy`: PDF pp.2,8: matrix Rényi entropy from the actual density operator. At infinity the largest eigenvalue is its maximum Rayleigh quotient. Every use below has a normalized density operator on a nonempty finite register.
--   - `noisyChoi`: PDF pp.2,4: encode half of the normalized maximally entangled input and apply the frozen stochastic Pauli channel. This is the actual noisy Choi state.
--   - `coherentInformation`: PDF p.2, Eq.(4): H_n(Q)-H_n(RQ), with the reference traced out.
--   - `quantumDeficit`: PDF p.4, Eq.(32): the absolute deficit of the actual noisy state.
--   - `PositiveNegativeCrossing`: PDF p.5, Eq.(41): a crossing has strict positive/negative signs on either side in the specified closed parameter interval, and is zero at the crossing.
--   - `parameterInformation`: PDF p.5, Eq.(41): the family is specified only on its parameter interval. The zero extension is unused in the crossing signs and places no conditions on the noise outside the interval.
--   - `labelX`: PDF p.8, convention (I,X,Y,Z): labels use the accepted (x,z) ordering.
--   - `labelY`: PDF p.8: the Y label in (x,z) coordinates.
--   - `labelZ`: PDF p.8: the Z label in (x,z) coordinates.
--   - `pauliVector`: PDF p.8: convert a probability vector in the printed I,X,Y,Z order.
--   - `xyzEvents`: PDF p.8, Eq.(S3): the three elementary event labels.
--   - `FourierFactors`: PDF p.8, Eq.(S3): the exact Fourier factorization criterion.
--   - `positiveFourierLaw`: PDF p.8: the counterexample law is constructed by the accepted inverse WHT.
--   - `depolarizingLaw`: PDF pp.8–9: p is the total nonidentity probability.
--   - `depolarizingEventProbability`: PDF p.8, Eq.(S5), confirmed in the PDF: the square root is essential.
--   - `pauliMarginal`: PDF p.9: the actual single-qubit marginal, without assuming independent qubits.
--   - `singleSyndromeState`: PDF pp.5,7: with the unique syndrome, matching has acceptance one and retains exactly this trivially flagged Choi state, at every matching order.
--   - `shannonCounterexampleJoint`: PDF p.9, Eq.(S7): rows s=0,1 and columns I,X,Y,Z.
--   - `shannonCounterexampleNoise`: PDF p.9, Eq.(S6): noise on the first qubit, with the second noiseless.
--   - `shannonCounterexampleEncoder`: PDF p.9: normalized XX-stabilized codewords with logical X=X1,Z=Z1Z2.
--   - `IsEncoderFor`: PDF pp.9–10: specifying the full eigenspace prevents restricting to a smaller code.
--   - `shannonBellSector`: PDF p.9: normalized logical Bell-sector projectors, with reference Z1 for s=1 and logical labels in the printed I,X,Y,Z order.
--   - `higherFactors`: PDF p.9, Eq.(S10): the four inhomogeneous product factors.
--   - `higherNoise`: PDF pp.9–10: only the fourth factor varies in the stability assertion.
--   - `higherEncoder`: PDF p.9: the [[4,1,2]] CSS code has logical Z=Z1Z2, logical X=X1X3.
--   - `higherGenerators`: PDF p.9: stabilizer generators XXXX, ZZZZ, XXII.
--   - `labelWeight`: PDF p.9: Pauli weight, independent of its irrelevant overall phase.
-- source:
--   Hierarchy of Rényi Coherent Information in Stabilizer Codes, arXiv:2609.11930v1, https://arxiv.org/abs/2609.11930v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_QAlgorithms_Defs_PauliNoiseFourier

/-!
Statements from Vijay, Colmenarez and Lee, arXiv:2609.11930v1.
All entropies in this module use natural logarithms. Local definitions below
are paper-specific. Deferred operational results are listed in the unit's GAPS.json.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P39

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF p.2: the binary field. -/
abbrev F2 := ZMod 2

/-- PDF p.2: finitely many fault coordinates, including the empty family. -/
abbrev Bits (m : ℕ) := Fin m → F2

/-- PDF p.2: positive integer orders and infinity; theorem guards exclude zero. -/
abbrev Order := WithTop ℕ

/-- PDF p.2: the independent Bernoulli law, including deterministic bits and m=0. -/
def binaryLaw {m : ℕ} (p : Fin m → ℝ) (b : Bits m) : ℝ :=
  ∏ a, if b a = 1 then p a else 1 - p a

/-- PDF p.2: a finite observation has the pushforward of the fault law. -/
def pushLaw {A B : Type*} [Fintype A] (p : A → ℝ) (f : A → B) (y : B) : ℝ :=
  ∑ x, if f x = y then p x else 0

/-- PDF pp.2,8: Shannon, positive-integer Rényi, and min-entropy, in nats.
Only orders at least 1 are used. On finite normalized laws the range has a
nonempty, bounded maximum; zero masses contribute 0 to Shannon entropy. -/
def entropy {A : Type*} [Fintype A] (r : Order) (p : A → ℝ) : ℝ :=
  if r = ⊤ then -Real.log (sSup (Set.range p))
  else if r.untopD 0 = 1 then -∑ a, p a * Real.log (p a)
  else Real.log (∑ a, p a ^ r.untopD 0) / (1 - ((r.untopD 0 : ℕ) : ℝ))

/-- PDF p.2, Eq.(1): the quotient-label distribution. -/
def quotientLaw {m : ℕ} (p : Fin m → ℝ) (K : Submodule F2 (Bits m)) :
    (Bits m ⧸ K) → ℝ :=
  pushLaw (binaryLaw p) K.mkQ

/-- PDF p.2, Eq.(2): fine-minus-coarse entropy. -/
def linearDeficit {m : ℕ} (p : Fin m → ℝ)
    (KT KC : Submodule F2 (Bits m)) (r : Order) : ℝ :=
  entropy r (quotientLaw p KT) - entropy r (quotientLaw p KC)

/-- PDF pp.2–4: comparisons include all positive integers and the infinite endpoint. -/
def DecreasingOrders (f : Order → ℝ) : Prop :=
  ∀ r s, 1 ≤ r → r ≤ s → f s ≤ f r

/-- PDF p.2, Eq.(6): patterns supported on the erased coordinates. The displayed
set is a subspace; taking its linear span leaves it unchanged. -/
def supported {m : ℕ} (g : Finset (Fin m)) : Submodule F2 (Bits m) :=
  Submodule.span F2 {b | ∀ a, a ∉ g → b a = 0}

/-- PDF p.2, Eq.(6): dimension of T_Gamma(ker C_Gamma). -/
def kappa {m : ℕ} (KT KC : Submodule F2 (Bits m)) (g : Finset (Fin m)) : ℕ :=
  Module.finrank F2 ((KC ⊓ supported g).map KT.mkQ)

/-- PDF p.2: independent erasures of probability 4p(1-p). -/
def erasedLaw {m : ℕ} (p : Fin m → ℝ) (g : Finset (Fin m)) : ℝ :=
  ∏ a, if a ∈ g then 4 * p a * (1 - p a) else 1 - 4 * p a * (1 - p a)

example (p : Fin 0 → ℝ) (b : Bits 0) : binaryLaw p b = 1 := by
  simp [binaryLaw]

example {m : ℕ} (p : Fin m → ℝ) (K : Submodule F2 (Bits m)) (r : Order) :
    linearDeficit p K K r = 0 := by
  simp [linearDeficit]

example {m : ℕ} (p : Fin m → ℝ) (g : Finset (Fin m)) :
    erasedLaw p g = ∏ a, if a ∈ g then 4 * p a * (1 - p a)
      else 1 - 4 * p a * (1 - p a) := by
  rfl

example : entropy 1 (fun _ : Unit => (1 : ℝ)) = 0 := by
  simp [entropy]

/-- PDF pp.4,8: accepted Pauli labels modulo phase in (x,z) coordinates. -/
abbrev PauliLabel := SparsePauliNoise.Label

/-- PDF p.4, Eq.(33): summing binary event vectors gives the realized Pauli modulo phase. -/
def eventLaw {N m : ℕ} (e : Fin m → PauliLabel N) (p : Fin m → ℝ) :
    PauliLabel N → ℝ :=
  pushLaw (binaryLaw p) (fun b => ∑ a, b a • e a)

/-- PDF pp.2,4,8: independent Bernoulli events may act on several qubits. -/
def HasIndependentEvents {N : ℕ} (nu : PauliLabel N → ℝ) : Prop :=
  ∃ m, ∃ e : Fin m → PauliLabel N, ∃ p : Fin m → ℝ,
    (∀ a, 0 ≤ p a ∧ p a ≤ 1) ∧ nu = eventLaw e p

/-- PDF p.8: the reduced representation used after complementing fault bits. -/
def HasSmallEvents {N : ℕ} (nu : PauliLabel N → ℝ) : Prop :=
  ∃ m, ∃ e : Fin m → PauliLabel N, ∃ p : Fin m → ℝ,
    (∀ a, 0 ≤ p a ∧ p a ≤ 1 / 2) ∧ nu = eventLaw e p

/-- PDF pp.2,4: an encoding isometry onto the full stabilizer codespace. The
frozen stabilizer predicate excludes -I. No CSS or locality restriction is used. -/
structure StabilizerCode (N k : ℕ) where
  group : Subgroup (Matrix.unitaryGroup (Qubits N) ℂ)
  stabilizer : IsStabilizerGroup group
  encoder : Matrix (Qubits N) (Qubits k) ℂ
  isometry : encoderᴴ * encoder = 1
  fullRange : LinearMap.range (Matrix.toEuclideanLin encoder) = stabilizedSpace group

/-- PDF pp.2,8: matrix Rényi entropy from the actual density operator. At
infinity the largest eigenvalue is its maximum Rayleigh quotient. Every use
below has a normalized density operator on a nonempty finite register. -/
def quantumEntropy {A : Type*} [Fintype A] [DecidableEq A]
    (r : Order) (rho : Matrix A A ℂ) : ℝ :=
  if r = ⊤ then
    -Real.log (sSup {t : ℝ | ∃ v : EuclideanSpace ℂ A,
      ‖v‖ = 1 ∧ t = (inner ℂ v (act rho v)).re})
  else if r.untopD 0 = 1 then
    -(cfc (fun x : ℝ => x * Real.log x) rho).trace.re
  else Real.log ((rho ^ r.untopD 0).trace.re) / (1 - ((r.untopD 0 : ℕ) : ℝ))

/-- PDF pp.2,4: encode half of the normalized maximally entangled input and
apply the frozen stochastic Pauli channel. This is the actual noisy Choi state. -/
def noisyChoi {N k : ℕ} (V : Matrix (Qubits N) (Qubits k) ℂ)
    (nu : PauliLabel N → ℝ) (hnu : Learning.IsDistribution nu) :
    Matrix (Qubits k × Qubits N) (Qubits k × Qubits N) ℂ :=
  idTensorSuperop (R := Qubits k)
    (fun rho => SparsePauliNoise.channelFromRates nu hnu (conjSuperop V rho))
    (pureDensity (maxEntangled k))

/-- PDF p.2, Eq.(4): H_n(Q)-H_n(RQ), with the reference traced out. -/
def coherentInformation {R Q : Type*} [Fintype R] [Fintype Q]
    [DecidableEq R] [DecidableEq Q]
    (r : Order) (rho : Matrix (R × Q) (R × Q) ℂ) : ℝ :=
  quantumEntropy r (traceLeft rho) - quantumEntropy r rho

/-- PDF p.4, Eq.(32): the absolute deficit of the actual noisy state. -/
def quantumDeficit {N k : ℕ} (V : Matrix (Qubits N) (Qubits k) ℂ)
    (nu : PauliLabel N → ℝ) (hnu : Learning.IsDistribution nu) (r : Order) : ℝ :=
  Real.log ((2 : ℝ) ^ k) - coherentInformation r (noisyChoi V nu hnu)

example {N k : ℕ} (V : Matrix (Qubits N) (Qubits k) ℂ)
    (nu : PauliLabel N → ℝ) (hnu : Learning.IsDistribution nu) (r : Order) :
    quantumDeficit V nu hnu r = Real.log ((2 : ℝ) ^ k) -
      coherentInformation r (noisyChoi V nu hnu) := by
  rfl

example : quantumEntropy 2 (1 : Matrix Unit Unit ℂ) = 0 := by
  norm_num [quantumEntropy, Matrix.trace]

example : pureDensity (maxEntangled 0)
    ((fun _ => false), (fun _ => false)) ((fun _ => false), (fun _ => false)) = 1 := by
  simp [pureDensity, maxEntangled]

/-- PDF p.5, Eq.(41): a crossing has strict positive/negative signs on either
side in the specified closed parameter interval, and is zero at the crossing. -/
def PositiveNegativeCrossing (f : ℝ → ℝ) (a b c : ℝ) : Prop :=
  c ∈ Set.Icc a b ∧ f c = 0 ∧
    (∀ p ∈ Set.Icc a b, p < c → 0 < f p) ∧
    (∀ p ∈ Set.Icc a b, c < p → f p < 0)

/-- PDF p.5, Eq.(41): the family is specified only on its parameter interval.
The zero extension is unused in the crossing signs and places no conditions
on the noise outside the interval. -/
def parameterInformation {N k : ℕ} (C : StabilizerCode N k)
    (a b : ℝ) (nu : ℝ → PauliLabel N → ℝ)
    (hnu : ∀ p ∈ Set.Icc a b, Learning.IsDistribution (nu p))
    (r : Order) (p : ℝ) : ℝ :=
  if h : p ∈ Set.Icc a b then
    coherentInformation r (noisyChoi C.encoder (nu p) (hnu p h)) else 0

/-- PDF p.8, convention (I,X,Y,Z): labels use the accepted (x,z) ordering. -/
def labelX : PauliLabel 1 := (![1], ![0])

/-- PDF p.8: the Y label in (x,z) coordinates. -/
def labelY : PauliLabel 1 := (![1], ![1])

/-- PDF p.8: the Z label in (x,z) coordinates. -/
def labelZ : PauliLabel 1 := (![0], ![1])

/-- PDF p.8: convert a probability vector in the printed I,X,Y,Z order. -/
def pauliVector (v : Fin 4 → ℝ) (e : PauliLabel 1) : ℝ :=
  if e = 0 then v 0 else if e = labelX then v 1 else if e = labelY then v 2 else v 3

/-- PDF p.8, Eq.(S3): the three elementary event labels. -/
def xyzEvents : Fin 3 → PauliLabel 1 := ![labelX, labelY, labelZ]

/-- PDF p.8, Eq.(S3): the exact Fourier factorization criterion. -/
def FourierFactors (nu : PauliLabel 1 → ℝ) (a b c : ℝ) : Prop :=
  SparsePauliNoise.eigenvalueWHT nu labelX = b * c ∧
  SparsePauliNoise.eigenvalueWHT nu labelY = a * c ∧
  SparsePauliNoise.eigenvalueWHT nu labelZ = a * b

example : pauliVector (![1,0,0,0]) 0 = 1 := by
  simp [pauliVector]

example : SparsePauliNoise.symplecticPairing labelX labelZ = 1 := by
  simp [SparsePauliNoise.symplecticPairing, labelX, labelZ, dotProduct, Fin.sum_univ_one]

/-- PDF p.8: the counterexample law is constructed by the accepted inverse WHT. -/
def positiveFourierLaw : PauliLabel 1 → ℝ :=
  SparsePauliNoise.inverseWHT (pauliVector (![1,161/200,9/10,9/10]))

/-- PDF pp.8–9: p is the total nonidentity probability. -/
def depolarizingLaw (p : ℝ) : PauliLabel 1 → ℝ :=
  pauliVector (![1-p,p/3,p/3,p/3])

/-- PDF p.8, Eq.(S5), confirmed in the PDF: the square root is essential. -/
def depolarizingEventProbability (p : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - 4*p/3)) / 2

example : depolarizingEventProbability 0 = 0 := by
  norm_num [depolarizingEventProbability]

example : depolarizingEventProbability (3/4) = 1/2 := by
  norm_num [depolarizingEventProbability]

/-- PDF p.9: the actual single-qubit marginal, without assuming independent qubits. -/
def pauliMarginal {N : ℕ} (nu : PauliLabel N → ℝ) (j : Fin N) : PauliLabel 1 → ℝ :=
  pushLaw nu (fun e => ((fun _ => e.1 j), (fun _ => e.2 j)))

/-- PDF pp.5,7: with the unique syndrome, matching has acceptance one and
retains exactly this trivially flagged Choi state, at every matching order. -/
def singleSyndromeState {R Q : Type*} (J : Matrix (R × Q) (R × Q) ℂ) :
    Matrix (R × (Unit × Q)) (R × (Unit × Q)) ℂ :=
  fun a b => J (a.1,a.2.2) (b.1,b.2.2)

example {R Q : Type*} (J : Matrix (R × Q) (R × Q) ℂ) (r t : R) (q u : Q) :
    singleSyndromeState J (r,((),q)) (t,((),u)) = J (r,q) (t,u) := by
  rfl

/-- PDF p.9, Eq.(S7): rows s=0,1 and columns I,X,Y,Z. -/
def shannonCounterexampleJoint : Fin 2 × Fin 4 → ℝ :=
  fun x => (!![1,3,0,0; 6,6,0,0] : Matrix (Fin 2) (Fin 4) ℝ) x.1 x.2 / 16

/-- PDF p.9, Eq.(S6): noise on the first qubit, with the second noiseless. -/
def shannonCounterexampleNoise (e : PauliLabel 2) : ℝ :=
  if e.1 1 = 0 ∧ e.2 1 = 0 then
    pauliVector (![1/16,3/16,6/16,6/16]) ((fun _ => e.1 0), (fun _ => e.2 0))
  else 0

/-- PDF p.9: normalized XX-stabilized codewords with logical X=X1,Z=Z1Z2. -/
def shannonCounterexampleEncoder : Matrix (Qubits 2) (Qubits 1) ℂ :=
  fun y x => if x 0 = Bool.xor (y 0) (y 1) then (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- PDF pp.9–10: specifying the full eigenspace prevents restricting to a smaller code. -/
def IsEncoderFor {N k t : ℕ} (g : Fin t → Matrix (Qubits N) (Qubits N) ℂ)
    (V : Matrix (Qubits N) (Qubits k) ℂ) : Prop :=
  Vᴴ * V = 1 ∧ LinearMap.range (Matrix.toEuclideanLin V) =
    ⨅ i, LinearMap.ker (Matrix.toEuclideanLin (g i - 1))

example : shannonCounterexampleJoint (0,1) = 3/16 := by
  norm_num [shannonCounterexampleJoint]

/-- PDF p.9: normalized logical Bell-sector projectors, with reference Z1 for
s=1 and logical labels in the printed I,X,Y,Z order. -/
def shannonBellSector (s : Fin 2) (l : Fin 4) :
    Matrix (Qubits 1 × Qubits 2) (Qubits 1 × Qubits 2) ℂ :=
  let P : Matrix (Qubits 2) (Qubits 2) ℂ :=
    if s = 0 then 1 else pauliOps (![Stabilizer.Pauli.Z,Stabilizer.Pauli.I])
  let L := SparsePauliNoise.labelOperator ((![0,labelX,labelY,labelZ]) l)
  idTensorSuperop (R := Qubits 1) (conjSuperop (P * shannonCounterexampleEncoder * L))
    (pureDensity (maxEntangled 1))

/-- PDF p.9, Eq.(S10): the four inhomogeneous product factors. -/
def higherFactors : Fin 4 → PauliLabel 1 → ℝ :=
  ![pauliVector (![49/50,1/50,0,0]), pauliVector (![49/50,0,1/50,0]),
    pauliVector (![1/2,0,0,1/2]), pauliVector (![2/5,3/10,0,3/10])]

/-- PDF pp.9–10: only the fourth factor varies in the stability assertion. -/
def higherNoise (v : PauliLabel 1 → ℝ) (e : PauliLabel 4) : ℝ :=
  (∏ j : Fin 3, higherFactors j.castSucc ((fun _ => e.1 j.castSucc),
    (fun _ => e.2 j.castSucc))) * v ((fun _ => e.1 3), (fun _ => e.2 3))

/-- PDF p.9: the [[4,1,2]] CSS code has logical Z=Z1Z2, logical X=X1X3. -/
def higherEncoder : Matrix (Qubits 4) (Qubits 1) ℂ :=
  fun y x => if Bool.xor (y 0) (y 1) = x 0 ∧ Bool.xor (y 2) (y 3) = x 0
    then 1/2 else 0

/-- PDF p.9: stabilizer generators XXXX, ZZZZ, XXII. -/
def higherGenerators : Fin 3 → Matrix (Qubits 4) (Qubits 4) ℂ :=
  ![pauliOps (fun _ => Stabilizer.Pauli.X), pauliOps (fun _ => Stabilizer.Pauli.Z),
    pauliOps (fun j => if j.val < 2 then Stabilizer.Pauli.X else Stabilizer.Pauli.I)]

/-- PDF p.9: Pauli weight, independent of its irrelevant overall phase. -/
def labelWeight {N : ℕ} (e : PauliLabel N) : ℕ :=
  (Finset.univ.filter fun j => e.1 j ≠ 0 ∨ e.2 j ≠ 0).card

example : higherEncoder (fun _ => false) (fun _ => false) = 1/2 := by
  simp [higherEncoder]

end QAlgorithms.Papers.Independent.Information100.P39


