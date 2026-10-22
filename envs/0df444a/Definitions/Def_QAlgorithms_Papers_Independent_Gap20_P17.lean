-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17
-- name    : QAlgorithms_Papers_Independent_Gap20_P17
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T20:35:23.460565+00:00
-- url     : https://prove2.me/theorems/723fa869-bc0e-4cdc-b33e-cce3c99f43d8
-- title:
--   Definitions for Reverse Coherent Information
-- statement:
--   The objects the formalized statements of *Reverse Coherent Information* (arXiv:0808.0210) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `forwardInfo`: PDF pp.1–3, Eqs.(2),(6): coherent information from the receiver and complement of one fixed dilation. Theorems require an isometry and a density input.
--   - `reverseInfo`: PDF pp.2–3, Eq.(6): signed reverse coherent information. For a pure reference/input purification, S(R)=S(input) and S(RB)=S(E).
--   - `reverseMaximum`: PDF p.3: maximum over normalized density inputs, without max(0,·). For a nonzero finite input and an isometry this set is nonempty and bounded.
--   - `forwardMaximum`: PDF pp.1,3: the forward one-use maximum over normalized density inputs.
--   - `composeDilation`: PDF p.3: sequential output processing; both environment registers are retained.
--   - `channelTransfer`: PDF p.2: one physical channel use transfers Alice's last input factor to Bob. The off-diagonal blocks in both retained memories are kept.
--   - `Assistance`: PDF pp.1–2: allowed free classical directions.
--   - `Executes`: PDF p.2, Fig.2: actual finite protocol trees with exactly n channel calls on each branch, arbitrary finite local memories, and no implicit quantum messages. Alice can announce outcomes only with two-way assistance; Bob only with feedback or two-way assistance. Hidden local outcomes are already included in local CPTP maps.
--   - `ReverseOutput`: PDF p.2, Fig.3: a parallel input prepared entirely by Alice, followed by one Bob-to-Alice classical message. Bob's finite complete instrument may retain quantum memory; a conditional Alice channel finishes the protocol. No prior shared state.
--   - `ProtocolOutput`: PDF pp.1–2: actual n-use shared output from a product singleton laboratory state. The protocol itself is quantified before execution.
--   - `EntanglementRateAchievable`: PDF pp.1–2: rate r ebits per physical use, vanishing full-state trace-norm error, arbitrary finite block memory, and positive block lengths and target sizes.
--   - `operationalSup`: PDF pp.1–2: extended operational supremum, explicitly including rate zero. This definition never clips the signed entropy objective.
--   - `entanglementCapacity`: PDF pp.1–2: unassisted, feedback, or two-way entanglement-generation capacity.
--   - `reverseCapacity`: PDF p.2, Fig.3: reverse-protocol operational capacity E_triangle.
--   - `adKraus`: PDF p.3, Eq.(8): survival-parameter amplitude-damping Kraus family.
--   - `adDilation`: PDF p.3, Eq.(8): fixed normalized dilation for 0≤eta≤1.
--   - `adChannel`: PDF p.3: the actual amplitude-damping map on every operator.
--   - `gadKraus`: PDF pp.3–4, Eq.(10): thermal GAD Kraus family, with environment excited population alpha. Corrects the reversed coefficients in the p.3 prose mixture: alpha=0 is AD, consistently with Eqs.(11),(26)–(28).
--   - `gadDilation`: PDF pp.3–4: GAD dilation retains the full four-dimensional pure environment.
--   - `gadChannel`: PDF pp.3–4, Eq.(10): thermal GAD channel, on all operators.
--   - `diagonalInput`: PDF p.3: population p denotes the excited-state probability.
--   - `inputPurification`: PDF pp.4–5, Eqs.(14)–(15): the actual normalized purification, reference first. The positive phase agrees with (15); conjugation gives the negative phase in (14).
--   - `generalInput`: PDF p.4, Eq.(14): input obtained by tracing the reference from (15).
--   - `dampingJointOutput`: PDF pp.5–6, Eqs.(16),(25): output constructed by applying the channel to (15). Coordinates are Bob first, reference second, as in the displayed matrices.
--   - `adEigenvalues`: PDF p.5, Eq.(18): two eigenvalues, indexed plus then minus.
--   - `adJointEigenvalues`: PDF p.5, Eq.(19): all four joint eigenvalues, including the zero eigenvalues.
--   - `HasSpectrum`: Spectrum as a characteristic-polynomial identity, preserving multiplicities.
--   - `gadDiagonalEigenvalues`: PDF p.4, Eq.(13): the visually checked diagonal-input GAD spectrum.
--   - `entropy4`: PDF p.4, Eq.(12): finite Shannon entropy in bits, with zero terms included.
--   - `gadBlockMatrix`: PDF p.6, Eqs.(25)–(28): printed GAD block matrix, Bob first; phi=0.
--   - `gadBobEigenvalues`: PDF p.6, Eq.(35): Bob's two eigenvalues for general real-coherence input.
--   - `populationMaximum`: PDF p.3: optimize the one-variable entropy formula on the closed population interval.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, https://arxiv.org/abs/0808.0210v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24

/-! Statements from García-Patrón et al., arXiv:0808.0210v2.
PDF pages are used throughout. All entropies and rates are in bits.
The signed reverse-information maximum is distinct from operational capacity.
Local definitions implement only this paper's finite-register model.
Source corrections and deferred claims are recorded in the unit artifacts.
Compilation and independent moderation are pending the batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate
open Filter
open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)
open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)
open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1–3, Eqs.(2),(6): coherent information from the receiver and complement
of one fixed dilation. Theorems require an isometry and a density input. -/
def forwardInfo {I B E : Type} [Fintype I] [Fintype B] [Fintype E]
    [DecidableEq B] [DecidableEq E]
    (V : Matrix (B × E) I ℂ) (rho : Matrix I I ℂ) : ℝ :=
  vnEntropy (receiverChannel V rho) - vnEntropy (complementaryChannel V rho)

/-- PDF pp.2–3, Eq.(6): signed reverse coherent information. For a pure
reference/input purification, S(R)=S(input) and S(RB)=S(E). -/
def reverseInfo {I B E : Type} [Fintype I] [Fintype B] [Fintype E]
    [DecidableEq I] [DecidableEq E]
    (V : Matrix (B × E) I ℂ) (rho : Matrix I I ℂ) : ℝ :=
  vnEntropy rho - vnEntropy (complementaryChannel V rho)

/-- PDF p.3: maximum over normalized density inputs, without max(0,·).
For a nonzero finite input and an isometry this set is nonempty and bounded. -/
def reverseMaximum {I B E : Type} [Fintype I] [Fintype B] [Fintype E]
    [DecidableEq I] [DecidableEq E] (V : Matrix (B × E) I ℂ) : ℝ :=
  sSup {r | ∃ rho : Matrix I I ℂ, IsDensityMatrix rho ∧ r = reverseInfo V rho}

/-- PDF pp.1,3: the forward one-use maximum over normalized density inputs. -/
def forwardMaximum {I B E : Type} [Fintype I] [Fintype B] [Fintype E]
    [DecidableEq B] [DecidableEq E] (V : Matrix (B × E) I ℂ) : ℝ :=
  sSup {r | ∃ rho : Matrix I I ℂ, IsDensityMatrix rho ∧ r = forwardInfo V rho}

/-- PDF p.3: sequential output processing; both environment registers are retained. -/
def composeDilation {I B C E F : Type} [Fintype B]
    (V : Matrix (B × E) I ℂ) (W : Matrix (C × F) B ℂ) :
    Matrix (C × (E × F)) I ℂ :=
  fun cef a => ∑ b, W (cef.1,cef.2.2) b * V (b,cef.2.1) a

/-- PDF p.2: one physical channel use transfers Alice's last input factor to Bob.
The off-diagonal blocks in both retained memories are kept. -/
def channelTransfer {i o : ℕ} (N : Superop (Fin i) (Fin o)) (a b : ℕ) :
    Superop (Fin (a*i) × Fin b) (Fin a × Fin (b*o)) :=
  fun X p q =>
    let u := finProdFinEquiv.symm p.2
    let v := finProdFinEquiv.symm q.2
    N (fun x y => X (finProdFinEquiv (p.1,x),u.1)
      (finProdFinEquiv (q.1,y),v.1)) u.2 v.2

/-- PDF pp.1–2: allowed free classical directions. -/
inductive Assistance where
  | unassisted
  | feedback
  | twoWay
  deriving DecidableEq

/-- PDF p.2, Fig.2: actual finite protocol trees with exactly n channel calls on
each branch, arbitrary finite local memories, and no implicit quantum messages.
Alice can announce outcomes only with two-way assistance; Bob only with feedback
or two-way assistance. Hidden local outcomes are already included in local CPTP maps. -/
inductive Executes {i o : ℕ} (N : Superop (Fin i) (Fin o)) (mode : Assistance) :
    {n a b c d : ℕ} → Superop (Fin a × Fin b) (Fin c × Fin d) → Prop
  | identityStep (a b : ℕ) : Executes N mode (n := 0) (fun X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ => X)
  | localStep {n a b c d h j : ℕ}
      (A : Superop (Fin a) (Fin h)) (B : Superop (Fin b) (Fin j))
      (hA : IsChannel A) (hB : IsChannel B)
      (next : Superop (Fin h × Fin j) (Fin c × Fin d))
      (valid : Executes N mode (n := n) next) :
      Executes N mode (n := n) (fun X => next (tensorAction A B X))
  | aliceStep {n a b c d h k : ℕ} (allowed : mode = .twoWay)
      (K : Fin k → Matrix (Fin h) (Fin a) ℂ) (complete : IsKrausFamily K)
      (next : Fin k → Superop (Fin h × Fin b) (Fin c × Fin d))
      (valid : ∀ t, Executes N mode (n := n) (next t)) :
      Executes N mode (n := n) (fun X => ∑ t, next t
        (conjSuperop (Matrix.kronecker (K t) (1 : Matrix (Fin b) (Fin b) ℂ)) X))
  | bobStep {n a b c d h k : ℕ} (allowed : mode ≠ .unassisted)
      (K : Fin k → Matrix (Fin h) (Fin b) ℂ) (complete : IsKrausFamily K)
      (next : Fin k → Superop (Fin a × Fin h) (Fin c × Fin d))
      (valid : ∀ t, Executes N mode (n := n) (next t)) :
      Executes N mode (n := n) (fun X => ∑ t, next t
        (conjSuperop (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (K t)) X))
  | channelStep {n a b c d : ℕ}
      (next : Superop (Fin a × Fin (b*o)) (Fin c × Fin d))
      (valid : Executes N mode (n := n) next) :
      Executes N mode (n := n+1) (fun X => next (channelTransfer N a b X))

/-- PDF p.2, Fig.3: a parallel input prepared entirely by Alice, followed by one
Bob-to-Alice classical message. Bob's finite complete instrument may retain quantum
memory; a conditional Alice channel finishes the protocol. No prior shared state. -/
def ReverseOutput {i o : ℕ} (N : Superop (Fin i) (Fin o))
    (n d : ℕ) (out : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ∃ a k j : ℕ, ∃ rho : Matrix (Fin a × (Fin n → Fin i)) _ ℂ,
    IsDensityMatrix rho ∧
    ∃ K : Fin k → Matrix (Fin j) (Fin n → Fin o) ℂ, IsKrausFamily K ∧
    ∃ A : Fin k → Superop (Fin a) (Fin d), (∀ t, IsChannel (A t)) ∧
    ∃ B : Superop (Fin j) (Fin d), IsChannel B ∧
    out = ∑ t, tensorAction (A t) B
      (conjSuperop (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (K t))
        (idTensorSuperop (piSuperop (fun _ : Fin n => N)) rho))

/-- PDF pp.1–2: actual n-use shared output from a product singleton laboratory
state. The protocol itself is quantified before execution. -/
def ProtocolOutput {i o : ℕ} (N : Superop (Fin i) (Fin o)) (mode : Assistance)
    (n d : ℕ) (out : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ∃ P : Superop (Fin 1 × Fin 1) (Fin d × Fin d),
    Executes N mode (n := n) P ∧ out = P (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)

/-- PDF pp.1–2: rate r ebits per physical use, vanishing full-state trace-norm
error, arbitrary finite block memory, and positive block lengths and target sizes. -/
def EntanglementRateAchievable (output : (n d : ℕ) → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → Prop)
    (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ eps : ℝ, 0 < eps → ∀ delta : ℝ, 0 < delta →
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0, ∃ d : ℕ, 0 < d ∧
      (r-delta) * (n : ℝ) ≤ Real.logb 2 d ∧
      ∃ out, output n d out ∧ traceNorm (out - entangledPhi (Fin d)) ≤ eps

/-- PDF pp.1–2: extended operational supremum, explicitly including rate zero.
This definition never clips the signed entropy objective. -/
def operationalSup (output : (n d : ℕ) → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → Prop) :
    EReal := sSup ({0} ∪ {r | ∃ s : ℝ, EntanglementRateAchievable output s ∧ r = (s : EReal)})

/-- PDF pp.1–2: unassisted, feedback, or two-way entanglement-generation capacity. -/
def entanglementCapacity {i o : ℕ} (N : Superop (Fin i) (Fin o)) (mode : Assistance) : EReal :=
  operationalSup (ProtocolOutput N mode)

/-- PDF p.2, Fig.3: reverse-protocol operational capacity E_triangle. -/
def reverseCapacity {i o : ℕ} (N : Superop (Fin i) (Fin o)) : EReal :=
  operationalSup (ReverseOutput N)

/-- PDF p.3, Eq.(8): survival-parameter amplitude-damping Kraus family. -/
def adKraus (eta : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, (Real.sqrt eta : ℂ)], !![0, (Real.sqrt (1-eta) : ℂ); 0, 0]]

/-- PDF p.3, Eq.(8): fixed normalized dilation for 0≤eta≤1. -/
def adDilation (eta : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
  fun be a => adKraus eta be.2 be.1 a

/-- PDF p.3: the actual amplitude-damping map on every operator. -/
def adChannel (eta : ℝ) : Superop (Fin 2) (Fin 2) := krausApply (adKraus eta)

/-- PDF pp.3–4, Eq.(10): thermal GAD Kraus family, with environment excited
population alpha. Corrects the reversed coefficients in the p.3 prose mixture:
alpha=0 is AD, consistently with Eqs.(11),(26)–(28). -/
def gadKraus (eta alpha : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  ![(Real.sqrt (1-alpha) : ℂ) • adKraus eta 0,
    (Real.sqrt (1-alpha) : ℂ) • adKraus eta 1,
    (Real.sqrt alpha : ℂ) • (X * adKraus eta 0 * X),
    (Real.sqrt alpha : ℂ) • (X * adKraus eta 1 * X)]

/-- PDF pp.3–4: GAD dilation retains the full four-dimensional pure environment. -/
def gadDilation (eta alpha : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2) ℂ :=
  fun be a => gadKraus eta alpha be.2 be.1 a

/-- PDF pp.3–4, Eq.(10): thermal GAD channel, on all operators. -/
def gadChannel (eta alpha : ℝ) : Superop (Fin 2) (Fin 2) := krausApply (gadKraus eta alpha)

/-- PDF p.3: population p denotes the excited-state probability. -/
def diagonalInput (p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(1-p : ℝ), p]

/-- PDF pp.4–5, Eqs.(14)–(15): the actual normalized purification, reference first.
The positive phase agrees with (15); conjugation gives the negative phase in (14). -/
def inputPurification (p theta phi : ℝ) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun ra =>
    if ra.2 = 0 then (if ra.1 = 0 then (Real.sqrt (1-p) : ℂ) else 0)
    else (Real.sqrt p : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) *
      (if ra.1 = 0 then (Real.cos theta : ℂ) else (Real.sin theta : ℂ))

/-- PDF p.4, Eq.(14): input obtained by tracing the reference from (15). -/
def generalInput (p theta phi : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  traceLeft (pureDensity (inputPurification p theta phi))

/-- PDF pp.5–6, Eqs.(16),(25): output constructed by applying the channel to (15).
Coordinates are Bob first, reference second, as in the displayed matrices. -/
def dampingJointOutput (N : Superop (Fin 2) (Fin 2)) (p theta phi : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun br cs => idTensorSuperop N (pureDensity (inputPurification p theta phi))
    (br.2,br.1) (cs.2,cs.1)

/-- PDF p.5, Eq.(18): two eigenvalues, indexed plus then minus. -/
def adEigenvalues (x p theta : ℝ) : Fin 2 → ℝ :=
  let t := Real.sqrt ((1-2*x*p)^2 + 4*x*(1-p)*p*(Real.cos theta)^2)
  ![(1+t)/2, (1-t)/2]

/-- PDF p.5, Eq.(19): all four joint eigenvalues, including the zero eigenvalues. -/
def adJointEigenvalues (eta p theta : ℝ) : Fin 4 → ℝ :=
  ![adEigenvalues (1-eta) p theta 0, adEigenvalues (1-eta) p theta 1, 0, 0]

/-- Spectrum as a characteristic-polynomial identity, preserving multiplicities. -/
def HasSpectrum {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    (rho : Matrix I I ℂ) (lambda : Fin k → ℝ) : Prop :=
  rho.charpoly = ∏ j, (Polynomial.X - Polynomial.C (lambda j : ℂ))

/-- PDF p.4, Eq.(13): the visually checked diagonal-input GAD spectrum. -/
def gadDiagonalEigenvalues (eta alpha p : ℝ) : Fin 4 → ℝ :=
  let u := alpha*(1-eta)*(1-p)
  let v := (1-alpha)*(1-eta)*p
  let t := Real.sqrt (1-2*(u+v)+(v-u)^2)
  ![u, v, (1-u-v+t)/2, (1-u-v-t)/2]

/-- PDF p.4, Eq.(12): finite Shannon entropy in bits, with zero terms included. -/
def entropy4 (lambda : Fin 4 → ℝ) : ℝ := -∑ j, lambda j * Real.logb 2 (lambda j)

/-- PDF p.6, Eqs.(25)–(28): printed GAD block matrix, Bob first; phi=0. -/
def gadBlockMatrix (eta alpha p theta : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  let c := Real.cos theta
  let s := Real.sin theta
  let Z : Matrix (Fin 2) (Fin 2) ℂ :=
    !![((1-p)*alpha*eta+(1-alpha)*(1-p+p*(1-eta)*c^2) : ℝ),
      (p*(1-alpha)*(1-eta)*c*s : ℝ);
      (p*(1-alpha)*(1-eta)*c*s : ℝ), (p*(1-alpha)*(1-eta)*s^2 : ℝ)]
  let W : Matrix (Fin 2) (Fin 2) ℂ :=
    !![(alpha*(1-p)*(1-eta)+p*(alpha+(1-alpha)*eta)*c^2 : ℝ),
      (p*(alpha+(1-alpha)*eta)*c*s : ℝ);
      (p*(alpha+(1-alpha)*eta)*c*s : ℝ), (p*(alpha+(1-alpha)*eta)*s^2 : ℝ)]
  let C : Matrix (Fin 2) (Fin 2) ℂ :=
    !![(Real.sqrt (eta*(1-p)*p)*c : ℝ), (Real.sqrt (eta*(1-p)*p)*s : ℝ); 0, 0]
  fun u v => if u.1 = 0 then (if v.1 = 0 then Z u.2 v.2 else C u.2 v.2)
    else (if v.1 = 0 then C v.2 u.2 else W u.2 v.2)

/-- PDF p.6, Eq.(35): Bob's two eigenvalues for general real-coherence input. -/
def gadBobEigenvalues (eta alpha p theta : ℝ) : Fin 2 → ℝ :=
  let t := Real.sqrt ((1-2*(p*eta+alpha*(1-eta)))^2 +
    4*eta*p*(1-p)*(Real.cos theta)^2)
  ![(1+t)/2, (1-t)/2]

/-- PDF p.3: optimize the one-variable entropy formula on the closed population interval. -/
def populationMaximum (f : ℝ → ℝ) : ℝ := sSup {r | ∃ p ∈ Set.Icc (0 : ℝ) 1, r = f p}

/-- A memoryless zero-fold dilation has its unique entry equal to one. -/
example {I B E : Type} (V : Matrix (B × E) I ℂ)
    (b : Fin 0 → B) (e : Fin 0 → E) (a : Fin 0 → I) :
    dilationPower V 0 (b,e) a = 1 := by simp [dilationPower]

/-- Identity execution uses zero physical calls. -/
example {i o : ℕ} (N : Superop (Fin i) (Fin o)) (mode : Assistance) :
    Executes N mode (n := 0) (fun X : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ => X) :=
  Executes.identityStep 1 1

/-- A ground-state input is untouched by AD's no-emission Kraus operator. -/
example (eta : ℝ) : adKraus eta 0 0 0 = 1 := rfl

/-- Thermal population alpha=0 eliminates the heating Kraus operators. -/
example (eta : ℝ) : gadKraus eta 0 2 = 0 := by simp [gadKraus]

/-- The population convention places p in the excited diagonal entry. -/
example (p : ℝ) : diagonalInput p 1 1 = (p : ℂ) := rfl

/-- The two null joint eigenvalues in (19) are retained. -/
example (eta p theta : ℝ) : adJointEigenvalues eta p theta 2 = 0 := rfl

/-- The declared diagonal GAD eigenvalues retain the erasure branches. -/
example (eta alpha p : ℝ) : gadDiagonalEigenvalues eta alpha p 0 = alpha*(1-eta)*(1-p) := rfl

/-- The signed objective has no clipping. -/
example {a b e : ℕ} (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (rho : Matrix (Fin a) (Fin a) ℂ) :
    reverseInfo V rho = vnEntropy rho - vnEntropy (complementaryChannel V rho) := rfl

end QAlgorithms.Papers.Independent.Gap20.P17


