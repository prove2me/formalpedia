-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P21
-- name    : QAlgorithms_Papers_Independent_Gap48_P21
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T22:12:02.55388+00:00
-- url     : https://prove2.me/theorems/622c02c9-fea5-4ef9-ae44-662f2a57d405
-- title:
--   Definitions for Entanglement-Assisted Classical Capacity of Noisy Quantum Channels
-- statement:
--   The objects the formalized statements of *Entanglement-Assisted Classical Capacity of Noisy Quantum Channels* (arXiv:quant-ph/9904023) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `accessibleValues`: PDF p.2, Fig.1b: all single-use accessible mutual information values. The finite ensemble, normalized states and POVM precede the sampled input.
--   - `oneShotCapacity`: PDF p.2: C1 optimizes actual input/output classical mutual information.
--   - `symmetricEntropy`: PDF p.2, Eq.(1): one probability p and d-1 equal remaining probabilities. Only d>=2 and p in [0,1] occur in statements; zero log zero contributes zero.
--   - `basisProjector`: PDF p.2: the projectors of an arbitrary orthonormal basis.
--   - `basisInformation`: PDF p.2, Eq.(1): the uniform basis preparation and same-basis measurement.
--   - `randomizing`: PDF pp.2--3: replacement by a uniform symbol with probability x.
--   - `classicalErasure`: PDF p.3: a classical erasure has exactly one additional flag.
--   - `kernelCapacity`: PDF pp.1--3: Shannon capacity of an actual classical arm. Invalid kernels have a zero total extension and are excluded wherever used as simulators.
--   - `encodedBell`: PDF p.3, Fig.2a: Alice applies W_s to the accepted normalized Bell resource; Bob is first.
--   - `denseKernel`: PDF p.3, Fig.2a: the fixed dense-coding encoder and Bell decoder.
--   - `denseRate`: PDF p.3: C_Sd is the capacity of this specific induced classical channel.
--   - `teleportMap`: PDF p.3, Fig.2b: actual teleportation with classical transition matrix P. Bell measurement convention: outcome s has subchannel W_s† X W_s/d²; the receiver applies W_t. Thus a noiseless arm gives the identity channel.
--   - `measurePrepare`: PDF p.2, Fig.1c: Haar-random common basis, basis measurement, classical arm, and preparation in the same common basis. Complex traces extend the physical map linearly to all operators, including off-diagonal reference blocks.
--   - `erasureBellEffect`: PDF p.3: Bell measurement on the surviving sector, one flag on the erased sector. The reference is first and the channel output is second.
--   - `erasureDenseKernel`: PDF p.3: actual dense coding through a quantum erasure channel.
--   - `erasureTeleportMap`: PDF p.3: teleportation using a classical arm with an erasure output. On a flag Bob produces the orthogonal erasure symbol, not a d-dimensional state.
--   - `replaceFlag`: PDF p.3: the receiver's actual replacement map, retained although the full capacity-reduction node is deferred because its Q2 interface is missing.
--   - `EbitTransmissionCode`: PDF pp.1,4: a quantum transmission code with e prior EPR pairs, no classical side channel, arbitrary local CPTP maps and n counted parallel channel uses.
--   - `quantumCodeMap`: PDF p.4: actual effective quantum channel; the resource is independent of all unknown states. The first register belongs to Bob throughout.
--   - `EbitTransmissionAchievable`: PDF p.4: arbitrary e for QE. One code precedes EVERY unit input vector. Fidelity tends uniformly to one, and the block rate is k/n in qubits.
--   - `ebitTransmissionCapacity`: PDF p.4: QE is an independently operational supremum, not CE/2. Unassisted Q is imported from the accepted operational transmission definition.
--   - `SourceClassicalFamily`: PDF p.4, note [4]: only the actual symmetric and erasure families used here, up to fixed alphabet bijections; no invented general class of symmetric DMCs.
--   - `RandomCodebook`: PDF p.4, note [4]: a finite random codebook, chosen independently of input. Every book is nonempty and has an explicit fallback member; at most 2^b output words permit a fixed b-bit index message. Shared randomness is unrestricted.
--   - `bookConditional`: PDF p.4, note [4]: native block probabilities renormalized inside the chosen book. If its mass is zero, output the designated member rather than zero mass.
--   - `bookAverage`: PDF p.4, note [4]: average shared randomness BEFORE comparing with the target.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, https://arxiv.org/abs/quant-ph/9904023v5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

/-!
Bennett--Shor--Smolin--Thapliyal, arXiv:quant-ph/9904023v5.
All locators refer to PDF pages. Capacities are operational; C1 is accessible
information, not Holevo information. The noise range is always [0,1].
Compilation and independent moderation are pending the batch handoff.
-/

-- Match the transparency setting used by the accepted Haar-measure module.
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.Elementwise
open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Gap48.P21

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

-- Reuse the finite Pi-space extended norm explicitly. Matrix has the same
-- product topology, but the generic instance search did not bridge the alias.
local instance matrixContinuousENorm (d : ℕ) :
    ContinuousENorm (Matrix (Fin d) (Fin d) ℂ) :=
  inferInstanceAs (ContinuousENorm (Fin d → Fin d → ℂ))

open QAlgorithms.Papers.Independent.Dependency50.P45
  (resourceCapacity standardEbit DMC shannonCapacity blockProb)
open QAlgorithms.Papers.Independent.Claimed50.P43 (finiteWeyl chaotic)
open QAlgorithms.Papers.Independent.Information100.P58 (singleErasure)
open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

-- CE uses resourceCapacity standardEbit directly; C uses the same accepted
-- operational capacity with the one-dimensional product resource.
open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

/-- PDF p.2, Fig.1b: all single-use accessible mutual information values.
The finite ensemble, normalized states and POVM precede the sampled input. -/
def accessibleValues {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : Set ℝ :=
  {v | ∃ (m l : ℕ) (q : Fin m → ℝ) (rho : Fin m → Matrix A A ℂ)
      (M : Fin l → Matrix B B ℂ),
    (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧ (∀ i, IsDensityMatrix (rho i)) ∧
    IsPOVM M ∧ v = mutualInfoBits (fun z : Fin m × Fin l =>
      q z.1 * effectProb (M z.2) (N (rho z.1)))}

/-- PDF p.2: C1 optimizes actual input/output classical mutual information. -/
def oneShotCapacity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : ℝ :=
  sSup (accessibleValues N)

/-- PDF p.2, Eq.(1): one probability p and d-1 equal remaining probabilities.
Only d>=2 and p in [0,1] occur in statements; zero log zero contributes zero. -/
def symmetricEntropy (d : ℕ) (p : ℝ) : ℝ :=
  -p * Real.logb 2 p - (1-p) * Real.logb 2 ((1-p) / (d-1 : ℕ))

/-- PDF p.2: the projectors of an arbitrary orthonormal basis. -/
def basisProjector {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket i))

/-- PDF p.2, Eq.(1): the uniform basis preparation and same-basis measurement. -/
def basisInformation {d : ℕ} (N : Superop (Fin d) (Fin d))
    (U : Matrix.unitaryGroup (Fin d) ℂ) : ℝ :=
  mutualInfoBits (fun z : Fin d × Fin d =>
    (d : ℝ)⁻¹ * effectProb (basisProjector U z.2) (N (basisProjector U z.1)))

/-- PDF pp.2--3: replacement by a uniform symbol with probability x. -/
def randomizing {A : Type*} [Fintype A] [DecidableEq A] (x : ℝ) : A → A → ℝ :=
  fun a b => (if a = b then 1-x else 0) + x / Fintype.card A

/-- PDF p.3: a classical erasure has exactly one additional flag. -/
def classicalErasure {A : Type*} [DecidableEq A] (x : ℝ) : A → Option A → ℝ :=
  fun a b => match b with
    | some c => if a = c then 1-x else 0
    | none => x

/-- PDF pp.1--3: Shannon capacity of an actual classical arm. Invalid kernels
have a zero total extension and are excluded wherever used as simulators. -/
def kernelCapacity {X Y : Type} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) : ℝ :=
  if h : IsStochastic P then shannonCapacity ⟨P, (fun x y => (h x).1 y), (fun x => (h x).2)⟩ else 0

/-- PDF p.3, Fig.2a: Alice applies W_s to the accepted normalized Bell resource; Bob is first. -/
def encodedBell (d : ℕ) (hd : 0 < d) (s : Fin d × Fin d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  act (Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ) (finiteWeyl d hd s.1 s.2))
    (QAlgorithms.Papers.Independent.Information100.P22.bell (Fin d))

/-- PDF p.3, Fig.2a: the fixed dense-coding encoder and Bell decoder. -/
def denseKernel (d : ℕ) (hd : 0 < d) (N : Superop (Fin d) (Fin d)) :
    (Fin d × Fin d) → (Fin d × Fin d) → ℝ :=
  fun s t => effectProb (pureDensity (encodedBell d hd t))
    (idTensorSuperop N (pureDensity (encodedBell d hd s)))

/-- PDF p.3: C_Sd is the capacity of this specific induced classical channel. -/
def denseRate (d : ℕ) (hd : 0 < d) (N : Superop (Fin d) (Fin d)) : ℝ :=
  kernelCapacity (denseKernel d hd N)

/-- PDF p.3, Fig.2b: actual teleportation with classical transition matrix P.
Bell measurement convention: outcome s has subchannel W_s† X W_s/d²;
the receiver applies W_t. Thus a noiseless arm gives the identity channel. -/
def teleportMap (d : ℕ) (hd : 0 < d)
    (P : (Fin d × Fin d) → (Fin d × Fin d) → ℝ) : Superop (Fin d) (Fin d) :=
  fun X => ∑ s, ∑ t, ((P s t / (d : ℝ)^2 : ℝ) : ℂ) •
    conjSuperop (finiteWeyl d hd t.1 t.2 * (finiteWeyl d hd s.1 s.2)ᴴ) X

/-- PDF p.2, Fig.1c: Haar-random common basis, basis measurement, classical arm,
and preparation in the same common basis. Complex traces extend the physical
map linearly to all operators, including off-diagonal reference blocks. -/
def measurePrepare (d : ℕ) (P : Fin d → Fin d → ℝ) : Superop (Fin d) (Fin d) :=
  fun X => ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    ∑ i, ∑ j, ((P i j : ℂ) * (basisProjector U i * X).trace) • basisProjector U j
    ∂Schur.unitaryHaar d

/-- PDF p.3: Bell measurement on the surviving sector, one flag on the erased
sector. The reference is first and the channel output is second. -/
def erasureBellEffect (d : ℕ) (hd : 0 < d) (t : Option (Fin d × Fin d)) :
    Matrix (Fin d × Option (Fin d)) (Fin d × Option (Fin d)) ℂ :=
  fun a b => match t, a.2, b.2 with
    | some s, some i, some j => pureDensity (encodedBell d hd s) (a.1,i) (b.1,j)
    | none, none, none => if a.1 = b.1 then 1 else 0
    | _, _, _ => 0

/-- PDF p.3: actual dense coding through a quantum erasure channel. -/
def erasureDenseKernel (d : ℕ) (hd : 0 < d) (x : ℝ) :
    (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ :=
  fun s t => effectProb (erasureBellEffect d hd t)
    (idTensorSuperop (singleErasure d x) (pureDensity (encodedBell d hd s)))

/-- PDF p.3: teleportation using a classical arm with an erasure output.
On a flag Bob produces the orthogonal erasure symbol, not a d-dimensional state. -/
def erasureTeleportMap (d : ℕ) (hd : 0 < d)
    (P : (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ) :
    Superop (Fin d) (Option (Fin d)) :=
  fun X a b => match a,b with
    | some i, some j => (teleportMap d hd (fun s t => P s (some t)) X) i j
    | none, none => (((∑ s, P s none) / (d : ℝ)^2 : ℝ) : ℂ) * X.trace
    | _, _ => 0

/-- PDF p.3: the receiver's actual replacement map, retained although the full
capacity-reduction node is deferred because its Q2 interface is missing. -/
def replaceFlag (d : ℕ) : Superop (Option (Fin d)) (Fin d) :=
  fun X i j => X (some i) (some j) + if i = j then X none none / d else 0

/-- PDF pp.1,4: a quantum transmission code with e prior EPR pairs, no classical
side channel, arbitrary local CPTP maps and n counted parallel channel uses. -/
structure EbitTransmissionCode (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (n k e : ℕ) where
  encode : Superop (Qubits k × Qubits e) (Fin n → A)
  encode_channel : IsChannel encode
  decode : Superop (Qubits e × (Fin n → B)) (Qubits k)
  decode_channel : IsChannel decode

/-- PDF p.4: actual effective quantum channel; the resource is independent of
all unknown states. The first register belongs to Bob throughout. -/
def quantumCodeMap {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {n k e : ℕ}
    (N : Superop A B) (P : EbitTransmissionCode A B n k e) : Superop (Qubits k) (Qubits k) :=
  fun rho => P.decode (idTensorSuperop (piSuperop (fun _ : Fin n => N))
    (idTensorSuperop P.encode
      (fun a b => rho a.2.1 b.2.1 * pureDensity (maxEntangled e) (a.1,a.2.2) (b.1,b.2.2))))

/-- PDF p.4: arbitrary e for QE. One code precedes EVERY unit input
vector. Fidelity tends uniformly to one, and the block rate is k/n in qubits. -/
def EbitTransmissionAchievable {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ,
    ∀ n ≥ n0, 0 < n → ∃ k e : ℕ, (R-delta)*n ≤ k ∧
      ∃ P : EbitTransmissionCode A B n k e,
        ∀ psi : EuclideanSpace ℂ (Qubits k), ‖psi‖ = 1 →
          1-eps ≤ effectProb (pureDensity psi) (quantumCodeMap N P (pureDensity psi))

/-- PDF p.4: QE is an independently operational supremum, not CE/2.
Unassisted Q is imported from the accepted operational transmission definition. -/
def ebitTransmissionCapacity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : ℝ :=
  sSup {R | EbitTransmissionAchievable N R}

/-- PDF p.4, note [4]: only the actual symmetric and erasure families used here,
up to fixed alphabet bijections; no invented general class of symmetric DMCs. -/
def SourceClassicalFamily {X Y : Type*} [Fintype X] [Fintype Y]
    (N : DMC X Y) : Prop :=
  ∃ d : ℕ, 2 ≤ d ∧ ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧
    ((∃ (e : X ≃ Fin d) (f : Y ≃ Fin d),
       ∀ a b, N.prob a b = randomizing x (e a) (f b)) ∨
     (∃ (e : X ≃ Fin d) (f : Y ≃ Option (Fin d)),
       ∀ a b, N.prob a b = classicalErasure x (e a) (f b)))

/-- PDF p.4, note [4]: a finite random codebook, chosen independently of input.
Every book is nonempty and has an explicit fallback member; at most 2^b output
words permit a fixed b-bit index message. Shared randomness is unrestricted. -/
structure RandomCodebook (Y : Type*) [Fintype Y] (n b : ℕ) where
  r : ℕ
  weight : Fin r → ℝ
  nonnegative : ∀ i, 0 ≤ weight i
  normalized : ∑ i, weight i = 1
  words : Fin r → Finset (Fin n → Y)
  fallback : Fin r → (Fin n → Y)
  fallback_mem : ∀ i, fallback i ∈ words i
  budget : ∀ i, (words i).card ≤ 2^b

/-- PDF p.4, note [4]: native block probabilities renormalized inside the chosen
book. If its mass is zero, output the designated member rather than zero mass. -/
def bookConditional {X Y : Type*} [Fintype Y] {n b : ℕ}
    (N : DMC X Y) (P : RandomCodebook Y n b) (i : Fin P.r)
    (x : Fin n → X) (y : Fin n → Y) : ℝ :=
  let mass := ∑ z ∈ P.words i, blockProb N n x z
  if mass = 0 then (if y = P.fallback i then 1 else 0)
  else if y ∈ P.words i then blockProb N n x y / mass else 0

/-- PDF p.4, note [4]: average shared randomness BEFORE comparing with the target. -/
def bookAverage {X Y : Type*} [Fintype Y] {n b : ℕ}
    (N : DMC X Y) (P : RandomCodebook Y n b)
    (x : Fin n → X) (y : Fin n → Y) : ℝ :=
  ∑ i, P.weight i * bookConditional N P i x y

/-! Sanity examples for the paper-local interfaces. -/

example : symmetricEntropy 2 1 = 0 := by simp [symmetricEntropy]

example : symmetricEntropy 2 0 = 0 := by simp [symmetricEntropy]

example {A : Type*} [Fintype A] [DecidableEq A] (a b : A) :
    randomizing 0 a b = if a = b then 1 else 0 := by simp [randomizing]

example (d : ℕ) (P : Fin d → Fin d → ℝ) : measurePrepare d P 0 = 0 := by
  simp [measurePrepare]

example (d : ℕ) : replaceFlag d 0 = 0 := by
  funext i j
  simp [replaceFlag]

example (d : ℕ) (hd : 0 < d) (X : Matrix (Fin d) (Fin d) ℂ) :
    erasureTeleportMap d hd (fun _ _ => 0) X = 0 := by
  funext a b
  cases a <;> cases b <;> simp [erasureTeleportMap, teleportMap]

example {X Y : Type*} [Fintype Y] {n b : ℕ} (N : DMC X Y)
    (P : RandomCodebook Y n b) (i : Fin P.r) (x : Fin n → X)
    (h : ∑ z ∈ P.words i, blockProb N n x z = 0) :
    bookConditional N P i x (P.fallback i) = 1 := by
  simp [bookConditional, h]

end QAlgorithms.Papers.Independent.Gap48.P21


