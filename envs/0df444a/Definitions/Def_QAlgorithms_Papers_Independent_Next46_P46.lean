-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P46
-- name    : QAlgorithms_Papers_Independent_Next46_P46
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:57:35.609335+00:00
-- url     : https://prove2.me/theorems/587b9ee8-49eb-4200-be88-3ec115c15544
-- title:
--   Definitions for Relating quantum privacy and quantum coherence: an operational approach
-- statement:
--   The objects the formalized statements of *Relating quantum privacy and quantum coherence: an operational approach* (arXiv:quant-ph/0307053) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `dephased`: PDF p.2, (1): the dephased source, distinguished from the coherent source.
--   - `classicalCosts`: PDF p.2: the two classical-information costs used in static protocols.
--   - `dilationCopies`: PDF p.1: n independent uses of the same dilation; entangled inputs are allowed.
--   - `idealKey`: PDF p.1: a uniform, perfectly correlated classical key independent of the rest.
--   - `measurementBlock`: PDF p.1: unnormalized conditional block after measuring the first register. This is Tr_A[(F tensor I)rho], including off-diagonal matrix entries.
--   - `StaticKeyProtocol`: PDF pp.1,3: a complete one-way private protocol; Bob knows only the public l. The complete Alice POVM incorporates type selection, failures, and concentration.
--   - `StaticKeyProtocol.Valid`: PDF p.1: no initial assistance, complete local operations, only forward messages.
--   - `StaticKeyProtocol.output`: PDF pp.1,3: the actual joint key/key/transcript/E state; Eve receives l.
--   - `StaticKeyProtocol.Good`: PDF p.1: joint trace-norm correctness, uniformity and secrecy, not a leakage surrogate.
--   - `PrivateProtocol`: PDF p.1: unassisted dynamic private encoding and one fixed Bob POVM.
--   - `PrivateProtocol.Valid`: PDF pp.1,3: legality independent of the random uniform message.
--   - `PrivateProtocol.output`: PDF p.3: the actual dynamic joint key/key/E state, with no public side information.
--   - `PrivateProtocol.Good`: PDF pp.1,3: one arbitrary common environmental state; no unjustified sigma^n target.
--   - `GenerationProtocol`: PDF pp.1,3: pure Alice-side preparation and a Bob isometry with a retained ancilla.
--   - `GenerationProtocol.Valid`: PDF p.3: the decoder isometry includes its standard-state ancilla and corrections.
--   - `GenerationProtocol.outputVector`: PDF p.3, (4)--(5): actual coherent output, retaining Bob's entire residual system and E.
--   - `GenerationProtocol.Good`: PDF p.3: decoupling from the full residual B'E state, in trace norm.
--   - `RetainedEntProtocol`: PDF pp.1,4: a dilation of an accepted one-way protocol, retaining its local environments. Alice's complete instrument data are imported, not restated.
--   - `RetainedEntProtocol.toProtocol`: PDF p.4: forgetting the local environments gives the accepted EntProtocol. Bob's retained-register slices are exactly the Kraus operators of this channel.
--   - `RetainedEntProtocol.Valid`: PDF p.4: validity comes from the imported complete instrument/channel model. Positive retained dimensions exclude empty ancillary registers.
--   - `RetainedEntProtocol.branchVector`: PDF p.4: a subnormalized pure branch, with both local environments retained.
--   - `RetainedEntProtocol.output`: PDF p.1: the public l is copied to Eve; coherence of unobserved Kraus labels is kept.
--   - `RetainedEntProtocol.Good`: PDF pp.1,4: EPR output decoupled from transcripts and all retained environments.
--   - `StaticPrivateAchievable`: PDF p.1: positive blocklengths and all positive error/rate slacks. Negative coherent information imposes no positive resource demand.
--   - `StaticQuantumAchievable`: PDF p.1: one-way static quantum achievability, with complete evaluated protocols.
--   - `DynamicPrivateAchievable`: PDF p.1: unassisted dynamic private achievability, code before its random message.
--   - `DynamicQuantumAchievable`: PDF p.1: unassisted dynamic quantum achievability, including ancillary decoupling.
--   - `fourierCoefficient`: PDF p.4: positive Fourier phase and normalization, with zero-based residues.
--   - `fourierBranch`: PDF p.4: the unnormalized Fourier measurement branch of the duplicated-label state.
--   - `correctedBranch`: PDF p.4: the positive phase shift on Bob's s register cancels the measurement bra.
--   - `erasedVector`: PDF p.3, (5): normalized target after erasing Alice's duplicated s label.
--   - `fourierCode`: PDF p.4: Fourier code vectors, transforming s separately in each message block.
--   - `SplitProtocol`: PDF p.4: an actual split instrument. The first public register is l; the second is the Fourier outcome t in Fin s. Unobserved a is an ancillary Kraus label. No disjointness or completeness is inferred from a collection of covering sets.
--   - `SplitProtocol.toEntProtocol`: PDF p.4: the actual sequential Fourier-measurement/feed-forward map, packed into the one-way protocol interface. The message is (l,t), not a free cost.
--   - `SplitProtocol.Valid`: PDF p.4: completeness of the first measurement, positive ancillary dimensions, and an isometric coherent decoder. The final packed instrument is also checked.
--   - `codePreparation`: PDF p.3, (3)--(4): coherent superpositions of orthonormal channel-input words. Phases are selected with the code, absorbing the permissible input-vector phases.
--   - `CoherentGenerationData`: PDF p.3, (3)--(5): finite data for the particular coherent construction. The embedding retains the original channel-output payload plus Bob's ancilla. The m-controlled correction acts on his randomization label and residual payload.
--   - `CoherentGenerationData.Valid`: PDF p.3: legality is algebraic, without assuming any decoding or secrecy conclusion.
--   - `CoherentGenerationData.uncorrected`: PDF p.3, (4): coherent HSW decoder before the Uhlmann corrections.
--   - `CoherentGenerationData.idealDecoded`: PDF p.3, (5): ideal coherent copying of m,s, retaining the actual dilated codeword.
--   - `CoherentGenerationData.corrected`: PDF p.3: the final decoder applies the m-controlled residual correction after copying.
-- source:
--   Relating quantum privacy and quantum coherence: an operational approach, arXiv:quant-ph/0307053v1, https://arxiv.org/abs/quant-ph/0307053v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

/-!
Devetak--Winter, arXiv:quant-ph/0307053v1. All page numbers are PDF pages.
Only operational achievability is asserted, not optimal single-letter capacities.
The literal PA-subset assertion and the universal Fourier-code performance claim
are deferred in HARD.md. The hashing capacity inequality is recorded as reuse.
The p.4 global mutually-unbiased claim is corrected to its exact block overlap.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P46

open QAlgorithms
open scoped Matrix ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

-- The repair request explicitly authorizes imports from the pinned accepted papers.
open QAlgorithms.Papers.Independent.Information100.P21 (Vec Op)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P22 (bell)
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
open QAlgorithms.Papers.Independent.Frontier30.P12
  (coherentInfo quantumMutualInfo mutualAE marginalAE triCopies EntProtocol RectangularKrausData)
open QAlgorithms.Papers.Independent.Dependency50.P19 (channelSource)
open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation)

/-- PDF p.2, (1): the dephased source, distinguished from the coherent source. -/
def dephased {X B E : Type} (p : X → ℝ) (phi : X → Vec (B × E)) :
    Op (X × (B × E)) :=
  fun z w => if z.1 = w.1 then (p z.1 : ℂ) * pureDensity (phi z.1) z.2 w.2 else 0

/-- PDF p.2: the two classical-information costs used in static protocols. -/
def classicalCosts {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    (p : X → ℝ) (phi : X → Vec (B × E)) : ℝ × ℝ :=
  let rho := dephased p phi
  (shannon p - quantumMutualInfo (marginalAB rho), quantumMutualInfo (marginalAE rho))

/-- PDF p.1: n independent uses of the same dilation; entangled inputs are allowed. -/
def dilationCopies {P B E : Type} (U : Matrix (B × E) P ℂ) (n : ℕ) :
    Matrix ((Fin n → B) × (Fin n → E)) (Fin n → P) ℂ :=
  fun z x => ∏ i, U (z.1 i,z.2 i) (x i)

/-- PDF p.1: a uniform, perfectly correlated classical key independent of the rest. -/
def idealKey {F : Type} (m : ℕ) (theta : Op F) : Op ((Fin m × Fin m) × F) :=
  fun z w => if z.1 = w.1 ∧ z.1.1 = z.1.2 then (m : ℂ)⁻¹ * theta z.2 w.2 else 0

/-- PDF p.1: unnormalized conditional block after measuring the first register.
This is Tr_A[(F tensor I)rho], including off-diagonal matrix entries. -/
def measurementBlock {A B : Type} [Fintype A] (rho : Op (A × B)) (F : Op A) : Op B :=
  fun b c => ∑ a, ∑ a2, F a2 a * rho (a,b) (a2,c)

/-- PDF pp.1,3: a complete one-way private protocol; Bob knows only the public l.
The complete Alice POVM incorporates type selection, failures, and concentration. -/
structure StaticKeyProtocol (A B : Type) (n : ℕ) where
  m : ℕ
  l : ℕ
  alice : Fin l × Fin m → Op (Fin n → A)
  bob : Fin l → Fin m → Op (Fin n → B)

/-- PDF p.1: no initial assistance, complete local operations, only forward messages. -/
def StaticKeyProtocol.Valid {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (C : StaticKeyProtocol A B n) : Prop :=
  0 < C.m ∧ 0 < C.l ∧ IsPOVM C.alice ∧ ∀ l, IsPOVM (C.bob l)

/-- PDF pp.1,3: the actual joint key/key/transcript/E state; Eve receives l. -/
def StaticKeyProtocol.output {A B E : Type} [Fintype A] [Fintype B] {n : ℕ}
    (C : StaticKeyProtocol A B n) (rho : Op (A × (B × E))) :
    Op ((Fin C.m × Fin C.m) × (Fin C.l × (Fin n → E))) :=
  fun z w => if z.1 = w.1 ∧ z.2.1 = w.2.1 then
    measurementBlock (measurementBlock (triCopies rho n) (C.alice (z.2.1,z.1.1)))
      (C.bob z.2.1 z.1.2) z.2.2 w.2.2 else 0

/-- PDF p.1: joint trace-norm correctness, uniformity and secrecy, not a leakage surrogate. -/
def StaticKeyProtocol.Good {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    {n : ℕ} (C : StaticKeyProtocol A B n) (rho : Op (A × (B × E))) (eps : ℝ) : Prop :=
  C.Valid ∧ ∃ theta : Op (Fin C.l × (Fin n → E)), IsDensityMatrix theta ∧
    traceNorm (C.output rho - idealKey C.m theta) ≤ eps

/-- PDF p.1: unassisted dynamic private encoding and one fixed Bob POVM. -/
structure PrivateProtocol (P B : Type) (n : ℕ) where
  m : ℕ
  input : Fin m → Op (Fin n → P)
  bob : Fin m → Op (Fin n → B)

/-- PDF pp.1,3: legality independent of the random uniform message. -/
def PrivateProtocol.Valid {P B : Type} [Fintype P] [Fintype B] {n : ℕ}
    (C : PrivateProtocol P B n) : Prop :=
  0 < C.m ∧ (∀ k, IsDensityMatrix (C.input k)) ∧ IsPOVM C.bob

/-- PDF p.3: the actual dynamic joint key/key/E state, with no public side information. -/
def PrivateProtocol.output {P B E : Type} [Fintype P] [Fintype B] {n : ℕ}
    (C : PrivateProtocol P B n) (U : Matrix (B × E) P ℂ) :
    Op ((Fin C.m × Fin C.m) × (Fin n → E)) :=
  let W := dilationCopies U n
  fun z w => if z.1 = w.1 then (C.m : ℂ)⁻¹ *
    measurementBlock (W * C.input z.1.1 * Wᴴ) (C.bob z.1.2) z.2 w.2 else 0

/-- PDF pp.1,3: one arbitrary common environmental state; no unjustified sigma^n target. -/
def PrivateProtocol.Good {P B E : Type} [Fintype P] [Fintype B] [Fintype E] {n : ℕ}
    (C : PrivateProtocol P B n) (U : Matrix (B × E) P ℂ) (eps : ℝ) : Prop :=
  C.Valid ∧ ∃ theta : Op (Fin n → E), IsDensityMatrix theta ∧
    traceNorm (C.output U - idealKey C.m theta) ≤ eps

/-- PDF pp.1,3: pure Alice-side preparation and a Bob isometry with a retained ancilla. -/
structure GenerationProtocol (P B : Type) (n : ℕ) where
  m : ℕ
  r : ℕ
  input : Vec (Fin m × (Fin n → P))
  bob : Matrix (Fin m × Fin r) (Fin n → B) ℂ

/-- PDF p.3: the decoder isometry includes its standard-state ancilla and corrections. -/
def GenerationProtocol.Valid {P B : Type} [Fintype P] [Fintype B] {n : ℕ}
    (C : GenerationProtocol P B n) : Prop :=
  0 < C.m ∧ 0 < C.r ∧ IsState C.input ∧ C.bobᴴ * C.bob = 1

/-- PDF p.3, (4)--(5): actual coherent output, retaining Bob's entire residual system and E. -/
def GenerationProtocol.outputVector {P B E : Type} [Fintype P] [Fintype B] {n : ℕ}
    (C : GenerationProtocol P B n) (U : Matrix (B × E) P ℂ) :
    Vec ((Fin C.m × Fin C.m) × (Fin C.r × (Fin n → E))) :=
  WithLp.toLp 2 fun z => ∑ x, ∑ b,
    C.input (z.1.1,x) * dilationCopies U n (b,z.2.2) x * C.bob (z.1.2,z.2.1) b

/-- PDF p.3: decoupling from the full residual B'E state, in trace norm. -/
def GenerationProtocol.Good {P B E : Type} [Fintype P] [Fintype B] [Fintype E]
    {n : ℕ} (C : GenerationProtocol P B n) (U : Matrix (B × E) P ℂ) (eps : ℝ) : Prop :=
  C.Valid ∧ ∃ theta : Op (Fin C.r × (Fin n → E)), IsDensityMatrix theta ∧
    traceNorm (pureDensity (C.outputVector U) -
      Matrix.kronecker (pureDensity (bell (Fin C.m))) theta) ≤ eps

/-- PDF pp.1,4: a dilation of an accepted one-way protocol, retaining its
local environments. Alice's complete instrument data are imported, not restated. -/
structure RetainedEntProtocol (A B : Type) (n : ℕ) where
  m : ℕ
  r : ℕ
  alice : RectangularKrausData (Fin n → A) (Fin m)
  bob : Fin alice.l → Matrix (Fin m × Fin r) (Fin n → B) ℂ

/-- PDF p.4: forgetting the local environments gives the accepted EntProtocol.
Bob's retained-register slices are exactly the Kraus operators of this channel. -/
def RetainedEntProtocol.toProtocol {A B : Type} {n : ℕ}
    (C : RetainedEntProtocol A B n) : EntProtocol A B n where
  m := C.m
  alice := C.alice
  bob l := ⟨C.r, fun a m b => C.bob l (m,a) b⟩

/-- Sanity check: the imported Bob channel is exactly the retained isometry
with its residual register read as a Kraus index. -/
example {A B : Type} {n : ℕ} (C : RetainedEntProtocol A B n)
    (l : Fin C.alice.l) (a : Fin C.r) (m : Fin C.m) (b : Fin n → B) :
    ((C.toProtocol.bob l).kraus a) m b = C.bob l (m,a) b := rfl

/-- PDF p.4: validity comes from the imported complete instrument/channel model.
Positive retained dimensions exclude empty ancillary registers. -/
def RetainedEntProtocol.Valid {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (C : RetainedEntProtocol A B n) : Prop :=
  0 < C.alice.k ∧ 0 < C.r ∧ C.toProtocol.Valid

/-- PDF p.4: a subnormalized pure branch, with both local environments retained. -/
def RetainedEntProtocol.branchVector {A B E : Type} [Fintype A] [Fintype B] {n : ℕ}
    (C : RetainedEntProtocol A B n) (psi : Vec (A × (B × E))) (l : Fin C.alice.l) :
    Vec ((Fin C.m × Fin C.m) × (Fin C.alice.k × (Fin C.r × (Fin n → E)))) :=
  WithLp.toLp 2 fun z => ∑ x, ∑ b,
    (∏ i, psi (x i,(b i,z.2.2.2 i))) *
      C.alice.kraus l z.2.1 z.1.1 x * C.bob l (z.1.2,z.2.2.1) b

/-- PDF p.1: the public l is copied to Eve; coherence of unobserved Kraus labels is kept. -/
def RetainedEntProtocol.output {A B E : Type} [Fintype A] [Fintype B] {n : ℕ}
    (C : RetainedEntProtocol A B n) (psi : Vec (A × (B × E))) :
    Op ((Fin C.m × Fin C.m) ×
      (Fin C.alice.l × (Fin C.alice.k × (Fin C.r × (Fin n → E))))) :=
  fun z w => if z.2.1 = w.2.1 then
    pureDensity (C.branchVector psi z.2.1) (z.1,z.2.2) (w.1,w.2.2) else 0

/-- PDF pp.1,4: EPR output decoupled from transcripts and all retained environments. -/
def RetainedEntProtocol.Good {A B E : Type} [Fintype A] [Fintype B] [Fintype E] {n : ℕ}
    (C : RetainedEntProtocol A B n) (psi : Vec (A × (B × E))) (eps : ℝ) : Prop :=
  C.Valid ∧ ∃ theta : Op (Fin C.alice.l × (Fin C.alice.k × (Fin C.r × (Fin n → E)))),
    IsDensityMatrix theta ∧ traceNorm (C.output psi -
      Matrix.kronecker (pureDensity (bell (Fin C.m))) theta) ≤ eps

/-- PDF p.1: positive blocklengths and all positive error/rate slacks.
Negative coherent information imposes no positive resource demand. -/
def StaticPrivateAchievable {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (rho : Op (A × (B × E))) (rate : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧
    ∀ n ≥ n0, ∃ C : StaticKeyProtocol A B n, C.Good rho eps ∧
      rate - delta ≤ Real.logb 2 (C.m : ℝ) / n

/-- PDF p.1: one-way static quantum achievability, with complete evaluated protocols. -/
def StaticQuantumAchievable {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (psi : Vec (A × (B × E))) (rate : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧
    ∀ n ≥ n0, ∃ C : RetainedEntProtocol A B n, C.Good psi eps ∧
      rate - delta ≤ Real.logb 2 (C.m : ℝ) / n

/-- PDF p.1: unassisted dynamic private achievability, code before its random message. -/
def DynamicPrivateAchievable {P B E : Type} [Fintype P] [Fintype B] [Fintype E]
    (U : Matrix (B × E) P ℂ) (rate : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧
    ∀ n ≥ n0, ∃ C : PrivateProtocol P B n, C.Good U eps ∧
      rate - delta ≤ Real.logb 2 (C.m : ℝ) / n

/-- PDF p.1: unassisted dynamic quantum achievability, including ancillary decoupling. -/
def DynamicQuantumAchievable {P B E : Type} [Fintype P] [Fintype B] [Fintype E]
    (U : Matrix (B × E) P ℂ) (rate : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧
    ∀ n ≥ n0, ∃ C : GenerationProtocol P B n, C.Good U eps ∧
      rate - delta ≤ Real.logb 2 (C.m : ℝ) / n

/-- PDF p.4: positive Fourier phase and normalization, with zero-based residues. -/
def fourierCoefficient (s : ℕ) (t j : Fin s) : ℂ :=
  ((Real.sqrt (s : ℝ))⁻¹ : ℂ) *
    Complex.exp (((2 * Real.pi * (j : ℝ) * (t : ℝ) / (s : ℝ) : ℝ) : ℂ) * Complex.I)

/-- PDF p.4: the unnormalized Fourier measurement branch of the duplicated-label state. -/
def fourierBranch {H : Type} {m s : ℕ} (phi : Fin m → Fin s → Vec H) (t : Fin s) :
    Vec ((Fin m × (Fin m × Fin s)) × H) :=
  WithLp.toLp 2 fun z => if z.1.1 = z.1.2.1 then
    ((Real.sqrt ((m : ℝ) * s))⁻¹ : ℂ) *
      conj (fourierCoefficient s t z.1.2.2) * phi z.1.1 z.1.2.2 z.2 else 0

/-- PDF p.4: the positive phase shift on Bob's s register cancels the measurement bra. -/
def correctedBranch {H : Type} {m s : ℕ} (phi : Fin m → Fin s → Vec H) (t : Fin s) :
    Vec ((Fin m × (Fin m × Fin s)) × H) :=
  WithLp.toLp 2 fun z =>
    Complex.exp (((2 * Real.pi * (z.1.2.2 : ℝ) * (t : ℝ) / (s : ℝ) : ℝ) : ℂ) *
      Complex.I) * fourierBranch phi t z

/-- PDF p.3, (5): normalized target after erasing Alice's duplicated s label. -/
def erasedVector {H : Type} {m s : ℕ} (phi : Fin m → Fin s → Vec H) :
    Vec ((Fin m × (Fin m × Fin s)) × H) :=
  WithLp.toLp 2 fun z => if z.1.1 = z.1.2.1 then
    ((Real.sqrt ((m : ℝ) * s))⁻¹ : ℂ) * phi z.1.1 z.1.2.2 z.2 else 0

/-- PDF p.4: Fourier code vectors, transforming s separately in each message block. -/
def fourierCode {H : Type} {m s : ℕ} (v : Fin m × Fin s → Vec H)
    (mt : Fin m × Fin s) : Vec H :=
  ∑ j, fourierCoefficient s mt.2 j • v (mt.1,j)

/-- PDF p.4: an actual split instrument. The first public register is l; the
second is the Fourier outcome t in Fin s. Unobserved a is an ancillary Kraus label.
No disjointness or completeness is inferred from a collection of covering sets. -/
structure SplitProtocol (A B : Type) (n : ℕ) where
  m : ℕ
  l : ℕ
  s : ℕ
  k : ℕ
  r : ℕ
  first : Fin l → Fin k → Matrix (Fin m × Fin s) (Fin n → A) ℂ
  decode : Fin l → Matrix (Fin m × (Fin s × Fin r)) (Fin n → B) ℂ
  correction : Fin l → Fin m → Matrix.unitaryGroup (Fin s × Fin r) ℂ

/-- PDF p.4: the actual sequential Fourier-measurement/feed-forward map,
packed into the one-way protocol interface. The message is (l,t), not a free cost. -/
def SplitProtocol.toEntProtocol {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (C : SplitProtocol A B n) : RetainedEntProtocol A B n where
  m := C.m
  r := C.s * C.r
  alice := ⟨C.l * C.s, C.k, fun lt a m x =>
    let p := finProdFinEquiv.symm lt
    ∑ j, conj (fourierCoefficient C.s p.2 j) * C.first p.1 a (m,j) x⟩
  bob lt mr b :=
    let p := finProdFinEquiv.symm lt
    let q := finProdFinEquiv.symm mr.2
    ∑ z : Fin C.s × Fin C.r,
      (C.correction p.1 mr.1 : Matrix _ _ ℂ) q z *
      Complex.exp (((2 * Real.pi * (z.1 : ℝ) * (p.2 : ℝ) /
        (C.s : ℝ) : ℝ) : ℂ) * Complex.I) * C.decode p.1 (mr.1,z) b

/-- PDF p.4: completeness of the first measurement, positive ancillary dimensions,
and an isometric coherent decoder. The final packed instrument is also checked. -/
def SplitProtocol.Valid {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (C : SplitProtocol A B n) : Prop :=
  0 < C.m ∧ 0 < C.l ∧ 0 < C.s ∧ 0 < C.k ∧ 0 < C.r ∧
    (∑ l, ∑ a, (C.first l a)ᴴ * C.first l a) = 1 ∧
    (∀ l, (C.decode l)ᴴ * C.decode l = 1) ∧ C.toEntProtocol.Valid

/-- PDF p.3, (3)--(4): coherent superpositions of orthonormal channel-input words.
Phases are selected with the code, absorbing the permissible input-vector phases. -/
def codePreparation {P X : Type} {m s n : ℕ} [Fintype X]
    (v : X → Vec P) (u : Fin m × Fin s → (Fin n → X))
    (phase : Fin m → Fin s → ℂ) : Vec (Fin m × (Fin n → P)) :=
  WithLp.toLp 2 fun z => ((Real.sqrt ((m : ℝ) * s))⁻¹ : ℂ) *
    ∑ j, phase z.1 j * ∏ i, v (u (z.1,j) i) (z.2 i)

/-- PDF p.3, (3)--(5): finite data for the particular coherent construction.
The embedding retains the original channel-output payload plus Bob's ancilla.
The m-controlled correction acts on his randomization label and residual payload. -/
structure CoherentGenerationData (X P B : Type) (n : ℕ) where
  m : ℕ
  s : ℕ
  r : ℕ
  word : Fin m × Fin s → (Fin n → X)
  phase : Fin m → Fin s → ℂ
  embed : Matrix (Fin r) (Fin n → B) ℂ
  decode : Matrix (Fin m × (Fin s × Fin r)) (Fin n → B) ℂ
  correction : Fin m → Matrix.unitaryGroup (Fin s × Fin r) ℂ

/-- PDF p.3: legality is algebraic, without assuming any decoding or secrecy conclusion. -/
def CoherentGenerationData.Valid {X P B : Type} [Fintype B] {n : ℕ}
    (C : CoherentGenerationData X P B n) : Prop :=
  0 < C.m ∧ 0 < C.s ∧ 0 < C.r ∧ Function.Injective C.word ∧
    (∀ m j, ‖C.phase m j‖ = 1) ∧ C.embedᴴ * C.embed = 1 ∧ C.decodeᴴ * C.decode = 1

/-- PDF p.3, (4): coherent HSW decoder before the Uhlmann corrections. -/
def CoherentGenerationData.uncorrected {X P B : Type} [Fintype X] {n : ℕ}
    (C : CoherentGenerationData X P B n) (v : X → Vec P) : GenerationProtocol P B n where
  m := C.m
  r := C.s * C.r
  input := codePreparation v C.word C.phase
  bob mr b := C.decode (mr.1,finProdFinEquiv.symm mr.2) b

/-- PDF p.3, (5): ideal coherent copying of m,s, retaining the actual dilated codeword. -/
def CoherentGenerationData.idealDecoded {X P B E : Type}
    [Fintype P] [Fintype B] {n : ℕ} (C : CoherentGenerationData X P B n)
    (v : X → Vec P) (U : Matrix (B × E) P ℂ) :
    Vec ((Fin C.m × Fin C.m) × (Fin (C.s * C.r) × (Fin n → E))) :=
  WithLp.toLp 2 fun z => if z.1.1 = z.1.2 then
    let q := finProdFinEquiv.symm z.2.1
    ((Real.sqrt ((C.m : ℝ) * C.s))⁻¹ : ℂ) * C.phase z.1.1 q.1 *
      ∑ x, ∑ b, (∏ i, v (C.word (z.1.1,q.1) i) (x i)) *
        dilationCopies U n (b,z.2.2) x * C.embed q.2 b
    else 0

/-- PDF p.3: the final decoder applies the m-controlled residual correction after copying. -/
def CoherentGenerationData.corrected {X P B : Type} [Fintype X] {n : ℕ}
    (C : CoherentGenerationData X P B n) (v : X → Vec P) : GenerationProtocol P B n where
  m := C.m
  r := C.s * C.r
  input := codePreparation v C.word C.phase
  bob mr b := ∑ z : Fin C.s × Fin C.r,
    (C.correction mr.1 : Matrix _ _ ℂ) (finProdFinEquiv.symm mr.2) z *
      C.decode (mr.1,z) b

/-- The coherent correction never changes Alice's encoded preparation. -/
example {X P B : Type} [Fintype X] {n : ℕ}
    (C : CoherentGenerationData X P B n) (v : X → Vec P) :
    (C.corrected v).input = (C.uncorrected v).input := rfl

/-- Normalization sanity check: the one-dimensional EPR vector is the scalar 1. -/
example : bell (Fin 1) (0,0) = 1 := by simp [bell]

/-- At zero copies the source tensor product is the scalar 1, never a rate denominator. -/
example {A B E : Type} (rho : Op (A × (B × E)))
    (z w : (Fin 0 → A) × ((Fin 0 → B) × (Fin 0 → E))) :
    triCopies rho 0 z w = 1 := by simp [triCopies]

/-- Zero-weight terms in the dephased source vanish. -/
example {X B E : Type} (p : X → ℝ) (phi : X → Vec (B × E))
    (x : X) (hp : p x = 0) (z w : B × E) :
    dephased p phi (x,z) (x,w) = 0 := by simp [dephased, hp]

/-- The trivial Fourier alphabet uses positive phase 1 and normalization 1. -/
example : fourierCoefficient 1 0 0 = 1 := by simp [fourierCoefficient]

/-- A one-outcome identity effect leaves exactly the unmeasured marginal. -/
example {A B : Type} [Fintype A] (rho : Op (A × B)) :
    measurementBlock rho 1 = traceLeft rho := by
  ext b c
  simp [measurementBlock, traceLeft, Matrix.one_apply]

/-- The size-one Fourier transform leaves each message vector unchanged. -/
example {H : Type} {m : ℕ} (v : Fin m × Fin 1 → Vec H) (a : Fin m) :
    fourierCode v (a,0) = v (a,0) := by
  simp [fourierCode, fourierCoefficient]

end QAlgorithms.Papers.Independent.Next46.P46


