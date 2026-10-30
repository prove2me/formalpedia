-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P49
-- name    : QAlgorithms_Papers_Independent_Extend50_P49
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T21:20:15.05628+00:00
-- url     : https://prove2.me/theorems/4f5cdbb3-c533-4f91-aeb1-c654c423ab89
-- title:
--   Definitions for One-shot Marton inner bound for classical-quantum broadcast channel
-- statement:
--   The objects the formalized statements of *One-shot Marton inner bound for classical-quantum broadcast channel* (arXiv:1410.3248) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AuxiliaryLaw`: Finite normalized law, PDF pp.3,5. Empty alphabets admit no such law.
--   - `extendedLog2`: Base-two logarithm with its extended value at zero, Definitions 3,4,7, PDF pp.5,11. All applications have nonnegative arguments.
--   - `leftLawMarginal`: First marginal of a finite joint weight table, PDF p.5.
--   - `secondMarginal`: Second marginal of a finite joint weight table, PDF p.5.
--   - `setMass`: Probability mass of a subset, Definitions 4,7, PDF pp.5,11.
--   - `logRatio`: Log likelihood ratio, Definition 4, PDF p.5. Zero joint mass has value -infinity; positive joint mass with zero product mass has value +infinity. The latter cannot occur for a normalized nonnegative joint law and its actual marginals.
--   - `strictSmoothMaxInformation`: Definition 4, PDF p.5: STRICT retained mass; original marginals remain fixed. Extended extrema make the empty feasible family at epsilon=0 have value +infinity.
--   - `smoothClassicalMin`: Definition 7, PDF p.11: NON-STRICT retained mass, including epsilon=0. Zero comparison mass contributes +infinity, never Real.log's junk value.
--   - `smoothQuantumMin`: Definition 3, PDF p.5: STRICT quantum acceptance and the actual product marginals. The supremum is extended, so an empty family has value -infinity.
--   - `CqChannel`: Definition 1, PDF p.5, with the printed H_A x H_B corrected to H_B tensor H_C. Arbitrary nonzero finite output dimensions are allowed, including dimension one.
--   - `ClassicalBroadcastChannel`: Definition 5, PDF p.10: arbitrary finite classical transition probabilities.
--   - `inducedState`: Equation (4), PDF p.3: actual cq density matrix from the auxiliary law, map, and channel.
--   - `inducedUB`: U,B marginal of (4), PDF pp.3,6; the other auxiliary and Charlie are traced out.
--   - `inducedVC`: V,C marginal of (4), PDF pp.3,6; the other auxiliary and Bob are traced out.
--   - `inducedUY`: The actual U,Y law in Theorem 4, PDF p.3.
--   - `inducedVZ`: The actual V,Z law in Theorem 4, PDF p.3.
--   - `CqCode`: Definition 2, PDF p.5: fixed deterministic encoder and separate fixed local POVMs.
--   - `cqJointError`: Definition 2, (12), PDF p.5: independent uniform messages and average joint error. Theorems require both message counts positive.
--   - `PrivateClassicalCode`: Definition 6, PDF p.10: deterministic encoding and separate deterministic decoders.
--   - `classicalError`: Definition 6, PDF p.10: actual average probability that either private message is wrong.
--   - `MartonConstraints`: Equations (5)-(7) and (8)-(10), PDF p.3: the three inequalities with constants 5,2,11,5. Rates are literal log2 positive integer message counts; no rounding convention is hidden.
--   - `PositiveBlockWord`: Positive block length k+1, Definitions 8-10, PDF pp.15-17.
--   - `strictPositiveSpectralProjector`: Positive spectral projector, Definition 9's words, PDF p.16.
--   - `spectralAcceptance`: Corrected Definition 9, PDF p.16: sum_u Tr[P_u (p(u) rho_(B|u))]. Printed: Tr[P_u rho_B]; changed: Tr[P_u rho_(B|u)] before weighting by p(u). Why: the printed marginal gives zero limiting mass for orthogonal iid signals, contradicting (47) and the Theorem 6 testing argument, PDF pp.16-17. Using unnormalized blocks avoids division on null auxiliary symbols.
--   - `spectralInfMutualInformation`: Corrected spectral inf quantum information rate, Definition 9, PDF p.16. Extended supremum and an actual limit of acceptance probabilities.
--   - `informationTail`: Probability tail of the information density, Definition 10, PDF p.17. Zero joint mass is excluded before taking a logarithm.
--   - `spectralSupMutualInformation`: Spectral sup classical information rate, Definition 10, PDF p.17. The probability tail tends to zero along the entire sequence.
--   - `SpectrumAchievable`: Definition 8, PDF pp.15-16, corrected second message domain/decoder labels. Counts are positive integers. The two eventual lower bounds express liminf rate constraints without totalized real infima on unbounded sequences.
--   - `Padding`: The four padding constraints (13)-(16), (35)-(38), PDF pp.6,11. The ceiling is integer-valued; the two message rates are log2 actual counts.
--   - `Codebook`: A realization of the source random codebook, PDF pp.7,11-12. Retained bits are exactly the pushforward of the independent uniform rejection coins. Repeated U,V values do not identify different row/column indices.
--   - `rejectionChance`: Rejection acceptance probability (18),(39), PDF pp.7,12. Clipping is exactly the event eta <= ratio for eta uniform on [0,1]. Null marginal rows have sampling probability zero and their coin boundary has measure zero.
--   - `bookWeight`: Computed finite law of the full random codebook, PDF pp.7,11-12. Rows and columns are mutually independent; rejection coins are independent conditional on them. This is the exact finite pushforward law, not an assumption on desired events.
--   - `selectPair`: Lexicographically first good retained pair in the message rectangle, PDF pp.7,12. Global zero-based indices have the same order and bands as the source's one-based indices.
--   - `selectedInput`: Source encoder, PDF pp.7,12: selected codeword, or one fixed input on failure.
--   - `classicalGood`: Classical local test acceptance alpha,beta, PDF p.12.
--   - `ClassicalSetup`: Data fixed before generating a classical random codebook, PDF pp.11-13. Test acceptances and comparison masses are the source test conditions, not event probability bounds. All information values are computed from N,p,f.
--   - `ErrorEvent`: The five events on PDF p.13, without any probability assumptions.
--   - `classicalEvent`: Actual error event for the first message rectangle, PDF p.13. A miss/collision is counted only after a good pair has been selected. Other rows/columns include indices with the same auxiliary symbol, exactly as in the source.
--   - `classicalEventProbability`: Probability of each constructed event over the actual random codebook AND the actual channel output, PDF pp.13-14; messages are fixed at (1,1) by symmetry.
--   - `firstHit`: Actual first-hit index decoder, PDF p.12, retaining row identity, with fixed zero-index fallback. Its band gives the message decoder.
--   - `classicalIndexError`: Classical average failure to recover the actual selected row AND column, PDF pp.12-14. Encoding failure is counted as failure even if fallback decoders agree.
--   - `QuantumSetup`: Quantum construction parameters, PDF pp.6-8. The test effects act on the actual computed U,B and V,C states and satisfy exactly the source acceptance/comparison bounds.
--   - `testBlock`: Diagonal test block (19)-(20), PDF p.7.
--   - `quantumGood`: Quantum pair-selection acceptance tests alpha,beta, PDF p.7.
--   - `completedPgm`: Square-root decoder (21)-(22), PDF p.7, completed on the kernel by assigning the residual projector to fixed index zero. On the support it is precisely S^(-1/2) L_k S^(-1/2). The completion only increases success at that outcome.
--   - `quantumIndexError`: Quantum actual-index error, PDF pp.8-10, with full local index POVMs. A failed encoder is counted as failure; the two receiver probabilities use their actual joint output state, not the product of the marginal states.
-- source:
--   One-shot Marton inner bound for classical-quantum broadcast channel, arXiv:1410.3248v5, https://arxiv.org/abs/1410.3248v5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement

/-!
Radhakrishnan, Sen, Warsi, arXiv:1410.3248v5. PDF page numbers; bits throughout.
Paper-local definitions under the independent-paper override. The joint cq state is
computed, never supplied as an unrelated witness. Definition 9's marginal-weighted
trace is corrected to the conditional-state trace, as explained in the audit.
Compilation is pending the separate batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P49

open QAlgorithms MeasureTheory Filter
open scoped BigOperators Matrix ComplexOrder Topology

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Finite normalized law, PDF pp.3,5. Empty alphabets admit no such law. -/
structure AuxiliaryLaw (A : Type) [Fintype A] where
  prob : A → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  total : ∑ a, prob a = 1

/-- Base-two logarithm with its extended value at zero, Definitions 3,4,7, PDF pp.5,11.
All applications have nonnegative arguments. -/
def extendedLog2 (x : ℝ) : EReal :=
  if 0 < x then (Real.logb 2 x : EReal) else ⊥

/-- First marginal of a finite joint weight table, PDF p.5. -/
def leftLawMarginal {A B : Type} [Fintype B] (p : A × B → ℝ) (a : A) : ℝ :=
  ∑ b, p (a, b)

/-- Second marginal of a finite joint weight table, PDF p.5. -/
def secondMarginal {A B : Type} [Fintype A] (p : A × B → ℝ) (b : B) : ℝ :=
  ∑ a, p (a, b)

/-- Probability mass of a subset, Definitions 4,7, PDF pp.5,11. -/
def setMass {A : Type} [Fintype A] (p : A → ℝ) (G : Finset A) : ℝ :=
  ∑ a ∈ G, p a

/-- Log likelihood ratio, Definition 4, PDF p.5. Zero joint mass has value -infinity;
positive joint mass with zero product mass has value +infinity. The latter cannot
occur for a normalized nonnegative joint law and its actual marginals. -/
def logRatio {A B : Type} [Fintype A] [Fintype B] (p : A × B → ℝ) (ab : A × B) : EReal :=
  if p ab = 0 then ⊥ else
    if leftLawMarginal p ab.1 * secondMarginal p ab.2 = 0 then ⊤ else
      extendedLog2 (p ab / (leftLawMarginal p ab.1 * secondMarginal p ab.2))

/-- Definition 4, PDF p.5: STRICT retained mass; original marginals remain fixed.
Extended extrema make the empty feasible family at epsilon=0 have value +infinity. -/
def strictSmoothMaxInformation {A B : Type} [Fintype A] [Fintype B]
    (p : A × B → ℝ) (epsilon : ℝ) : EReal :=
  sInf {t | ∃ G : Finset (A × B), 1 - epsilon < setMass p G ∧
    t = sSup ((fun ab => logRatio p ab) '' (↑G : Set (A × B)))}

/-- Definition 7, PDF p.11: NON-STRICT retained mass, including epsilon=0.
Zero comparison mass contributes +infinity, never Real.log's junk value. -/
def smoothClassicalMin {A B : Type} [Fintype A] [Fintype B]
    (p : A × B → ℝ) (epsilon : ℝ) : EReal :=
  sSup {t | ∃ G : Finset (A × B), 1 - epsilon ≤ setMass p G ∧
    t = -extendedLog2 (∑ ab ∈ G, leftLawMarginal p ab.1 * secondMarginal p ab.2)}

/-- Definition 3, PDF p.5: STRICT quantum acceptance and the actual product marginals.
The supremum is extended, so an empty family has value -infinity. -/
def smoothQuantumMin {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (epsilon : ℝ) : EReal :=
  sSup {t | ∃ G : Matrix (A × B) (A × B) ℂ,
    IsEffect G ∧ 1 - epsilon < effectProb G rho ∧
    t = -extendedLog2 (effectProb G (Matrix.kronecker (traceRight rho) (traceLeft rho)))}

/-- Definition 1, PDF p.5, with the printed H_A x H_B corrected to H_B tensor H_C.
Arbitrary nonzero finite output dimensions are allowed, including dimension one. -/
structure CqChannel (X B C : Type) [Fintype B] [Fintype C] where
  input_nonempty : Nonempty X
  bob_nonempty : Nonempty B
  charlie_nonempty : Nonempty C
  output : X → Matrix (B × C) (B × C) ℂ
  density : ∀ x, IsDensityMatrix (output x)

/-- Definition 5, PDF p.10: arbitrary finite classical transition probabilities. -/
structure ClassicalBroadcastChannel (X Y Z : Type) [Fintype Y] [Fintype Z] where
  input_nonempty : Nonempty X
  output : X → AuxiliaryLaw (Y × Z)

/-- Equation (4), PDF p.3: actual cq density matrix from the auxiliary law, map, and channel. -/
def inducedState {X U V B C : Type} [Fintype U] [Fintype V] [Fintype B] [Fintype C]
    (N : CqChannel X B C) (p : AuxiliaryLaw (U × V)) (f : U → V → X) :
    Matrix ((U × V) × (B × C)) ((U × V) × (B × C)) ℂ :=
  fun a b => if a.1 = b.1 then (p.prob a.1 : ℂ) * N.output (f a.1.1 a.1.2) a.2 b.2 else 0

/-- U,B marginal of (4), PDF pp.3,6; the other auxiliary and Charlie are traced out. -/
def inducedUB {X U V B C : Type} [Fintype U] [Fintype V] [Fintype B] [Fintype C]
    (N : CqChannel X B C) (p : AuxiliaryLaw (U × V)) (f : U → V → X) :
    Matrix (U × B) (U × B) ℂ :=
  fun a b => if a.1 = b.1 then
    ∑ v, (p.prob (a.1, v) : ℂ) * traceRight (N.output (f a.1 v)) a.2 b.2 else 0

/-- V,C marginal of (4), PDF pp.3,6; the other auxiliary and Bob are traced out. -/
def inducedVC {X U V B C : Type} [Fintype U] [Fintype V] [Fintype B] [Fintype C]
    (N : CqChannel X B C) (p : AuxiliaryLaw (U × V)) (f : U → V → X) :
    Matrix (V × C) (V × C) ℂ :=
  fun a b => if a.1 = b.1 then
    ∑ u, (p.prob (u, a.1) : ℂ) * traceLeft (N.output (f u a.1)) a.2 b.2 else 0

/-- The actual U,Y law in Theorem 4, PDF p.3. -/
def inducedUY {X U V Y Z : Type} [Fintype U] [Fintype V] [Fintype Y] [Fintype Z]
    (N : ClassicalBroadcastChannel X Y Z) (p : AuxiliaryLaw (U × V)) (f : U → V → X) (uy : U × Y) : ℝ :=
  ∑ v, p.prob (uy.1, v) * ∑ z, (N.output (f uy.1 v)).prob (uy.2, z)

/-- The actual V,Z law in Theorem 4, PDF p.3. -/
def inducedVZ {X U V Y Z : Type} [Fintype U] [Fintype V] [Fintype Y] [Fintype Z]
    (N : ClassicalBroadcastChannel X Y Z) (p : AuxiliaryLaw (U × V)) (f : U → V → X) (vz : V × Z) : ℝ :=
  ∑ u, p.prob (u, vz.1) * ∑ y, (N.output (f u vz.1)).prob (y, vz.2)

/-- Definition 2, PDF p.5: fixed deterministic encoder and separate fixed local POVMs. -/
structure CqCode (X B C : Type) [Fintype B] [Fintype C] (M1 M2 : ℕ) where
  encode : Fin M1 → Fin M2 → X
  bob : Fin M1 → Matrix B B ℂ
  charlie : Fin M2 → Matrix C C ℂ
  bob_povm : IsPOVM bob
  charlie_povm : IsPOVM charlie

/-- Definition 2, (12), PDF p.5: independent uniform messages and average joint error.
Theorems require both message counts positive. -/
def cqJointError {X B C : Type} [Fintype B] [Fintype C] {M1 M2 : ℕ}
    (N : CqChannel X B C) (D : CqCode X B C M1 M2) : ℝ :=
  ((M1 : ℝ) * M2)⁻¹ * ∑ m1, ∑ m2,
    (1 - effectProb (Matrix.kronecker (D.bob m1) (D.charlie m2)) (N.output (D.encode m1 m2)))

/-- Definition 6, PDF p.10: deterministic encoding and separate deterministic decoders. -/
structure PrivateClassicalCode (X Y Z : Type) (M1 M2 : ℕ) where
  encode : Fin M1 → Fin M2 → X
  bob : Y → Fin M1
  charlie : Z → Fin M2

/-- Definition 6, PDF p.10: actual average probability that either private message is wrong. -/
def classicalError {X Y Z : Type} [Fintype Y] [Fintype Z] {M1 M2 : ℕ}
    (N : ClassicalBroadcastChannel X Y Z) (D : PrivateClassicalCode X Y Z M1 M2) : ℝ :=
  ((M1 : ℝ) * M2)⁻¹ * ∑ m1, ∑ m2, ∑ yz : Y × Z,
    if D.bob yz.1 = m1 ∧ D.charlie yz.2 = m2 then 0
    else (N.output (D.encode m1 m2)).prob yz

/-- Equations (5)-(7) and (8)-(10), PDF p.3: the three inequalities with constants 5,2,11,5.
Rates are literal log2 positive integer message counts; no rounding convention is hidden. -/
def MartonConstraints (a b c : EReal) (M1 M2 : ℕ) (tildeEpsilon : ℝ) : Prop :=
  let R1 : EReal := (Real.logb 2 (M1 : ℝ) : EReal)
  let R2 : EReal := (Real.logb 2 (M2 : ℝ) : EReal)
  let L : EReal := (Real.logb 2 (1 / tildeEpsilon) : EReal)
  R1 ≤ a - 5 * L - 2 ∧ R2 ≤ b - 5 * L - 2 ∧
    R1 + R2 ≤ a + b - c - 11 * L - 5

/-- Positive block length k+1, Definitions 8-10, PDF pp.15-17. -/
abbrev PositiveBlockWord (A : Type) (k : ℕ) := Fin (k + 1) → A

/-- Positive spectral projector, Definition 9's words, PDF p.16. -/
def strictPositiveSpectralProjector {A : Type} [Fintype A] (H : Matrix A A ℂ) : Matrix A A ℂ :=
  cfc (fun x : ℝ => if 0 < x then 1 else 0) H

/-- Corrected Definition 9, PDF p.16: sum_u Tr[P_u (p(u) rho_(B|u))].
Printed: Tr[P_u rho_B]; changed: Tr[P_u rho_(B|u)] before weighting by p(u).
Why: the printed marginal gives zero limiting mass for orthogonal iid signals,
contradicting (47) and the Theorem 6 testing argument, PDF pp.16-17.
Using unnormalized blocks avoids division on null auxiliary symbols. -/
def spectralAcceptance {U B : Type} [Fintype U] [Fintype B]
    (n gamma : ℝ) (rho : Matrix (U × B) (U × B) ℂ) : ℝ :=
  ∑ u, let block : Matrix B B ℂ := fun b b2 => rho (u, b) (u, b2)
    let marginal := traceLeft rho
    let weight := (Matrix.trace block).re
    effectProb (strictPositiveSpectralProjector (block - ((2 : ℝ) ^ (n * gamma) * weight : ℝ) • marginal)) block

/-- Corrected spectral inf quantum information rate, Definition 9, PDF p.16.
Extended supremum and an actual limit of acceptance probabilities. -/
def spectralInfMutualInformation {U B : Type} [Fintype U] [Fintype B]
    (rho : (k : ℕ) → Matrix (PositiveBlockWord U k × PositiveBlockWord B k) (PositiveBlockWord U k × PositiveBlockWord B k) ℂ) : EReal :=
  sSup {t : EReal | ∃ gamma : ℝ, t = (gamma : EReal) ∧
    Tendsto (fun k : ℕ => spectralAcceptance ((k + 1 : ℕ) : ℝ) gamma (rho k)) atTop (nhds 1)}

/-- Probability tail of the information density, Definition 10, PDF p.17.
Zero joint mass is excluded before taking a logarithm. -/
def informationTail {U V : Type} [Fintype U] [Fintype V]
    (p : AuxiliaryLaw (U × V)) (n lambda : ℝ) : ℝ :=
  ∑ uv, if 0 < p.prob uv ∧
      lambda < Real.logb 2 (p.prob uv /
        (leftLawMarginal p.prob uv.1 * secondMarginal p.prob uv.2)) / n
    then p.prob uv else 0

/-- Spectral sup classical information rate, Definition 10, PDF p.17.
The probability tail tends to zero along the entire sequence. -/
def spectralSupMutualInformation {U V : Type} [Fintype U] [Fintype V]
    (p : (k : ℕ) → AuxiliaryLaw (PositiveBlockWord U k × PositiveBlockWord V k)) : EReal :=
  sInf {t : EReal | ∃ lambda : ℝ, t = (lambda : EReal) ∧
    Tendsto (fun k => informationTail (p k) (k + 1) lambda) atTop (nhds 0)}

/-- Definition 8, PDF pp.15-16, corrected second message domain/decoder labels.
Counts are positive integers. The two eventual lower bounds express liminf rate
constraints without totalized real infima on unbounded sequences. -/
def SpectrumAchievable {X B C : Type} [Fintype B] [Fintype C]
    (N : (k : ℕ) → CqChannel (PositiveBlockWord X k) (PositiveBlockWord B k) (PositiveBlockWord C k)) (R1 R2 : ℝ) : Prop :=
  ∃ M1 M2 : ℕ → ℕ, (∀ k, 0 < M1 k ∧ 0 < M2 k) ∧
    ∃ D : (k : ℕ) → CqCode (PositiveBlockWord X k) (PositiveBlockWord B k) (PositiveBlockWord C k) (M1 k) (M2 k),
      Tendsto (fun k => cqJointError (N k) (D k)) atTop (nhds 0) ∧
      (∀ delta > (0 : ℝ), ∀ᶠ k in atTop,
        R1 - delta ≤ Real.logb 2 (M1 k : ℝ) / (k + 1)) ∧
      (∀ delta > (0 : ℝ), ∀ᶠ k in atTop,
        R2 - delta ≤ Real.logb 2 (M2 k : ℝ) / (k + 1))

/-- Sanity check: the extended logarithm sends zero to minus infinity. -/
example : extendedLog2 0 = ⊥ := by simp [extendedLog2]

example (p : Unit × Unit → ℝ) : leftLawMarginal p () = p ((), ()) := by
  simp [leftLawMarginal]

example (p : Unit × Unit → ℝ) : secondMarginal p () = p ((), ()) := by
  simp [secondMarginal]

example {A : Type} [Fintype A] (p : A → ℝ) : setMass p ∅ = 0 := by
  simp [setMass]

example {U V : Type} [Fintype U] [Fintype V] (p : U × V → ℝ)
    (uv : U × V) (h : p uv = 0) : logRatio p uv = ⊥ := by simp [logRatio, h]

example : IsEffect (0 : Matrix Unit Unit ℂ) := by
  exact ⟨Matrix.PosSemidef.zero, by simpa using (Matrix.PosSemidef.one :
    (1 : Matrix Unit Unit ℂ).PosSemidef)⟩

example {X U V B C : Type} [Fintype U] [Fintype V] [Fintype B] [Fintype C]
    (N : CqChannel X B C) (p : AuxiliaryLaw (U × V)) (f : U → V → X)
    (uv : U × V) (bc bc2 : B × C) :
    inducedState N p f (uv, bc) (uv, bc2) =
      (p.prob uv : ℂ) * N.output (f uv.1 uv.2) bc bc2 := by simp [inducedState]

example {X Y Z : Type} [Fintype Y] [Fintype Z]
    (N : ClassicalBroadcastChannel X Y Z) (D : PrivateClassicalCode X Y Z 1 1) :
    classicalError N D = 0 := by
  have h1 : ∀ y, D.bob y = (0 : Fin 1) := fun _ => Subsingleton.elim _ _
  have h2 : ∀ z, D.charlie z = (0 : Fin 1) := fun _ => Subsingleton.elim _ _
  simp [classicalError, h1, h2]

example (A : Type) : PositiveBlockWord A 0 = (Fin 1 → A) := rfl

example {U V : Type} [Fintype U] [Fintype V] (p : AuxiliaryLaw (U × V))
    (n lambda : ℝ) : informationTail p n lambda =
      ∑ uv, if 0 < p.prob uv ∧ lambda < Real.logb 2
        (p.prob uv / (leftLawMarginal p.prob uv.1 * secondMarginal p.prob uv.2)) / n
      then p.prob uv else 0 := rfl

/-- The four padding constraints (13)-(16), (35)-(38), PDF pp.6,11.
The ceiling is integer-valued; the two message rates are log2 actual counts. -/
def Padding (a b c tildeEpsilon : ℝ) (M1 M2 r1 r2 : ℕ) : Prop :=
  let L := Real.logb 2 (1 / tildeEpsilon)
  0 < r1 ∧ 0 < r2 ∧
    Real.logb 2 (M1 : ℝ) + r1 ≤ a - 4 * L - 1 ∧
    Real.logb 2 (M2 : ℝ) + r2 ≤ b - 4 * L - 1 ∧
    L ≤ (r1 : ℝ) ∧ L ≤ (r2 : ℝ) ∧
    ((r1 + r2 : ℕ) : ℤ) = Int.ceil (c + 3 * L)

/-- A realization of the source random codebook, PDF pp.7,11-12. Retained bits are
exactly the pushforward of the independent uniform rejection coins. Repeated U,V
values do not identify different row/column indices. -/
structure Codebook (U V : Type) (rows columns : ℕ) where
  row : Fin rows → U
  column : Fin columns → V
  retained : Fin rows → Fin columns → Bool
  deriving Fintype

/-- Rejection acceptance probability (18),(39), PDF pp.7,12.
Clipping is exactly the event eta <= ratio for eta uniform on [0,1]. Null marginal
rows have sampling probability zero and their coin boundary has measure zero. -/
def rejectionChance {U V : Type} [Fintype U] [Fintype V]
    (p : AuxiliaryLaw (U × V)) (c : ℝ) (u : U) (v : V) : ℝ :=
  min 1 (max 0 (p.prob (u, v) /
    ((2 : ℝ) ^ c * leftLawMarginal p.prob u * secondMarginal p.prob v)))

/-- Computed finite law of the full random codebook, PDF pp.7,11-12. Rows and columns
are mutually independent; rejection coins are independent conditional on them.
This is the exact finite pushforward law, not an assumption on desired events. -/
def bookWeight {U V : Type} [Fintype U] [Fintype V] {rows columns : ℕ}
    (p : AuxiliaryLaw (U × V)) (c : ℝ) (book : Codebook U V rows columns) : ℝ :=
  (∏ k, leftLawMarginal p.prob (book.row k)) *
    (∏ l, secondMarginal p.prob (book.column l)) *
    ∏ k, ∏ l, if book.retained k l then
      rejectionChance p c (book.row k) (book.column l)
    else 1 - rejectionChance p c (book.row k) (book.column l)

/-- Lexicographically first good retained pair in the message rectangle, PDF pp.7,12.
Global zero-based indices have the same order and bands as the source's one-based indices. -/
def selectPair {U V : Type} {M1 M2 r1 r2 : ℕ}
    (book : Codebook U V (M1 * 2 ^ r1) (M2 * 2 ^ r2))
    (good : U → V → Prop) (m1 : Fin M1) (m2 : Fin M2) :
    Option (Fin (M1 * 2 ^ r1) × Fin (M2 * 2 ^ r2)) :=
  ((List.finRange (M1 * 2 ^ r1)).flatMap fun k =>
    (List.finRange (M2 * 2 ^ r2)).map fun l => (k, l)).find? fun kl =>
      decide (kl.1.val / 2 ^ r1 = m1.val ∧ kl.2.val / 2 ^ r2 = m2.val ∧
        book.retained kl.1 kl.2 = true ∧ good (book.row kl.1) (book.column kl.2))

/-- Source encoder, PDF pp.7,12: selected codeword, or one fixed input on failure. -/
def selectedInput {X U V : Type} {M1 M2 r1 r2 : ℕ}
    (fallback : X) (f : U → V → X)
    (book : Codebook U V (M1 * 2 ^ r1) (M2 * 2 ^ r2))
    (good : U → V → Prop) (m1 : Fin M1) (m2 : Fin M2) : X :=
  match selectPair book good m1 m2 with
  | none => fallback
  | some kl => f (book.row kl.1) (book.column kl.2)

/-- Classical local test acceptance alpha,beta, PDF p.12. -/
def classicalGood {X U V Y Z : Type} [Fintype Y] [Fintype Z]
    (N : ClassicalBroadcastChannel X Y Z) (f : U → V → X)
    (A1 : Finset (U × Y)) (A2 : Finset (V × Z)) (epsilon0 : ℝ) (u : U) (v : V) : Prop :=
  1 - 4 * epsilon0 < (∑ y, if (u, y) ∈ A1 then ∑ z, (N.output (f u v)).prob (y, z) else 0) ∧
  1 - 4 * epsilon0 < (∑ z, if (v, z) ∈ A2 then ∑ y, (N.output (f u v)).prob (y, z) else 0)

/-- Data fixed before generating a classical random codebook, PDF pp.11-13.
Test acceptances and comparison masses are the source test conditions, not event
probability bounds. All information values are computed from N,p,f. -/
structure ClassicalSetup (X U V Y Z : Type) [Fintype U] [Fintype V] [Fintype Y] [Fintype Z] where
  channel : ClassicalBroadcastChannel X Y Z
  law : AuxiliaryLaw (U × V)
  map : U → V → X
  M1 : ℕ
  M2 : ℕ
  positive1 : 0 < M1
  positive2 : 0 < M2
  r1 : ℕ
  r2 : ℕ
  epsilon0 : ℝ
  epsilonInfinity : ℝ
  tildeEpsilon : ℝ
  zero_domain : 0 < epsilon0 ∧ epsilon0 < 1
  infinity_domain : 0 < epsilonInfinity ∧ epsilonInfinity ≤ 1 / 4
  tilde_domain : 0 < tildeEpsilon ∧ tildeEpsilon ≤ 1 / 37
  a : ℝ
  b : ℝ
  c : ℝ
  a_value : smoothClassicalMin (inducedUY channel law map) epsilon0 = (a : EReal)
  b_value : smoothClassicalMin (inducedVZ channel law map) epsilon0 = (b : EReal)
  c_value : strictSmoothMaxInformation law.prob epsilonInfinity = (c : EReal)
  test1 : Finset (U × Y)
  test2 : Finset (V × Z)
  acceptance1 : 1 - epsilon0 < setMass (inducedUY channel law map) test1
  acceptance2 : 1 - epsilon0 < setMass (inducedVZ channel law map) test2
  comparison1 : (∑ uy ∈ test1, leftLawMarginal (inducedUY channel law map) uy.1 *
    secondMarginal (inducedUY channel law map) uy.2) ≤ (2 : ℝ) ^ (-a)
  comparison2 : (∑ vz ∈ test2, leftLawMarginal (inducedVZ channel law map) vz.1 *
    secondMarginal (inducedVZ channel law map) vz.2) ≤ (2 : ℝ) ^ (-b)
  padding : Padding a b c tildeEpsilon M1 M2 r1 r2

/-- The five events on PDF p.13, without any probability assumptions. -/
inductive ErrorEvent where
  | noPair
  | bobMiss
  | charlieMiss
  | bobCollision
  | charlieCollision
  deriving DecidableEq

/-- Actual error event for the first message rectangle, PDF p.13. A miss/collision
is counted only after a good pair has been selected. Other rows/columns include
indices with the same auxiliary symbol, exactly as in the source. -/
def classicalEvent {X U V Y Z : Type} [Fintype U] [Fintype V] [Fintype Y] [Fintype Z]
    (D : ClassicalSetup X U V Y Z)
    (book : Codebook U V (D.M1 * 2 ^ D.r1) (D.M2 * 2 ^ D.r2))
    (event : ErrorEvent) (yz : Y × Z) : Prop :=
  match selectPair book (classicalGood D.channel D.map D.test1 D.test2 D.epsilon0)
      ⟨0, D.positive1⟩ ⟨0, D.positive2⟩ with
  | none => event = .noPair
  | some kl => match event with
    | .noPair => False
    | .bobMiss => (book.row kl.1, yz.1) ∉ D.test1
    | .charlieMiss => (book.column kl.2, yz.2) ∉ D.test2
    | .bobCollision => ∃ k, k ≠ kl.1 ∧ (book.row k, yz.1) ∈ D.test1
    | .charlieCollision => ∃ l, l ≠ kl.2 ∧ (book.column l, yz.2) ∈ D.test2

/-- Probability of each constructed event over the actual random codebook AND the
actual channel output, PDF pp.13-14; messages are fixed at (1,1) by symmetry. -/
def classicalEventProbability {X U V Y Z : Type}
    [Fintype U] [Fintype V] [Fintype Y] [Fintype Z]
    (D : ClassicalSetup X U V Y Z) (event : ErrorEvent) : ℝ :=
  ∑ book : Codebook U V (D.M1 * 2 ^ D.r1) (D.M2 * 2 ^ D.r2),
    bookWeight D.law D.c book * ∑ yz,
      (D.channel.output (selectedInput (Classical.choice D.channel.input_nonempty) D.map book
        (classicalGood D.channel D.map D.test1 D.test2 D.epsilon0)
        ⟨0, D.positive1⟩ ⟨0, D.positive2⟩)).prob yz *
        (if classicalEvent D book event yz then 1 else 0)

/-- Actual first-hit index decoder, PDF p.12, retaining row identity, with fixed
zero-index fallback. Its band gives the message decoder. -/
def firstHit {A O : Type} {n : ℕ} (h : 0 < n) (symbols : Fin n → A)
    (test : Finset (A × O)) (outcome : O) : Fin n :=
  ((List.finRange n).find? fun k => decide ((symbols k, outcome) ∈ test)).getD ⟨0, h⟩

/-- Classical average failure to recover the actual selected row AND column,
PDF pp.12-14. Encoding failure is counted as failure even if fallback decoders agree. -/
def classicalIndexError {X U V Y Z : Type}
    [Fintype U] [Fintype V] [Fintype Y] [Fintype Z]
    (D : ClassicalSetup X U V Y Z)
    (book : Codebook U V (D.M1 * 2 ^ D.r1) (D.M2 * 2 ^ D.r2)) : ℝ :=
  ((D.M1 : ℝ) * D.M2)⁻¹ * ∑ m1 : Fin D.M1, ∑ m2 : Fin D.M2,
    match selectPair book (classicalGood D.channel D.map D.test1 D.test2 D.epsilon0) m1 m2 with
    | none => 1
    | some kl => ∑ yz, (D.channel.output (D.map (book.row kl.1) (book.column kl.2))).prob yz *
        (if firstHit (Nat.mul_pos D.positive1 (by positivity)) book.row D.test1 yz.1 = kl.1 ∧
          firstHit (Nat.mul_pos D.positive2 (by positivity)) book.column D.test2 yz.2 = kl.2
        then 0 else 1)

/-- Quantum construction parameters, PDF pp.6-8. The test effects act on the actual
computed U,B and V,C states and satisfy exactly the source acceptance/comparison bounds. -/
structure QuantumSetup (X U V B C : Type) [Fintype U] [Fintype V] [Fintype B] [Fintype C] where
  channel : CqChannel X B C
  law : AuxiliaryLaw (U × V)
  map : U → V → X
  M1 : ℕ
  M2 : ℕ
  positive1 : 0 < M1
  positive2 : 0 < M2
  r1 : ℕ
  r2 : ℕ
  epsilon0 : ℝ
  epsilonInfinity : ℝ
  tildeEpsilon : ℝ
  zero_domain : 0 < epsilon0 ∧ epsilon0 < 1
  infinity_domain : 0 < epsilonInfinity ∧ epsilonInfinity ≤ 1 / 4
  tilde_domain : 0 < tildeEpsilon ∧ tildeEpsilon ≤ 1 / 40
  a : ℝ
  b : ℝ
  c : ℝ
  a_value : smoothQuantumMin (inducedUB channel law map) epsilon0 = (a : EReal)
  b_value : smoothQuantumMin (inducedVC channel law map) epsilon0 = (b : EReal)
  c_value : strictSmoothMaxInformation law.prob epsilonInfinity = (c : EReal)
  test1 : Matrix (U × B) (U × B) ℂ
  test2 : Matrix (V × C) (V × C) ℂ
  effect1 : IsEffect test1
  effect2 : IsEffect test2
  acceptance1 : 1 - epsilon0 ≤ effectProb test1 (inducedUB channel law map)
  acceptance2 : 1 - epsilon0 ≤ effectProb test2 (inducedVC channel law map)
  comparison1 : effectProb test1 (Matrix.kronecker (traceRight (inducedUB channel law map))
    (traceLeft (inducedUB channel law map))) ≤ (2 : ℝ) ^ (-a)
  comparison2 : effectProb test2 (Matrix.kronecker (traceRight (inducedVC channel law map))
    (traceLeft (inducedVC channel law map))) ≤ (2 : ℝ) ^ (-b)
  padding : Padding a b c tildeEpsilon M1 M2 r1 r2

/-- Diagonal test block (19)-(20), PDF p.7. -/
def testBlock {A B : Type} (G : Matrix (A × B) (A × B) ℂ) (a : A) : Matrix B B ℂ :=
  fun b b2 => G (a, b) (a, b2)

/-- Quantum pair-selection acceptance tests alpha,beta, PDF p.7. -/
def quantumGood {X U V B C : Type} [Fintype U] [Fintype V] [Fintype B] [Fintype C]
    (D : QuantumSetup X U V B C) (u : U) (v : V) : Prop :=
  1 - 4 * D.epsilon0 < effectProb (testBlock D.test1 u) (traceRight (D.channel.output (D.map u v))) ∧
  1 - 4 * D.epsilon0 < effectProb (testBlock D.test2 v) (traceLeft (D.channel.output (D.map u v)))

/-- Square-root decoder (21)-(22), PDF p.7, completed on the kernel by assigning the
residual projector to fixed index zero. On the support it is precisely S^(-1/2) L_k S^(-1/2).
The completion only increases success at that outcome. -/
def completedPgm {B : Type} [Fintype B] {n : ℕ}
    (L : Fin n → Matrix B B ℂ) (k : Fin n) : Matrix B B ℂ :=
  let S := ∑ j, L j
  let K := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) S
  K * L k * K + if k.val = 0 then 1 - strictPositiveSpectralProjector S else 0

/-- Quantum actual-index error, PDF pp.8-10, with full local index POVMs.
A failed encoder is counted as failure; the two receiver probabilities use their
actual joint output state, not the product of the marginal states. -/
def quantumIndexError {X U V B C : Type}
    [Fintype U] [Fintype V] [Fintype B] [Fintype C]
    (D : QuantumSetup X U V B C)
    (book : Codebook U V (D.M1 * 2 ^ D.r1) (D.M2 * 2 ^ D.r2)) : ℝ :=
  ((D.M1 : ℝ) * D.M2)⁻¹ * ∑ m1 : Fin D.M1, ∑ m2 : Fin D.M2,
    match selectPair book (quantumGood D) m1 m2 with
    | none => 1
    | some kl => 1 - effectProb
        (Matrix.kronecker (completedPgm (fun k => testBlock D.test1 (book.row k)) kl.1)
          (completedPgm (fun l => testBlock D.test2 (book.column l)) kl.2))
        (D.channel.output (D.map (book.row kl.1) (book.column kl.2)))

example {U V : Type} [Fintype U] [Fintype V] {r s : ℕ}
    (p : AuxiliaryLaw (U × V)) (c : ℝ) (book : Codebook U V r s) :
    bookWeight p c book = (∏ k, leftLawMarginal p.prob (book.row k)) *
      (∏ l, secondMarginal p.prob (book.column l)) *
      ∏ k, ∏ l, if book.retained k l then rejectionChance p c (book.row k) (book.column l)
        else 1 - rejectionChance p c (book.row k) (book.column l) := rfl

example {U V : Type} {M1 M2 r1 r2 : ℕ} (fallback : Unit) (f : U → V → Unit)
    (book : Codebook U V (M1 * 2 ^ r1) (M2 * 2 ^ r2))
    (good : U → V → Prop) (m1 : Fin M1) (m2 : Fin M2) :
    selectedInput fallback f book good m1 m2 = () := Subsingleton.elim _ _

example {A B : Type} (G : Matrix (A × B) (A × B) ℂ) (a : A) (b b2 : B) :
    testBlock G a b b2 = G (a, b) (a, b2) := rfl

/-- Total-extension sanity: the zero operator cannot pass the strict zero-error test. -/
example : smoothQuantumMin (0 : Matrix (Unit × Unit) (Unit × Unit) ℂ) 0 = ⊥ := by
  simp [smoothQuantumMin, effectProb]

example : strictSmoothMaxInformation (fun _ : Unit × Unit => (0 : ℝ)) 0 = ⊤ := by
  simp [strictSmoothMaxInformation, setMass]

example : smoothClassicalMin (fun _ : Unit × Unit => (0 : ℝ)) 0 = ⊥ := by
  simp [smoothClassicalMin, setMass]

/-- A normalized independent singleton pair has zero log likelihood ratio. -/
example : logRatio (fun _ : Unit × Unit => (1 : ℝ)) ((), ()) = 0 := by
  norm_num [logRatio, extendedLog2, leftLawMarginal, secondMarginal]

/-- With no good pair the explicit source encoder reports failure. -/
example {U V : Type} {M1 M2 r1 r2 : ℕ}
    (book : Codebook U V (M1 * 2 ^ r1) (M2 * 2 ^ r2))
    (m1 : Fin M1) (m2 : Fin M2) :
    selectPair book (fun _ _ => False) m1 m2 = none := by
  simp [selectPair]

/-- Kernel-completion sanity: one zero test becomes the identity measurement. -/
example : completedPgm (fun _ : Fin 1 => (0 : Matrix Unit Unit ℂ)) 0 = 1 := by
  ext i j
  simp [completedPgm, strictPositiveSpectralProjector] <;> rfl

end QAlgorithms.Papers.Independent.Extend50.P49


