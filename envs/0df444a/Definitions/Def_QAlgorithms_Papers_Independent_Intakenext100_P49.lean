-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P49
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P49
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T06:22:55.310262+00:00
-- url     : https://prove2.me/theorems/e4bedaa4-6bc0-4c65-9d70-6a2b7d55ade3
-- title:
--   Definitions for An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels
-- statement:
--   The objects the formalized statements of *An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels* (arXiv:0903.1638) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `cloner`: PDF p.3, Eqs.(9)--(11): all k+1 clones in their (k+2)-dimensional symmetric space, from the accepted occupation-basis dilation.
--   - `clonerComplement`: PDF p.3, Eq.(11): the actual complement of the same dilation, with environment dimension k+1, including the trace-map case k=0.
--   - `StrongHolevoAdditive`: PDF pp.1--2: additivity against every auxiliary finite-dimensional CPTP channel, with arbitrary entangled inputs included by the matrix-unit tensor map.
--   - `WeakHolevoAdditive`: PDF pp.1,5, Eqs.(18),(19): every positive identical tensor power; this predicate asserts CPTP as well as the stated Holevo equality.
--   - `classicalCapacityBits`: PDF p.1: classical capacity defined by regularization, independently of Eq.(16). All finite ensembles and entangled block inputs enter holevoCapacity.
--   - `transposeOutput`: PDF pp.4--5: the complex-linear extension of conjugation on Hermitian outputs is transpose, not the conjugate-linear operation on arbitrary operators.
--   - `clonerDelta`: PDF p.4, Eq.(16): Delta_ell with ell=k+2; its denominator is positive.
--   - `clonerLogSum`: PDF p.4, Eq.(16): the finite k log2 k sum, including the zero term.
--   - `depolarizedCloner`: PDF p.4, Fig.2 and Section III-A: lambda=(ell-1)/(ell+1). The accepted depolarizing map takes NOISE probability 1-lambda=2/(k+3).
--   - `entropyHolevoValues`: PDF pp.1,5: possible Holevo values from a specified output-entropy functional. Ensembles are finite, normalized, positive, and otherwise unrestricted.
--   - `unruhAuxBlock`: PDF p.5, Theorem 2: one exact subnormalized block of U_z^tensor n tensor T. Sector labels run over all Nat^n; coherences of the joint input are retained. Together these blocks specify the full countable direct-sum output.
--   - `unruhAuxEntropy`: PDF p.5: entropy of the full countable output, including flag entropy. Blocks are subnormalized, so no additional Shannon term is added. Summability for every normalized joint input is a conclusion of unruh_strongAdditivity.
--   - `unruhHolevo`: PDF pp.1,5: unrestricted finite-ensemble Holevo capacity of the exact n-use countable-output channel, before any single-letter identity is asserted.
--   - `unruhAuxHolevo`: PDF pp.1,5: unrestricted Holevo optimization on U_z^tensor n tensor T.
--   - `unruhClassicalRates`: PDF p.1: all positive regularized block rates of the full Unruh channel.
--   - `unruhClassicalCapacity`: PDF pp.1,5: regularized classical capacity; it is not defined by Eq.(23).
--   - `UnruhRegular`: PDF pp.2,5: analytic well-definedness of the exact infinite output. These conditions are conclusions, never assumptions replacing capacity content. The finite ensembles and all finite auxiliary references include mixed inputs entangled across every channel use.
--   - `unruhFirstTerm`: PDF p.5, Eq.(23): first infinite series, ell=k+2.
--   - `unruhSecondTerm`: PDF p.5, Eq.(23): second infinite series with its own p_ell/Delta_ell.
--   - `highestCoupling`: PDF pp.5--6, Eqs.(24)--(26): normalized occupation coefficient of Sym^(2k+1)(C^2) inside Sym^k(C^2) tensor Sym^(k+1)(C^2), with the ordinary SU(2) tensor action. This fixes the highest irrep, including its phases.
--   - `highestProjector`: PDF p.6: orthogonal highest-irrep projector, output factor first. Its irrep dimension is 2k+2, not the full (k+1)(k+2) tensor dimension.
--   - `degradingChoi`: PDF p.6: unnormalized Choi ansatz. Trace preservation forces the coefficient (k+2)/(2k+2)=ell/(2ell-2).
--   - `highestDegradingMap`: PDF p.6: Choi reconstruction Tr_in[(I tensor X^T)R], output first. There is no normalized-Choi dimension factor or extra input conjugation.
-- source:
--   An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels, arXiv:0903.1638v7, https://arxiv.org/abs/0903.1638v7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

/-!
Bradler, arXiv:0903.1638v7. All page numbers are PDF pages; all entropies are bits.
The parameter k = ell - 2 ranges over Nat, so ell >= 2 holds without truncated
subtraction. The full Unruh output retains every countable sector. Lemma 3 is
explicitly deferred in HARD.md. Compilation is pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P49

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter
open QAlgorithms.Papers.Independent.Support50.P01
  (unruhSectorDilation unruhWeight unruhBlockDilation unruhBlockWeight
   unruhReceiver unruhReceiverEntropy)
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable)
open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)
open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)
open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)
open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)
open QAlgorithms.QuditFidelity (depolarizingMap)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Eqs.(9)--(11): all k+1 clones in their (k+2)-dimensional
symmetric space, from the accepted occupation-basis dilation. -/
def cloner (k : ℕ) : Superop (Fin 2) (Fin (k+2)) :=
  receiverChannel (unruhSectorDilation k)

/-- PDF p.3, Eq.(11): the actual complement of the same dilation,
with environment dimension k+1, including the trace-map case k=0. -/
def clonerComplement (k : ℕ) : Superop (Fin 2) (Fin (k+1)) :=
  complementaryChannel (unruhSectorDilation k)

/-- PDF pp.1--2: additivity against every auxiliary finite-dimensional CPTP
channel, with arbitrary entangled inputs included by the matrix-unit tensor map. -/
def StrongHolevoAdditive {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (N : Superop I O) : Prop :=
  IsChannel N ∧ ∀ a b : ℕ, 0 < a → 0 < b →
    ∀ T : Superop (Fin a) (Fin b), IsChannel T →
      holevoCapacity (tensorChannel N T) = holevoCapacity N + holevoCapacity T

/-- PDF pp.1,5, Eqs.(18),(19): every positive identical tensor power;
this predicate asserts CPTP as well as the stated Holevo equality. -/
def WeakHolevoAdditive {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (N : Superop I O) : Prop :=
  IsChannel N ∧ ∀ n : ℕ, 1 ≤ n →
    holevoCapacity (piSuperop (fun _ : Fin n => N)) = (n : ℝ) * holevoCapacity N

/-- PDF p.1: classical capacity defined by regularization, independently of
Eq.(16). All finite ensembles and entangled block inputs enter holevoCapacity. -/
def classicalCapacityBits {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (N : Superop I O) : ℝ :=
  sSup (Set.range (fun m : ℕ =>
    holevoCapacity (piSuperop (fun _ : Fin (m+1) => N)) / (m+1 : ℝ)))

/-- PDF pp.4--5: the complex-linear extension of conjugation on Hermitian
outputs is transpose, not the conjugate-linear operation on arbitrary operators. -/
def transposeOutput {I O : Type} (N : Superop I O) : Superop I O :=
  fun X => (N X)ᵀ

/-- PDF p.4, Eq.(16): Delta_ell with ell=k+2; its denominator is positive. -/
def clonerDelta (k : ℕ) : ℝ := (k+2 : ℝ) * (k+1 : ℝ) / 2

/-- PDF p.4, Eq.(16): the finite k log2 k sum, including the zero term. -/
def clonerLogSum (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+2), (j : ℝ) * Real.logb 2 j

/-- PDF p.4, Fig.2 and Section III-A: lambda=(ell-1)/(ell+1).
The accepted depolarizing map takes NOISE probability 1-lambda=2/(k+3). -/
def depolarizedCloner (k : ℕ) : Superop (Fin 2) (Fin (k+2)) :=
  depolarizingMap (k+2) (by omega) (2 / (k+3 : ℝ)) ∘ cloner k

/-- PDF pp.1,5: possible Holevo values from a specified output-entropy
functional. Ensembles are finite, normalized, positive, and otherwise unrestricted. -/
def entropyHolevoValues {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ → ℝ) : Set ℝ :=
  {v | ∃ (m : ℕ) (q : Fin m → ℝ) (rho : Fin m → Matrix I I ℂ),
    (∀ j, 0 ≤ q j) ∧ (∑ j, q j) = 1 ∧ (∀ j, IsDensityMatrix (rho j)) ∧
    v = H (∑ j, (q j : ℂ) • rho j) - ∑ j, q j * H (rho j)}

/-- PDF p.5, Theorem 2: one exact subnormalized block of U_z^tensor n tensor T.
Sector labels run over all Nat^n; coherences of the joint input are retained.
Together these blocks specify the full countable direct-sum output. -/
def unruhAuxBlock {n a b : ℕ} (z : ℝ) (ks : Fin n → ℕ)
    (T : Superop (Fin a) (Fin b)) :
    Superop ((Fin n → Fin 2) × Fin a) (((i : Fin n) → Fin (ks i+2)) × Fin b) :=
  fun X => (unruhBlockWeight z ks : ℂ) •
    tensorChannel (receiverChannel (unruhBlockDilation ks)) T X

/-- PDF p.5: entropy of the full countable output, including flag entropy.
Blocks are subnormalized, so no additional Shannon term is added. Summability
for every normalized joint input is a conclusion of unruh_strongAdditivity. -/
def unruhAuxEntropy {a b : ℕ} (z : ℝ) (n : ℕ)
    (T : Superop (Fin a) (Fin b))
    (rho : Matrix ((Fin n → Fin 2) × Fin a) ((Fin n → Fin 2) × Fin a) ℂ) : ℝ :=
  ∑' ks : Fin n → ℕ, vnEntropy (unruhAuxBlock z ks T rho)

/-- PDF pp.1,5: unrestricted finite-ensemble Holevo capacity of the exact
n-use countable-output channel, before any single-letter identity is asserted. -/
def unruhHolevo (z : ℝ) (n : ℕ) : ℝ :=
  sSup (entropyHolevoValues (unruhReceiverEntropy (n := n) z))

/-- PDF pp.1,5: unrestricted Holevo optimization on U_z^tensor n tensor T. -/
def unruhAuxHolevo {a b : ℕ} (z : ℝ) (n : ℕ)
    (T : Superop (Fin a) (Fin b)) : ℝ :=
  sSup (entropyHolevoValues (unruhAuxEntropy z n T))

/-- PDF p.1: all positive regularized block rates of the full Unruh channel. -/
def unruhClassicalRates (z : ℝ) : Set ℝ :=
  Set.range (fun m : ℕ => unruhHolevo z (m+1) / (m+1 : ℝ))

/-- PDF pp.1,5: regularized classical capacity; it is not defined by Eq.(23). -/
def unruhClassicalCapacity (z : ℝ) : ℝ := sSup (unruhClassicalRates z)

/-- PDF pp.2,5: analytic well-definedness of the exact infinite output.
These conditions are conclusions, never assumptions replacing capacity content.
The finite ensembles and all finite auxiliary references include mixed inputs
entangled across every channel use. -/
def UnruhRegular (z : ℝ) : Prop :=
  (∀ k, 0 ≤ unruhWeight z k) ∧ HasSum (unruhWeight z) 1 ∧
  (∀ n : ℕ, 1 ≤ n →
    (∀ rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
      IsDensityMatrix rho → Summable (fun ks : Fin n → ℕ =>
        vnEntropy (QAlgorithms.Papers.Independent.Support50.P01.unruhReceiverBlock z ks rho))) ∧
    (entropyHolevoValues (unruhReceiverEntropy (n := n) z)).Nonempty ∧
    BddAbove (entropyHolevoValues (unruhReceiverEntropy (n := n) z))) ∧
  BddAbove (unruhClassicalRates z) ∧
  (∀ a b : ℕ, 0 < a → 0 < b → ∀ T : Superop (Fin a) (Fin b), IsChannel T →
    ∀ n : ℕ, 1 ≤ n →
      (∀ rho : Matrix ((Fin n → Fin 2) × Fin a) ((Fin n → Fin 2) × Fin a) ℂ,
        IsDensityMatrix rho → Summable (fun ks : Fin n → ℕ =>
          vnEntropy (unruhAuxBlock z ks T rho))) ∧
      (entropyHolevoValues (unruhAuxEntropy z n T)).Nonempty ∧
      BddAbove (entropyHolevoValues (unruhAuxEntropy z n T)))

/-- PDF p.5, Eq.(23): first infinite series, ell=k+2. -/
def unruhFirstTerm (z : ℝ) (k : ℕ) : ℝ :=
  unruhWeight z k * Real.logb 2 (k+1 : ℝ)

/-- PDF p.5, Eq.(23): second infinite series with its own p_ell/Delta_ell. -/
def unruhSecondTerm (z : ℝ) (k : ℕ) : ℝ :=
  unruhWeight z k / clonerDelta k * clonerLogSum k

/-- PDF pp.5--6, Eqs.(24)--(26): normalized occupation coefficient of
Sym^(2k+1)(C^2) inside Sym^k(C^2) tensor Sym^(k+1)(C^2), with the ordinary
SU(2) tensor action. This fixes the highest irrep, including its phases. -/
def highestCoupling (k : ℕ) (a : Fin (k+1)) (i : Fin (k+2)) : ℝ :=
  Real.sqrt (((Nat.choose k a.val : ℝ) * Nat.choose (k+1) i.val) /
    (Nat.choose (2*k+1) (a.val+i.val) : ℝ))

/-- PDF p.6: orthogonal highest-irrep projector, output factor first.
Its irrep dimension is 2k+2, not the full (k+1)(k+2) tensor dimension. -/
def highestProjector (k : ℕ) :
    Matrix (Fin (k+1) × Fin (k+2)) (Fin (k+1) × Fin (k+2)) ℂ :=
  fun ai bj => if ai.1.val + ai.2.val = bj.1.val + bj.2.val then
    ((highestCoupling k ai.1 ai.2 * highestCoupling k bj.1 bj.2 : ℝ) : ℂ) else 0

/-- PDF p.6: unnormalized Choi ansatz. Trace preservation forces the
coefficient (k+2)/(2k+2)=ell/(2ell-2). -/
def degradingChoi (k : ℕ) :
    Matrix (Fin (k+1) × Fin (k+2)) (Fin (k+1) × Fin (k+2)) ℂ :=
  (((k+2 : ℝ) / (2*k+2 : ℝ) : ℝ) : ℂ) • highestProjector k

/-- PDF p.6: Choi reconstruction Tr_in[(I tensor X^T)R], output first.
There is no normalized-Choi dimension factor or extra input conjugation. -/
def highestDegradingMap (k : ℕ) : Superop (Fin (k+2)) (Fin (k+1)) :=
  fun X a b => ∑ i, ∑ j, X i j * degradingChoi k (a,i) (b,j)

/-- The complement and receiver are tied to exactly one dilation. -/
example : cloner 0 = receiverChannel (unruhSectorDilation 0) ∧
    clonerComplement 0 = complementaryChannel (unruhSectorDilation 0) := ⟨rfl, rfl⟩

/-- Positive regularization lengths include one use. -/
example {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (N : Superop I O) :
    holevoCapacity (piSuperop (fun _ : Fin 1 => N)) / (1 : ℝ) ∈ Set.range (fun m : ℕ =>
      holevoCapacity (piSuperop (fun _ : Fin (m+1) => N)) / (m+1 : ℝ)) := by
  refine ⟨0, ?_⟩
  simp

/-- Transposing twice restores every operator, not just the Hermitian ones. -/
example {I O : Type} (N : Superop I O) : transposeOutput (transposeOutput N) = N := rfl

/-- Identity-sector normalization and zero-log-zero convention in Eq.(16). -/
example : clonerDelta 0 = 1 ∧ (0 : ℝ) * Real.logb 2 0 = 0 := by
  norm_num [clonerDelta]

/-- Normalized singleton ensembles give zero Holevo information for any H. -/
example {I : Type} [Fintype I] [DecidableEq I] (H : Matrix I I ℂ → ℝ)
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) :
    0 ∈ entropyHolevoValues H := by
  refine ⟨1, (fun _ => 1), (fun _ => rho), ?_, ?_, ?_, ?_⟩
  · intro j; norm_num
  · simp
  · intro j; exact hrho
  · simp

/-- At zero acceleration only the identity sector survives. -/
example : unruhWeight 0 0 = 1 ∧ unruhWeight 0 1 = 0 := by
  norm_num [unruhWeight]

/-- Highest-weight phase and the trace-map Choi normalization at ell=2. -/
example : highestCoupling 1 0 0 = 1 ∧ degradingChoi 0 (0,0) (0,0) = 1 := by
  norm_num [highestCoupling, degradingChoi, highestProjector]

end QAlgorithms.Papers.Independent.Intakenext100.P49


