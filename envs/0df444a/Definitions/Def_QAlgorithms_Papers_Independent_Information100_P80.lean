-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80
-- name    : QAlgorithms_Papers_Independent_Information100_P80
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T13:14:17.14227+00:00
-- url     : https://prove2.me/theorems/cc306d87-a811-4194-8455-99597961696e
-- title:
--   Definitions for Strong Converses for Quantum Channel Capacities from Blowing-Up Lemmata
-- statement:
--   The objects the formalized statements of *Strong Converses for Quantum Channel Capacities from Blowing-Up Lemmata* (arXiv:2609.11771) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `OperatorLE`: PDF p.5, (8)–(11): Loewner order, rather than entrywise matrix order.
--   - `liftBR`: PDF p.5, (9): lift a BR operator to B(ER), explicitly leaving E untouched.
--   - `traceBR`: PDF p.5, (9): trace out B and R from an operator in B(ER) order.
--   - `decompositionCosts`: PDF p.6, (17): costs of all finite exact bipartite decompositions.
--   - `projectiveNorm`: PDF p.6, (17): projective norm induced by the two local spectral norms. Exact matrix-unit decompositions make this infimum nonempty; all costs are nonnegative.
--   - `groupedPower`: PDF p.9: tensor power with the regrouped bipartition B^n:E^n.
--   - `log2`: PDF p.4: base-two logarithm.
--   - `TransmissionCode`: PDF p.4, (4): arbitrary CPTP encoder and decoder with positive message dimension.
--   - `transmissionFidelity`: PDF p.4, (4): actual squared entanglement fidelity, with untouched reference.
--   - `GenerationCode`: PDF p.2: a general mixed entanglement-generation input and a joint CPTP decoder. There is no constraint on the reference marginal beyond normalization of the joint state.
--   - `generationFidelity`: PDF p.2: squared generation fidelity is overlap with the normalized entangled target.
--   - `AchievableRate`: PDF p.10: operational achievability by entanglement-transmission codes. The eventual lower bounds for every positive tolerance express liminf rate at least r.
--   - `quantumCapacity`: PDF p.10: unassisted operational quantum capacity, the supremum of achievable nonnegative rates. For a channel on positive finite registers this set contains zero and is bounded above by log₂(dim A), so the real supremum has no junk case.
-- source:
--   Strong Converses for Quantum Channel Capacities from Blowing-Up Lemmata, arXiv:2609.11771v1, https://arxiv.org/abs/2609.11771v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_Measurement

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P80

open scoped Matrix ComplexConjugate ComplexOrder
open Filter

/-- PDF p.5, (8)–(11): Loewner order, rather than entrywise matrix order. -/
def OperatorLE {I : Type*} [Fintype I] (X Y : Matrix I I ℂ) : Prop :=
  (Y - X).PosSemidef

/-- PDF p.5, (9): lift a BR operator to B(ER), explicitly leaving E untouched. -/
def liftBR {B E R : Type*} [DecidableEq E]
    (Q : Matrix (B × R) (B × R) ℂ) : Matrix (B × (E × R)) (B × (E × R)) ℂ :=
  fun i j => Q (i.1, i.2.2) (j.1, j.2.2) * if i.2.1 = j.2.1 then 1 else 0

/-- PDF p.5, (9): trace out B and R from an operator in B(ER) order. -/
def traceBR {B E R : Type*} [Fintype B] [Fintype R]
    (X : Matrix (B × (E × R)) (B × (E × R)) ℂ) : Matrix E E ℂ :=
  traceRight (traceLeft X)

/-- PDF p.6, (17): costs of all finite exact bipartite decompositions. -/
def decompositionCosts {B E : Type*} [Fintype B] [Fintype E]
    [DecidableEq B] [DecidableEq E] (Z : Matrix (B × E) (B × E) ℂ) : Set ℝ :=
  {t | ∃ (m : ℕ) (X : Fin m → Matrix B B ℂ) (Y : Fin m → Matrix E E ℂ),
    Z = ∑ j, Matrix.kronecker (X j) (Y j) ∧
    t = ∑ j, specNorm (X j) * specNorm (Y j)}

/-- PDF p.6, (17): projective norm induced by the two local spectral norms.
Exact matrix-unit decompositions make this infimum nonempty; all costs are nonnegative. -/
def projectiveNorm {B E : Type*} [Fintype B] [Fintype E]
    [DecidableEq B] [DecidableEq E] (Z : Matrix (B × E) (B × E) ℂ) : ℝ :=
  sInf (decompositionCosts Z)

/-- PDF p.9: tensor power with the regrouped bipartition B^n:E^n. -/
def groupedPower {B E : Type*} (P : Matrix (B × E) (B × E) ℂ) (n : ℕ) :
    Matrix ((Fin n → B) × (Fin n → E)) ((Fin n → B) × (Fin n → E)) ℂ :=
  fun x y => ∏ i, P (x.1 i, x.2 i) (y.1 i, y.2 i)

/-- PDF p.4: base-two logarithm. -/
def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- PDF p.4, (4): arbitrary CPTP encoder and decoder with positive message dimension. -/
structure TransmissionCode (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] where
  M : ℕ
  positive : 0 < M
  encoder : Superop (Fin M) A
  decoder : Superop B (Fin M)
  encoder_channel : IsChannel encoder
  decoder_channel : IsChannel decoder

/-- PDF p.4, (4): actual squared entanglement fidelity, with untouched reference. -/
def transmissionFidelity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (C : TransmissionCode A B) : ℝ :=
  letI : NeZero C.M := ⟨Nat.ne_of_gt C.positive⟩
  let phi := finiteMaxEntangled (Fin C.M)
  effectProb (pureDensity phi)
    (idTensorSuperop (C.decoder ∘ N ∘ C.encoder) (pureDensity phi))

/-- PDF p.2: a general mixed entanglement-generation input and a joint CPTP decoder.
There is no constraint on the reference marginal beyond normalization of the joint state. -/
structure GenerationCode (A B : Type*) [Fintype A] [Fintype B] [DecidableEq B] where
  M : ℕ
  positive : 0 < M
  input : Matrix (Fin M × A) (Fin M × A) ℂ
  input_density : IsDensityMatrix input
  decoder : Superop B (Fin M)
  decoder_channel : IsChannel decoder

/-- PDF p.2: squared generation fidelity is overlap with the normalized entangled target. -/
def generationFidelity {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) (C : GenerationCode A B) : ℝ :=
  letI : NeZero C.M := ⟨Nat.ne_of_gt C.positive⟩
  effectProb (pureDensity (finiteMaxEntangled (Fin C.M)))
    (idTensorSuperop (C.decoder ∘ N) C.input)

/-- PDF p.10: operational achievability by entanglement-transmission codes.
The eventual lower bounds for every positive tolerance express liminf rate at least r. -/
def AchievableRate {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (r : ℝ) : Prop :=
  ∃ C : (n : ℕ) → TransmissionCode (Fin n → A) (Fin n → B),
    Tendsto (fun n => transmissionFidelity (piSuperop (fun _ : Fin n => N)) (C n))
      atTop (nhds 1) ∧
    ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n in atTop, r - delta ≤ log2 ((C n).M : ℝ) / (n : ℝ)

/-- PDF p.10: unassisted operational quantum capacity, the supremum of achievable
nonnegative rates. For a channel on positive finite registers this set contains zero
and is bounded above by log₂(dim A), so the real supremum has no junk case. -/
def quantumCapacity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (N : Superop A B) : ℝ := sSup {r : ℝ | 0 ≤ r ∧ AchievableRate N r}

/-- PDF p.5: zero is below itself in Loewner order. -/
example {I : Type*} [Fintype I] : OperatorLE (0 : Matrix I I ℂ) 0 := by
  simp only [OperatorLE, sub_self]
  exact Matrix.PosSemidef.zero

/-- PDF p.5: tracing out B,R leaves exactly the E indices. -/
example {B E R : Type*} [Fintype B] [Fintype R]
    (X : Matrix (B × (E × R)) (B × (E × R)) ℂ) (e f : E) :
    traceBR X e f = ∑ r, ∑ b, X (b, (e, r)) (b, (f, r)) := rfl

/-- PDF p.5: the BR lift acts as the identity on the omitted E factor. -/
example {B E R : Type*} [DecidableEq E]
    (Q : Matrix (B × R) (B × R) ℂ) (b c : B) (e : E) (r s : R) :
    liftBR (E := E) Q (b, (e, r)) (c, (e, s)) = Q (b, r) (c, s) := by
  simp [liftBR]

/-- PDF p.6: zero has an exact empty decomposition of cost zero. -/
example {B E : Type*} [Fintype B] [Fintype E] [DecidableEq B] [DecidableEq E] :
    (0 : ℝ) ∈ decompositionCosts (0 : Matrix (B × E) (B × E) ℂ) := by
  refine ⟨0, (fun j => Fin.elim0 j), (fun j => Fin.elim0 j), ?_, ?_⟩ <;> simp

/-- PDF p.9: the empty tensor power is the scalar identity. -/
example {B E : Type*} (P : Matrix (B × E) (B × E) ℂ)
    (x y : (Fin 0 → B) × (Fin 0 → E)) : groupedPower P 0 x y = 1 := by
  simp [groupedPower]

/-- PDF p.4: a dimension-one message has zero logarithmic size. -/
example : log2 1 = 0 := by simp [log2]

/-- PDF p.5: the right partial trace of a product retains the first factor. -/
example {I J : Type*} [Fintype J] (X : Matrix I I ℂ) (Y : Matrix J J ℂ) :
    traceRight (Matrix.kronecker X Y) = Y.trace • X := by
  ext i k
  simp [traceRight, Matrix.kronecker, Matrix.trace, Finset.mul_sum, Finset.sum_mul,
    mul_comm]

/-- PDF p.9: one use preserves the original B:E ordering. -/
example {B E : Type*} (P : Matrix (B × E) (B × E) ℂ)
    (x y : (Fin 1 → B) × (Fin 1 → E)) :
    groupedPower P 1 x y = P (x.1 0, x.2 0) (y.1 0, y.2 0) := by
  simp [groupedPower]

/-- PDF p.4: the dimension-one maximally entangled target has amplitude one. -/
example : finiteMaxEntangled (Fin 1) (0, 0) = 1 := by
  simp [finiteMaxEntangled]

end QAlgorithms.Papers.Independent.Information100.P80


