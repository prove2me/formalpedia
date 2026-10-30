-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P35
-- name    : QAlgorithms_Papers_Independent_Bridge50_P35
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T16:11:57.279976+00:00
-- url     : https://prove2.me/theorems/28789426-9a23-4586-9dea-1727b25bf35b
-- title:
--   Definitions for "Pretty strong" converse for the private capacity of degraded quantum wiretap channels
-- statement:
--   The objects the formalized statements of *"Pretty strong" converse for the private capacity of degraded quantum wiretap channels* (arXiv:1601.06611) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CqqChannel`: Section II, PDF p.1: a cqq channel with normalized joint output on B,E. Nonempty finite registers are imposed by the result binders.
--   - `CqqChannel.IsDegraded`: Section II, PDF p.1: one CPTP degrading map reproduces every Eve marginal from the corresponding Bob marginal. No complementary-channel or isometric-channel-input assumption is made.
--   - `encodedOutput`: Section II, PDF pp.1–2: the actual channel output conditioned on u. The accepted cqPower tensors the fixed letter outputs independently and groups all Bob registers before all Eve registers.
--   - `decodingState`: Equation (1), PDF p.1: the actual classical U,Uhat marginal. U is uniform; off-diagonal classical entries vanish.
--   - `secrecyState`: Equation (2), PDF p.1: the actual U,E^n marginal, before or after Bob's measurement, which does not change this marginal.
--   - `idealSecrecyState`: Equation (2), PDF p.1: the uniform message marginal tensor a single common normalized comparison state sigma. The density condition is in cqqCodeGood.
--   - `cqqCodeGood`: Equations (1)–(2), PDF p.1: two separate purified-distance errors. The comparison sigma is optimized and need not be the actual Eve marginal. The accepted generalized purified distance reduces to sqrt(1-F_root^2) on these normalized states.
--   - `logMessageNumber`: Section II, PDF p.1: log_2 of the largest admissible message number, equivalently the supremum of log_2 M over actual codes. Taking this supremum in EReal preserves an unbounded value at error one and an empty feasible set at impossible tolerances; neither becomes a spurious real zero. For nonnegative tolerances and epsilon<1 the finite-dimensional coding model makes this a finite, attained maximum, with M=1 feasible.
--   - `cqqBlockRate`: Section II, PDF p.1: rate in bits per use. The unused zero-blocklength term is explicitly zero, so no division by zero or zero-times-infinity convention enters the asymptotics.
--   - `cqqPrivateCapacity`: Section II, PDF p.1: the operational private capacity, exactly the infimum over positive transmission and secrecy tolerances of the liminf of their optimal block rates. This is not defined by a single-letter information formula. EReal extrema retain all endpoint values; for finite nonempty alphabets and registers the resulting capacity is finite.
-- source:
--   "Pretty strong" converse for the private capacity of degraded quantum wiretap channels, arXiv:1601.06611v2, https://arxiv.org/abs/1601.06611v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-!
Winter, arXiv:1601.06611v2, PDF pp.1–5. Only Theorem 2's finite-block
bound and its separately documented positive-tolerance limit are drafted.
The accepted paper modules supply only reviewed definitions: cqPower,
P56.PrivateCode (stochastic encoding and a POVM), purifiedDistance, and
idealClassicalKey. Their operational capacities, error predicates, and
quantum-input code models are not used.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P35

open scoped BigOperators Matrix ComplexConjugate
open Filter
open QAlgorithms.Papers.Independent.Dependency50.P48 (cqPower)
open QAlgorithms.Papers.Independent.Information100.P56 (PrivateCode)
open QAlgorithms.Papers.Independent.Information100.P67
  (purifiedDistance idealClassicalKey)

attribute [local instance] Classical.propDecidable

variable {X B E : Type*}
variable [Fintype X] [DecidableEq X]
variable [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E]

/-- Section II, PDF p.1: a cqq channel with normalized joint output on B,E.
Nonempty finite registers are imposed by the result binders. -/
structure CqqChannel (X B E : Type*) [Fintype B] [Fintype E] where
  output : X → Matrix (B × E) (B × E) ℂ
  density : ∀ x, IsDensityMatrix (output x)

/-- Section II, PDF p.1: one CPTP degrading map reproduces every Eve
marginal from the corresponding Bob marginal. No complementary-channel
or isometric-channel-input assumption is made. -/
def CqqChannel.IsDegraded (W : CqqChannel X B E) : Prop :=
  ∃ D : Superop B E, IsChannel D ∧
    ∀ x, D (traceRight (W.output x)) = traceLeft (W.output x)

/- Section II, PDF p.1: reuse the accepted P56.PrivateCode raw code data.
Its positive message count, whole-string stochastic law, and Bob POVM match
this paper exactly. Its separate error/leakage definitions are not used. -/

/-- Section II, PDF pp.1–2: the actual channel output conditioned on u.
The accepted cqPower tensors the fixed letter outputs independently and
groups all Bob registers before all Eve registers. -/
def encodedOutput (W : CqqChannel X B E) {n : ℕ}
    (code : PrivateCode X B n) (u : Fin code.messages) :
    Matrix ((Fin n → B) × (Fin n → E))
      ((Fin n → B) × (Fin n → E)) ℂ :=
  ∑ x, (code.input u x : ℂ) • cqPower W.output n x

/-- Equation (1), PDF p.1: the actual classical U,Uhat marginal.
U is uniform; off-diagonal classical entries vanish. -/
def decodingState (W : CqqChannel X B E) {n : ℕ}
    (code : PrivateCode X B n) :
    Matrix (Fin code.messages × Fin code.messages)
      (Fin code.messages × Fin code.messages) ℂ :=
  fun a b => if a = b then
    (code.messages : ℂ)⁻¹ * (effectProb (code.decoder a.2)
      (traceRight (encodedOutput W code a.1)) : ℂ)
  else 0

/-- Equation (2), PDF p.1: the actual U,E^n marginal, before or after
Bob's measurement, which does not change this marginal. -/
def secrecyState (W : CqqChannel X B E) {n : ℕ}
    (code : PrivateCode X B n) :
    Matrix (Fin code.messages × (Fin n → E)) (Fin code.messages × (Fin n → E)) ℂ :=
  fun a b => if a.1 = b.1 then
    (code.messages : ℂ)⁻¹ * traceLeft (encodedOutput W code a.1) a.2 b.2
  else 0

/-- Equation (2), PDF p.1: the uniform message marginal tensor a single
common normalized comparison state sigma. The density condition is in cqqCodeGood. -/
def idealSecrecyState (M : ℕ) {n : ℕ}
    (sigma : Matrix (Fin n → E) (Fin n → E) ℂ) :
    Matrix (Fin M × (Fin n → E)) (Fin M × (Fin n → E)) ℂ :=
  fun a b => if a.1 = b.1 then (M : ℂ)⁻¹ * sigma a.2 b.2 else 0

/-- Equations (1)–(2), PDF p.1: two separate purified-distance errors.
The comparison sigma is optimized and need not be the actual Eve marginal.
The accepted generalized purified distance reduces to sqrt(1-F_root^2)
on these normalized states. -/
def cqqCodeGood {n : ℕ} (code : PrivateCode X B n)
    (W : CqqChannel X B E) (epsilon delta : ℝ) : Prop :=
  purifiedDistance (decodingState W code) (idealClassicalKey code.messages) ≤ epsilon ∧
    ∃ sigma : Matrix (Fin n → E) (Fin n → E) ℂ,
      IsDensityMatrix sigma ∧
        purifiedDistance (secrecyState W code) (idealSecrecyState code.messages sigma) ≤ delta

/-- Section II, PDF p.1: log_2 of the largest admissible message number,
equivalently the supremum of log_2 M over actual codes. Taking this supremum
in EReal preserves an unbounded value at error one and an empty feasible set
at impossible tolerances; neither becomes a spurious real zero.
For nonnegative tolerances and epsilon<1 the finite-dimensional coding
model makes this a finite, attained maximum, with M=1 feasible. -/
def logMessageNumber (W : CqqChannel X B E) (n : ℕ)
    (epsilon delta : ℝ) : EReal :=
  sSup {r : EReal | ∃ code : PrivateCode X B n,
    cqqCodeGood code W epsilon delta ∧
      r = (Real.logb 2 (code.messages : ℝ) : EReal)}

/-- Section II, PDF p.1: rate in bits per use. The unused zero-blocklength
term is explicitly zero, so no division by zero or zero-times-infinity
convention enters the asymptotics. -/
def cqqBlockRate (W : CqqChannel X B E) (n : ℕ) (epsilon delta : ℝ) : EReal :=
  if n = 0 then 0 else ((n : ℝ)⁻¹ : EReal) * logMessageNumber W n epsilon delta

/-- Section II, PDF p.1: the operational private capacity, exactly the
infimum over positive transmission and secrecy tolerances of the liminf
of their optimal block rates. This is not defined by a single-letter
information formula. EReal extrema retain all endpoint values; for finite
nonempty alphabets and registers the resulting capacity is finite. -/
def cqqPrivateCapacity (W : CqqChannel X B E) : EReal :=
  ⨅ (epsilon : ℝ) (_ : 0 < epsilon) (delta : ℝ) (_ : 0 < delta),
    Filter.liminf (fun n : ℕ => cqqBlockRate W n epsilon delta) atTop

/-- Empty tensor products are one: the zero-use channel adds no output
information (Section II, PDF p.1). This is only a kernel sanity check. -/
example (W : CqqChannel X B E) (x : Fin 0 → X)
    (a b : (Fin 0 → B) × (Fin 0 → E)) : cqPower W.output 0 x a b = 1 := by
  simp [cqPower]

/-- With a single message, the comparison has precisely sigma's entries. -/
example {n : ℕ} (sigma : Matrix (Fin n → E) (Fin n → E) ℂ)
    (e f : Fin n → E) : idealSecrecyState 1 sigma (0, e) (0, f) = sigma e f := by
  simp [idealSecrecyState]

/-- The zero-length rate is the deliberately explicit unused value zero. -/
example (W : CqqChannel X B E) (epsilon delta : ℝ) :
    cqqBlockRate W 0 epsilon delta = 0 := by
  simp [cqqBlockRate]

/-- The ideal decoding target for one message is the scalar density one. -/
example : idealClassicalKey 1 (0, 0) (0, 0) = 1 := by
  simp [idealClassicalKey]

end QAlgorithms.Papers.Independent.Bridge50.P35


