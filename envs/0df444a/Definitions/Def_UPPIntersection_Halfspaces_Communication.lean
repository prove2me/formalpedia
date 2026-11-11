-- Prove2me | Definitions.Def_UPPIntersection_Halfspaces_Communication
-- name    : UPPIntersection_Halfspaces_Communication
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:26:58.561441+00:00
-- url     : https://prove2.me/theorems/172e0d9d-9feb-4b74-8408-81304167e611
-- title:
--   §1–2 — private-coin protocols and unbounded-error communication complexity $U(F)$
-- statement:
--   Alice holds $a\in A$, Bob holds $b\in B$, and they want to compute a known function $F:A\times B\to\{-1,1\}$ (stored as a bit, $\mathsf{true}$ standing for $+1$). Each player has an **unlimited private random tape** $\omega\in\{0,1\}^{\mathbb N}$ of independent fair bits; the two tapes are independent. A **private-coin protocol** is a binary protocol tree: at an internal node one player sends a bit that may depend on that player's input and that player's tape (and, through the position in the tree, on the bits sent so far); a leaf carries the output. Its **cost** is the depth of the tree, the largest number of bits exchanged on any run.
--
--   The protocol **computes $F$ with unbounded error** if every bit function is measurable in the speaker's tape and, for each input pair $(a,b)$,
--   $$\Pr_{\omega_A,\omega_B}\bigl[\text{output on }(a,\omega_A),(b,\omega_B)=F(a,b)\bigr]>\tfrac12 .$$
--   The **unbounded-error communication complexity** is
--   $$U(F)=\min\{\operatorname{cost}(P): P \text{ computes } F \text{ with unbounded error}\}.$$
--   For finite input sets the deterministic protocol in which Alice announces her input and Bob announces the answer shows that this set is nonempty, so the minimum exists.
--
--   These are the objects of the paper's headline theorem: $U(F)$ is polylogarithmic in the input length exactly for the problems in $\mathrm{UPP}^{cc}$, and Theorem 2.1 relates it to sign rank.
--
--   **Formalization Note** Trees are the published `DetCCHard.Protocol` over `(input, tape)` pairs; the tape law is `Measure.infinitePi` of fair coins on `ℕ → Bool`; the output is the leaf label (transcript-determined), a convention that changes $U$ by at most one. $U$ is an `sInf` over attainable costs; it is never defined through sign rank.
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 3 (§1, definition of the unbounded-error model and U(F)) and p. 13 (§2, recalled definition of U); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_DetCCHard_Protocol

namespace UPPIntersection.Halfspaces

open MeasureTheory

/-- An unlimited private random tape: an infinite sequence of random bits. -/
abbrev Tape : Type := ℕ → Bool

/-- The fair coin on `Bool`: each bit has probability `1/2`. -/
noncomputable def fairCoin : Measure Bool :=
  (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairCoin := by
  constructor
  simp only [fairCoin, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The law of an unlimited sequence of independent fair bits (infinite product measure). -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi (fun _ : ℕ => fairCoin)

/-- A **private-coin protocol** for Alice holding `a : α` and Bob holding `b : β`: a deterministic
public-output protocol tree in which each of Alice's bits is a function of her input and her own
private tape, and each of Bob's bits a function of his input and his own private tape. The output
is the label of the leaf reached; its cost is the depth of the tree (maximum number of bits sent). -/
abbrev PrivateCoinProtocol (α β : Type) : Type :=
  DetCCHard.Protocol (α × Tape) (β × Tape)

/-- Every bit function of the protocol is measurable in the speaker's private tape, for every fixed
input of the speaker. This makes all success events measurable. -/
def CoinMeasurable {α β : Type} : PrivateCoinProtocol α β → Prop
  | .leaf _ => True
  | .alice f p₀ p₁ =>
      (∀ a : α, Measurable fun ω : Tape => f (a, ω)) ∧ CoinMeasurable p₀ ∧ CoinMeasurable p₁
  | .bob g p₀ p₁ =>
      (∀ b : β, Measurable fun ω : Tape => g (b, ω)) ∧ CoinMeasurable p₀ ∧ CoinMeasurable p₁

/-- The probability, over Alice's and Bob's independent private tapes, that the protocol outputs
`F a b` on the input pair `(a, b)`. -/
noncomputable def successProb {α β : Type} (P : PrivateCoinProtocol α β)
    (F : α → β → Bool) (a : α) (b : β) : ENNReal :=
  (tapeLaw.prod tapeLaw) {ω : Tape × Tape | P.eval (a, ω.1) (b, ω.2) = F a b}

/-- The protocol computes `F` with **unbounded error**: it is coin-measurable and on each input pair
it outputs the correct value with probability strictly greater than `1/2`. -/
def ComputesUnbounded {α β : Type} (P : PrivateCoinProtocol α β) (F : α → β → Bool) : Prop :=
  CoinMeasurable P ∧ ∀ a b, (2⁻¹ : ENNReal) < successProb P F a b

/-- The **unbounded-error communication complexity** `U(F)`: the minimum worst-case number of bits
exchanged by a private-coin protocol computing `F` with unbounded error. (For finite input sets
the trivial deterministic protocol shows the set of attainable costs is nonempty.) -/
noncomputable def U {α β : Type} (F : α → β → Bool) : ℕ :=
  sInf {c : ℕ | ∃ P : PrivateCoinProtocol α β, ComputesUnbounded P F ∧ P.depth ≤ c}

end UPPIntersection.Halfspaces


