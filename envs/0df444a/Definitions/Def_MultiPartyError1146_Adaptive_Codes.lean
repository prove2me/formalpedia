-- Prove2me | Definitions.Def_MultiPartyError1146_Adaptive_Codes
-- name    : MultiPartyError1146_Adaptive_Codes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T18:32:47.260477+00:00
-- url     : https://prove2.me/theorems/8e2ee4e9-84eb-462f-8261-2b71b49499fc
-- title:
--   Binary encoders, joint-pattern balance, bounded-distance decoding and selectors
-- statement:
--   A binary encoder maps messages to words of a specified finite length $\ell$. Relative distance at least $d$ means $d_H(C(x),C(y))\ge d\ell$ for every distinct pair. Joint-pattern balance is Definition 3.3:
--   $$|\{t:(C_t(x_1),\ldots,C_t(x_d))=(b_1,\ldots,b_d)\}|\ge \zeta\ell/2^d$$
--   for every tuple of distinct messages and every prescribed bit pattern. Decoding selects a message at ternary Hamming discrepancy strictly below $0.49\ell/2$, or returns failure. Erasures count as discrepancies. All maps are deterministic; quality is stated separately from encoder data.
--
--   A selector family $(S^{(t)})_{t<q}$ consists of sets of size at most $\sqrt n$. For every $U$ of size at most $\sqrt n$ and $i\in U$, at least $q/(10\sqrt n)$ members intersect $U$ in exactly $\{i\}$. These predicates provide reusable finite coding and selector interfaces without assuming their existence.
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Sections 3.1–3.2; Definition 3.3, printed p.18, PDF p.20

import Mathlib

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

/-- An encoder, without any distance, balance or existence assertion. -/
structure BinaryCode (α : Type) where
  length : ℕ
  encode : α → Fin length → Bool

noncomputable def BinaryCode.HasDistance {α : Type} (C : BinaryCode α) (d : ℝ) : Prop :=
  ∀ a b, a ≠ b → d * C.length ≤ (hammingDist (C.encode a) (C.encode b) : ℝ)

/-- Definition 3.3: all joint patterns on distinct messages, rather than marginal balance. -/
noncomputable def BinaryCode.Balanced {α : Type} (C : BinaryCode α) (d : ℕ) (ζ : ℝ) : Prop := by
  classical
  exact ∀ (xs : Fin d → α), Function.Injective xs → ∀ bits : Fin d → Bool,
    ζ * (C.length : ℝ) / (2 : ℝ) ^ d ≤
      ((Finset.univ.filter fun t => ∀ j, C.encode (xs j) t = bits j).card : ℝ)

/-- Ternary Hamming discrepancy from a binary codeword; erasures count as errors. -/
noncomputable def BinaryCode.errors {α : Type} (C : BinaryCode α)
    (y : Fin C.length → Option Bool) (a : α) : ℕ := by
  classical
  exact (Finset.univ.filter fun t => y t ≠ some (C.encode a t)).card

/-- Fixed deterministic bounded-distance decoding; none when no word is close enough.
The distance-0.49 predicate, separately, gives uniqueness below 0.49/2. -/
noncomputable def BinaryCode.decode {α : Type} (C : BinaryCode α)
    (y : Fin C.length → Option Bool) : Option α := by
  classical
  exact if h : ∃ a, (C.errors y a : ℝ) < (49 : ℝ) / 200 * C.length
    then some (Classical.choose h) else none

/-- A selector is just a finite indexed family; its combinatorial quality is separate. -/
abbrev Selector (n q : ℕ) := Fin q → Finset (Fin n)

noncomputable def IsSelector {n q : ℕ} (S : Selector n q) : Prop := by
  classical
  exact (∀ t, ((S t).card : ℝ) ≤ Real.sqrt n) ∧
    ∀ U : Finset (Fin n), (U.card : ℝ) ≤ Real.sqrt n → ∀ i ∈ U,
      (q : ℝ) / (10 * Real.sqrt n) ≤
        ((Finset.univ.filter fun t => S t ∩ U = {i}).card : ℝ)

end MultiPartyError1146.Adaptive


