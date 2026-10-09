-- Prove2me | Definitions.Def_OCB2012_appA
-- name    : OCB2012_appA
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-09T09:43:59.132832+00:00
-- url     : https://prove2.me/theorems/900a08f3-8591-4197-866a-9c20704e498a
-- title:
--   Event-based setting of the causal inequality: causal relation of $A_1, B_1$, joint distribution of $(a,b,b',x,y)$, $p_{succ}$
-- statement:
--   Definitions for the event-based derivation of the causal inequality in Appendix A of Oreshkov, Costa and Brukner (2012).
--
--   1. **Causal relation $R$.** Assumption CS places the events $A_1$ and $B_1$ (the system entering Alice's and Bob's laboratory) in a causal structure. Their relation is then exactly one of $A_1\preceq B_1$, $B_1\preceq A_1$, or $A_1\not\preceq\not\succeq B_1$, encoded as `CausalRel.AB`, `CausalRel.BA` and `CausalRel.incomparable`.
--   2. **Joint distribution.** `EventDist` is a joint distribution $p(a,b,b',x,y,R)$ of Alice's bit $a$, Bob's bits $b, b'$, the guesses $x$ (Alice) and $y$ (Bob), and $R$. Bits are encoded as Booleans, with $0\mapsto$ `false`. `IsProb` requires it to be non-negative and normalized. `pr` gives the probability of an event, and `cond` the conditional probability $p(E\mid F) = p(E\wedge F)/p(F)$, set to $0$ when $p(F)=0$.
--   3. **Success probability, Eq. (9):**
--   $$p_{succ} = \tfrac12\,p(x=b\mid b'=0) + \tfrac12\,p(y=a\mid b'=1).$$
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, Appendix A, pp. 6-7 (assumptions CS, FC, CL and Eqs. (9)-(10))

import Mathlib

/-!
# Event-based setting of the causal inequality (Oreshkov–Costa–Brukner 2012, App. A)

O. Oreshkov, F. Costa, Č. Brukner, *Quantum correlations with no causal order*,
Nat. Commun. 3, 1092 (2012), arXiv:1105.4464v3, Appendix A ("Formal derivation of the causal
inequality"), pp. 6–7.

The relevant random variables are Alice's bit `a`, Bob's bits `b, b'`, the guesses `x` (Alice)
and `y` (Bob), and the causal relation `R` between the events `A1` and `B1` (the system
entering Alice's and Bob's laboratory). Bits are encoded as `Bool` (`false ↦ 0`, `true ↦ 1`).
Under assumption CS the three possibilities `A1 ⪯ B1`, `B1 ⪯ A1`, `A1 ⋠⋡ B1` are mutually
exclusive and exhaustive, so `R` takes exactly three values.
-/

namespace OCB2012

/-- App. A (CS): the causal relation between `A1` and `B1`. -/
inductive CausalRel
  /-- `A1 ⪯ B1`: `A1` is in the causal past of `B1`. -/
  | AB
  /-- `B1 ⪯ A1`: `B1` is in the causal past of `A1`. -/
  | BA
  /-- `A1 ⋠⋡ B1`: neither is in the causal past of the other. -/
  | incomparable
  deriving DecidableEq

instance : Fintype CausalRel :=
  ⟨{CausalRel.AB, CausalRel.BA, CausalRel.incomparable}, fun x => by cases x <;> simp⟩

/-- A joint distribution of `(a, b, b', x, y, R)`, listed in this order. -/
abbrev EventDist := Bool → Bool → Bool → Bool → Bool → CausalRel → ℝ

namespace EventDist

/-- `P` is a probability distribution. -/
def IsProb (P : EventDist) : Prop :=
  (∀ a b b' x y R, 0 ≤ P a b b' x y R) ∧
    ∑ a, ∑ b, ∑ b', ∑ x, ∑ y, ∑ R, P a b b' x y R = 1

/-- The probability `p(E)` of an event `E`, given as a Boolean predicate of
`(a, b, b', x, y, R)`. -/
noncomputable def pr (P : EventDist) (E : Bool → Bool → Bool → Bool → Bool → CausalRel → Bool) :
    ℝ :=
  ∑ a, ∑ b, ∑ b', ∑ x, ∑ y, ∑ R, if E a b b' x y R then P a b b' x y R else 0

/-- The conditional probability `p(E | F) = p(E ∧ F) / p(F)` (equal to `0` when `p(F) = 0`). -/
noncomputable def cond (P : EventDist)
    (E F : Bool → Bool → Bool → Bool → Bool → CausalRel → Bool) : ℝ :=
  P.pr (fun a b b' x y R => E a b b' x y R && F a b b' x y R) / P.pr F

/-- Eq. (9): the success probability `p_succ = ½ p(x = b | b' = 0) + ½ p(y = a | b' = 1)`. -/
noncomputable def pSucc (P : EventDist) : ℝ :=
  (1 / 2 : ℝ) * P.cond (fun _ b _ x _ _ => decide (x = b)) (fun _ _ b' _ _ _ => decide (b' = false)) +
  (1 / 2 : ℝ) * P.cond (fun a _ _ _ y _ => decide (y = a)) (fun _ _ b' _ _ _ => decide (b' = true))

end EventDist

end OCB2012


