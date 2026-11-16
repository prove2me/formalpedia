-- Prove2me | Definitions.Def_ConcurrentStochasticApprox_Approx_Supplement_Decision
-- name    : ConcurrentStochasticApprox_Approx_Supplement_Decision
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:30:13.790344+00:00
-- url     : https://prove2.me/theorems/ade65b75-5998-4124-8e68-b1e36ca7c37e
-- title:
--   §2, Theorem 4.1 — Exact value decision and restricted instance codes
-- statement:
--   An input game has rational transition probabilities, a nonempty finite state set and two nonempty finite action sets. For a state $s$ and an arbitrary rational threshold $\alpha$, the reachability language contains the code of $(G,T,s,\alpha)$ exactly when $\alpha\le\operatorname{val}_T(s)$. The limit-average language contains the code of $(G,r,s,\alpha)$ exactly when $r$ is rational and $[0,1]$-valued and $\alpha\le\operatorname{val}(s)$. The games, objectives, full-history strategies and values are the published base definitions. The binary code concatenates the published self-delimiting game, target/reward, state and rational-threshold fields. There is no accuracy field and no promise. Malformed strings, invalid distributions, invalid rewards and out-of-range states are excluded.
--
--   A restricted game has exactly two actions for each player, every transition row is a Dirac distribution, and two distinct states $t_1,t_2$ are absorbing under every action pair. Every legal infinite path from every initial state reaches $\{t_1,t_2\}$, regardless of the action sequence. The path condition is sure reachability. The two restricted-code sets consist of all valid objective instances of such games at threshold exactly $1/2$, including both yes- and no-instances. There is no additional restriction on targets or rewards.
--
--   These code sets express the complete image restriction on the hardness reductions independently of their membership equivalences.
-- source:
--   Ali Asadi, Krishnendu Chatterjee, STOC 2027 submission #285 (October 2026), §2 computational problems, printed 5 (PDF 7); Theorem 4.1, printed 10 (PDF 12); §8.1, printed 32–35 (PDF 34–37)

import Mathlib
import Definitions.Def_ConcurrentStochasticApprox_Approx_Problems

/-! §2, printed p. 5 (PDF 7), and Theorem 4.1, printed p. 10 (PDF 12).
Exact decision has a rational threshold, no accuracy field and no promise.
Only valid encodings are admitted. The hardness image restriction is independent of
the value comparison: it must hold for yes- and no-inputs alike.
-/

open NetworkEquilibriumCLS.LinearNash

noncomputable section

namespace ConcurrentStochasticApprox.Approx.Supplement

def reachDecisionCode (G : RatGame) (T : Fin G.n → Bool) (s : ℕ) (α : ℚ) : List Bool :=
  G.enc ++ encTarget T ++ encNat s ++ encRat α

def limAvgDecisionCode (G : RatGame) (r : RatReward G) (s : ℕ) (α : ℚ) : List Bool :=
  G.enc ++ encList encRat r.entries ++ encNat s ++ encRat α

/-- CsgDecision for reachability; thresholds range over all rationals. -/
def reachDecision : CookPvsNP.Lang Bool :=
  {bs | ∃ (G : RatGame) (h : G.Valid) (T : Fin G.n → Bool) (s : ℕ) (hs : s < G.n) (α : ℚ),
    reachDecisionCode G T s α = bs ∧
      (α : ℝ) ≤ reachValue (G.toCSG h) (targetSet T) ⟨s, hs⟩}

/-- CsgDecision for limit-average; invalid rewards and malformed strings are excluded. -/
def limAvgDecision : CookPvsNP.Lang Bool :=
  {bs | ∃ (G : RatGame) (h : G.Valid) (r : RatReward G), r.Valid ∧
    ∃ (s : ℕ) (hs : s < G.n) (α : ℚ), limAvgDecisionCode G r s α = bs ∧
      (α : ℝ) ≤ limAvgValue (G.toCSG h) r.toReal ⟨s, hs⟩}

/-- Exactly two actions per player, Dirac transitions, and two distinct absorbing states
that every play reaches. Quantifying all legal paths includes every initial state and
every infinite action sequence; the property is sure reachability. -/
def RestrictedGame (G : RatGame) : Prop :=
  G.Valid ∧ G.mA = 2 ∧ G.mB = 2 ∧
  (∀ s a b, ∃ t : Fin G.n, ∀ s', G.δ s a b s' = if s' = t then 1 else 0) ∧
  ∃ t₁ t₂ : Fin G.n, t₁ ≠ t₂ ∧
    (∀ a b, G.δ t₁ a b t₁ = 1 ∧ G.δ t₂ a b t₂ = 1) ∧
    ∀ ω : Play G.n G.mA G.mB,
      (∀ i, 0 < G.δ (ω i).1 (ω i).2.1 (ω i).2.2 (ω (i + 1)).1) →
      ∃ i, (ω i).1 = t₁ ∨ (ω i).1 = t₂

/-- Codes of restricted reachability instances with threshold exactly one half.
This set contains both yes- and no-instances. -/
def restrictedReachCodes : Set (List Bool) :=
  {bs | ∃ (G : RatGame), RestrictedGame G ∧
    ∃ (T : Fin G.n → Bool) (s : ℕ), s < G.n ∧ reachDecisionCode G T s (1 / 2) = bs}

/-- Codes of restricted limit-average instances with threshold exactly one half. -/
def restrictedLimAvgCodes : Set (List Bool) :=
  {bs | ∃ (G : RatGame), RestrictedGame G ∧
    ∃ (r : RatReward G), r.Valid ∧
    ∃ s : ℕ, s < G.n ∧ limAvgDecisionCode G r s (1 / 2) = bs}

end ConcurrentStochasticApprox.Approx.Supplement


