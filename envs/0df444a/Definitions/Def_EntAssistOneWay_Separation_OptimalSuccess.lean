-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_OptimalSuccess
-- name    : EntAssistOneWay_Separation_OptimalSuccess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:30.488698+00:00
-- url     : https://prove2.me/theorems/4909dd74-1688-4bae-b631-d6c45ecb841f
-- title:
--   Success and optimal-state values for partial functions
-- statement:
--   Let $\mathrm{Dom}\subseteq X\times Y$ be a finite domain, let $f:\mathrm{Dom}\to\{0,1\}$, and let $\mu$ be a probability law on that domain. For an unassisted $C$-qubit strategy $P$ define its average success by the weighted sum of correct-output Born probabilities. For a family of binary effects $M^y_1$ with $M^y_0=I-M^y_1$, define
--   $$V(M)=\sum_{x\in X}\left\|\sum_{t\in\mathrm{Dom}:t_X=x}\mu(t)M^{t_Y}_{f(t)}\right\|_\infty.$$
--
--   This is the conditional-expectation expression in Lemma 3.2 with the marginal probability absorbed inside the norm. It is defined even when an Alice marginal is zero and keeps the function partial. Neither an optimal state nor its value is a free parameter constrained by the desired theorem.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 16, Lemma 3.2 and its distributional success formula

import Definitions.Def_EntAssistOneWay_Separation_Analysis
import Definitions.Def_EntAssistOneWay_Separation_Probability
import Definitions.Def_EntAssistOneWay_Separation_POVM

open scoped BigOperators ComplexOrder
open Classical
open BooleanHiddenPartition.LowerBounds
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- The output-1 effect of an unassisted strategy, bundled as a binary POVM. -/
def strategyEffect {X Y : Type} {C : ℕ} (P : QuantumStrategy X Y C)
    (y : Y) : BinaryEffect (Fin (2 ^ C)) :=
  ⟨P.effect y, P.positive y, P.complement_positive y⟩

/-- The correct-outcome POVM operator for a bit. -/
def outcomeEffect {I : Type} [Fintype I] [DecidableEq I]
    (M : BinaryEffect I) (b : Bool) : Matrix I I ℂ :=
  if b then M.op else 1 - M.op

/-- Distributional success for a genuinely partial function on Dom. -/
def partialSuccess {X Y : Type} [Fintype X] [Fintype Y] {C : ℕ}
    (Dom : Finset (X × Y)) (f : Dom → Bool) (μ : FiniteLaw Dom)
    (P : QuantumStrategy X Y C) : ℝ :=
  ∑ t : Dom, μ.mass t *
    (if f t then quantumAccept P t.val.1 t.val.2 else 1 - quantumAccept P t.val.1 t.val.2)

/-- The unconditioned form of the optimal-state expression in Lemma 3.2.
Rows with marginal mass zero contribute the norm of the zero matrix. -/
def povmValue {X Y : Type} [Fintype X] [Fintype Y] {C : ℕ}
    (Dom : Finset (X × Y)) (f : Dom → Bool) (μ : FiniteLaw Dom)
    (M : Y → BinaryEffect (Fin (2 ^ C))) : ℝ :=
  ∑ x : X, spectralNorm (∑ t : Dom,
    if t.val.1 = x then (μ.mass t : ℂ) • outcomeEffect (M t.val.2) (f t) else 0)

end

end EntAssistOneWay.Separation


