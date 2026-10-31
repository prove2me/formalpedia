-- Prove2me | Definitions.Def_ParallelSmallWorlds_SEU_CorrectionC1
-- name    : ParallelSmallWorlds_SEU_CorrectionC1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:20.942244+00:00
-- url     : https://prove2.me/theorems/e2264cd8-65db-4f0f-93af-28c5f82cd6de
-- title:
--   Correction C1: the strict form of Axiom PSW5(b)
-- statement:
--   For events $R,S$ of $\Theta$ and reference events $E,F$ with $R\cap S=\emptyset=E\cap F$:
--
--   1. if $R\succeq_\Theta E$ and $S\succeq_\Theta F$, at least one strictly, then $R\cup S\succ_\Theta E\cup F$;
--   2. if $E\succeq_\Theta R$ and $F\succeq_\Theta S$, at least one strictly, then $E\cup F\succ_\Theta R\cup S$.
--
--   The proof of Lemma 1 (step (12), p.43) uses "the implication of PSW5 for strictly more likely", which Axiom PSW5(b) as printed does not provide. Without it the calibrated probability need not be additive: take $\Theta=\{a,b\}$, rank events by $v(\emptyset)=0$, $v\{a\}=v\{b\}=0.6$, $v(\Theta)=1$ and reference events by Lebesgue measure; PSW1–PSW8 as printed hold, but $\pi_{\{a\}}+\pi_{\{b\}}=1.2\neq1=\pi_\Theta$. Every finitely additive probability on $Q$ together with Lebesgue measure on $\mathcal B$ satisfies the strict form.
--
--   **Formalization Note** This is a correction of the source, kept as its own hypothesis so that every theorem using it says so.
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), Axiom PSW5(b), p.21 (PDF p.22), as used in the proof of Lemma 1(a), eq. (12), p.43 (PDF p.44)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_SmallWorld

namespace ParallelSmallWorlds.SEU

open SmallWorld

/-- **Correction C1: the strict form of Axiom PSW5(b).**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), Axiom PSW5(b), p.21 (PDF p.22), as used in the proof
of Lemma 1(a), eq. (12), p.43 (PDF p.44): "then using the implication of PSW5 for strictly more
likely, ≻Θw".

For `R, S ∈ Qw` and `E, F ∈ B` with `R ∩ S = ∅ = E ∩ F`:

1. if `R ⪰Θw E` and `S ⪰Θw F`, at least one strictly, then `R ∪ S ≻Θw E ∪ F`;
2. if `E ⪰Θw R` and `F ⪰Θw S`, at least one strictly, then `E ∪ F ≻Θw R ∪ S`.

**Formalization Note.** This is a correction, not one of the paper's axioms. PSW5(b) as printed
has only weak conclusions, and without the strict form the paper's `PΘw` need not be additive:
with `Θ = {a, b}`, every event of `Θ` ranked by `v(∅) = 0`, `v{a} = v{b} = 0.6`, `v(Θ) = 1` and
reference events by Lebesgue measure, PSW1–PSW8 as printed hold but `π{a} + π{b} = 1.2 ≠ 1 = πΘ`.
Every finitely additive probability on `Qw` together with Lebesgue measure on `B` satisfies C1. -/
structure CorrectionC1 {Θ C : Type*} (W : SmallWorld Θ C) : Prop where
  /-- Strict form of the first implication of PSW5(b). -/
  strict_ge : ∀ R ∈ W.Q, ∀ S ∈ W.Q, ∀ E ∈ RefEvents, ∀ F ∈ RefEvents, R ∩ S = ∅ → E ∩ F = ∅ →
    W.lik (Sum.inl R) (Sum.inr E) → W.lik (Sum.inl S) (Sum.inr F) →
    (W.strictLik (Sum.inl R) (Sum.inr E) ∨ W.strictLik (Sum.inl S) (Sum.inr F)) →
    W.strictLik (Sum.inl (R ∪ S)) (Sum.inr (E ∪ F))
  /-- Strict form of the second implication of PSW5(b). -/
  strict_le : ∀ R ∈ W.Q, ∀ S ∈ W.Q, ∀ E ∈ RefEvents, ∀ F ∈ RefEvents, R ∩ S = ∅ → E ∩ F = ∅ →
    W.lik (Sum.inr E) (Sum.inl R) → W.lik (Sum.inr F) (Sum.inl S) →
    (W.strictLik (Sum.inr E) (Sum.inl R) ∨ W.strictLik (Sum.inr F) (Sum.inl S)) →
    W.strictLik (Sum.inr (E ∪ F)) (Sum.inl (R ∪ S))

end ParallelSmallWorlds.SEU


