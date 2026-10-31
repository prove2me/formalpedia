-- Prove2me | Definitions.Def_ParallelSmallWorlds_SEU_PSW16
-- name    : ParallelSmallWorlds_SEU_PSW16
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:11.624989+00:00
-- url     : https://prove2.me/theorems/13e7353c-b36e-4269-8d8e-de7b9de9e807
-- title:
--   Axiom PSW16: an act is valued as the simple distribution it induces
-- statement:
--   For an act $a$ with finitely many consequences, the paper defines (eq. (5)) the probability that $a$ leads to $c$ as $P_C(c\mid a)=P_\Theta(a^{-1}\{c\})$ and the induced simple distribution $p_a=\langle P_C(c_1\mid a),c_1;\dots;P_C(c_r\mid a),c_r\rangle$. **Axiom PSW16** says that for acts $a,b$ with finitely many consequences,
--
--   $$a\succeq_A b\iff p_a\succeq_S p_b .$$
--
--   Here $P_\Theta$ is the calibrated probability. The axiom links the preferences over acts to the preferences over bets on the reference experiment, and is what turns Lemmas 1 and 2 into a subjective expected utility theorem.
--
--   **Formalization Note** The axiom is stated for every pair of simple distributions $p,q$ whose weights are the calibrated fibre probabilities of $a$ and $b$; it does not presuppose that these weights sum to $1$, which follows from the other axioms.
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), eq. (5) and Axiom PSW16, p.27 (PDF p.28)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_calib

namespace ParallelSmallWorlds.SEU

/-- **Axiom PSW16: an act is valued as the simple distribution it induces.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), eq. (5) and Axiom PSW16, p.27 (PDF p.28):
"PCw(c′ | a) = Σ_{θ∈Θw | c′=a(θ)} PΘw(θ) … for each a ∈ Aw define pa ∈ PSw as
⟨PCw(c1 | a),c1; …; PCw(cr | a),cr⟩ … suppose that a,b ∈ Aw are such that both lead only to a
finite number of consequences … Then: a ⪰Aw b ⟺ pa ⪰Sw pb."

For acts `a, b ∈ Aw` with finitely many consequences, and simple distributions `p, q` over `Cw`
whose weights are the calibrated probabilities of the fibres, `p(c) = PΘw(a⁻¹{c})` and
`q(c) = PΘw(b⁻¹{c})`: `a ⪰Aw b ⟺ p ⪰Sw q`.

**Formalization Note.** `PΘw` is the calibrated probability `calib W` of Lemma 1's proof (reading
R1), and `PCw(c | a)` is `calib W (a⁻¹{c})` (reading R2). The axiom does not presuppose that these
weights sum to `1`: it quantifies over the simple distributions `p_a, p_b` having them as weights.
Under Axioms PSW1–PSW6 and correction C1 the calibrated probability is finitely additive, so such
distributions exist for every act whose fibres are events. -/
def PSW16 {Θ C : Type*} (W : SmallWorld Θ C) : Prop :=
  ∀ a ∈ W.A, ∀ b ∈ W.A, (Set.range a).Finite → (Set.range b).Finite →
    ∀ p q : SimpleDist C, (∀ c, p.toFun c = calib W (a ⁻¹' {c})) →
      (∀ c, q.toFun c = calib W (b ⁻¹' {c})) →
      (W.prefA a b ↔ W.prefS (simpObj p) (simpObj q))

end ParallelSmallWorlds.SEU


