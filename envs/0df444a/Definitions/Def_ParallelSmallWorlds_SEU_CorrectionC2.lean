-- Prove2me | Definitions.Def_ParallelSmallWorlds_SEU_CorrectionC2
-- name    : ParallelSmallWorlds_SEU_CorrectionC2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:27.190097+00:00
-- url     : https://prove2.me/theorems/31fbfe3b-6f5b-4875-a551-17273b58f785
-- title:
--   Correction C2: a consequence is indifferent to its degenerate gamble, $c\sim_{S_w}\Psi_c$
-- statement:
--   For every consequence $c$,
--
--   $$c\sim_S\Psi_c.$$
--
--   The proof of Lemma 2 (p.45) states "by PSW10(c), $c^*_w\sim_{S_w}c^*_w1c_{w*}$", but Axiom PSW10(c) only compares degenerate gambles with each other and the set $C\cup\mathcal P_S$ keeps $c$ and $\Psi_c$ apart. Without this indifference Lemma 2 is false: with $C=\{c^*,m,c_*\}$, every consequence ranked above every gamble, and gambles ranked lexicographically by the probabilities of $c^*$ and then $m$ in their reduction, Axioms PSW9–PSW15 as printed hold, but no utility function represents the lexicographic order. Every expected-utility model satisfies it.
--
--   **Formalization Note** This is a correction of the source, kept as its own hypothesis.
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), Axiom PSW10(c), p.24 (PDF p.25), as used in the proof of Lemma 2, p.45 (PDF p.46)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_SmallWorld

namespace ParallelSmallWorlds.SEU

/-- **Correction C2: a consequence and its degenerate gamble are indifferent, `c ∼Sw Ψc`.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), Axiom PSW10(c), p.24 (PDF p.25), as used in the proof
of Lemma 2, p.45 (PDF p.46): "Note that by PSW10(c), c∗_w ∼Sw c∗_w 1 c_w∗ and c_w∗ ∼Sw c∗_w 0 c_w∗."

For every consequence `c`, `c ∼Sw Ψc`.

**Formalization Note.** This is a correction, not one of the paper's axioms: PSW10(c) only
compares degenerate gambles with each other, and the set `C ∪ PSw` keeps `c` and `Ψc` distinct.
Without it Lemma 2 fails: with `Cw = {c*, m, c_*}`, every consequence ranked above every gamble
and gambles ranked lexicographically by their reduced distribution, PSW9–PSW15 as printed hold
but no utility represents `⪰Sw` on `PSw`. Every expected-utility model satisfies C2. -/
def CorrectionC2 {Θ C : Type*} (W : SmallWorld Θ C) : Prop :=
  ∀ c : C, W.indiffS (Sum.inl c) (simpObj (SimpleDist.pure c))

end ParallelSmallWorlds.SEU


