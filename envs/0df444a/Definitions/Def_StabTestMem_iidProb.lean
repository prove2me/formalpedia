-- Prove2me | Definitions.Def_StabTestMem_iidProb
-- name    : StabTestMem_iidProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:17.433452+00:00
-- url     : https://prove2.me/theorems/73e889e0-4635-4e5a-8c3d-22d81093f469
-- title:
--   Probability of an event under $N$ independent samples
-- statement:
--   For a function $P$ on a finite set $\Omega$ (a probability distribution in the uses) and an event $E\subseteq\Omega^N$,
--
--   $$\Pr_{w\sim P^{\otimes N}}[w\in E]=\sum_{w\in E}\ \prod_{j=1}^N P(w_j),$$
--
--   the probability that $N$ independent samples from $P$ form a tuple in $E$.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 4.5, p. 30

import Mathlib

namespace StabTestMem

open Classical in
/-- **Probability of an event under `N` independent samples.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 4.5, p. 30: "Let
(s_1, b_1), …, (s_N, b_N) be N independent samples from P^β_{a,r}. Then Pr[…]".

For a function `P : Ω → ℝ` on a finite set (a probability distribution in the uses) and an event
`E` on `N`-tuples, `iidProb P N E = Σ_{w ∈ E} Π_j P(w_j)`, the probability of `E` under the
product law `P^{⊗N}`. -/
noncomputable def iidProb {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (N : ℕ) (E : (Fin N → Ω) → Prop) :
    ℝ :=
  ∑ w : Fin N → Ω, if E w then ∏ j, P (w j) else 0

end StabTestMem


