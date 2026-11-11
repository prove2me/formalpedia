-- Prove2me | Definitions.Def_GapAgnosticGS_secondReward
-- name    : GapAgnosticGS_secondReward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:32.607165+00:00
-- url     : https://prove2.me/theorems/47f910e7-6709-4984-916f-3d010f3ddbe0
-- title:
--   Second largest reward $p_2$ (with multiplicity)
-- statement:
--   For rewards $p_0,\dots,p_{n-1}$ ($n\ge2$), the **second largest reward with multiplicity** is
--
--   $$p_{(2)}=\min_{j}\ \max_{k\ne j}p_k .$$
--
--   Relabelling the arms so that $p_1\ge p_2\ge\cdots\ge p_n$ (as in App. A.6), this is $p_2$; with a tie at the top it equals $p_\star$. It is the quantity $p_k$, $k=2$, of Lemma 3.7.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.7, p.12 (PDF p.13) (p_k, k = 2); App. A.6, p.32 (PDF p.33): "relabel the arms so that p⋆ = p_1 > p_2 ≥ ⋯ ≥ p_n"

import Definitions.Def_GapAgnosticGS_reward

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.7, p.12 (PDF p.13) ("p_k" for `k = 2`) and Appendix A.6, p.32 (PDF p.33):
"relabel the arms so that p⋆ = p_1 > p_2 ≥ ⋯ ≥ p_n". The second largest reward, counted with
multiplicity: `min_j max_{k ≠ j} p_k` (removing one copy of the largest reward leaves the second
largest; removing any other arm leaves `p⋆`).

**Formalization Note.** With a tie at the top it equals `p⋆`. For `n ≥ 2` every inner supremum
is a maximum over a nonempty finite set. -/
noncomputable def secondReward {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A}
    {Prj : Matrix A A ℂ} (Env : HidEnv n A a₀ Prj) : ℝ :=
  ⨅ j : Fin n, ⨆ k : {k : Fin n // k ≠ j}, reward Env k

end GapAgnosticGS


