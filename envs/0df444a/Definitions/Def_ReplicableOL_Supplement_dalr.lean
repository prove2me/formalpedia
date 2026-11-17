-- Prove2me | Definitions.Def_ReplicableOL_Supplement_dalr
-- name    : ReplicableOL_Supplement_dalr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:18:43.369384+00:00
-- url     : https://prove2.me/theorems/d0c5082c-5e4d-4e9b-b016-3e27e9174c07
-- title:
--   DALR (dithered-anchor level rule) as a learner
-- statement:
--   **DALR** is the two-expert learner with seed $R=(\chi,(\omega_{i,q}))$ that plays in blocks of length $B=A_K$: for rounds $t\in(mB,(m+1)B]$ it plays
--
--   $$
--   a_t=\begin{cases}1 & \text{if } \hat D^{(K)}_m<\chi,\\ 2&\text{otherwise,}\end{cases}
--   $$
--
--   where $\hat D^{(K)}_m$ is the level-$K$ anchor value at time $mB$. The action on block $m+1$ depends only on $D_{\le mB}$ and the seed, so DALR is causal and all of its randomness is in its seed.
--
--   **Formalization Note** DALR is an instance of the published `ReplicableOL.Learner` with $n=2$. Rounds are $0$-based: Lean round $t$ is the paper's round $t+1$, which lies in block $m+1$ with $m=\lfloor t/B\rfloor$, and $mB\le t$, so the decision reads only the prefix. Lean expert $0$ is the paper's expert $1$. The level scale $H$ appears only in the seed law. Measurability of each action is proved.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 5.1, pp.17–18

import Mathlib
import Definitions.Def_ReplicableOL_Learner
import Definitions.Def_ReplicableOL_Supplement_prefixGap
import Definitions.Def_ReplicableOL_Supplement_anchorVal

namespace ReplicableOL.Supplement

/-- **DALR as a learner.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 5.1, pp.17–18. "Decision. For t ∈ (mB, (m + 1)B], play a_t := 1 if D̂^{(K)}_m < χ and a_t := 2 otherwise." The anchor values are `anchorVal` computed from the losses seen so far and the seed `R = (χ, (ω_{i,q}))`.

**Formalization Note.** Rounds are 0-based: Lean round `t` is the paper's round `t + 1`, which lies in block `m + 1` with `m = ⌊t/B⌋`, `B = A_K`; the decision reads `D` only at times `≤ mB ≤ t`, which the prefix of length `t` supplies through `prefixGap`. Lean expert `0` is the paper's expert 1. The level scale `H` enters only through the seed law `seedLaw C H`. -/
noncomputable def dalr {T : ℕ} (C : Chain T) : ReplicableOL.Learner 2 T (Seed C) where
  act t x r :=
    if anchorVal C (prefixGap x) r C.K (t.val / C.A C.K) < r.1 then 0 else 1
  act_meas t := by
    have hg : Measurable fun p : (Fin t.val → Fin 2 → ℝ) × Seed C =>
        anchorVal C (prefixGap p.1) p.2 C.K (t.val / C.A C.K) :=
      (measurable_anchorVal C C.K _).comp
        (Measurable.prodMk
          (measurable_pi_lambda _ fun s => (measurable_prefixGap s).comp measurable_fst)
          measurable_snd)
    exact Measurable.ite (measurableSet_lt hg (measurable_fst.comp measurable_snd))
      measurable_const measurable_const

end ReplicableOL.Supplement


