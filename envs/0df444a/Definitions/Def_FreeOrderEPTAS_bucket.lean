-- Prove2me | Definitions.Def_FreeOrderEPTAS_bucket
-- name    : FreeOrderEPTAS_bucket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:52.975423+00:00
-- url     : https://prove2.me/theorems/6c388451-7b16-4b75-b6c8-e01bd5412aae
-- title:
--   The corrected buckets and BaseVal
-- statement:
--   Fix a permutation $\sigma$ with values $V^*_t=R_t$ and an accuracy $\epsilon$. The variable $X_{\sigma(s)}$ is a **jump variable** if the half-open interval $(V^*_{s+1},V^*_s]$ contains an integer multiple of $\epsilon V^*_1$; $K$ is the number of jump variables. Buckets alternate from the end, as in Figure 1: $B_1$ is the run of non-jump variables after the last jump variable, $B_2$ is the last jump variable, and so on, $2K+1$ buckets in all, some possibly empty.
--
--   $\mathrm{BaseVal}(B_i)=V^*_{\max\{t:X_{\sigma(t)}\in B_i\}+1}$, with $V^*_{n+1}=0$.
--
--   **Formalization Note** Times and buckets are 0-based: `bucket s` is $2a$ for a non-jump variable and $2a+1$ for a jump variable, where $a$ is the number of jump variables strictly after time $s$. So even indices are stable and odd indices are jump buckets. `BaseVal i` is the value of $R$ at the first time after bucket $i$, which is also meaningful on an empty bucket, and is $V^*_1$ at the index $2K+1$ above the top bucket. The milestone `bucket_facts` records these identities.
--
--   The paper's closed intervals make every time in a run of equal values at a multiple a jump, so that $K\le1/\epsilon$ fails ($\epsilon=1/2$, values $(1,0,0,0,0)$); and the text's indexing disagrees with Figure 1 on which side of a jump a variable falls (values $(1,0.6,0.6,0)$ at $\epsilon=1/2$).
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.2, pp.17–18, Figure 1

import Mathlib
import Definitions.Def_FreeOrderEPTAS_R

namespace FreeOrderEPTAS

variable {n : ℕ}

/-- The corrected jump test (arXiv:2007.13121v3, §3.2, p.17, and Figure 1). With 0-based
time `s`, the variable `X_{σ*(s)}` is a jump variable iff the half-open interval `(V*_{s+1}, V*_s]`
contains an integer multiple of `ϵ V*_0`, where `V*_s = R I σ s`.

**Formalization Note.** The paper's closed intervals make every time of a run of equal values at
a multiple a jump, so that `K ≤ 1/ϵ` fails; half-open intervals are disjoint. -/
def IsJump (I : Instance n) (σ : Equiv.Perm (Fin n)) (ϵ : ℝ) (s : ℕ) : Prop :=
  ∃ k : ℕ, R I σ (s + 1) < (k : ℝ) * (ϵ * R I σ 0) ∧ (k : ℝ) * (ϵ * R I σ 0) ≤ R I σ s

open Classical in
/-- `K`, the number of jump variables. -/
noncomputable def numJumps (I : Instance n) (σ : Equiv.Perm (Fin n)) (ϵ : ℝ) : ℕ :=
  ((Finset.range n).filter fun s => IsJump I σ ϵ s).card

open Classical in
/-- The 0-based bucket of the variable at time `s`: buckets alternate from the end, as in Figure 1
(p.18). With `a` the number of jump variables strictly after time `s`, a non-jump variable lies in
the bucket `2a` (the paper's stable `B_{2a+1}`) and a jump variable in the bucket `2a + 1` (the
paper's jump `B_{2a+2}`). So even buckets are stable, odd ones are jump buckets, and the buckets are
`0, …, 2K`, some possibly empty. -/
noncomputable def bucket (I : Instance n) (σ : Equiv.Perm (Fin n)) (ϵ : ℝ) (s : ℕ) : ℕ :=
  2 * ((Finset.range n).filter fun s' => s < s' ∧ IsJump I σ ϵ s').card +
    if IsJump I σ ϵ s then 1 else 0

open Classical in
/-- The first time at which the bucket index is below `i`, and `n` if there is none: the time
right after bucket `i`, also when bucket `i` is empty. Bucket indices do not increase with time. -/
noncomputable def endTime (I : Instance n) (σ : Equiv.Perm (Fin n)) (ϵ : ℝ) (i : ℕ) : ℕ :=
  ((List.range n).find? fun s => decide (bucket I σ ϵ s < i)).getD n

/-- `BaseVal(B_i) = V*_{max{t : X_{σ*(t)} ∈ B_i}+1}` (p.18), with `V*_{n+1} = 0`.

**Formalization Note.** `endTime` is also defined on empty buckets and at the index `2K + 1`, where
`BaseVal = V*_1 = OPT` for optimal `σ*`, the value the paper needs in (15) for the top bucket
(it is undefined in the paper). `FreeOrderEPTAS.bucket_facts` records these identities. -/
noncomputable def BaseVal (I : Instance n) (σ : Equiv.Perm (Fin n)) (ϵ : ℝ) (i : ℕ) : ℝ :=
  R I σ (endTime I σ ϵ i)

end FreeOrderEPTAS


