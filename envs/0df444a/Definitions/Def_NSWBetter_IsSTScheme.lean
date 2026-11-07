-- Prove2me | Definitions.Def_NSWBetter_IsSTScheme
-- name    : NSWBetter_IsSTScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:36.955428+00:00
-- url     : https://prove2.me/theorems/8447aefd-3289-47e0-b3ac-7c05902624ec
-- title:
--   Shmoys–Tardos rounding scheme (Marginals, Cardinality)
-- statement:
--   A probability distribution $D$ over integral matchings between the buckets of $x$ (for the value orders $r$) and the goods is an **ST rounding scheme** when
--   1. (Marginals) for every bucket $b$ and good $g$, $\Pr[g\text{ is matched to }b]=b_g$;
--   2. (Cardinality) every bucket $b$ with $|b|_1=1$ is matched with probability $1$.
--
--   The allocation $X$ gives each agent the goods matched to its buckets.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4, p.16 (Marginals, Cardinality)

import Mathlib
import Definitions.Def_NSWBetter_bucket
import Definitions.Def_NSWBetter_IsBucketMatching

namespace NSWBetter

open Classical in
/-- **Distribution of the ST integral matching.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4, p.16: "Marginals For every bucket b and good g, Pr[g is matched to b] = bg. Cardinality For every bucket b such that |b|1 = 1, b is matched in the integral matching with probability 1."

`D M` is the probability of the matching `M`: `D ≥ 0`, `Σ D = 1`, the support consists of matchings, and Marginals and Cardinality hold for the buckets `bucket r x`.

**Formalization Note.** The random matching is a finitely supported distribution on matchings (a function on all sets of triples). Rationality is the separate predicate `IsRationalScheme`. -/
def IsSTScheme {n m : ℕ} (r : Fin n → Fin m ≃ Fin m) (x : Fin n → Fin m → ℝ)
    (D : Finset (Fin n × Fin m × Fin m) → ℝ) : Prop :=
  (∀ M, 0 ≤ D M) ∧ (∑ M, D M = 1) ∧ (∀ M, D M ≠ 0 → IsBucketMatching M) ∧
  (∀ i t g, ∑ M ∈ Finset.univ.filter (fun M => (i, t, g) ∈ M), D M = bucket r x i t g) ∧
  ∀ i t, ∑ g, bucket r x i t g = 1 →
    ∑ M ∈ Finset.univ.filter (fun M => ∃ g, (i, t, g) ∈ M), D M = 1

end NSWBetter


