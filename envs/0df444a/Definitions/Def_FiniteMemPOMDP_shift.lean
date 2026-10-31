-- Prove2me | Definitions.Def_FiniteMemPOMDP_shift
-- name    : FiniteMemPOMDP_shift
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:12.767774+00:00
-- url     : https://prove2.me/theorems/108fe25a-d320-493a-9205-af0c28573ebf
-- title:
--   The $h$-shift $\sigma[h]$ of a strategy
-- statement:
--   For a history $h$, the **$h$-shift** of $\sigma$ is the strategy $\sigma[h]$ defined by
--
--   $$\sigma[h](h')=\sigma(h,h')$$
--
--   for every history $h'$: it is the continuation of $\sigma$ after the history $h$.
--
--   **Formalization Note** Histories are chronological lists, so $(h,h')$ is the concatenation `h ++ h'`.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Definition 6.4, p.15

import Mathlib

namespace FiniteMemPOMDP

/-- **The `h`-shift `σ[h]` of a strategy.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Definition 6.4, p.15: "Let m ≥ 1 and
hm ∈ Hm. The hm-shift of σ is the strategy σ[hm] defined by, for all m′ ≥ 1,
σ[hm](hm′) := σ(hm, hm′)."

`shift σ h` plays, after the history `h'`, what `σ` plays after the concatenated history
`h ++ h'`.

**Formalization Note** Histories are chronological lists, so `(hm, hm′)` is `h ++ h'`. -/
def shift {A S : Type} (σ : List (A × S) → A) (h : List (A × S)) : List (A × S) → A :=
  fun h' => σ (h ++ h')

end FiniteMemPOMDP


