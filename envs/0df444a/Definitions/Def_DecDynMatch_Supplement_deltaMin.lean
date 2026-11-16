-- Prove2me | Definitions.Def_DecDynMatch_Supplement_deltaMin
-- name    : DecDynMatch_Supplement_deltaMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:32:19.80764+00:00
-- url     : https://prove2.me/theorems/0a8110ed-8b3b-42eb-a7fd-e64131da6876
-- title:
--   The minimum gap $\Delta_{\min}$ of the final market (11)
-- statement:
--   In the final market $P_{t^*}$, the smallest absolute difference between a player's mean utilities for two distinct arms or an arm's mean utilities for two distinct final players:
--   $$
--   \Delta_{\min}=\min\Bigl(\{|\mu_{i,k}-\mu_{i,\ell}|: i\in P_{t^*},\ k\ne\ell\}\cup\{|\pi_{k,i}-\pi_{k,j}|: k\in\mathcal K,\ i\ne j\in P_{t^*}\}\Bigr).
--   $$
--   Strict preferences give $\Delta_{\min}>0$ when $P_{t^*}\ne\emptyset$.
--
--   **Formalization Note** For an empty final market the set is empty and the value is $0$; then $\Delta_{\min}^{-2}=0$ in Lean, and the paper's bound in that case, $D(T;I)\le\min\{T,t^*-1\}$ (p.51), has no gap term.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), eq. (11), p.12

import Mathlib
import Definitions.Def_DecDynMatch_Instance

namespace DecDynMatch.Supplement

open DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

open Classical in
/-- The finite set of utility gaps in the final market `P_{t*}`: `|μ_{i,k} − μ_{i,ℓ}|` for
`i ∈ P_{t*}`, `k ≠ ℓ`, and `|π_{k,i} − π_{k,j}|` for every arm `k` and `i ≠ j` in `P_{t*}`. -/
noncomputable def gapSet (I : Instance K ι) : Finset ℝ :=
  ((active I (tstar I)) ×ˢ (Finset.univ : Finset (Fin K)).offDiag).image
      (fun p => |I.μ p.1 p.2.1 - I.μ p.1 p.2.2|) ∪
    ((Finset.univ : Finset (Fin K)) ×ˢ (active I (tstar I)).offDiag).image
      (fun p => |I.π p.1 p.2.1 - I.π p.1 p.2.2|)

/-- **The minimum gap `Δ_min`.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), eq. (11), p.12: "In the final market, compare each player's
mean utilities for distinct arms and each arm's mean utilities for distinct players. The smallest
absolute difference is Δ_min = min({|μ_{i,k} − μ_{i,ℓ}| : i ∈ P_{t*}, k, ℓ ∈ 𝒦, k ≠ ℓ} ∪
{|π_{k,i} − π_{k,j}| : k ∈ 𝒦, i, j ∈ P_{t*}, i ≠ j}). Strict preferences give Δ_min > 0."

**Formalization Note.** The set is nonempty exactly when the final market `P_{t*}` is nonempty
(`K ≥ 2`), and then `Δ_min > 0` by strict rankings. For an empty final market the value is `0`, so
`Δ_min^{-2} = 0` in Lean; the paper's bound in that case is `D(T; I) ≤ min{T, t* − 1}` (p.51), which
needs no gap term. -/
noncomputable def deltaMin (I : Instance K ι) : ℝ :=
  if h : (gapSet I).Nonempty then (gapSet I).min' h else 0

end DecDynMatch.Supplement


