-- Prove2me | Definitions.Def_GuhaBroadcast_bobCodeword
-- name    : GuhaBroadcast_bobCodeword
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:24:40.777409+00:00
-- url     : https://prove2.me/theorems/72189323-e052-4b20-baf9-171d7bcaede8
-- title:
--   Bob's state for Charlie's message, $\hat\rho^{B^n}_k$
-- statement:
--   With Bob's message uniform on a set of size $M_B$, **Bob's state for Charlie's message $k$** is
--
--   $$
--   \hat\rho^{B^n}_k=\sum_{m} p_{W_B}(m)\,\hat\rho^{B^n}_{m,k}=\frac1{M_B}\sum_m\hat\rho^{B^n}_{m,k}.
--   $$
--
--   It is the state whose entropy is bounded in (16)–(17) and whose average over $k$ appears in (19)–(21).
--
--   **Formalization Note** $M_B$ is the cardinality of Bob's message set; the code structure guarantees $M_B>0$, so the weights sum to one.
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eqs. (16)-(21), pp.3-4; uniform messages, Section II, p.1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture
import Definitions.Def_GuhaBroadcast_bobOutput

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, pp.3–4 (PDF pages; the paper prints no page numbers): Bob's state for Charlie's
message `k`, `ρ̂_k^{Bⁿ} = Σ_m p_{W_B}(m) ρ̂_{m,k}^{Bⁿ}` (the Bob analogue of the definition below (14),
used in (16)–(21)), with the uniform prior `p_{W_B}(m) = 1/M_B` of p.1 ("The messages (m, k) are
assumed to be uniformly distributed").

**Formalization Note.** `M_B` is the cardinality of Bob's message set `Fin MB` (`2^{nR_B}` on the page);
`BroadcastCode` guarantees `0 < MB`, so the weights `1/M_B` sum to one. -/
noncomputable def bobCodeword {n MB MC : ℕ} {O : Type} [Fintype O] (eta : ℝ)
    (C : BroadcastCode n MB MC O) (k : Fin MC) : FockKernel n :=
  mixture (fun _ : Fin MB => ((MB : ℝ)⁻¹)) (fun m => bobOutput eta C m k)

end GuhaBroadcast


