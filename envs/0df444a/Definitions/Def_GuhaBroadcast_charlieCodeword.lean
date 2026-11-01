-- Prove2me | Definitions.Def_GuhaBroadcast_charlieCodeword
-- name    : GuhaBroadcast_charlieCodeword
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:24:41.20577+00:00
-- url     : https://prove2.me/theorems/fbe1ffaf-b456-49c6-a211-e81b0fec203a
-- title:
--   Charlie's state for his message, $\hat\rho^{C^n}_k$
-- statement:
--   With Bob's message uniform on a set of size $M_B$, **Charlie's state for his message $k$** is
--
--   $$
--   \hat\rho^{C^n}_k=\sum_m p_{W_B}(m)\,\hat\rho^{C^n}_{m,k}=\frac1{M_B}\sum_m\hat\rho^{C^n}_{m,k},
--   $$
--
--   as defined below (14). Its ensemble $\{p_{W_C}(k),\hat\rho^{C^n}_k\}$ carries Charlie's information.
--
--   **Formalization Note** $M_B$ is the cardinality of Bob's message set, positive by the code structure.
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, below eq. (14), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture
import Definitions.Def_GuhaBroadcast_charlieOutput

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, p.3 (PDF page; the paper prints no page numbers), below (14):
"`ρ̂_k^{Cⁿ} = Σ_m p_{W_B}(m) ρ̂_{m,k}^{Cⁿ}`", Charlie's state for his message `k`, with the uniform
prior `p_{W_B}(m) = 1/M_B` of p.1.

**Formalization Note.** `M_B` is the cardinality of `Fin MB`; `BroadcastCode` guarantees `0 < MB`. -/
noncomputable def charlieCodeword {n MB MC : ℕ} {O : Type} [Fintype O] (eta : ℝ)
    (C : BroadcastCode n MB MC O) (k : Fin MC) : FockKernel n :=
  mixture (fun _ : Fin MB => ((MB : ℝ)⁻¹)) (fun m => charlieOutput eta C m k)

end GuhaBroadcast


