-- Prove2me | Definitions.Def_GuhaBroadcast_bobMessageState
-- name    : GuhaBroadcast_bobMessageState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:24:24.92435+00:00
-- url     : https://prove2.me/theorems/d4ab0541-8f20-470e-8fce-f54ad40bad94
-- title:
--   Bob's state for his own message, $\hat\rho^{B^n}_m$
-- statement:
--   With Charlie's message uniform on a set of size $M_C$, **Bob's state for his message $m$** is
--
--   $$
--   \hat\rho^{B^n}_m=\sum_k p_{W_C}(k)\,\hat\rho^{B^n}_{m,k}=\frac1{M_C}\sum_k\hat\rho^{B^n}_{m,k},
--   $$
--
--   the state in the second line of (15), $\chi(p_{W_B}(m),\hat\rho^{B^n}_m)$.
--
--   **Formalization Note** $M_C$ is the cardinality of Charlie's message set, positive by the code structure.
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eq. (15), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture
import Definitions.Def_GuhaBroadcast_bobOutput

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, Eq. (15), p.3 (PDF page; the paper prints no page numbers): Bob's state
`ρ̂_m^{Bⁿ} = Σ_k p_{W_C}(k) ρ̂_{m,k}^{Bⁿ}` for his own message `m`, averaged over Charlie's message with
the uniform prior `p_{W_C}(k) = 1/M_C` (p.1, p.4 "the uniform distribution p_{W_C}(k) = 1/2^{nR_C}");
it appears in the second line of (15), `χ(p_{W_B}(m), ρ̂_m^{Bⁿ})`.

**Formalization Note.** `M_C` is the cardinality of `Fin MC`; `BroadcastCode` guarantees `0 < MC`. -/
noncomputable def bobMessageState {n MB MC : ℕ} {O : Type} [Fintype O] (eta : ℝ)
    (C : BroadcastCode n MB MC O) (m : Fin MB) : FockKernel n :=
  mixture (fun _ : Fin MC => ((MC : ℝ)⁻¹)) (fun k => bobOutput eta C m k)

end GuhaBroadcast


