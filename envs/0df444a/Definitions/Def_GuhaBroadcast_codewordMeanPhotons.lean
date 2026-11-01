-- Prove2me | Definitions.Def_GuhaBroadcast_codewordMeanPhotons
-- name    : GuhaBroadcast_codewordMeanPhotons
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:24:37.924378+00:00
-- url     : https://prove2.me/theorems/27a8cdee-85f8-4dbf-a07d-c464cd059b67
-- title:
--   Per-use mean photon number $\bar N_k$ of codeword $k$
-- statement:
--   For Charlie's message $k$,
--
--   $$
--   \bar N_k=\sum_{j=1}^n\frac1n\bar N_{k_j},
--   $$
--
--   the average over the $n$ modes of the input mean photon numbers $\bar N_{k_j}$. It is the argument of the bounds $n\,g(\eta\bar N_k)$ in (16) and $n\,g(\eta\beta_k\bar N_k)$ in (17).
--
--   **Formalization Note** At $n=0$ the division returns $0$; every statement using $\bar N_k$ assumes $n\ge1$.
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eq. (16), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_modeMeanPhotons

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, Eq. (16), p.3 (PDF page; the paper prints no page numbers):
"`N̄_k ≡ Σ_{j=1}^n (1/n) N̄_{k_j}`", the per-use mean photon number of the k-th codeword.

**Formalization Note.** `N̄_{k_j}` is `modeMeanPhotons` (input means, reading R5). At `n = 0` the
division returns `0`; every statement using it assumes `0 < n`. -/
noncomputable def codewordMeanPhotons {n MB MC : ℕ} {O : Type} [Fintype O]
    (C : BroadcastCode n MB MC O) (k : Fin MC) : ℝ :=
  (∑ j, modeMeanPhotons C k j) / (n : ℝ)

end GuhaBroadcast


