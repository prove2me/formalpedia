-- Prove2me | Definitions.Def_GuhaBroadcast_mixture
-- name    : GuhaBroadcast_mixture
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:34.000993+00:00
-- url     : https://prove2.me/theorems/83c6e790-ee5b-4c63-ad7f-37647351d4d8
-- title:
--   Finite mixture $\sum_i p_i\rho_i$ of Fock-space kernels
-- statement:
--   Given finitely many $n$-mode states $\rho_i$ (written as coefficient arrays in the photon-number basis of the full Fock space) and real weights $p_i$, their **mixture** is
--
--   $$
--   \sum_i p_i\,\rho_i .
--   $$
--
--   The paper uses it for the averaged states $\hat\rho^{C^n}_k=\sum_m p_{W_B}(m)\hat\rho^{C^n}_{m,k}$ (below (14)), $\hat\rho^{B^n}=\sum_k p_{W_C}(k)\hat\rho^{B^n}_k$ (before (19)) and the state $\sum_j p_j\hat\sigma_j$ inside the Holevo information (3).
--
--   **Formalization Note** The kernels are the published `FockKernel n` arrays (no photon-number cutoff). The definition is entrywise and total; the mission applies it only with probability weights.
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section II, eq. (3), p.2; Section III, below eq. (14), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, p.3 (PDF page; the paper prints no page numbers): the
averaged states `ρ̂_k^{Cⁿ} = Σ_m p_{W_B}(m) ρ̂_{m,k}^{Cⁿ}` (below (14)), `ρ̂^{Bⁿ} = Σ_k p_{W_C}(k) ρ̂_k^{Bⁿ}`
(p.4, before (19)) and the state `Σ_j p_j σ̂_j` inside the Holevo information (3), p.2. This is the
entrywise weighted sum `Σ_i p_i ρ_i` of finitely many Fock-space coefficient kernels.

**Formalization Note.** The kernels are the published `FockKernel n` coefficient arrays of
`QAlgorithms.Papers.Independent.Next46.P32` (full n-mode number basis, no photon cutoff). The
definition is total: it does not require the weights to form a probability vector; every statement of
this mission applies it with nonnegative weights summing to one (the uniform weights `1/M`). -/
noncomputable def mixture {n : ℕ} {ι : Type} [Fintype ι] (p : ι → ℝ) (ρ : ι → FockKernel n) :
    FockKernel n :=
  fun a b => ∑ i, (p i : ℂ) * ρ i a b

end GuhaBroadcast


