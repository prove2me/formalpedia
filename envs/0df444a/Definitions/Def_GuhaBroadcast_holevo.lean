-- Prove2me | Definitions.Def_GuhaBroadcast_holevo
-- name    : GuhaBroadcast_holevo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:24:29.383598+00:00
-- url     : https://prove2.me/theorems/04fe3ba6-c7fd-45e8-8d5f-a4dca44c0faa
-- title:
--   Holevo information $\chi(p_j,\hat\sigma_j)$, Eq. (3)
-- statement:
--   For a probability vector $(p_j)$ and states $\hat\sigma_j$ the **Holevo information** is
--
--   $$
--   \chi(p_j,\hat\sigma_j)=S\Big(\sum_j p_j\hat\sigma_j\Big)-\sum_j p_j S(\hat\sigma_j),
--   $$
--
--   where $S(\hat\rho)=-\operatorname{Tr}(\hat\rho\log\hat\rho)$ is the von Neumann entropy. It bounds the classical information extractable from the ensemble (Holevo's bound) and is the quantity in which the capacity converse (14)–(25) is written.
--
--   **Formalization Note** $S$ is the published spectral entropy `spectralEntropyNats` (nats, values in $[0,\infty]$). The difference is formed with `toReal`, which reads $+\infty$ as $0$, so it equals $\chi$ exactly when $S(\sum_j p_j\hat\sigma_j)$ and every $S(\hat\sigma_j)$ with $p_j>0$ are finite; each statement of the mission that uses it assumes or proves this finiteness.
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section II, eq. (3), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section II, Eq. (3), p.2 (PDF page; the paper prints no page numbers): the Holevo information
`χ(p_j, σ̂_j) ≡ S(Σ_j p_j σ̂_j) − Σ_j p_j S(σ̂_j)`, with `S(ρ̂) = −Tr(ρ̂ log ρ̂)` the von Neumann entropy.

**Formalization Note.** `S` is the published `spectralEntropyNats` (natural logarithm, values in
`ℝ≥0∞`, `+∞` allowed). The paper treats the entropies in (3) as real numbers; here they are converted
with `ENNReal.toReal`, which reads `+∞` as `0`. So `holevo` is the paper's `χ` exactly when
`S(Σ_j p_j σ̂_j)` and every `S(σ̂_j)` with `p_j > 0` are finite. Every statement of this mission that
uses `holevo` either assumes that finiteness where the paper's own statement does (Holevo's bound) or
proves it as part of its conclusion. -/
noncomputable def holevo {n : ℕ} {ι : Type} [Fintype ι] (p : ι → ℝ) (ρ : ι → FockKernel n) : ℝ :=
  (spectralEntropyNats (mixture p ρ)).toReal - ∑ i, p i * (spectralEntropyNats (ρ i)).toReal

end GuhaBroadcast


