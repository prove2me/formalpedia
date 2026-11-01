-- Prove2me | Definitions.Def_GuhaBroadcast_modeMeanPhotons
-- name    : GuhaBroadcast_modeMeanPhotons
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:48.679465+00:00
-- url     : https://prove2.me/theorems/fc706456-7233-4c3c-83f0-291e1be5fc97
-- title:
--   Mean photon number $\bar N_{k_j}$ of mode $j$ of codeword $k$
-- statement:
--   For Charlie's message $k$ and a mode $j\in\{1,\dots,n\}$, $\bar N_{k_j}$ is the mean photon number $\langle\hat a_j^\dagger\hat a_j\rangle$ of the $j$-th input mode, averaged over Bob's uniform message:
--
--   $$
--   \bar N_{k_j}=\frac1{M_B}\sum_m\langle\hat a_j^\dagger\hat a_j\rangle_{x^n(m,k)} .
--   $$
--
--   It enters (16) through $g(\eta\bar N_{k_j})$, the entropy bound for Bob's $j$-th mode.
--
--   **Formalization Note** The page calls $\bar N_{k_j}$ "the mean photon number of the jth symbol" of Bob's codeword, but (16) evaluates $g(\eta\bar N_{k_j})$, which is the right bound only if $\bar N_{k_j}$ is measured at the transmitter: Bob's mode then has mean $\eta\bar N_{k_j}$. So this is the input mean. Photon numbers are the published `modeEnergy` in $[0,\infty]$, converted with `toReal`; under the codebook budget every statement assumes, they are finite.
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eq. (16), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, Eq. (16), p.3 (PDF page; the paper prints no page numbers): `N̄_{k_j}`, the mean
photon number of the j-th symbol of the k-th codeword, averaged over Bob's message `m` with the uniform
prior `1/M_B`: `N̄_{k_j} = (1/M_B) Σ_m ⟨â_j†â_j⟩_{x^n(m,k)}`.

**Formalization Note.** Reading R5 of the mission: the page calls `N̄_{k_j}` "the mean photon number of
the jth symbol `ρ̂_k^{B_j}`", but (16) evaluates `g(η N̄_{k_j})`, which is the bound for Bob's j-th mode
only when `N̄_{k_j}` is measured at the transmitter (Bob's mode has mean `η N̄_{k_j}`). So this is the
**input** mean. Energies are the published `modeEnergy` (in `ℝ≥0∞`) and are converted with `toReal`;
under the codebook energy budget used by every statement of the mission they are finite, so `toReal`
loses nothing. -/
noncomputable def modeMeanPhotons {n MB MC : ℕ} {O : Type} [Fintype O]
    (C : BroadcastCode n MB MC O) (k : Fin MC) (j : Fin n) : ℝ :=
  ((∑ m, modeEnergy (C.encoder m k).coefficients j) / (MB : ℝ≥0∞)).toReal

end GuhaBroadcast


