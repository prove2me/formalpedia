-- Prove2me | Definitions.Def_OppenheimRelay_RelayAchievable
-- name    : OppenheimRelay_RelayAchievable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:32:18.959744+00:00
-- url     : https://prove2.me/theorems/ea1408a4-d92f-4180-aafa-23b3047d6fe5
-- title:
--   Achievable relay rates $(Q^{A\to C},E^{AC},Q^{C\to B},E^{CB})$
-- statement:
--   Let $\psi$ be a vector on the relay source. A tuple of real numbers $(Q^{A\to C},E^{AC},Q^{C\to B},E^{CB})$ is **achievable** when $Q^{A\to C}\ge0$, $Q^{C\to B}\ge0$, and for every $\varepsilon>0$ and $\delta>0$ there is $N$ such that for every blocklength $n\ge\max(N,1)$ some single relay code $P$ of blocklength $n$ satisfies
--
--   $$
--   \|\rho_{\text{output}}-\rho_{\text{target}}\|_1\le\varepsilon,\quad
--   q_{AC}\le n(Q^{A\to C}+\delta),\quad q_{CB}\le n(Q^{C\to B}+\delta),
--   $$
--   $$
--   k_{AC}-l_{AC}\le n(E^{AC}+\delta),\quad k_{CB}-l_{CB}\le n(E^{CB}+\delta).
--   $$
--
--   Each $E$ bounds the **net consumption** $k-l$ of ebits on its link; a negative $E$ means that ebits are produced at rate $-E$ ("If this quantity is negative, that this amount of entanglement is produced", p.1). One code meets all four rates at once.
--
--   **Formalization Note** The differences $k-l$ are computed in $\mathbb R$. The definition mirrors the published two-party `RedistributionAchievable`, link by link.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.2, "Accounting for sent qubits Q^{A→C} between Alice and Charlie and Q^{C→B} between Charlie and Bob, as well as consumed ebits"; p.1, "The protocol is allowed to consume (or produce) ebits"

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_RelaySource
import Definitions.Def_OppenheimRelay_RelayCode
import Definitions.Def_OppenheimRelay_RelayCode_relayError

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **Achievable relay rates.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.2, "Accounting for sent qubits Q^{A→C} between Alice and
Charlie and Q^{C→B} between Charlie and Bob, as well as consumed ebits": `(qAC, eAC, qCB, eCB)` is
achievable when, for every `eps, delta > 0`, every large enough blocklength `n` has one relay code
with error at most `eps` that meets all four rates up to `delta` per copy.

**Formalization Note** Each `E` bounds the net consumption `k − l` of its link, computed in `ℝ`:
a negative value means ebits produced (p.1, "If this quantity is negative, that this amount of
entanglement is produced"). The two `Q` are nonnegative, as in the published
`RedistributionAchievable`, which this definition mirrors link by link. The guard `1 ≤ n` excludes
only the empty blocklength. -/
def RelayAchievable {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RelaySource A C B R)) (qAC eAC qCB eCB : ℝ) : Prop :=
  0 ≤ qAC ∧ 0 ≤ qCB ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
    ∃ P : RelayCode A C B n, P.relayError psi ≤ eps ∧
      (P.qAC : ℝ) ≤ n * (qAC + delta) ∧ (P.qCB : ℝ) ≤ n * (qCB + delta) ∧
      (P.kAC : ℝ) - P.lAC ≤ n * (eAC + delta) ∧ (P.kCB : ℝ) - P.lCB ≤ n * (eCB + delta)

end OppenheimRelay


