-- Prove2me | Definitions.Def_RLCDiscrepancy_IsMonotone
-- name    : RLCDiscrepancy_IsMonotone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:16.985293+00:00
-- url     : https://prove2.me/theorems/257d7e3a-4af8-46c6-ad72-88d9d78e37ca
-- title:
--   The event $S_{\mathrm{monotone}}(f)$
-- statement:
--   For a construction sequence $C_0,\dots,C_k$, a function $f$ and a threshold $\Gamma'$, the event $S_{\mathrm{monotone}}$ holds if
--
--   $$
--   |\delta_{C_j,f}|\le|\delta_{C_{j-1},f}|\quad\text{for every } 1\le j\le k \text{ such that } (C_0,\dots,C_{j-1}) \text{ is } (f,\Gamma',j-1)\text{-smooth}.
--   $$
--
--   Lemma 4.13 uses $\Gamma'=q^t\Lambda$: as long as the sequence has stayed smooth, the deviation never increases.
--
--   **Formalization Note** The prefix condition is Definition 4.2 with index $j-1$ and the same $k$.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.13, p.32

import Mathlib
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_consSeq
import Definitions.Def_RLCDiscrepancy_IsSmooth

namespace RLCDiscrepancy

/-- **The event S_monotone** of Lemma 4.13, for a threshold Γ′ (the lemma uses Γ′ = q^t · Λ).
Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.13, p.32: "Let S_monotone(f) denote the event that |δ_{C_j,f}| ≤ |δ_{C_{j−1},f}|
for all j such that (C_0, …, C_{j−1}) is (f, q^t · Λ, j − 1)-smooth."

**Formalization Note.** j ranges over 1 ≤ j ≤ k, the steps of the sequence. The prefix
(C_0, …, C_{j−1}) being (f, Γ′, j − 1)-smooth is Definition 4.2 with index j − 1 and the same k
(the condition only involves C_0, …, C_{j−1}). -/
def IsMonotone {F : Type*} [Field F] [Fintype F] {n k : ℕ} (u : Fin k → Fin n → F) (f : (Fin n → F) → ℝ)
    (Γ' : ℝ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ k → IsSmooth u f Γ' (j - 1) →
    |relDev (consSeq u j) f| ≤ |relDev (consSeq u (j - 1)) f|

end RLCDiscrepancy


