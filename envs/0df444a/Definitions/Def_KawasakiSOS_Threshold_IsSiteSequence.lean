-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsSiteSequence
-- name    : KawasakiSOS_Threshold_IsSiteSequence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:04:47.539996+00:00
-- url     : https://prove2.me/theorems/44dfa294-b9fb-4377-9340-525e13a636b0
-- title:
--   Site sequences of the climbers
-- statement:
--   Two climbers start at the ends of the profile $F$ and meet at its peak $m$, staying at equal height. Recording the sites containing them gives a site sequence: a list of admissible pairs that starts at $(0,k-1)$, whose consecutive pairs differ by $\pm1$ in exactly one coordinate, with $s_a\le m\le s_b$ throughout, and which ends at a pair with $s_a=s_b$.
--
--   **Formalization Note** The predicate records these properties and does not refer to the continuous climbers. A sequence that actually arises from climbers satisfies it.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_IsAdmissiblePair
import Definitions.Def_KawasakiSOS_Threshold_IsAdjacentPair
import Definitions.Def_KawasakiSOS_Threshold_peak

namespace KawasakiSOS.Threshold

/-- A site sequence: admissible pairs starting at `(0, k−1)`, consecutive pairs differing by ±1 in exactly one coordinate, ending at a pair with `s_a = s_b`, with `s_a ≤ m ≤ s_b` throughout. Formalization Note: the last two conditions are read from `a(t) ∈ [0, m]`, `b(t) ∈ [m, k]`, `a(1) = b(1) = m` and "The last site pair has D_U = 0" (p. 12).

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11). -/
def IsSiteSequence {n k : ℕ} [NeZero k] (x y : Config n k) (p0 : ZMod k)
    (σ : List (ℕ × ℕ)) : Prop :=
  σ.head? = some (0, k - 1) ∧ (∃ q, σ.getLast? = some q ∧ q.1 = q.2) ∧
    (∀ q ∈ σ, IsAdmissiblePair x y p0 q.1 q.2 ∧ q.1 ≤ peak x y p0 ∧ peak x y p0 ≤ q.2) ∧
    σ.IsChain IsAdjacentPair

end KawasakiSOS.Threshold


