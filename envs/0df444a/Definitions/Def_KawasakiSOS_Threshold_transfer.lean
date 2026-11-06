-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_transfer
-- name    : KawasakiSOS_Threshold_transfer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:43.136306+00:00
-- url     : https://prove2.me/theorems/759e6be8-46ee-488f-a30f-f1531b8e3fbd
-- title:
--   Moving one unit: $h-e_i+e_j$
-- statement:
--   For $h\in\Omega_{n,k}$ with $h(i)\ge1$ and columns $i,j$, this is the configuration
--
--   $$h-e_i+e_j,$$
--
--   where $e_i$ is the $i$-th unit vector. It again has total mass $n$.
--
--   **Formalization Note** When $h(i)=0$ the value is $h$ itself, so the operation is total on $\Omega_{n,k}$. Every use in this mission either has $h(i)\ge1$ as a hypothesis or tests it first.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config

namespace KawasakiSOS.Threshold

/-- The configuration `h − e_i + e_j`, moving one unit from column `i` to column `j`. Formalization Note: this is only meaningful when `h(i) ≥ 1`, so the definition returns `h` itself when `h(i) = 0`; no truncated subtraction reaches a result. For `j = i` it returns `h`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2). -/
def transfer {n k : ℕ} [NeZero k] (h : Config n k) (i j : ZMod k) : Config n k :=
  if hi : 1 ≤ h.1 i then
    ⟨fun l => h.1 l - (if l = i then 1 else 0) + (if l = j then 1 else 0), by
      have h1 : ∑ l, (h.1 l - (if l = i then 1 else 0) + (if l = i then 1 else 0)) = n := by
        refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) h.2
        split_ifs with hl
        · subst hl; omega
        · omega
      rw [Finset.sum_add_distrib] at h1
      rw [Finset.sum_add_distrib]
      simpa using h1⟩
  else h

end KawasakiSOS.Threshold


