-- Prove2me | Definitions.Def_FreeOrderEPTAS_prophetInstance
-- name    : FreeOrderEPTAS_prophetInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:14.837956+00:00
-- url     : https://prove2.me/theorems/626c14ef-3ac4-4246-afc2-efb3d039444c
-- title:
--   The scaled One-Dimensional Santa Claus instance
-- statement:
--   The instance of §3.4 in the normal form of p.8, for marginal loads $w_{ij}$ and lower bounds $\Delta_i$: one dimension, active on machine $i$ iff $\Delta_i>0$, with load $w_{ij}/\Delta_i$ truncated to $[0,1]$; jump machines accept one job and stable machines accept $n$.
--
--   **Formalization Note** The genuine loads are non-negative, so the truncation at $0$ changes nothing; it makes the definition total on an arbitrary function in the place of the oracle.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.4, p.19; scaling, §2.1, p.8

import Mathlib
import Definitions.Def_FreeOrderEPTAS_SCInstance

namespace FreeOrderEPTAS

variable {m n : ℕ}

/-- The instance of §3.4 (arXiv:2007.13121v3, p.19) scaled to the normal form of p.8, for marginal
loads `w i j` and lower bounds `Δ i`: machine `i` is active iff `Δ_i > 0`, its only dimension has
load `w_ij/Δ_i` truncated to `[0, 1]`; jump machines (odd 0-based index) take one job, stable
machines take `n`.

**Formalization Note.** The genuine loads are `≥ 0`, so the truncation at `0` changes nothing; it
makes the instance total for an arbitrary function in the place of the oracle. -/
noncomputable def prophetInstance (w : Fin m → Fin n → ℝ) (Δ : Fin m → ℝ) : SCInstance m 1 n where
  k i := if i.val % 2 = 1 then 1 else n
  A i := if 0 < Δ i then {0} else ∅
  ℓ i j _ := if 0 < Δ i then max 0 (min (w i j / Δ i) 1) else 0
  ℓ_mem i j _ := by
    split_ifs
    · exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    · exact ⟨le_refl _, zero_le_one⟩

end FreeOrderEPTAS


