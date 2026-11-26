-- Prove2me | Definitions.Def_FairShares_Supplement_ptasShare
-- name    : FairShares_Supplement_ptasShare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:27:47.943082+00:00
-- url     : https://prove2.me/theorems/48babda5-8cfb-46c0-86f5-6cca18dca69d
-- title:
--   Two-agent $\operatorname{PTAS}(\varepsilon)$ share
-- statement:
--   For two agents and fixed $\varepsilon>0$, let $k=\lceil3/(2\varepsilon)\rceil$. The $\operatorname{PTAS}(\varepsilon)$ share is exact MMS when $m<3/\varepsilon$ or when some item has value greater than $2v(M)/3$. Otherwise it maximizes the smaller bundle value over partitions in which the first bundle contains an arbitrary subset of the top $k$ ranks and a suffix of the remaining ranks.
--
--   This is the exact share used in Theorem 5, including both exceptional cases from its proof.
--
--   **Formalization Note** Items are `Fin m`. The value ranges over every compatible non-increasing order, so equal-value tie breaking is immaterial. Outside $\varepsilon>0$, the total Lean function returns zero.
-- source:
--   Babaioff & Feige, arXiv:2205.07519v1, Theorem 5 and proof, pp.20-21

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

set_option autoImplicit false

namespace FairShares.Supplement

/-- **The two-agent `PTAS(ε)` share.**
Babaioff & Feige, arXiv:2205.07519v1, Theorem 5 and its proof, pp.20--21.

For `ε > 0`, the share is exact MMS when `m < 3/ε`, or when some item has value greater than
`2 v(M)/3`.  Otherwise put `k = ⌈3/(2ε)⌉`: among the top `k` ranks the first bundle is arbitrary,
and among the remaining ranks it must be a suffix.  The share maximizes the smaller bundle
value over exactly those partitions.

**Formalization Note.** Items are `Fin m`; rank zero is the most valuable rank.  The first bundle
is label `0 : Fin 2`.  Outside the theorem's domain `ε > 0` the total Lean function is set to
zero.  MMS is `LittleCharity.MMS.mms v 2 univ`. -/
noncomputable def ptasShare (ε : ℝ) (m : ℕ) (v : Finset (Fin m) → ℝ) : ℝ :=
  if 0 < ε then
    if (m : ℝ) < 3 / ε ∨ ∃ g : Fin m, 2 * v Finset.univ < 3 * v {g} then
      LittleCharity.MMS.mms v 2 Finset.univ
    else
      let k : ℕ := ⌈(3 : ℝ) / (2 * ε)⌉₊
      ⨆ (σ : Equiv.Perm (Fin m))
          (_ : ∀ a b : Fin m, a.val < b.val → v {σ a} ≥ v {σ b})
          (P : Fin m → Fin 2)
          (_ : P ∈ Finset.univ.filter (fun P : Fin m → Fin 2 =>
            ∀ a b : Fin m, k ≤ a.val → a.val ≤ b.val → P a = 0 → P b = 0)),
        ⨅ i : Fin 2, v (Finset.univ.filter (fun g => P (σ.symm g) = i))
  else 0

end FairShares.Supplement


