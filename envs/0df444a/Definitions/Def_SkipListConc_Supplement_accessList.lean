-- Prove2me | Definitions.Def_SkipListConc_Supplement_accessList
-- name    : SkipListConc_Supplement_accessList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:57:09.417441+00:00
-- url     : https://prove2.me/theorems/3378db67-d0f4-484f-9c23-7e677cc35079
-- title:
--   Accessed items $X$ as a list
-- statement:
--   The $n$ items are listed in their insertion order $\mathrm{ins}$; access $i$ is to the item $\mathrm{ins}[v_i]$. This gives the access sequence $X$ as a list of items, and the operation sequence the structure serves is $\sigma_X=\mathrm{ins}\mathbin{+\!\!+}X$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem F, p.11; §5.3, p.34

import Mathlib

namespace SkipListConc.Supplement

/-- The list of accessed items `X = (X_1, …, X_m)` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Theorem F, p.11, and §5.3, p.34): the
`n` items are given by their insertion order `ins`, and access `i` is to the item `ins[v i]`.
The operation sequence the structure serves is `σ_X = ins ++ accessList ins v`. -/
def accessList {α : Type*} {m : ℕ} (ins : List α) (v : Fin m → Fin ins.length) : List α :=
  List.ofFn fun i => ins.get (v i)

end SkipListConc.Supplement


