-- Prove2me | Definitions.Def_LawLocalComp_dirRank
-- name    : LawLocalComp_dirRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:54.29894+00:00
-- url     : https://prove2.me/theorems/ffa24ada-bd5c-47d4-9d46-486b143d92cb
-- title:
--   Direction rank $\dim\operatorname{span}\{a_j\}$
-- statement:
--   For directions $a_1,\dots,a_n\in\mathbb R^d$, the **direction rank** is $\dim\operatorname{span}\{a_1,\dots,a_n\}$. A rank promise $q$ admits every finite selection whose direction rank is at most $q$, whatever the number of jobs.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2

import Mathlib

namespace LawLocalComp

/-- **The direction rank `dim span{a_j}`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("a rank promise permits every finite selection with dim span{aj} ≤ q"). -/
noncomputable def dirRank {d n : ℕ} (a : Fin n → Fin d → ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range a))

end LawLocalComp


