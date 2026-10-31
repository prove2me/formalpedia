-- Prove2me | Definitions.Def_StrategyproofMultidim_IsFeasible
-- name    : StrategyproofMultidim_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:37.324556+00:00
-- url     : https://prove2.me/theorems/99b5e451-a1c3-46af-b38f-d86e6e953c31
-- title:
--   Feasible decision matrices $\mathcal D$
-- statement:
--   A **decision matrix** is an $n\times m$ matrix $d=(d_i^k)$ with entries in $\{0,1\}$ in which every column has at most one entry equal to $1$: each object is sold to at most one buyer. $\mathcal D$ is the set of such matrices.
--
--   **Formalization Note** The paper says that the elements of each column "sum up to 1". This is read as *at most* 1: the paper sets $\mathcal D=\{0,1\}^m$ for one buyer (p.7), states "sells all objects at all profiles" as a separate hypothesis of Theorem 4, and uses a mechanism that sells nothing in §7.2. Under that hypothesis the two readings coincide.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), §3, p.5 (PDF p.6)

import Mathlib

namespace StrategyproofMultidim

/-- **Decision matrices `𝒟`** (§3, p.5).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.5: "Define an n × m decision matrix d := (dᵢᵏ) such that: (i) its elements are either
0 or 1, (ii) each of its n rows are points in {0, 1}ᵐ, and (iii) elements of each column sum up
to 1. Define 𝒟 to be the set of all such decision matrices."

`IsFeasible e` says every object `k` is assigned to at most one buyer.

**Formalization Note.** Column sums are read as **at most** 1, not exactly 1: p.7 sets
`𝒟 = {0,1}ᵐ` for one buyer, Theorem 4 assumes "sells all objects at all profiles" as a separate
hypothesis, and §7.2 (p.24) uses "a mechanism which does not sell any object". Under the
"sells all objects" hypothesis of the main theorem the two readings coincide. -/
def IsFeasible {n m : ℕ} (e : Fin n → Fin m → Bool) : Prop :=
  ∀ k, (Finset.univ.filter (fun i => e i k = true)).card ≤ 1

end StrategyproofMultidim


