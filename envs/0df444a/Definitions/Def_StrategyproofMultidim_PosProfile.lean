-- Prove2me | Definitions.Def_StrategyproofMultidim_PosProfile
-- name    : StrategyproofMultidim_PosProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:35.815762+00:00
-- url     : https://prove2.me/theorems/2f8c7037-e106-4601-be6e-661f6fbad9ef
-- title:
--   Valuation profiles $v\in\mathcal V=(\mathbb R^m_{++})^n$
-- statement:
--   Each buyer $i$ has a positive valuation $v_i^k\in\mathbb R_{++}$ for each object $k$. A **valuation profile** is the $n\times m$ matrix $v=(v_i^k)$; the set of profiles is $\mathcal V=\prod_{i\in N}\mathbb R^m_{++}$. The predicate states that every entry of the matrix is strictly positive.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), §3, p.5 (PDF p.6)

import Mathlib

namespace StrategyproofMultidim

/-- **Valuation profiles `v ∈ 𝒱`** (§3, p.5).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.5: "each buyer i has a positive private valuation vᵢᵏ ∈ ℝ₊₊ for each object k ∈ M
… let 𝒱 := Πᵢ∈N Vᵢ be the set of all possible valuation profiles, where each profile is a
n × m matrix."

`PosProfile v` says the `n × m` real matrix `v` (row `i` = buyer `i`'s valuation vector) has all
entries strictly positive, i.e. `v ∈ 𝒱 = (ℝᵐ₊₊)ⁿ`.

**Formalization Note.** Profiles are `Fin n → Fin m → ℝ`; positivity is a predicate, not a
subtype. -/
def PosProfile {n m : ℕ} (v : Fin n → Fin m → ℝ) : Prop :=
  ∀ i k, 0 < v i k

end StrategyproofMultidim


