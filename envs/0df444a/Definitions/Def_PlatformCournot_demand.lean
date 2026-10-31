-- Prove2me | Definitions.Def_PlatformCournot_demand
-- name    : PlatformCournot_demand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:20.82181+00:00
-- url     : https://prove2.me/theorems/d013f644-6707-4406-b8f4-8be4a0c79b6f
-- title:
--   Aggregate quantity $d_j=\sum_i q_{ij}$ supplied to market $j$
-- statement:
--   For a supply profile $q=(q_{ij})$, the **aggregate quantity supplied to market $j$** is
--
--   $$d_j=\sum_{i=1}^n q_{ij}.$$
--
--   **Formalization Note** A supply profile is a function `q : Fin n → Fin m → ℝ`, firm first.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, §2.1 Demand model, p.9

import Mathlib

namespace PlatformCournot

/-- **Aggregate quantity supplied to market `j`.**
Pang et al., arXiv:1903.04574v3, §2.1, p.9: "dj := Σ_{i=1}^n qij denotes the aggregate quantity
supplied to market j."

**Formalization Note** A supply profile is `q : Fin n → Fin m → ℝ`, firm first. -/
def demand {n m : ℕ} (q : Fin n → Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ i, q i j

end PlatformCournot


