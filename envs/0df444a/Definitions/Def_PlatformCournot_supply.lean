-- Prove2me | Definitions.Def_PlatformCournot_supply
-- name    : PlatformCournot_supply
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:22.940246+00:00
-- url     : https://prove2.me/theorems/deccd1da-d017-4d86-bf99-f691d767182a
-- title:
--   Aggregate output $s_i=\sum_j q_{ij}$ of firm $i$, display (1)
-- statement:
--   For a supply profile $q=(q_{ij})$, where $q_{ij}$ is the quantity firm $i$ supplies to market $j$, the **aggregate output** of firm $i$ is
--
--   $$s_i=\sum_{j=1}^m q_{ij}.$$
--
--   **Formalization Note** A supply profile is a function `q : Fin n → Fin m → ℝ`, firm first.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, display (1), p.8

import Mathlib

namespace PlatformCournot

/-- **Aggregate output of firm `i`, display (1).**
Pang et al., arXiv:1903.04574v3, display (1), p.8: "si := Σ_{j=1}^m qij."

**Formalization Note** A supply profile is `q : Fin n → Fin m → ℝ`, firm first: `q i j` is `qᵢⱼ`,
the quantity firm `i` supplies to market `j`. -/
def supply {n m : ℕ} (q : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ j, q i j

end PlatformCournot


