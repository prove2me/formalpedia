-- Prove2me | Definitions.Def_SelectiveDPT_prodDist
-- name    : SelectiveDPT_prodDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:31.671841+00:00
-- url     : https://prove2.me/theorems/1904f999-28ea-468e-be72-dc0aa0b093d2
-- title:
--   Product distribution $\mathcal D^m$
-- statement:
--   For a distribution $\mu$ on $X^\iota$ and $m \ge 0$, the **product distribution** of $m$ independent copies is
--   $$\mu^m(x_1, \dots, x_m) = \prod_{j=1}^m \mu(x_j) .$$
--   If $\mu$ is a distribution on $D$, then $\mu^m$ is a distribution on $D^m$.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.2, p.9; Theorem 4.7, p.33 (D^m)

import Mathlib
import Definitions.Def_SelectiveDPT_copy

namespace SelectiveDPT

/-- The product distribution `D^m` of `m` independent copies of the input distribution `μ`
(arXiv:2609.26678, §2.2, p.9: "we will be given `m` inputs, each independently drawn from `D`";
Theorem 4.7, p.33): `μ^m(x_1, …, x_m) = Π_j μ(x_j)`. -/
noncomputable def prodDist {ι α : Type*} (μ : (ι → α) → ℝ) (m : ℕ) : (Fin m × ι → α) → ℝ :=
  fun x => ∏ j, μ (copy x j)

end SelectiveDPT


