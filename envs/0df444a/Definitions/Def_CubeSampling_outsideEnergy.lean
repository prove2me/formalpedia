-- Prove2me | Definitions.Def_CubeSampling_outsideEnergy
-- name    : CubeSampling_outsideEnergy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:21.132969+00:00
-- url     : https://prove2.me/theorems/e92fe359-b5bc-4e42-b962-2e87ff43516e
-- title:
--   Energy outside a set, $\mathbb E[h^2\mathbf 1_{E^c}]$
-- statement:
--   For $h : \{-1,1\}^d \to \mathbb R$ and $E \subseteq \{-1,1\}^d$, the **energy of $h$ outside $E$** is
--   $$
--   \mathbb E[h^2 \mathbf 1_{E^c}] = 2^{-d} \sum_{x \notin E} h(x)^2 .
--   $$
--   A function concentrates its energy on $E$ with leakage $\rho$ when $\mathbb E[h^2\mathbf 1_{E^c}] \le \rho\,\mathbb E[h^2]$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Theorem 1.9, p.6; (3), p.8

import Mathlib
import Definitions.Def_CubeSampling_cubeMean

namespace CubeSampling

/-- The energy of `h` outside a set `E`, `E[h² 1_{E^c}]` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Theorem 1.9, p.6; (3), p.8). -/
noncomputable def outsideEnergy (d : ℕ) (E : Set (Cube d)) (h : Cube d → ℝ) : ℝ :=
  cubeMean d (Eᶜ.indicator fun x => h x ^ 2)

end CubeSampling


