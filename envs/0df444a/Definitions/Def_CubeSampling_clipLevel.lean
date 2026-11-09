-- Prove2me | Definitions.Def_CubeSampling_clipLevel
-- name    : CubeSampling_clipLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:23.696233+00:00
-- url     : https://prove2.me/theorems/f1bae019-386e-4ef6-adf4-a8c7901f96cc
-- title:
--   Clipping level $b_\eta(h) = \inf\{B > 0 : \mathbb E[h^2\wedge B] \ge \eta\}$
-- statement:
--   For $\eta \in (0,1)$ and $h : \{-1,1\}^d \to \mathbb R$,
--   $$
--   b_\eta(h) = \inf\{B > 0 : \mathbb E[h^2 \wedge B] \ge \eta\},
--   $$
--   the smallest level at which clipping $h^2$ retains energy $\eta$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 2.2, p.8

import Mathlib
import Definitions.Def_CubeSampling_cubeMean

namespace CubeSampling

/-- The clipping level `b_η(h) = inf{B > 0 : E[h² ∧ B] ≥ η}` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §2.2, p.8). -/
noncomputable def clipLevel (d : ℕ) (η : ℝ) (h : Cube d → ℝ) : ℝ :=
  sInf {B : ℝ | 0 < B ∧ η ≤ cubeMean d (fun x => min (h x ^ 2) B)}

end CubeSampling


