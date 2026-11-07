-- Prove2me | Definitions.Def_ConstDepthUnitary_GammaHat
-- name    : ConstDepthUnitary_GammaHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:03.690807+00:00
-- url     : https://prove2.me/theorems/c186471e-7217-4ad1-9df9-8549122d1d9c
-- title:
--   The half-algorithm $\hat\Gamma_S$
-- statement:
--   The algorithm's isometry up to right before the middle oracle query:
--   $$\hat\Gamma_S=\hat F\,\hat Q_S\,\hat E.$$
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §5.2.1, Eq. (56), p.25

import Mathlib
import Definitions.Def_ConstDepthUnitary_EHat
import Definitions.Def_ConstDepthUnitary_QHat
import Definitions.Def_ConstDepthUnitary_FHat

namespace ConstDepthUnitary

/-- The half-algorithm isometry `Γ̂_S = F̂ Q̂_S Ê`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Eq. (56), p.25. -/
noncomputable def GammaHat {N : ℕ} (K : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N → Fin K) (Fin N) ℂ :=
  FHat N K * QHat K S * EHat N K

end ConstDepthUnitary


