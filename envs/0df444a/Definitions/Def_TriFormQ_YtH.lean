-- Prove2me | Definitions.Def_TriFormQ_YtH
-- name    : TriFormQ_YtH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:56:08.660355+00:00
-- url     : https://prove2.me/theorems/efcacc4e-3df5-46f1-a7b0-d0ee6a9da928
-- title:
--   Projected good weight $\tilde Y_H$
-- statement:
--   For a trilinear form $f$ with good set $G$, probe vectors $w_1,\dots,w_e$ and an affine subspace $H$,
--
--   $$\tilde Y_H=\sum_{v\in H\cap G}\tilde w(v).$$
--
--   Sampling $v\in H$ with probability proportional to $\tilde w$ returns a good base point with probability $\tilde Y_H/\tilde X_H$.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Eq. (19), p.27 (PDF p.30)

import Definitions.Def_TriFormQ_projWeight
import Definitions.Def_TriFormQ_goodSet

namespace TriFormQ

open Classical in
/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Eq. (19), p.27 (PDF p.30):
"Ỹ_H := Σ_{v∈H∩G} w̃(v)", for the projection given by the probe vectors `ws`. -/
noncomputable def YtH {F : Type} [Field F] [Fintype F] [DecidableEq F] {n e : ℕ}
    (θ : TriForm F n) (ws : Fin e → Vec F n) (H : AffineSubspace F (Vec F n)) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => v ∈ H ∧ v ∈ goodSet θ), projWeight θ ws v

end TriFormQ


