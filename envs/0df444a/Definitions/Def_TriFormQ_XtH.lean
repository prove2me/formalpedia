-- Prove2me | Definitions.Def_TriFormQ_XtH
-- name    : TriFormQ_XtH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:21.222558+00:00
-- url     : https://prove2.me/theorems/ab6daaea-c60b-4302-875b-8b66ae2f2113
-- title:
--   Projected total weight $\tilde X_H$
-- statement:
--   For a trilinear form $f$, probe vectors $w_1,\dots,w_e$ (the projection $\Pi$) and an affine subspace $H$,
--
--   $$\tilde X_H=\sum_{v\in H}\tilde w(v),$$
--
--   where $\tilde w$ is the projected weight; the dependence on $\Pi$ is suppressed in the notation, as in the paper.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Eq. (19), p.27 (PDF p.30)

import Definitions.Def_TriFormQ_projWeight

namespace TriFormQ

open Classical in
/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Eq. (19), p.27 (PDF p.30):
"X̃_H := Σ_{v∈H} w̃(v)", for the projection given by the probe vectors `ws` ("We suppress the
dependence on Π in this notation"). -/
noncomputable def XtH {F : Type} [Field F] [Fintype F] {n e : ℕ} (θ : TriForm F n)
    (ws : Fin e → Vec F n) (H : AffineSubspace F (Vec F n)) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => v ∈ H), projWeight θ ws v

end TriFormQ


