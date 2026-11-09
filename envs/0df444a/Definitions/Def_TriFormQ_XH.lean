-- Prove2me | Definitions.Def_TriFormQ_XH
-- name    : TriFormQ_XH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:48:51.543001+00:00
-- url     : https://prove2.me/theorems/265e704c-6bc6-4011-a9a7-d6a1e107d2b6
-- title:
--   Total weight $X_H$ of an affine subspace
-- statement:
--   For a trilinear form $f$ and an affine subspace $H\subseteq\mathbb F_q^n$,
--
--   $$X_H=\sum_{v\in H}w(v),\qquad w(v)=q^{-\mathrm{rk} f\langle v\rangle}.$$
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Eq. (7), p.24 (PDF p.27)

import Definitions.Def_TriFormQ_weight

namespace TriFormQ

open Classical in
/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Eq. (7), p.24 (PDF p.27): "For an
affine subspace H, define X_H := Σ_{v∈H} w(v)". -/
noncomputable def XH {F : Type} [Field F] [Fintype F] {n : ℕ} (θ : TriForm F n)
    (H : AffineSubspace F (Vec F n)) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => v ∈ H), weight θ v

end TriFormQ


