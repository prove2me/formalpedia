-- Prove2me | Definitions.Def_TriFormQ_YH
-- name    : TriFormQ_YH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:56:07.528522+00:00
-- url     : https://prove2.me/theorems/31cf291a-8472-4c2e-96fc-c37382647991
-- title:
--   Good weight $Y_H$ of an affine subspace
-- statement:
--   For a trilinear form $f$ with good set $G$ and an affine subspace $H\subseteq\mathbb F_q^n$,
--
--   $$Y_H=\sum_{v\in H\cap G}w(v).$$
--
--   If a point of $H$ is sampled with probability proportional to $w$, it is good with probability $Y_H/X_H$.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Eq. (7), p.24 (PDF p.27)

import Definitions.Def_TriFormQ_weight
import Definitions.Def_TriFormQ_goodSet

namespace TriFormQ

open Classical in
/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Eq. (7), p.24 (PDF p.27):
"Y_H := Σ_{v∈H∩G} w(v)", with `G` the good set (Definition 2). -/
noncomputable def YH {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (θ : TriForm F n)
    (H : AffineSubspace F (Vec F n)) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => v ∈ H ∧ v ∈ goodSet θ), weight θ v

end TriFormQ


