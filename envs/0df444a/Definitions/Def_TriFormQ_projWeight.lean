-- Prove2me | Definitions.Def_TriFormQ_projWeight
-- name    : TriFormQ_projWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:48:18.489195+00:00
-- url     : https://prove2.me/theorems/50bfa331-52a7-4bdc-9a76-247df0493f98
-- title:
--   Projected weight $\tilde w(v)=q^{-\mathrm{rk}\tilde f\langle v\rangle}$
-- statement:
--   For a trilinear form $f$, probe vectors $w_1,\dots,w_e$ and $v\in\mathbb F_q^n$, the projected weight is
--
--   $$\tilde w(v)=q^{-\mathrm{rk}\,\tilde f\langle v\rangle}.$$
--
--   Projection can only lower the rank, so $\tilde w(v)\ge w(v)$; the projected weights are what the sampling algorithm can compute with few queries.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Eq. (17), p.26 (PDF p.29)

import Definitions.Def_TriFormQ_projSlice

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Eq. (17), p.26 (PDF p.29): "assign
to v the projected weight w̃(v) := q^{−rk f̃⟨v⟩}". -/
noncomputable def projWeight {F : Type} [Field F] [Fintype F] {n e : ℕ} (θ : TriForm F n)
    (ws : Fin e → Vec F n) (v : Vec F n) : ℝ :=
  ((Fintype.card F : ℝ) ^ (projSlice θ ws v).rank)⁻¹

end TriFormQ


