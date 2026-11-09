-- Prove2me | Definitions.Def_TriFormQ_weight
-- name    : TriFormQ_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:56.957603+00:00
-- url     : https://prove2.me/theorems/a641f72a-e645-49cd-8454-0079be982bfb
-- title:
--   Sampling weight $w(v)=q^{-\mathrm{rk} f\langle v\rangle}$
-- statement:
--   For a trilinear form $f$ on $\mathbb F_q^n$ and $v\in\mathbb F_q^n$, the unnormalized sampling weight of $v$ is
--
--   $$w(v)=q^{-\mathrm{rk} f\langle v\rangle}.$$
--
--   Up to normalization it is the distribution $p_Z$: $p_Z(v)=w(v)/\sum_{v'}w(v')$.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), §5.2, p.22 (PDF p.25)

import Definitions.Def_TriFormQ_sliceV

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), §5.2, p.22 (PDF p.25): "Define
w(v) := q^{−rk f⟨v⟩} for every v ∈ V". -/
noncomputable def weight {F : Type} [Field F] [Fintype F] {n : ℕ} (θ : TriForm F n)
    (v : Vec F n) : ℝ :=
  ((Fintype.card F : ℝ) ^ (sliceV θ v).rank)⁻¹

end TriFormQ


