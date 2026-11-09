-- Prove2me | Definitions.Def_TriFormQ_Mv
-- name    : TriFormQ_Mv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:48:15.311987+00:00
-- url     : https://prove2.me/theorems/075c1eea-5be0-4b2e-9bd5-a7ca0cdc71a4
-- title:
--   Average slice size $M(v)=\mathbb E_{u\in Z_v}q^{\mathrm{rk} f[u]}$
-- statement:
--   For a trilinear form $f$ and $v\in\mathbb F_q^n$,
--
--   $$M(v)=\mathbb E_{u\in Z_v}\, q^{\mathrm{rk} f[u]}=\frac{1}{|Z_v|}\sum_{u\in Z_v}q^{\mathrm{rk} f[u]},$$
--
--   the average, over the fiber $Z_v$ (a nonempty subspace), of the size of the row space of the slice $f[u]$. It enters the definition of good base points.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.14 (PDF p.17)

import Definitions.Def_TriFormQ_fiber
import Definitions.Def_TriFormQ_sliceU

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.14 (PDF p.17): "For
every v ∈ V, define M(v) := E_{u∈Z_v} q^{rk f[u]}", the average over the fiber `Z_v` (uniform;
it contains `0`, so it is nonempty) of `q^{rk f[u]}` with `q = |F|`. -/
noncomputable def Mv {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (θ : TriForm F n)
    (v : Vec F n) : ℝ :=
  (∑ u ∈ fiber θ v, (Fintype.card F : ℝ) ^ (sliceU θ u).rank) / (fiber θ v).card

end TriFormQ


