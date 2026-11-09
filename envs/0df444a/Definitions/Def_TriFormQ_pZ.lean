-- Prove2me | Definitions.Def_TriFormQ_pZ
-- name    : TriFormQ_pZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:48:23.562001+00:00
-- url     : https://prove2.me/theorems/df266e2f-8308-42e9-a723-342455dabe08
-- title:
--   Distribution $p_Z$ on base points
-- statement:
--   For a trilinear form $f$ with zero locus $Z$ and fibers $Z_v$, the distribution $p_Z$ on $\mathbb F_q^n$ is
--
--   $$p_Z(v)=\frac{|Z_v|}{|Z|}=\frac{q^{\,n-\mathrm{rk} f\langle v\rangle}}{|Z|},$$
--
--   the law of the second coordinate of a uniform element of $Z$. It sums to $1$ (proved sanity check). Lemma 2 and Fact 1 are statements about it.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.13 (PDF p.16)

import Definitions.Def_TriFormQ_zeroLocus
import Definitions.Def_TriFormQ_fiber

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.13 (PDF p.16): "Since
Z = ∪_{v∈V} Z_v, it naturally induces a distribution p_Z : V → ℝ_{≥0} over the base space V:
p_Z(v) := |{u ∈ U : (u, v) ∈ Z}| / |Z| = |Z_v| / |Z|". -/
noncomputable def pZ {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (θ : TriForm F n)
    (v : Vec F n) : ℝ :=
  ((fiber θ v).card : ℝ) / (zeroLocus θ).card

end TriFormQ


