-- Prove2me | Definitions.Def_SecondBestBT_roundedMass
-- name    : SecondBestBT_roundedMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:59.166672+00:00
-- url     : https://prove2.me/theorems/309a44e5-d0d4-48c7-b9b2-52b3e9e4c72d
-- title:
--   Mass of a prior at a dyadic grid point
-- statement:
--   For a prior $\nu$ on $\mathbb R$, the mass at the dyadic grid point $t_k=k2^{-M}$ is $\nu(\{k2^{-M}\})$. Applied to the rounded priors $\hat F^M_S,\hat F^M_B$ it gives the grid masses $\hat f^M_S(k)$, $\hat f^M_B(k)$, $k=0,\dots,2^M$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 3, p.6; proof of Lemma 3.3, p.32

import Mathlib

open MeasureTheory

namespace SecondBestBT

/-- The mass `f̂^M(k) = F̂^M({k 2^{−M}})` of a prior `ν` at the dyadic grid point `t_k = k 2^{−M}`
(Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 3, p.6, and the proof
of Lemma 3.3, p.32). Applied to `ν = μ.map π^M`, the rounded prior, it gives the grid masses of
`F̂^M_S` and `F̂^M_B`. -/
noncomputable def roundedMass (ν : Measure ℝ) (M k : ℕ) : ℝ :=
  ν.real {(k : ℝ) / 2 ^ M}

end SecondBestBT


