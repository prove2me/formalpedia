-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
-- name    : ShallowShadows_ShadowNorm_uniformDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:53.572204+00:00
-- url     : https://prove2.me/theorems/e2fca904-a1ce-4f29-bdd6-186df6110c99
-- title:
--   Uniform distribution on a finite set
-- statement:
--   For a finite nonempty set $I$, the **uniform distribution** gives each $i \in I$ probability $1/|I|$. It is the law of the labels of the random Clifford gates.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §III, p. 3; §V, p. 4

import Mathlib
import Definitions.Def_WildeQIT_FinDist

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §III, p. 3 and §V,
p. 4: the uniform distribution on a finite nonempty set of labels, each label drawn with
probability `1 / |ι|`. -/
noncomputable def uniformDist (ι : Type) [Fintype ι] [Nonempty ι] : WildeQIT.FinDist ι where
  prob _ := 1 / (Fintype.card ι : ℝ)
  nonneg _ := by positivity
  sum_eq_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

end ShallowShadows.ShadowNorm


