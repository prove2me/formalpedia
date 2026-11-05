-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_testFunctions
-- name    : JRCurvedQFT_Symmetries_testFunctions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:02.567599+00:00
-- url     : https://prove2.me/theorems/6d181a1f-916a-4552-a4f1-e51b5c925662
-- title:
--   Test functions $C_c^\infty(M,\mathbb R)$
-- statement:
--   The real vector space $C_c^\infty(M,\mathbb R)$ of smooth compactly supported real functions on $M$, which index the Euclidean field.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, §2.1, pp. 2–3

import Mathlib

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory

namespace JRCurvedQFT.Symmetries

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]

/-- The real **test functions** `C_c^∞(M, ℝ)`, as a real vector space.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, §2.1, pp. 2–3: monomials `Φ(f₁)…Φ(f_n)` with `f_i ∈ S`, and for open `Ω` those with
`supp(f_i) ⊂ Ω`.

**Formalization Note** Reading 3: the test functions are smooth with compact support, the elements
of `S` with compact support in `M`. -/
def testFunctions (M : Type) [EMetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] :
    Submodule ℝ (M → ℝ) where
  carrier := {u | ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, ℝ) ∞ u ∧ HasCompactSupport u}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contMDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c _ ha => ⟨(contDiff_const_smul c).comp_contMDiff ha.1,
    ha.2.comp_left (g := fun x : ℝ => c • x) (smul_zero c)⟩

end JRCurvedQFT.Symmetries


