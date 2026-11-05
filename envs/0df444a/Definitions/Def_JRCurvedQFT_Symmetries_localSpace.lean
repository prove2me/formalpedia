-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_localSpace
-- name    : JRCurvedQFT_Symmetries_localSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:04:56.051196+00:00
-- url     : https://prove2.me/theorems/18b0e881-03d3-45aa-851e-5ea2d006fa05
-- title:
--   Local field space $\mathcal E_U$ and the positive-time subspace $\mathcal E_+$
-- statement:
--   For $U\subset M$, the **local field space** $\mathcal E_U$ is the closure in $\mathcal E$ of the span of the monomials $\Phi(f_1)\cdots\Phi(f_n)$, $n\ge0$, with $\operatorname{supp}f_i\subset U$ for all $i$. The **positive-time subspace** is $\mathcal E_+=\mathcal E_{\Omega_+}$. The constant $1$ lies in every $\mathcal E_U$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, §2.1, p. 3

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_fieldSpace

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory

namespace JRCurvedQFT.Symmetries

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The **local field space** `E_U`: the closure in `E` of the span of the monomials
`Φ(f₁)…Φ(f_n)`, `n ≥ 0`, with `supp f_i ⊂ U` for all `i`. `E₊` is `localSpace Φ S.positiveTime`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, §2.1, p. 3: "For an open set Ω ⊂ M, let E_Ω denote the closure in E of the set of monomials
A(Φ) = ∏_i Φ(f_i) where supp(f_i) ⊂ Ω for all i ... the positive-time subspace E₊ := E_{Ω₊}."

**Formalization Note** The closure is of the span: `E₊` is used as a subspace (Definition 3.1). The
constant `1` (`n = 0`) belongs to every `E_U`. -/
noncomputable def localSpace (Φ : EuclideanField (d := d) M P) (U : Set M) :
    Submodule ℂ (fieldSpace Φ) :=
  (Submodule.span ℂ {x | ∃ (n : ℕ) (f : Fin n → testFunctions (d := d) M),
    (∀ i, tsupport (f i : M → ℝ) ⊆ U) ∧ x = fieldMonomial Φ f}).topologicalClosure

end JRCurvedQFT.Symmetries


