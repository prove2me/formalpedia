-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_wickExp
-- name    : JRCurvedQFT_SharpTime_wickExp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:56.831809+00:00
-- url     : https://prove2.me/theorems/a3b86f51-843b-401f-8908-884f7c32cc4a
-- title:
--   Wick exponential $:e^{i\Phi(h)}:=e^{\frac12\|h\|_{-1}^2}e^{i\Phi(h)}$
-- statement:
--   The **Wick-ordered exponential** is
--   $$:e^{i\Phi(h)}:\;=e^{\frac12\|h\|_{-1}^2}\,e^{i\Phi(h)},$$
--   the exponential vector divided by its expectation $e^{-\frac12\|h\|_{-1}^2}$. With it, $\langle :e^{i\Phi(g)}:,:e^{i\Phi(f)}:\rangle_{\mathcal E}=\exp\langle g,Cf\rangle$, as used in (4.19).
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Eqs. (4.17), p. 25, and (4.19), p. 26

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_expVec
import Definitions.Def_JRCurvedQFT_SharpTime_negSobolevNorm

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The **Wick-ordered exponential** `:e^{iΦ(h)}: = e^{½‖h‖²₋₁} e^{iΦ(h)}`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, (4.17), p. 25, and (4.19), p. 26, where `⟨:e^{iΦ(θg_s)}:, :e^{iΦ(f_t)}:⟩_ℰ =
exp⟨θg_s, Cf_t⟩_M`; Wick ordering divides by the expectation `E e^{iΦ(h)} = e^{−½‖h‖²₋₁}` (p. 5).

**Formalization Note** Meaningful for `h ∈ H₋₁` (finite norm). -/
noncomputable def wickExp [MeasurableSpace M] (μ : Measure M) (m : ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (Φ : ((M → ℝ) → ℝ) → Ω → ℝ)
    (h : (M → ℝ) → ℝ) : Lp ℂ 2 P :=
  (Real.exp ((negSobolevNorm (d := d) μ m h).toReal ^ 2 / 2) : ℂ) • expVec P Φ h

end JRCurvedQFT.SharpTime


