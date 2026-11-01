-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_expVec
-- name    : JRCurvedQFT_SharpTime_expVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:46.996164+00:00
-- url     : https://prove2.me/theorems/a92eccf2-62e3-46f2-afbe-5565e1766740
-- title:
--   Exponential vector $e^{i\Phi(h)}\in\mathcal E$
-- statement:
--   For a field $\Phi$ on $(\Omega,P)$ and an index $h$, the **exponential vector** is the class in $\mathcal E=L^2(\Omega,P;\mathbb C)$ of
--   $$\omega\longmapsto e^{i\Phi(h)(\omega)} .$$
--   It has modulus one, so it lies in $L^2$ as soon as $\Phi(h)$ is measurable.
--
--   **Formalization Note** If $\Phi(h)$ is not measurable the value is $0$; this never happens for $h\in H_{-1}(M)$ under the free-field hypothesis.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, p. 5; Definition 1.2, p. 5; Theorem 4.4, p. 24

import Mathlib

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

/-- The **exponential vector** `e^{iΦ(h)} ∈ ℰ = L²(Ω, P; ℂ)`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, p. 5 (`ℰ := L²(H₋∞, µ)`, the vectors `e^{iΦ(f)}`), Definition 1.2, p. 5, and Theorem 4.4,
p. 24 (`exp(iΦ(f₀))`).

**Formalization Note** The function `w ↦ exp(iΦ(h)(w))` has modulus 1, so it is in `L²` as soon as it
is (a.e. strongly) measurable, which holds for every `h ∈ H₋₁` under `IsGaussianField`. For a
non-measurable `Φ(h)` the value is the junk `0`; no statement uses it there. -/
noncomputable def expVec {X Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Φ : X → Ω → ℝ) (h : X) : Lp ℂ 2 P :=
  open Classical in
  if hm : AEStronglyMeasurable (fun w => Complex.exp (↑(Φ h w) * Complex.I)) P then
    (MemLp.of_bound hm 1 (ae_of_all _ fun w => le_of_eq (Complex.norm_exp_ofReal_mul_I _))).toLp _
  else 0

end JRCurvedQFT.SharpTime


