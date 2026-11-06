-- Prove2me | Definitions.Def_ZOGlobalLB_IsHaarFrame
-- name    : ZOGlobalLB_IsHaarFrame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:46:38.929047+00:00
-- url     : https://prove2.me/theorems/57d13afe-7f1f-40d9-b38b-709fe9a7a2ce
-- title:
--   Haar orthonormal frames
-- statement:
--   A random frame $U=(u_1,\dots,u_T)$ in $\mathbb R^r$ is a **Haar orthonormal frame** if it is measurable, almost surely orthonormal, and its law is invariant under every orthogonal transformation of $\mathbb R^r$ applied to all columns. These properties determine the law (the uniform law on orthonormal $T$-frames).
--
--   The hidden chain directions and workspace directions of the construction are independent Haar frames.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Section 3, footnote 1, p.9; Appendix B, p.36

import Mathlib
import Definitions.Def_ZOGlobalLB_Admissible

open MeasureTheory

namespace ZOGlobalLB

/-- **Haar orthonormal frame.** Xia, Yuan, arXiv:2610.19652, Section 3, footnote 1, p.9 ("A Haar
orthonormal frame consists of uniformly random, mutually orthogonal unit vectors, with a
distribution invariant under rotations"), and Appendix B, p.36 ("independent Haar orthonormal
frames").

A random frame `U : Ω → (Fin T → ℝʳ)` is Haar if it is measurable, almost surely orthonormal, and
its law is invariant under every linear isometry `L` of `ℝʳ` acting on each column. These three
properties determine the law: the orthogonal group acts transitively on orthonormal `T`-frames,
and the invariant probability measure on them is unique.

**Formalization Note.** The same pattern as the platform's `IsUniformOnUnitSphere` (v2), which is
the case `T = 1`. Measurability is required, since for a non-measurable map `Measure.map` is the
zero measure and the invariance clause would hold vacuously. -/
def IsHaarFrame {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {r T : ℕ}
    (U : Ω → Fin T → E r) : Prop :=
  Measurable U ∧
  (∀ᵐ ω ∂P, Orthonormal ℝ (U ω)) ∧
  ∀ L : E r ≃ₗᵢ[ℝ] E r, P.map (fun ω i => L (U ω i)) = P.map U

end ZOGlobalLB


