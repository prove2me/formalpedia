-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_IsHminus1
-- name    : JRCurvedQFT_SharpTime_IsHminus1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:53.000529+00:00
-- url     : https://prove2.me/theorems/6d50f3ed-3b65-476f-99f8-53456105b994
-- title:
--   Membership in the Sobolev space $H_{-1}(M)$
-- statement:
--   A functional $\ell$ on test functions **belongs to $H_{-1}(M)$** if it is linear on test functions, $\ell(au+v)=a\,\ell(u)+\ell(v)$ for test functions $u,v$ and $a\in\mathbb R$, and $\|\ell\|_{-1}<\infty$.
--
--   The paper works "with test functions in $H_{-1}(M)$" (§1.3). Two functionals with $\|\ell-\ell'\|_{-1}=0$ represent the same element.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, §1.3, p. 4

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_negSobolevNorm

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- `ℓ` is an element of the **Sobolev space `H₋₁(M)`**: it is linear on test functions and has
finite norm `‖ℓ‖₋₁`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, §1.3, p. 4: "We work with test functions in H₋₁(M)".

**Formalization Note** Reading 4: an element of `H₋₁(M)` (the dual of `H₁(M)`) is represented by
any functional agreeing with it on `C_c^∞(M)`; two representatives with `‖ℓ − ℓ'‖₋₁ = 0` are the
same element. -/
def IsHminus1 [MeasurableSpace M] (μ : Measure M) (m : ℝ) (ℓ : (M → ℝ) → ℝ) : Prop :=
  (∀ (a : ℝ) (u v : M → ℝ), IsTestFunction (d := d) u → IsTestFunction (d := d) v →
    ℓ (a • u + v) = a * ℓ u + ℓ v) ∧ negSobolevNorm (d := d) μ m ℓ < ⊤

end JRCurvedQFT.SharpTime


