-- Prove2me | Definitions.Def_PADMPriv_meanSampleOp
-- name    : PADMPriv_meanSampleOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:09.864305+00:00
-- url     : https://prove2.me/theorems/d9a22f44-f875-4dc0-a9c1-f55ebea527c6
-- title:
--   Mean sample operator $\bar T(u)=\mathbb E_d[T_{f(\cdot,d)}(u)]$
-- statement:
--   The **mean sample operator** averages the sample PADM operators over the record distribution:
--   $$
--   \bar T(u) = \mathbb E_{d\sim P_R}\big[T_{f(\cdot,d)}(u)\big].
--   $$
--   It generally differs from the population operator $T_F$; the utility analysis compares the fixed points of the two.
--
--   **Formalization Note** A Bochner integral of $d\mapsto T_{f(\cdot,d)}(u)$; under the hypotheses of every statement using it the integrand is measurable and bounded.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Section 2.3, p.5; A.14, p.30

import Mathlib
import Definitions.Def_PADMPriv_padmOp

namespace PADMPriv

open MeasureTheory

/-- The mean sample operator `T̄(u) = E_{d ∼ P_R}[T_{f(·,d)}(u)]` of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d),
Section 2.3, p.5, and A.14, p.30.

**Formalization Note** A Bochner integral of `d ↦ T_{f(·,d)}(u)`; under the hypotheses of every
statement using it, this map is measurable and bounded in `d` (A.14, p.30). -/
noncomputable def meanSampleOp {m p l : ℕ} {R : Type*} [MeasurableSpace R] (β : ℝ)
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (PR : Measure R) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  ∫ d, padmOp β (fun x => f x d) g A B c u ∂PR

end PADMPriv


