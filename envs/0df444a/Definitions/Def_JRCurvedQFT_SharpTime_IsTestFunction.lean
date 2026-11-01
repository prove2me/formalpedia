-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_IsTestFunction
-- name    : JRCurvedQFT_SharpTime_IsTestFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:42.678341+00:00
-- url     : https://prove2.me/theorems/a361364b-1b65-4000-85b9-c591de858dae
-- title:
--   Test function $u\in C_c^\infty(M,\mathbb R)$
-- statement:
--   A **test function** on $M$ is a real-valued function $u\in C_c^\infty(M)$: smooth, with compact support.
--
--   Test functions are the dense core from which the Sobolev space $H_1(M)$ is completed, and the smooth test functions supported in an open set $\Omega$ generate the standard domain $\mathcal E_\Omega$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, §1.3, p. 4, Eq. (1.2); Definition 1.2, p. 5; proof of Theorem 4.4, p. 25

import Mathlib

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- `u` is a **test function** on `M`: a real-valued `C^∞` function with compact support,
`u ∈ C_c^∞(M, ℝ)`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, §1.3, p. 4 ((1.2): H_s(M) is the completion of smooth functions) and Definition 1.2, p. 5;
the proof of Theorem 4.4, p. 25 ("smooth test functions {g_n} with compact, positive-time
support").

**Formalization Note** Readings 4–5: `C_c^∞(M)` is the dense core from which `H₁(M)` is completed
and the class of functions generating the standard domains. -/
def IsTestFunction (u : M → ℝ) : Prop :=
  ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, ℝ) ∞ u ∧ HasCompactSupport u

end JRCurvedQFT.SharpTime


