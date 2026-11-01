-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_IsSliceTestFunction
-- name    : JRCurvedQFT_SharpTime_IsSliceTestFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:47.483548+00:00
-- url     : https://prove2.me/theorems/9f7f2693-e45e-439d-87b9-31d55e2d0af3
-- title:
--   Real test function on the slice, $f\in C_c^\infty(\Sigma,\mathbb R)$
-- statement:
--   A **test function on the slice** is a real $f\in C_c^\infty(\Sigma)$, represented by its lift $\tilde f(p)=f(\phi_{-t(p)}(p))$ to $M$: a smooth function on $M$, constant along the Killing trajectories ($\tilde f\circ\phi_s=\tilde f$), whose support meets $\Sigma$ in a compact set.
--
--   These are the functions $f$ of Theorems 4.2–4.4 (with "f real-valued", p. 23).
--
--   **Formalization Note** $\Sigma$ is not itself a Lean manifold; smooth compactly supported functions on $\Sigma$ correspond exactly to such invariant lifts (Reading 2).
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Theorem 4.2, p. 21; proof of Theorem 4.3, p. 23; p. 24

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_StaticStructure

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- `f` is (the ξ-invariant lift of) a **real test function on the slice**, `f ∈ C_c^∞(Σ, ℝ)`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, Theorem 4.2, p. 21 (domain `C_c^∞(Σ) ⊂ 𝒦_Σ`), Theorem 4.3, p. 23 ("assume f is
real-valued"), and the sharp-time distributions `f_t` of p. 24.

The lift `f : M → ℝ` is smooth, constant along the trajectories of ξ (`f ∘ φ_s = f`), and
`Σ ∩ tsupport f` is compact.

**Formalization Note** Reading 2: `Σ` is not a Lean manifold, so a function on `Σ` is represented
by its ξ-invariant lift `f̃(p) = f(φ_{−t(p)}(p))`; smooth compactly supported functions on `Σ`
correspond exactly to such lifts. -/
def IsSliceTestFunction (S : StaticStructure (d := d) M) (f : M → ℝ) : Prop :=
  ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, ℝ) ∞ f ∧ (∀ s p, f (S.flow s p) = f p) ∧
    IsCompact (S.slice ∩ tsupport f)

end JRCurvedQFT.SharpTime


