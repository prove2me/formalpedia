-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_positiveTimeSubspaceL2
-- name    : JRCurvedQFT_SharpTime_positiveTimeSubspaceL2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:14.011244+00:00
-- url     : https://prove2.me/theorems/091d2753-d397-4267-a785-22e18ccc477f
-- title:
--   Positive-time subspace $\mathcal E_+$ of a Gaussian field indexed by $L^2(M)$
-- statement:
--   For a static structure on $M$ (time function $t$, $\Omega_+=\{t>0\}$) and a family $\Psi=(\Psi(f))_{f\in L^2(M)}$ of real random variables on $(\Omega,P)$, the **positive-time subspace** $\mathcal E_+$ is the closed span in $L^2(\Omega,P;\mathbb C)$ of the vectors $e^{i\Psi(f)}$ over real $f\in L^2(M)$ vanishing almost everywhere on $\{t\le0\}$ (Definition 1.2 with $\Omega=\Omega_+$).
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Definition 1.2, p. 5

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_StaticStructure
import Definitions.Def_JRCurvedQFT_SharpTime_expVec

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The **positive-time subspace** `ℰ₊` of a Gaussian field `Ψ` indexed by real `L²(M)`: the closed
span in `L²(Ω, P; ℂ)` of the vectors `e^{iΨ(f)}`, `f ∈ L²(M)` vanishing a.e. outside `Ω₊ = {t > 0}`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, Definition 1.2, p. 5: "E_Ω = span{e^{iΦ(f)} : f ∈ H₋₁(M), supp(f) ⊂ Ω}. Let ℰ_Ω denote the
closure in ℰ of E_Ω", and "the positive-time subspace ℰ₊ := ℰ_{Ω₊}, where the notation Ω₊ refers to
the decomposition (1.1)".

**Formalization Note** Used for a Gaussian field with an arbitrary bounded covariance on `L²(M)`
(`IsCovGaussianField`), whose test functions are `L²(M)` functions. "supp f ⊂ Ω₊" is read as "f = 0
a.e. on {t ≤ 0}"; for a covariance bounded on `L²(M)` this gives the same closure as functions with
closed support in `Ω₊`, since `f ↦ e^{iΨ(f)}` is `L²`-continuous and the functions with closed
support in `Ω₊` are `L²`-dense among those vanishing a.e. on `{t ≤ 0}`. -/
noncomputable def positiveTimeSubspaceL2 [MeasurableSpace M] (S : StaticStructure (d := d) M)
    (μ : Measure M) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Ψ : Lp ℝ 2 μ → Ω → ℝ) : Submodule ℂ (Lp ℂ 2 P) :=
  (Submodule.span ℂ {A | ∃ f : Lp ℝ 2 μ, (∀ᵐ p ∂μ, S.time p ≤ 0 → f p = 0) ∧
    A = expVec P Ψ f}).topologicalClosure

end JRCurvedQFT.SharpTime


