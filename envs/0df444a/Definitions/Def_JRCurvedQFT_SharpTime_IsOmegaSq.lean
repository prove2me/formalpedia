-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_IsOmegaSq
-- name    : JRCurvedQFT_SharpTime_IsOmegaSq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:39:42.357151+00:00
-- url     : https://prove2.me/theorems/4d4e7a8d-4711-4a1b-9e87-52afa883bb12
-- title:
--   $\omega^2$ as the Friedrichs extension in $\mathcal K_\Sigma$
-- statement:
--   A linear operator $A$ on $\mathcal K_\Sigma$ **is $\omega^2$** if it is the Friedrichs extension of $F^{1/2}(-Q+m^2)F^{1/2}$ on $C_c^\infty(\Sigma)$, characterized by:
--
--   1. $A$ is self-adjoint;
--   2. $A$ extends $\omega^2$ on (real, hence complex) test functions on $\Sigma$;
--   3. every vector of the domain of $A$ is a $\mathcal K_\Sigma$-limit of $f_n+ig_n$ with $f_n,g_n$ real test functions on $\Sigma$ forming a Cauchy sequence for the form $\langle\cdot,\omega^2\cdot\rangle$.
--
--   The Friedrichs extension is the unique self-adjoint extension whose domain lies in the form domain. Then $\omega=(\omega^2)^{1/2}$ by the spectral theorem.
--
--   **Formalization Note** The paper chooses "the Friedrichs extension" "for definiteness" (p. 23); this is Reading 8. $\omega$ enters the statements only through the spectral calculus of $\omega^2$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, p. 23 (paragraph before Theorem 4.3) and Theorem 4.3, p. 23

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_omegaSqForm
import Definitions.Def_JRCurvedQFT_SharpTime_toKSigma
import Definitions.Def_JRCurvedQFT_SharpTime_IsSliceTestFunction

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- `A` is **`ω²`**: the Friedrichs extension, in `𝒦_Σ`, of `F^{1/2}(−Q + m²)F^{1/2}` on
`C_c^∞(Σ)`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, p. 23: "In order to apply spectral theory to Q, we choose a self-adjoint extension of the
symmetric operator constructed by theorem 4.2. For definiteness, we may choose the Friedrichs
extension"; Theorem 4.3: `ω = (√F µ² √F)^{1/2}`.

Characterization (the Friedrichs extension is the unique self-adjoint extension whose domain lies
in the form domain):
1. `A` is self-adjoint on `𝒦_Σ`;
2. `A` extends `ω²` on real test functions on `Σ` (hence on complex ones, by linearity);
3. every `v ∈ dom A` is a `𝒦_Σ`-limit of `f_n + i g_n`, `f_n, g_n` real test functions on `Σ`, that is
   Cauchy for the form `⟨·, ω² ·⟩`.

**Formalization Note** Reading 8: the paper's "any ambiguity ... will not enter" is not used; `ω²`
is the Friedrichs extension. `ω = (ω²)^{1/2}` enters only through the spectral calculus of `ω²`. -/
def IsOmegaSq [MeasurableSpace M] (S : StaticStructure (d := d) M) (μ : Measure M) (m : ℝ)
    (A : Lp ℂ 2 (sliceMeasure S μ) →ₗ.[ℂ] Lp ℂ 2 (sliceMeasure S μ)) : Prop :=
  IsSelfAdjoint A ∧
  (∀ f, IsSliceTestFunction S f →
    ∃ hf : toKSigma (sliceMeasure S μ) (fun x => (f x : ℂ)) ∈ A.domain,
      A ⟨_, hf⟩ = toKSigma (sliceMeasure S μ) (fun x => (omegaSqCore S m f x : ℂ))) ∧
  ∀ v ∈ A.domain, ∃ f g : ℕ → M → ℝ,
    (∀ n, IsSliceTestFunction S (f n) ∧ IsSliceTestFunction S (g n)) ∧
    Filter.Tendsto (fun n => toKSigma (sliceMeasure S μ) (fun x => (f n x : ℂ))
        + Complex.I • toKSigma (sliceMeasure S μ) (fun x => (g n x : ℂ))) Filter.atTop (𝓝 v) ∧
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N,
      omegaSqForm S μ m (f n - f k) + omegaSqForm S μ m (g n - g k) < ε

end JRCurvedQFT.SharpTime


