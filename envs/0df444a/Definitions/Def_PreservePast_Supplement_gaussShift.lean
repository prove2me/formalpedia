-- Prove2me | Definitions.Def_PreservePast_Supplement_gaussShift
-- name    : PreservePast_Supplement_gaussShift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:29:52.147818+00:00
-- url     : https://prove2.me/theorems/46f5f96f-092d-4b0a-b0e9-472cb5ba1dd6
-- title:
--   The Gaussian nearest-of-$k$ experiment: query law, success, full-data optimum, total and sample-specific information
-- statement:
--   On $\mathbb R^d$ let $N(a x, vI_d)$ be the Gaussian law with independent coordinates of means $a x_i$ and variance $v$ (`gaussShift d a v x`), and $N(0,I_d)$ the standard Gaussian law.
--
--   In the **Gaussian nearest-of-$k$ experiment** the records $X_1,\dots,X_k$ are independent $N(0,I_d)$, the index $J$ is uniform, and the query is $Z=\rho X_J+\sqrt{1-\rho^2}\,G$ with an independent standard Gaussian $G$, i.e. $Z\mid X_J\sim N(\rho X_J,(1-\rho^2)I_d)$. For a retained-state protocol this defines the success $\Pr\{\hat J=J\}$, the full-data optimum $S^\ast$, and the **total information** $I_{\rm tot}=I(X;M\mid R)$ in bits.
--
--   The same record–query law arises from hidden centres: $X_j=\sqrt\rho\,\Theta_j+\sqrt{1-\rho}\,E_j$ with independent standard Gaussian $\Theta_j,E_j$. The **sample-specific information** is $I_{\rm exc}=I(X;M\mid\Theta,R)$ in bits.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ`. $I_{\rm exc}$ is computed on the space of $(\Theta,E)$ and the coins, with $X=\sqrt\rho\,\Theta+\sqrt{1-\rho}\,E$.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Appendix J, pp.52–53 (PDF pp.54–55)

import Mathlib
import Definitions.Def_PreservePast_Supplement_StateProtocol

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace PreservePast.Supplement

/-- The standard Gaussian law `N(0, I_d)` on `ℝ^d = Fin d → ℝ`. -/
noncomputable def stdGauss (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance (d : ℕ) : IsProbabilityMeasure (stdGauss d) := by
  unfold stdGauss; infer_instance

/-- **The Gaussian law `N(a·x, v·I_d)`** on `ℝ^d`: independent coordinates with means `a x_i` and
variance `v`. P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held
version, PDF sha256 48013ceb…d00fa), Appendix J, pp.52–53 (PDF pp.54–55): the query law
"Z = ρX_J + √(1−ρ²) G" is `P_x = N(ρx, σ²I_d)`, `σ² = 1 − ρ²`, i.e. `gaussShift d ρ (1 − ρ²) x`;
the query from a hidden centre, "Z = √ρ Θ_J + √(1−ρ) E₀", is `gaussShift d (√ρ) (1 − ρ) θ`.

**Formalization Note.** The variance enters through `Real.toNNReal` (used for `v ≥ 0`). -/
noncomputable def gaussShift (d : ℕ) (a v : ℝ) (x : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun i => gaussianReal (a * x i) (Real.toNNReal v)

/-- The **success** `Pr{Ĵ = J}` of a protocol in the Gaussian nearest-of-k experiment of
Appendix J, p.52 (PDF p.54): "Use the same encoder and index, but let X_j ∼ N(0, I_d)
independently and Z = ρX_J + √(1−ρ²) G, with independent standard Gaussian G." -/
noncomputable def gaussIdSuccess {k d : ℕ}
    (π : StateProtocol (Fin k → Fin d → ℝ) (Fin d → ℝ) (Fin k)) (ρ : ℝ) : ℝ :=
  π.success (Measure.pi fun _ : Fin k => stdGauss d) id (idTest (gaussShift d ρ (1 - ρ ^ 2)))

/-- The **full-data optimum** `S*` of the Gaussian nearest-of-k experiment. -/
noncomputable def gaussIdOptimum (k d : ℕ) (ρ : ℝ) : ℝ :=
  fullDataOptimum (Out := Fin k) (Measure.pi fun _ : Fin k => stdGauss d) id
    (idTest (gaussShift d ρ (1 - ρ ^ 2)))

/-- The **total information** `I_tot = I(X; M | R)` in bits (Appendix J, p.52). -/
noncomputable def gaussIdTot {k d : ℕ}
    (π : StateProtocol (Fin k → Fin d → ℝ) (Fin d → ℝ) (Fin k)) : ENNReal :=
  π.info (Measure.pi fun _ : Fin k => stdGauss d) id id (fun _ => ())

/-- The **sample-specific information** `I_exc = I(X; M | Θ, R)` in bits (Appendix J, p.52):
"The same record–query law arises from two noisy observations of a hidden center:
X_j = √ρ Θ_j + √(1−ρ) E_j and Z = √ρ Θ_J + √(1−ρ) E₀. Here Θ₁, …, Θ_k, E₀, E₁, …, E_k are
independent standard Gaussian vectors; neither encoder nor decoder observes the centers."

**Formalization Note.** The latent variable is the pair `(Θ, E)` of two independent `k`-tuples of
standard Gaussian vectors; the database is `X = √ρ Θ + √(1−ρ) E`, and the conditioning is on
`(Θ, R)`. -/
noncomputable def gaussIdExc {k d : ℕ}
    (π : StateProtocol (Fin k → Fin d → ℝ) (Fin d → ℝ) (Fin k)) (ρ : ℝ) : ENNReal :=
  π.info ((Measure.pi fun _ : Fin k => stdGauss d).prod (Measure.pi fun _ : Fin k => stdGauss d))
    (fun l j i => Real.sqrt ρ * l.1 j i + Real.sqrt (1 - ρ) * l.2 j i)
    (fun l j i => Real.sqrt ρ * l.1 j i + Real.sqrt (1 - ρ) * l.2 j i) (fun l => l.1)

end PreservePast.Supplement


