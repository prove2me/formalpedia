-- Prove2me | Definitions.Def_GenEmpLik_Coverage_Supplement_empiricalProcess
-- name    : GenEmpLik_Coverage_Supplement_empiricalProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:11:02.805826+00:00
-- url     : https://prove2.me/theorems/9fe207fb-0045-4680-aa82-7377ba58c287
-- title:
--   Uniform-norm empirical process and outer weak convergence
-- statement:
--   Let $h_i:\Xi\to\mathbb R$, indexed by an arbitrary set $I$, be a function class. Its bounded-function space is $\ell^\infty(I)$ with norm $\|v\|_I=\sup_i|v_i|$. A law $P$ acts by $P h_i=\int h_i\,dP$, and indexed weights act by $p h_i=\sum_jp_jh_i(z_j)$. The empirical process is
--   $$\mathbb G_n=\sqrt n\,(\widehat P_n-P_0)\in\ell^\infty(I).$$
--   Weak convergence in outer expectation to a Borel law $\Gamma$ means
--   $$E^*\varphi(\mathbb G_n)\longrightarrow\int\varphi\,d\Gamma$$
--   for every nonnegative bounded continuous test $\varphi$. Translation makes these tests equivalent to all bounded continuous real tests. The outer expectation is the published measurable-majorant definition from PlugInRisk, which uses the same van der Vaart–Wellner convention.
--
--   **Formalization Note** The space is Mathlib's $\ell^\infty$ with its Borel sigma algebra; no separability of the index set or measurability of the empirical-process map is assumed. A total conversion returns zero on unbounded coordinate functions; the envelope and integrability clauses used downstream guarantee this branch is never used.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, pp. 5, notation; 21–22, Section 7.1

import Mathlib
import Definitions.Def_PlugInRisk_outerExp
import Definitions.Def_VarianceRegularization_Expansion_empMean

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

open Classical

namespace GenEmpLik.Coverage.Supplement

/-- The full bounded-function space L∞(H) with the uniform norm, pp. 21–22.
The index type is arbitrary, with no finiteness, countability or separability assumption. -/
abbrev ProcessSpace (ι : Type*) := lp (fun _ : ι => ℝ) ∞

noncomputable instance processMeasurableSpace (ι : Type*) : MeasurableSpace (ProcessSpace ι) :=
  borel (ProcessSpace ι)

instance processBorelSpace (ι : Type*) : BorelSpace (ProcessSpace ι) := ⟨rfl⟩

/-- Turn a bounded function into its uniform-norm element. The fallback is never used
under the envelope and integrability hypotheses of Theorems 9–10. -/
noncomputable def toProcess {ι : Type*} (v : ι → ℝ) : ProcessSpace ι :=
  if hv : Memℓp v ∞ then ⟨v, hv⟩ else 0

/-- A measure acting on the entire class by integration, pp. 21–22. -/
noncomputable def measureProcess {ι Ξ : Type*} [MeasurableSpace Ξ]
    (h : ι → Ξ → ℝ) (P : Measure Ξ) : ProcessSpace ι :=
  toProcess (fun i => ∫ z, h i z ∂P)

/-- A finitely supported signed measure acting on H; p are indexed weights,
so repeated observations are retained rather than deduplicated. -/
noncomputable def weightedProcess {ι Ξ : Type*} {n : ℕ}
    (h : ι → Ξ → ℝ) (z : Fin n → Ξ) (p : Fin n → ℝ) : ProcessSpace ι :=
  toProcess (fun i => ∑ j, p j * h i (z j))

/-- The empirical process sqrt(n)(P-hat_n - P0), Definition 3, p. 22. -/
noncomputable def empiricalProcess {Ω Ξ ι : Type*}
    [MeasurableSpace Ξ] (P : Measure Ξ) (ξ : ℕ → Ω → Ξ)
    (h : ι → Ξ → ℝ) (n : ℕ) (ω : Ω) : ProcessSpace ι :=
  Real.sqrt (n : ℝ) •
    (weightedProcess h (fun j : Fin n => ξ j ω) (fun _ => (1 : ℝ) / n) -
      measureProcess h P)

/-- Weak convergence in outer expectation, p. 5 and pp. 21–22. Nonnegative
bounded continuous tests suffice by translation. No measurability of X_n is imposed. -/
def OuterWeakly {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [MeasurableSpace E] (μ : Measure Ω) (X : ℕ → Ω → E) (Γ : Measure E) : Prop :=
  ∀ φ : BoundedContinuousFunction E ℝ, (∀ v, 0 ≤ φ v) →
    Tendsto (fun n => PlugInRisk.outerExp μ (fun ω => ENNReal.ofReal (φ (X n ω))))
      atTop (𝓝 (∫⁻ v, ENNReal.ofReal (φ v) ∂Γ))

end GenEmpLik.Coverage.Supplement


