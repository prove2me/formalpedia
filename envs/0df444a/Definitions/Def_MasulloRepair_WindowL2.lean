-- Prove2me | Definitions.Def_MasulloRepair_WindowL2
-- name    : MasulloRepair_WindowL2
-- status  : Definition
-- author  : @ibecca
-- created : 2026-11-21T02:10:26.255503+00:00
-- url     : https://prove2.me/theorems/33fcec7f-8959-4085-bb35-43330bc736f1
-- title:
--   Compatible weighted L2 spaces for compact half-line windows
-- statement:
--   For a measure $\mu$ on $\mathbf R$, define
--   $$w_n(t)=\max\{1,t^{2n}\},\qquad d\nu_n(t)=w_n(t)\,d\mu(t),\quad n\in\mathbf N.$$
--   Because $w_n\ge1$, the identity on functions induces a continuous complex-linear inclusion
--   $$J_n:L^2(\nu_n;\mathbf C)\longrightarrow L^2(\mu;\mathbf C).$$
--   Define the complex vector space of compatible tuples
--   $$X_\mu=\left\{(u_n)\in\prod_{n\ge0}L^2(\nu_n;\mathbf C):
--              J_nu_n=J_0u_0\text{ for every }n\right\},$$
--   with the subspace topology and uniformity from the product. Thus convergence is convergence in each weighted $L^2$ coordinate.
--
--   For the half-line application, also define the endpoint measure, for real $a,s$, by
--   $$d\mu_{a,s}(t)=1_{(0,\infty)}(t)t^{2a}(1+\log^2 t)^{s/2}\,\frac{dt}{t}.$$
--   The intended compact-window replacement is $X_{\mu_{a,s}}$. Completeness and representation by a common function are separate theorems; they are not hypotheses or axioms in this definition.
--
--   **Formalization Note.** The file contains the complex-linear inclusion for ordered measures, its almost-everywhere coefficient identity, the explicit weights and measures, and the compatibility submodule. The inherited topology is the product subspace topology, rather than the topology of a uniform supremum over all windows.
-- source:
--   Repair of A. M. Masullo, The Music of the Primes, Definition 9.2.2.1 and Lemma 9.2.2.2(3)(a), equations (9.2.2.3), (9.2.2.6)-(9.2.2.7), printed pp. 412-413, with relevance to the proposed space in Proposition 9.2.2.4, p. 414. Frozen draft: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . Yi identified the uniform-supremum finiteness defect and proposed compact-window seminorms in Prove2Me mission comment a96ab6a0-9f70-4b3f-ab3e-8c7e38a823f2 (mission 638f9b7f-e232-4624-ba08-5889465bb1e7). This contribution develops that replacement, following the accepted cofinal convergence criterion 2cf713aa-17bf-4fe0-9b9f-b73f1670aac5. It does not assert the original uniform-norm definition is valid on all of its stated tests. The compatible-product construction is supplied here as a replacement definition. Its structural maps use Mathlib L2 spaces and monotonicity under ordered measures.

import Mathlib

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MasulloRepair

/-- Canonical inclusion of complex L2 spaces for ordered measures. -/
noncomputable def l2Include {μ ν : Measure ℝ} (h : μ ≤ ν) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).mono_measure h).toLp f
      map_add' := by
        intro f g
        ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
        apply (Measure.absolutelyContinuous_of_le h).ae_eq
        grw [Lp.coeFn_add]
      map_smul' := by
        intro c f
        ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
        apply (Measure.absolutelyContinuous_of_le h).ae_eq
        grw [Lp.coeFn_smul]
        rfl }
    1 (by
      intro f
      change ‖((Lp.memLp f).mono_measure h).toLp f‖ ≤ 1 * ‖f‖
      rw [Lp.norm_toLp, one_mul, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure f h))

lemma l2Include_coe {μ ν : Measure ℝ} (h : μ ≤ ν) (f : Lp ℂ 2 ν) :
    (l2Include h f : ℝ → ℂ) =ᵐ[μ] f :=
  ((Lp.memLp f).mono_measure h).coeFn_toLp

/-- Relative weight of the anchored window [a,a+n] over its endpoint weight. -/
def windowWeight (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (max 1 (t^(2*n)))

noncomputable def windowMeasure (μ : Measure ℝ) (n : ℕ) : Measure ℝ :=
  μ.withDensity (windowWeight n)

lemma le_windowMeasure (μ : Measure ℝ) (n : ℕ) : μ ≤ windowMeasure μ n := by
  calc
    μ = μ.withDensity 1 := withDensity_one.symm
    _ ≤ windowMeasure μ n := by
      apply withDensity_mono
      exact Eventually.of_forall fun t => by
        simpa only [Pi.one_apply, windowWeight, ← ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (le_max_left (1 : ℝ) (t^(2*n)))

noncomputable def windowToBase (μ : Measure ℝ) (n : ℕ) :
    Lp ℂ 2 (windowMeasure μ n) →L[ℂ] Lp ℂ 2 μ :=
  l2Include (le_windowMeasure μ n)

/-- Compatible tuples in the product of all anchored-window L2 spaces. -/
noncomputable def windowSpace (μ : Measure ℝ) :
    Submodule ℂ (∀ n : ℕ, Lp ℂ 2 (windowMeasure μ n)) where
  carrier := {u | ∀ n, windowToBase μ n (u n) = windowToBase μ 0 (u 0)}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro u v hu hv n
    change windowToBase μ n (u n + v n) = windowToBase μ 0 (u 0 + v 0)
    rw [map_add, map_add, hu n, hv n]
  smul_mem' := by
    intro c u hu n
    change windowToBase μ n (c • u n) = windowToBase μ 0 (c • u 0)
    rw [map_smul, map_smul, hu n]

/-- The endpoint measure carrying both the Mellin and logarithmic Sobolev weights. -/
noncomputable def halflineBaseMeasure (a s : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun t => ENNReal.ofReal (t^(2*a) * (1+(Real.log t)^2)^(s/2) / t))

end MasulloRepair


