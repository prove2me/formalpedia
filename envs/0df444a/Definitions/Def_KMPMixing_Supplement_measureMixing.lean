-- Prove2me | Definitions.Def_KMPMixing_Supplement_measureMixing
-- name    : KMPMixing_Supplement_measureMixing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:53:43.683387+00:00
-- url     : https://prove2.me/theorems/d1f7ba94-6626-40eb-8f91-8ac8fab7d662
-- title:
--   Total variation between measures, $k$-step laws of a kernel, $\mathrm{Unif}[0,1]$
-- statement:
--   For probability measures $P,Q$ on a measurable space, the **total variation distance** is
--   $$
--   \|P-Q\|_{\mathrm{TV}}=\sup_{A\ \text{measurable}}|P(A)-Q(A)|.
--   $$
--   For a Markov kernel $K$ on a measurable space and a point $x$, $K^k(x,\cdot)$ is the law after $k$ steps of the chain started at $x$: the point mass at $x$ pushed $k$ times through $\mu\mapsto\int K(y,\cdot)\,d\mu(y)$. $\mathrm{Unif}[0,1]$ is Lebesgue measure restricted to $[0,1]$.
--
--   These define the total-variation mixing time of the continuous-state chains of Theorem 5.5 and Corollary 5.6: $T_{\mathrm{mix}}(\varepsilon)=\min\{k:\sup_x\|K^k(x,\cdot)-\mu\|_{\mathrm{TV}}\le\varepsilon\}$.
--
--   **Formalization Note** The total variation is a real supremum; it is used only for probability measures, where the family $\{|P(A)-Q(A)|\}$ is nonempty and bounded by $1$.
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), §2 (total variation, mixing time), p.12 (PDF p.14); Theorem 5.5, p.35 (PDF p.37); Corollary 5.6, p.38 (PDF p.40)

import Mathlib

namespace KMPMixing.Supplement

open MeasureTheory ProbabilityTheory

/-- The **total variation distance** between two measures on a measurable space,
`‖P − Q‖_TV = sup_{A measurable} |P(A) − Q(A)|` (arXiv:2609.38044, §2, p.12 (PDF p.14)).

**Formalization Note** Used only for probability measures, where every `|P(A) − Q(A)| ≤ 1`, so
the real supremum is over a nonempty bounded family (`A = ∅` is measurable). -/
noncomputable def tvMeasure {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ⨆ A : {A : Set α // MeasurableSet A}, |(μ A.1).toReal - (ν A.1).toReal|

/-- The law `K^k(x, ·)` after `k` steps of the Markov chain with transition kernel `K` started at
the point `x` (arXiv:2609.38044, §2, p.12 (PDF p.14); used for the mixing times of Theorem 5.5,
p.35, and Corollary 5.6, p.38).

**Formalization Note** `K^k(x, ·)` is obtained from the point mass at `x` by `k` applications
of `μ ↦ ∫ K(y, ·) dμ(y)` (`Measure.bind`). -/
noncomputable def kernelLaw {α : Type*} [MeasurableSpace α] (K : Kernel α α) (k : ℕ) (x : α) :
    Measure α :=
  (fun μ => μ.bind K)^[k] (Measure.dirac x)

/-- `Unif[0, 1]`, Lebesgue measure restricted to `[0, 1]` (a probability measure). -/
noncomputable def unif01 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unif01 := ⟨by simp [unif01]⟩

end KMPMixing.Supplement


