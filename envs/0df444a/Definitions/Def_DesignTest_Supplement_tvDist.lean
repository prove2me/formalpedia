-- Prove2me | Definitions.Def_DesignTest_Supplement_tvDist
-- name    : DesignTest_Supplement_tvDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:02:16.615281+00:00
-- url     : https://prove2.me/theorems/e50a3fcc-5162-479d-997d-0451d90d9634
-- title:
--   Total variation distance, finite support, and uniform laws on finite sets
-- statement:
--   For probability measures $\mu,\nu$ on a measurable space, the **total variation distance** is
--
--   $$\mathrm{Dist}_{\mathrm{TV}}(\mu,\nu)=\sup_{A\ \text{measurable}}|\mu(A)-\nu(A)|.$$
--
--   A measure **has finite support** if it is carried by a finite set. For a finite set $R$, $\mathrm{Unif}(R)=|R|^{-1}\sum_{x\in R}\delta_x$ is the **uniform distribution** on $R$.
--
--   These are the TV distance of Theorems 4.1 and 5.1, the finite-support clause of the lower bounds of §5, and the laws $\mu_W,\mu_C,\mu_{\mathrm{MUB}},q_S$ of §5.3.
--
--   **Formalization Note.** The supremum is a real `⨆` over measurable sets; for probability measures all values lie in $[0,1]$ and the index set contains $\emptyset$, so it is not a junk value.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), §3.1, p.13; Theorems 4.1, 5.1, pp.22, 44; §5.3, pp.59–62

import Mathlib

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory

/-- **Total variation distance** `Dist_TV(μ, ν) := sup_A |μ(A) − ν(A)|`, the supremum over measurable
sets `A` (A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission
(sha256 e2f0a429…), §3.1, p.13 and Theorems 4.1, 5.1, pp.22, 44).

**Formalization Note.** Only applied to probability measures, for which every value lies in `[0, 1]`;
the index set is nonempty (`∅`) and the real supremum is therefore not a junk value. -/
noncomputable def tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ⨆ A : {A : Set α // MeasurableSet A}, |(μ A.1).toReal - (ν A.1).toReal|

/-- A measure **has finite support**: it is carried by a finite set (STOC 2027 submission
(sha256 e2f0a429…), Theorems 5.7, 5.9, 5.13, 5.14, 5.19: "the hard YES and NO distributions have finite
support"). -/
def IsFinSupp {α : Type*} [MeasurableSpace α] (ν : Measure α) : Prop :=
  ∃ S : Finset α, ν ((S : Set α)ᶜ) = 0

/-- The **uniform distribution on a finite set** `R`, `|R|⁻¹ Σ_{x ∈ R} δ_x` (STOC 2027 submission
(sha256 e2f0a429…), §5.3, pp.59–62: `μ_W = Unif(W_d)`, `μ_C = Unif(C_d)`, `μ_MUB = Unif(M_d)`, and the
subset laws `q_S`). For the empty set it is the zero measure. -/
noncomputable def unifFinset {α : Type*} [MeasurableSpace α] (R : Finset α) : Measure α :=
  ((R.card : ENNReal))⁻¹ • ∑ x ∈ R, Measure.dirac x

end DesignTest.Supplement


