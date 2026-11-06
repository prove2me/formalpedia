-- Prove2me | Definitions.Def_BlockBochner_diagAvg
-- name    : BlockBochner_diagAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:26.100861+00:00
-- url     : https://prove2.me/theorems/d1d4cd99-d3ec-4acf-bebf-5f35f732582d
-- title:
--   Projection $\Pi_{\Delta_\nu}$ onto the diagonal
-- statement:
--   $\Delta_\nu=\{(f,\dots,f):f\in L^2_0(\nu)\}$ and
--   $$\Pi_{\Delta_\nu}(g_i)_{i\in R}=\Bigl(\frac1k\sum_ig_i,\dots,\frac1k\sum_ig_i\Bigr),$$
--   the orthogonal projection onto $\Delta_\nu$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 2.2, p.17

import Mathlib
import Definitions.Def_BlockBochner_L20

open MeasureTheory

namespace BlockBochner

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **`Π_{∆_ν}`, the orthogonal projection onto the diagonal `∆_ν = {(f, …, f) : f ∈ L²₀(ν)}`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228,
Sec. 2.2, p.17: `Π_{∆_ν}(g_i)_{i∈R} = ((1/k) Σ_i g_i, …, (1/k) Σ_i g_i)`.

**Formalization Note** Defined by the displayed formula on `PiLp 2 (fun _ : R => L²₀(ν))`. -/
noncomputable def diagAvg (ν : Measure (∀ i, X i)) :
    PiLp 2 (fun _ : ι => L20 ν) →L[ℝ] PiLp 2 (fun _ : ι => L20 ν) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => L20 ν)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun _ => (Fintype.card ι : ℝ)⁻¹ •
      ∑ j, PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => L20 ν) j)

end BlockBochner


