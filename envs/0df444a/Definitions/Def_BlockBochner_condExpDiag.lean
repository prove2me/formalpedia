-- Prove2me | Definitions.Def_BlockBochner_condExpDiag
-- name    : BlockBochner_condExpDiag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:25.070041+00:00
-- url     : https://prove2.me/theorems/14e1134e-1bba-455c-a495-17e9f5f17245
-- title:
--   $P_\nu=\mathrm{diag}(P^\nu_i)$ on $\bigoplus_iL^2_0(\nu)$
-- statement:
--   On $\bigoplus_{i\in R}L^2_0(\nu)$, $P_\nu=\mathrm{diag}(P^\nu_i)_{i\in R}$; $L_\nu=\mathrm{diag}(L^\nu_i)=I-P_\nu$.
--
--   **Formalization Note** Each $P^\nu_i$ preserves $L^2_0(\nu)$; its restriction is written as the compression to $L^2_0(\nu)$, which equals it.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 2.2, p.17

import Mathlib
import Definitions.Def_BlockBochner_condExpOn
import Definitions.Def_BlockBochner_blk
import Definitions.Def_BlockBochner_L20

open MeasureTheory

namespace BlockBochner

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **`P_ν = diag(P^ν_i)_{i∈R}` on `⊕_{i∈R} L²₀(ν)`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 2.2, p.17.

**Formalization Note** Each `P^ν_i` maps `L²₀(ν)` into itself; its restriction is written as the
compression `blk (condExpOn ν {i}ᶜ) (L20 ν) (L20 ν)`, which equals the restriction. The direct sum is
the `ℓ²` sum `PiLp 2`. -/
noncomputable def condExpDiag (ν : Measure (∀ i, X i)) :
    PiLp 2 (fun _ : ι => L20 ν) →L[ℝ] PiLp 2 (fun _ : ι => L20 ν) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => L20 ν)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => blk (condExpOn ν {i}ᶜ) (L20 ν) (L20 ν) ∘L
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => L20 ν) i)

end BlockBochner


