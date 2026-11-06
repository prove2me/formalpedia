-- Prove2me | Definitions.Def_BlockBochner_Uspace
-- name    : BlockBochner_Uspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:44.310961+00:00
-- url     : https://prove2.me/theorems/b0f502e6-90f3-4022-a96d-a3785e6b9a3a
-- title:
--   $U^\nu_i=\operatorname{ran}P^\nu_i\cap L^2_0(\nu)$
-- statement:
--   $U^\nu_i$ is the subspace of mean-zero functions in $L^2(\nu)$ that are functions of the spins of all sites other than $i$:
--   $$U^\nu_i=\operatorname{ran}P^\nu_i\cap L^2_0(\nu).$$
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 2.2, p.16

import Mathlib
import Definitions.Def_BlockBochner_condExpOn
import Definitions.Def_BlockBochner_L20

open MeasureTheory

namespace BlockBochner

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **`U^ν_i = ran P^ν_i ∩ L²₀(ν)`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 2.2, p.16: "the subspace of mean-zero functions in
`L²(ν)` which can be written as a function of the spins of all sites in `R ∖ {i}`".

**Formalization Note** `P^ν_i = condExpOn ν {i}ᶜ`. -/
noncomputable def Uspace (ν : Measure (∀ i, X i)) (i : ι) : Submodule ℝ (Lp ℝ 2 ν) :=
  LinearMap.range (condExpOn ν {i}ᶜ).toLinearMap ⊓ L20 ν

end BlockBochner


