-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:29.188559+00:00
-- url     : https://prove2.me/theorems/8dbc77dc-7474-4df9-8ebe-cec8c5da3075
-- title:
--   PPlace Centred Sum
-- statement:
--   Definitions and structural lemmas for PPlace Centred Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField IsDedekindDomain Ideal
namespace PlaceCentredSum
variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]
noncomputable def below (v : FinitePlace K) : HeightOneSpectrum (𝓞 L) where
  asIdeal := v.maximalIdeal.asIdeal.under (𝓞 L)
  isPrime := inferInstance
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
    exact comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
instance (v : FinitePlace K) : v.maximalIdeal.asIdeal.LiesOver (below (L := L) v).asIdeal := ⟨rfl⟩
noncomputable def deg (L : Type) [Field L] [NumberField L] [Algebra L K] (v : FinitePlace K) : ℕ :=
  v.maximalIdeal.asIdeal.ramificationIdx (𝓞 L) * v.maximalIdeal.asIdeal.inertiaDeg (𝓞 L)
noncomputable def fibreEquiv (Q : HeightOneSpectrum (𝓞 L)) :
    {v : FinitePlace K // below v = Q} ≃ Q.asIdeal.primesOver (𝓞 K) where
  toFun v := ⟨v.1.maximalIdeal.asIdeal, inferInstance, ⟨(congrArg HeightOneSpectrum.asIdeal v.2).symm⟩⟩
  invFun P := ⟨FinitePlace.mk ⟨P.1, P.2.1, ne_bot_of_liesOver_of_ne_bot Q.ne_bot P.1⟩, by
    ext1
    simp only [below, FinitePlace.maximalIdeal_mk]
    exact P.2.2.over.symm⟩
  left_inv v := Subtype.ext (FinitePlace.mk_maximalIdeal v.1)
  right_inv P := Subtype.ext (by simp only [FinitePlace.maximalIdeal_mk])
noncomputable instance (Q : HeightOneSpectrum (𝓞 L)) : Fintype {v : FinitePlace K // below v = Q} :=
  Fintype.ofEquiv _ (fibreEquiv Q).symm
end PlaceCentredSum
end GroundTheory.Heights₂.Heights


