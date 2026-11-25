-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnitaryGroupLocal
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_UnitaryGroupLocal
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:03:38.012054+00:00
-- url     : https://prove2.me/theorems/c18c00bf-61cb-5d79-abcb-3697d51ae61e
-- title:
--   Unitary Group Local
-- statement:
--   Definitions and structural lemmas for Unitary Group Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnitaryGroupLocal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApprox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.UnitaryGroupLocal
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open NumberField IsDedekindDomain Topology Matrix
section Top
variable {F E : Type} [Field F] [Field E] [Algebra F E]
def cm (F E R : Type) [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] : E ⊗[F] R ≃ₐ[F] R ⊗[F] E :=
  Algebra.TensorProduct.comm F E R
scoped instance topER (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) :=
  TopologicalSpace.induced (cm F E R) inferInstance
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
theorem continuous_cm (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] : Continuous (cm F E R) := continuous_induced_dom
def cmH : E ⊗[F] R ≃ₜ R ⊗[F] E where
  toEquiv := (cm F E R).toEquiv
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    refine continuous_induced_rng.2 ?_
    exact continuous_id.congr fun x => ((cm F E R).apply_symm_apply x).symm
variable [IsTopologicalRing R] [FiniteDimensional F E] [LocallyCompactSpace R] [T2Space R]
instance isTopologicalRing_ER : IsTopologicalRing (E ⊗[F] R) where
  continuous_add := by
    refine continuous_induced_rng.2 ?_
    simp only [Function.comp_def, map_add]
    exact ((continuous_cm F E R).comp continuous_fst).add ((continuous_cm F E R).comp continuous_snd)
  continuous_mul := by
    refine continuous_induced_rng.2 ?_
    simp only [Function.comp_def, map_mul]
    exact ((continuous_cm F E R).comp continuous_fst).mul ((continuous_cm F E R).comp continuous_snd)
  continuous_neg := by
    refine continuous_induced_rng.2 ?_
    simp only [Function.comp_def, map_neg]
    exact (continuous_cm F E R).neg
variable (σ : E →ₐ[F] E)
variable {n : Type} [Fintype n] [DecidableEq n]
instance t2Space_tensor_completion : T2Space (E ⊗[F] R) := (cmH (E := E) R).isEmbedding.t2Space
instance t2Space_matrix_tensor_completion : T2Space (Matrix n n (E ⊗[F] R)) := inferInstanceAs (T2Space (n → n → E ⊗[F] R))
end Top
section Int
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))
instance locallyCompactSpace_adicCompletion : LocallyCompactSpace (v.adicCompletion F) :=
  (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem (v.adicCompletionIntegers F)))
abbrev oE : Subring (E ⊗[F] v.adicCompletion F) :=
  PI.UnitaryApproxDefs.tensInt (F := F) (v.adicCompletion F) (PI.UnitaryApproxDefs.intOE E)
    (v.adicCompletionIntegers F).toSubring
abbrev Ix (E : Type) [Field E] [NumberField E] : Type := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
def bE (i : Ix E) : E := algebraMap (𝓞 E) E (RingOfIntegers.basis E i)
def psi (a : Ix E → v.adicCompletion F) : E ⊗[F] v.adicCompletion F := ∑ i, bE i ⊗ₜ[F] a i
def psiL : (Ix E → v.adicCompletion F) →ₗ[v.adicCompletion F] v.adicCompletion F ⊗[F] E :=
  ∑ i, (LinearMap.proj i : (Ix E → v.adicCompletion F) →ₗ[v.adicCompletion F] v.adicCompletion F).smulRight
    ((1 : v.adicCompletion F) ⊗ₜ[F] bE i)
def PsiInt : Set (E ⊗[F] v.adicCompletion F) :=
  {x | ∃ a : Ix E → v.adicCompletion F, (∀ i, a i ∈ v.adicCompletionIntegers F) ∧ psi v a = x}
end Int
end Formalism.MainNotions.UnitaryGroupLocal


