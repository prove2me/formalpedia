-- Prove2me | Definitions.Def_M4aHerbrand_AdeleTopologyFacts
-- name    : M4aHerbrand_AdeleTopologyFacts
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/55224958-7682-56a8-b778-c939e117222d
-- title:
--   σ-compactness of adele rings; continuity of adelic conjugation
-- statement:
--   Standing context: a Dedekind domain $R$ with fraction field a field $K$, and in the later sections number fields whose rings of integers are models finite and free over $\mathbb{Z}$.
--
--   The first group of declarations records σ-compactness of adelic rings. For an infinite place $v$ of a field $K$, the completion $v.\mathrm{Completion}$ is σ-compact, obtained from the isometric (hence closed) extension embedding of $v.\mathrm{Completion}$ into $\mathbb{C}$; for a number field $K$ the infinite adele ring $\prod_{v\mid\infty} K_v$ is then σ-compact as a finite product. `countable_of_free_finite_int` states that a ring $R$ that is free and finite as a $\mathbb{Z}$-module is countable. `iUnion_smul_integralFiniteAdeles` states that the union, over all $s\in R$, of the images of the set [`NumberField.AdelicBox.integralFiniteAdeles R K`](../def/NumberField_AdelicBox.html#L15) $=\{x\in\mathbb{A}_{K,\mathrm{fin}} : x_v\in\mathcal{O}_v \text{ for all } v\}$ under multiplication by $(\iota(s))^{-1}$, where $\iota\colon K\to\mathbb{A}_{K,\mathrm{fin}}$ is the structure map, is all of the finite adele ring; it follows from the fact that every finite adele can be scaled into the integral ones by a nonzero element of $R$. Under the further assumption that $R$ is free and finite over $\mathbb{Z}$, the integral finite adeles are compact (they are the range of the structure map of the restricted product, whose factors $\mathcal{O}_v$ are compact), so the finite adele ring is σ-compact, being a countable union of compact translates; consequently $\mathbb{A}_K = \mathbb{A}_{K,\infty}\times\mathbb{A}_{K,\mathrm{fin}}$ is σ-compact, and its local compactness is restated.
--
--   The last two sections apply these facts. Given Dedekind models $A\subseteq$ a number field $K$ and $B\subseteq$ a number field $L$, both free and finite over $\mathbb{Z}$, an algebra structure on $\mathbb{A}_L$ over $\mathbb{A}_K$ whose structure map is continuous, and an $\mathbb{A}_K$-algebra isomorphism $te\colon \mathbb{A}_K\otimes_K L\to\mathbb{A}_L$: the topology on $\mathbb{A}_L$ is the $\mathbb{A}_K$-module topology, and for every $\sigma\in\mathrm{Gal}(L/K)$ the ring automorphism `conjAct A K B L te σ` of $\mathbb{A}_L$ — namely $te^{-1}$ followed by $\mathrm{id}\otimes\sigma$ followed by $te$ — is continuous. Finiteness of $L/K$ is deduced from finiteness of both fields over $\mathbb{Q}$. The final statement is the same continuity assertion in the case of the rings of integers $\mathcal{O}_E\subseteq E$, $\mathcal{O}_F\subseteq F$.
--
--   **Relation to Mathlib.** Mathlib supplies the adele rings as a product of an infinite part with a restricted product, together with their local compactness; the σ-compactness instances here and the conjugation automorphism `conjAct` are the project's own.
--
--   **Where it is used.** These topological facts supply the hypotheses of the open-mapping bridge: they are what makes the $\mathbb{A}_K$-module topology on $\mathbb{A}_L$ agree with the adelic topology, and hence make the Galois conjugation action on adeles continuous, in the adelic setting used on the automorphic side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aHerbrand_AdeleTopologyFacts.lean

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_M4aHerbrand_OpenMappingBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain TensorProduct

section Infinite

variable (K : Type*) [Field K]

instance sigmaCompactSpace_completion (v : InfinitePlace K) : SigmaCompactSpace v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isClosedEmbedding.sigmaCompactSpace

instance sigmaCompactSpace_infiniteAdeleRing [NumberField K] : SigmaCompactSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (SigmaCompactSpace ((v : InfinitePlace K) → v.Completion))

end Infinite

section Finite

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] in

theorem countable_of_free_finite_int [Module.Free ℤ R] [Module.Finite ℤ R] : Countable R :=
  Countable.of_equiv _ (Module.Free.chooseBasis ℤ R).equivFun.toEquiv.symm

theorem iUnion_smul_integralFiniteAdeles :
    ⋃ s : R, (fun z => algebraMap K (FiniteAdeleRing R K) (algebraMap R K s)⁻¹ * z) ''
      NumberField.AdelicBox.integralFiniteAdeles R K = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨s, hs0, hs⟩ := NumberField.AdelicBox.exists_mul_mem_integralFiniteAdeles R K y
  refine Set.mem_iUnion.mpr ⟨s, _, hs, ?_⟩
  have hsK : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs0
  show algebraMap K (FiniteAdeleRing R K) (algebraMap R K s)⁻¹ *
      (algebraMap R (FiniteAdeleRing R K) s * y) = y
  rw [← mul_assoc, IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K) s, ← map_mul,
    inv_mul_cancel₀ hsK, map_one, one_mul]

variable [Module.Free ℤ R] [Module.Finite ℤ R]

theorem isCompact_integralFiniteAdeles :
    IsCompact (NumberField.AdelicBox.integralFiniteAdeles R K) := by
  haveI : ∀ v : HeightOneSpectrum R,
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum R => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

instance sigmaCompactSpace_finiteAdeleRing : SigmaCompactSpace (FiniteAdeleRing R K) := by
  haveI : Countable R := countable_of_free_finite_int R
  refine ⟨?_⟩
  rw [← iUnion_smul_integralFiniteAdeles R K]
  exact isSigmaCompact_iUnion_of_isCompact _ fun s =>
    (isCompact_integralFiniteAdeles R K).image (continuous_const.mul continuous_id)

instance sigmaCompactSpace_adeleRing [NumberField K] : SigmaCompactSpace (AdeleRing R K) :=
  inferInstanceAs (SigmaCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing R K))

theorem locallyCompactSpace_adeleRing [NumberField K] : LocallyCompactSpace (AdeleRing R K) :=
  inferInstance

end Finite

section Conjugation

variable (A K B L : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [NumberField K] [Algebra A K]
  [IsFractionRing A K] [Module.Free ℤ A] [Module.Finite ℤ A]
  [CommRing B] [IsDedekindDomain B] [Field L] [NumberField L] [Algebra B L] [IsFractionRing B L]
  [Module.Free ℤ B] [Module.Finite ℤ B] [Algebra K L]

theorem continuous_conjAct_of_continuous_of_free
    [Algebra (AdeleRing A K) (AdeleRing B L)]
    (hβ : Continuous (algebraMap (AdeleRing A K) (AdeleRing B L)))
    (te : ((AdeleRing A K) ⊗[K] L) ≃ₐ[AdeleRing A K] AdeleRing B L) (σ : L ≃ₐ[K] L) :
    Continuous (conjAct A K B L te σ) :=
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  continuous_conjAct_of_continuous A K B L hβ te σ

theorem isModuleTopology_adeleRing_of_free
    [Algebra (AdeleRing A K) (AdeleRing B L)]
    (hβ : Continuous (algebraMap (AdeleRing A K) (AdeleRing B L)))
    (te : ((AdeleRing A K) ⊗[K] L) ≃ₐ[AdeleRing A K] AdeleRing B L) :
    IsModuleTopology (AdeleRing A K) (AdeleRing B L) :=
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  isModuleTopology_adeleRing_of_continuous A K B L hβ te

end Conjugation

section ConjugationRingOfIntegers

variable (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]

theorem continuous_conjAct_of_continuous_numberField
    [Algebra (AdeleRing (𝓞 E) E) (AdeleRing (𝓞 F) F)]
    (hβ : Continuous (algebraMap (AdeleRing (𝓞 E) E) (AdeleRing (𝓞 F) F)))
    (te : ((AdeleRing (𝓞 E) E) ⊗[E] F) ≃ₐ[AdeleRing (𝓞 E) E] AdeleRing (𝓞 F) F) (σ : F ≃ₐ[E] F) :
    Continuous (conjAct (𝓞 E) E (𝓞 F) F te σ) :=
  continuous_conjAct_of_continuous_of_free (𝓞 E) E (𝓞 F) F hβ te σ

end ConjugationRingOfIntegers

end M4aHerbrand.Bridge


