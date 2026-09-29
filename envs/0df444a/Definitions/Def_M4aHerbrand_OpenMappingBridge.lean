-- Prove2me | Definitions.Def_M4aHerbrand_OpenMappingBridge
-- name    : M4aHerbrand_OpenMappingBridge
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/8d1910fc-50bf-53c7-843d-718a175b00df
-- title:
--   Module topology on adele rings via open mapping
-- statement:
--   Three statements about when a topological ring that is finite and free over a topological base ring carries the module topology, applied to adele rings. The general lemma `isModuleTopology_of_continuous_algebraMap_of_sigmaCompact` takes commutative topological rings $A$ and $B$ with $B$ an $A$-algebra, assumes $A$ is $\sigma$-compact, $B$ is Hausdorff and a Baire space, $B$ is free and finite as an $A$-module, and assumes the structure map $A \to B$ is continuous; it concludes `IsModuleTopology A B`, i.e. the given topology on $B$ is the $A$-module topology. The argument passes to the coordinate isomorphism $A^{n} \to B$ attached to a chosen basis: it is continuous because the structure map is, and being a continuous surjective additive map from a $\sigma$-compact group to a Baire group it is open, hence a homeomorphism, so the topology of $B$ is transported from the product topology. An instance `instT2SpaceAdeleRing` records that `AdeleRing S F` is Hausdorff, read off from its underlying model as the product of the completions at the infinite places of $F$ with the restricted product of the adic completions relative to the rings of adic integers. In the adelic setting, with $R$ a Dedekind domain with fraction field $E$, $S$ a Dedekind domain with fraction field $F$, and $F$ a finite $E$-algebra, `isModuleTopology_adeleRing_of_continuous` assumes an algebra structure of $\mathbb{A}_E$ on $\mathbb{A}_F$ whose structure map is continuous, $\sigma$-compactness of $\mathbb{A}_E$, local compactness of $\mathbb{A}_F$, and an $\mathbb{A}_E$-algebra isomorphism $te : \mathbb{A}_E \otimes_E F \simeq \mathbb{A}_F$ (which makes $\mathbb{A}_F$ finite free over $\mathbb{A}_E$); it concludes that $\mathbb{A}_F$ carries the $\mathbb{A}_E$-module topology. Finally `continuous_conjAct_of_continuous` deduces, under the same hypotheses, that for each $\sigma \in \mathrm{Aut}(F/E)$ the ring automorphism `conjAct R E S F te σ` of $\mathbb{A}_F$ — the transport of $\mathrm{id} \otimes \sigma$ along $te$ — is continuous.
--
--   **Relation to Mathlib.** Built on Mathlib's `IsModuleTopology`, `AdeleRing` and the open mapping theorem for continuous surjective additive maps out of $\sigma$-compact groups; the Hausdorff instance for `AdeleRing` is registered here by transfer from its underlying product and restricted product.
--
--   **Where it is used.** Part of the adelic topology infrastructure: it identifies the topology of $\mathbb{A}_F$ over a subfield's adeles as the module topology, and thereby gives continuity of the adelic action of $\mathrm{Aut}(F/E)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aHerbrand_OpenMappingBridge.lean

import Definitions.Def_M4aHerbrand_ModuleTopologyBridge
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain TensorProduct

section OMT

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Algebra A B]

theorem isModuleTopology_of_continuous_algebraMap_of_sigmaCompact
    [SigmaCompactSpace A] [T2Space B] [BaireSpace B] [Module.Free A B] [Module.Finite A B]
    (hβ : Continuous (algebraMap A B)) : IsModuleTopology A B := by
  let b := Module.Free.chooseBasis A B
  let Φ : (Module.Free.ChooseBasisIndex A B → A) ≃ₗ[A] B := b.equivFun.symm
  have hΦ : Continuous Φ := by
    have he : (Φ : (Module.Free.ChooseBasisIndex A B → A) → B)
        = fun c => ∑ i, algebraMap A B (c i) * b i := by
      funext c
      show b.equivFun.symm c = _
      rw [b.equivFun_symm_apply]
      simp_rw [Algebra.smul_def]
    rw [he]
    exact continuous_finsetSum _ fun i _ => (hβ.comp (continuous_apply i)).mul continuous_const
  have hopen : IsOpenMap Φ :=
    AddMonoidHom.isOpenMap_of_sigmaCompact Φ.toLinearMap.toAddMonoidHom Φ.surjective hΦ
  have hsymm : Continuous Φ.symm :=
    (Φ.toEquiv.toHomeomorphOfContinuousOpen hΦ hopen).continuous_symm
  let Ψ : (Module.Free.ChooseBasisIndex A B → A) ≃L[A] B :=
    { Φ with continuous_toFun := hΦ, continuous_invFun := hsymm }
  exact IsModuleTopology.iso Ψ

end OMT

section Adele

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]
variable (S F : Type*) [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F]
  [IsFractionRing S F]
variable [Algebra E F]

open scoped RestrictedProduct in

instance instT2SpaceAdeleRing : T2Space (AdeleRing S F) :=
  inferInstanceAs (T2Space (((v : InfinitePlace F) → v.Completion) ×
    Πʳ v : HeightOneSpectrum S, [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem isModuleTopology_adeleRing_of_continuous [Module.Finite E F]
    [Algebra (AdeleRing R E) (AdeleRing S F)]
    [SigmaCompactSpace (AdeleRing R E)] [LocallyCompactSpace (AdeleRing S F)]
    (hβ : Continuous (algebraMap (AdeleRing R E) (AdeleRing S F)))
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) :
    IsModuleTopology (AdeleRing R E) (AdeleRing S F) := by
  haveI : Module.Free (AdeleRing R E) (AdeleRing S F) := Module.Free.of_equiv te.toLinearEquiv
  haveI : Module.Finite (AdeleRing R E) (AdeleRing S F) := Module.Finite.equiv te.toLinearEquiv
  exact isModuleTopology_of_continuous_algebraMap_of_sigmaCompact hβ

theorem continuous_conjAct_of_continuous [Module.Finite E F]
    [Algebra (AdeleRing R E) (AdeleRing S F)]
    [SigmaCompactSpace (AdeleRing R E)] [LocallyCompactSpace (AdeleRing S F)]
    (hβ : Continuous (algebraMap (AdeleRing R E) (AdeleRing S F)))
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) (σ : F ≃ₐ[E] F) :
    Continuous (conjAct R E S F te σ) :=
  haveI := isModuleTopology_adeleRing_of_continuous R E S F hβ te
  continuous_conjAct R E S F te σ

end Adele

end M4aHerbrand.Bridge


