-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
-- name    : GroundTheory_GlobalFields_Adele_Topology
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:54.93682+00:00
-- url     : https://prove2.me/theorems/47e1eca2-b63e-4bc9-afe7-26423a9cb95e
-- title:
--   Topology
-- statement:
--   Definitions and structural lemmas for Topology, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Topology.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_units_adicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
namespace GroundTheory.Global
variable (K : Type*) [Field K] [NumberField K]
instance fact_isOpen_adicCompletionIntegers :
    Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
  ⟨fun v ↦ isOpen_adicCompletionIntegers v⟩
instance locallyCompactSpace_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) :=
  RestrictedProduct.locallyCompactSpace_of_addGroup
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (B := fun v ↦ v.adicCompletionIntegers K)
    (.of_forall fun v ↦ isCompact_adicCompletionIntegers v)
instance locallyCompactSpace_adeleRing : LocallyCompactSpace 𝔸[K] :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
instance IdeleGroup.locallyCompactSpace : LocallyCompactSpace (IdeleGroup K) :=
  inferInstance
instance locallyCompactSpace_units_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K)ˣ :=
  inferInstance
instance locallyCompactSpace_units_infiniteAdeleRing :
    LocallyCompactSpace (InfiniteAdeleRing K)ˣ :=
  inferInstance
theorem isCompact_units_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ) := by
  have h : IsCompact ((v.adicCompletionIntegers K : Set (v.adicCompletion K)) ×ˢ
      (MulOpposite.unop ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)))) :=
    (isCompact_adicCompletionIntegers v).prod
      (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 (isCompact_adicCompletionIntegers v))
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage h using 1
  ext u
  simp only [SetLike.mem_coe, Submonoid.mem_units_iff, Set.mem_preimage, Set.mem_prod,
    Units.embedProduct_apply, MulOpposite.unop_op]
  exact Iff.rfl
instance locallyCompactSpace_restrictedProduct_units :
    LocallyCompactSpace (Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) :=
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
        Set (v.adicCompletion K)ˣ)) :=
    ⟨fun v ↦ IdeleGroup.isOpen_units_adicCompletionIntegers K v⟩
  RestrictedProduct.locallyCompactSpace_of_group
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (B := fun v ↦ (Submonoid.ofClass (v.adicCompletionIntegers K)).units)
    (.of_forall fun v ↦ isCompact_units_adicCompletionIntegers K v)
end GroundTheory.Global


