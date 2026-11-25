-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:53.548642+00:00
-- url     : https://prove2.me/theorems/456531e8-7617-450b-a711-f15d8e6bfc57
-- title:
--   Irreducible
-- statement:
--   Definitions and structural lemmas for Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isRestricted_extend
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_windowEmbed_tprod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace RestrictedTensor
open PiTensorProduct Filter Function Module Set Topology
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {π : ∀ v, Representation ℂ (G v) (V v)} {ξ : ∀ v, V v}
section Window
variable (hπ : ∀ v, IsSmooth (π v)) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
  {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
  [DecidableEq ι] (S : Finset ι) (hSK : ∀ v ∉ S, K' v = K v)
  (hSξ : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (K v))
include hSK hSξ in
omit [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)] hKo hKc in
theorem windowEmbed_mem (t : ⨂[ℂ] v : S, fixedVectors (π v) (K' v)) :
    ∃ h : windowEmbed ξ S t ∈ restrictedTensor ξ,
      (⟨windowEmbed ξ S t, h⟩ : restrictedTensor ξ) ∈
        fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    have hmem : windowEmbed ξ S (c • tprod ℂ w) ∈ restrictedTensor ξ := by
      rw [map_smul, windowEmbed_tprod]
      exact Submodule.smul_mem _ _ (tprod_mem_restrictedTensor (isRestricted_extend ξ S _))
    refine ⟨hmem, fun g hg => Subtype.ext ?_⟩
    show tensorRep K π g (windowEmbed ξ S (c • tprod ℂ w)) = windowEmbed ξ S (c • tprod ℂ w)
    rw [map_smul, map_smul, windowEmbed_tprod, tensorRep_tprod]
    congr 2
    funext v
    unfold extend
    split_ifs with hv
    · exact (w ⟨v, hv⟩).2 _ (hg v)
    · exact hSξ v hv _ (hSK v hv ▸ hg v)
  | add a b ha hb =>
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨by rw [map_add]; exact Submodule.add_mem _ ha1 hb1, ?_⟩
    have := Submodule.add_mem _ ha2 hb2
    convert this using 1
    exact Subtype.ext (map_add _ _ _)
def windowEmbedFixed : (⨂[ℂ] v : S, fixedVectors (π v) (K' v)) →ₗ[ℂ]
    fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') :=
  LinearMap.codRestrict _ (LinearMap.codRestrict (restrictedTensor ξ) (windowEmbed ξ S)
    fun t => (windowEmbed_mem hξ S hSK hSξ t).1) fun t => (windowEmbed_mem hξ S hSK hSξ t).2
end Window
end RestrictedTensor
end GroundTheory.Automorphic


