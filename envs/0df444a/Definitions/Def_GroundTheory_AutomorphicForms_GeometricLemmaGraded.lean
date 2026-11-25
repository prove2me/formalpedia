-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaGraded
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaGraded
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:12.810082+00:00
-- url     : https://prove2.me/theorems/a1bc5ae2-297a-5e3e-b403-56422cf16fe5
-- title:
--   Geometric Lemma Graded
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Graded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaGraded.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgFinite_of_isOpen
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_add
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_avgOver
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_comp_mul_left
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_comp_mul_right
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_zero_of_forall
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_map_mulEquiv
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_mem
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_smul
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_compactOpen_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_unipotentCompactG_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_rightStab
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_unipotentCompactG_mono
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_unipotentRadical_le_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_coinvariantsKer
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
section Average
theorem avgOver_mem_supportedIn {Y : Set (GL (Fin n) F)}
    (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y) {K : Subgroup (GL (Fin n) F)}
    (hK : IsCompact (K : Set (GL (Fin n) F))) (hKQ : K ≤ blockUpper F n γ)
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) :
    ∃ g : parabolicIndSpace F n β σ, (g : GL (Fin n) F → W) = avgOver K f ∧ g ∈ supportedIn σ Y := by
  obtain ⟨U, hU, hUf⟩ := exists_rightStab_parabolicInd σ f
  have hfin : AvgFinite K (f : GL (Fin n) F → W) :=
    avgFinite_of_isOpen hK hU fun k hk => (mem_rightStab).2 fun x => hUf k hk x
  have hmem : avgOver K (f : GL (Fin n) F → W) ∈ parabolicIndSpace F n β σ :=
    avgOver_mem hfin fun k _ => (parabolicInd F n β σ k f).2
  refine ⟨⟨_, hmem⟩, rfl, fun g hg => ?_⟩
  show avgOver K (f : GL (Fin n) F → W) g = 0
  refine avgOver_eq_zero_of_forall fun k hk => hf _ fun hgk => hg ?_
  simpa using hYQ _ hgk _ ((blockUpper F n γ).inv_mem (hKQ hk))
theorem cellJacquet_avgOver {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {K : Subgroup (GL (Fin n) F)} (hK : IsCompact (K : Set (GL (Fin n) F)))
    (hKN : K ≤ unipotentRadical F n γ)
    {f g : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) (hg : g ∈ supportedIn σ Y)
    (hgf : (g : GL (Fin n) F → W) = avgOver K f) {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    cellJacquet γ w σ g m = cellJacquet γ w σ f m := by
  obtain ⟨e, hfe, hge⟩ := exists_cellSupp_pair σ hYo hCY hf hg hm
  have hmK : IsCompact ((K.map (MulAut.conj m).toMonoidHom : Subgroup (GL (Fin n) F)) :
      Set (GL (Fin n) F)) := by
    rw [Subgroup.coe_map]
    exact hK.image (conjHomeomorph m).continuous
  obtain ⟨e₂, he₂⟩ := exists_unipotentCompactG_of_isCompact (γ := γ) hmK (by
    rintro _ ⟨k, hk, rfl⟩
    exact conj_mem_unipotentRadical (levi_le_blockUpper hm) (hKN hk))
  set E := max e e₂
  have hE := isCellCompact_unipotentCompactG (F := F) (γ := γ) E
  rw [cellJacquet_eq_cellEv σ hYo hCY hg hm hE (hge.mono (unipotentCompactG_mono (le_max_left _ _))),
    cellJacquet_eq_cellEv σ hYo hCY hf hm hE (hfe.mono (unipotentCompactG_mono (le_max_left _ _)))]
  unfold cellEv
  obtain ⟨U, hU, hUf⟩ := exists_rightStab_parabolicInd σ f
  have hfinF : AvgFinite K (fun z => (f : GL (Fin n) F → W) (permGL F w * m * z)) := by
    refine avgFinite_of_isOpen hK hU fun k hk => (mem_rightStab).2 fun x => ?_
    rw [← mul_assoc, hUf k hk]
  have hcf : cellFun w σ g m = avgOver (K.map (MulAut.conj m).toMonoidHom) (cellFun w σ f m) := by
    funext y
    have h1 : cellFun w σ f m = fun y =>
        (fun z => (f : GL (Fin n) F → W) (permGL F w * m * z)) ((MulAut.conj m).symm y) := by
      funext y
      unfold cellFun
      rw [MulAut.conj_symm_apply]
      group
    rw [h1, avgOver_map_mulEquiv (MulAut.conj m) hfinF, avgOver_comp_mul_left]
    unfold cellFun
    rw [hgf, MulAut.conj_symm_apply]
    congr 1
    group
  have hfinC : AvgFinite (K.map (MulAut.conj m).toMonoidHom) (cellFun w σ f m) :=
    avgFinite_cellFun σ f m hmK
  rw [hcf, avgOver_avgOver (he₂.trans fun x hx => unipotentCompactG_mono (le_max_right _ _) hx)
    (avgFinite_cellFun σ f m hE.2.1)]
end Average
section Graded
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYQ in

theorem cellJacquet_eq_zero_of_mk_eq_zero {f : parabolicIndSpace F n β σ}
    (hf : f ∈ supportedIn σ Y)
    (h0 : Representation.Coinvariants.mk ((parabolicInd F n β σ).comp
      (unipotentRadical F n γ).subtype) f = 0) {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    cellJacquet γ w σ f m = 0 := by
  have hx := (Representation.Coinvariants.mk_eq_zero _).1 h0
  obtain ⟨K', hK'c, -, hK'⟩ := exists_mem_coinvariantsKer _ exists_compactOpen_unipotentRadical hx
  set K : Subgroup (GL (Fin n) F) := K'.map (unipotentRadical F n γ).subtype
  have hKc : IsCompact (K : Set (GL (Fin n) F)) := by
    rw [Subgroup.coe_map]
    exact hK'c.image continuous_subtype_val
  have hKN : K ≤ unipotentRadical F n γ := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2

  have hfinI : ∀ v : parabolicIndSpace F n β σ, AvgFinite K (v : GL (Fin n) F → W) := by
    intro v
    obtain ⟨U, hU, hUv⟩ := exists_rightStab_parabolicInd σ v
    exact avgFinite_of_isOpen hKc hU fun k hk => (mem_rightStab).2 fun x => hUv k hk x
  let L : parabolicIndSpace F n β σ →ₗ[ℂ] (GL (Fin n) F → W) :=
    { toFun := fun v => avgOver K (v : GL (Fin n) F → W)
      map_add' := fun v v' => by
        rw [Submodule.coe_add, avgOver_add (hfinI v) (hfinI v')]
      map_smul' := fun c v => by
        rw [Submodule.coe_smul, avgOver_smul c (hfinI v)]
        rfl }
  have hL : L f = 0 := by
    have : coinvariantsKer ((parabolicInd F n β σ).comp (unipotentRadical F n γ).subtype) K' ≤
        LinearMap.ker L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨k, v⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
      show avgOver K (((parabolicInd F n β σ ((k : unipotentRadical F n γ) : GL (Fin n) F) v :
        parabolicIndSpace F n β σ)) : GL (Fin n) F → W) = avgOver K (v : GL (Fin n) F → W)
      have : ((parabolicInd F n β σ ((k : unipotentRadical F n γ) : GL (Fin n) F) v :
          parabolicIndSpace F n β σ) : GL (Fin n) F → W) =
          fun y => (v : GL (Fin n) F → W) (y * ((k : unipotentRadical F n γ) : GL (Fin n) F)) := by
        funext y
        rw [coe_indRep_apply]
      rw [this]
      exact avgOver_comp_mul_right (hfinI v) (Subgroup.mem_map_of_mem _ k.2)
    exact this hK'
  obtain ⟨g, hg, hgY⟩ := avgOver_mem_supportedIn σ hYQ hKc
    (hKN.trans unipotentRadical_le_blockUpper) hf
  rw [← cellJacquet_avgOver σ hYo hCY hKc hKN hf hgY hg hm]
  have hg0 : (g : GL (Fin n) F → W) = 0 := hg.trans hL
  obtain ⟨e, he⟩ := exists_cellSupp σ hYo hCY hgY hm
  rw [cellJacquet_eq_cellEv σ hYo hCY hgY hm (isCellCompact_unipotentCompactG e) he]
  unfold cellEv
  rw [avgOver_eq_zero_of_forall (fun k _ => by unfold cellFun; rw [hg0]; rfl), map_zero, smul_zero]
variable (γ w) in

def jacquetSupported (Y : Set (GL (Fin n) F)) :
    supportedIn σ Y →ₗ[ℂ] jacquetFiltration γ (σ := σ) Y :=
  ((Representation.Coinvariants.mk _).comp (supportedIn σ Y).subtype).codRestrict _
    fun f => ⟨f, f.2, rfl⟩
theorem jacquetSupported_surjective (Y : Set (GL (Fin n) F)) :
    Function.Surjective (jacquetSupported γ σ Y) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩
include hYo hCY hYQ in
theorem ker_jacquetSupported_le :
    LinearMap.ker (jacquetSupported γ σ Y) ≤ LinearMap.ker (cellJacquetMap γ w σ hYo hCY) := by
  intro f hf
  rw [LinearMap.mem_ker] at hf ⊢
  have h0 : Representation.Coinvariants.mk ((parabolicInd F n β σ).comp
      (unipotentRadical F n γ).subtype) (f : parabolicIndSpace F n β σ) = 0 :=
    congrArg Subtype.val hf
  apply Subtype.ext
  funext m
  exact cellJacquet_eq_zero_of_mk_eq_zero σ hYo hCY hYQ f.2 h0 m.2
include hYo hCY hYQ in
theorem cellJacquetMap_eq_of_jacquetSupported_eq {f f' : supportedIn σ Y}
    (h : jacquetSupported γ σ Y f = jacquetSupported γ σ Y f') :
    cellJacquetMap γ w σ hYo hCY f = cellJacquetMap γ w σ hYo hCY f' := by
  rw [← sub_eq_zero, ← map_sub]
  apply ker_jacquetSupported_le σ hYo hCY hYQ
  rw [LinearMap.mem_ker, map_sub, h, sub_self]
variable (γ w) in

def gradedJacquetMap :
    jacquetFiltration γ (σ := σ) Y →ₗ[ℂ] indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ) where
  toFun x := cellJacquetMap γ w σ hYo hCY
    (Function.surjInv (jacquetSupported_surjective σ Y) x)
  map_add' x y := by
    rw [← map_add]
    apply cellJacquetMap_eq_of_jacquetSupported_eq σ hYo hCY hYQ
    have hs := jacquetSupported_surjective (γ := γ) σ Y
    rw [map_add, Function.surjInv_eq hs x, Function.surjInv_eq hs y, Function.surjInv_eq hs (x + y)]
  map_smul' c x := by
    rw [RingHom.id_apply, ← map_smul]
    apply cellJacquetMap_eq_of_jacquetSupported_eq σ hYo hCY hYQ
    have hs := jacquetSupported_surjective (γ := γ) σ Y
    rw [map_smul, Function.surjInv_eq hs x, Function.surjInv_eq hs (c • x)]
end Graded
section GradedProps
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
end GradedProps
end Parabolic
end GroundTheory.Automorphic


