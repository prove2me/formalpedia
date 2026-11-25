-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:46:42.179799+00:00
-- url     : https://prove2.me/theorems/a1388ddb-a54b-46dc-a162-74db987003b2
-- title:
--   Exists Smul Mem
-- statement:
--   Definitions and structural lemmas for Exists Smul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSmulMem.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Definitions.Def_Lemmata_GeneralBFactSecondForm_Imports
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_mem_isom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_gmap_res
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_res_mem_isom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_res_spec
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf___ee27e8a53762
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_x__7113d86d152c
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
namespace StabilizerLattices
section One
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
scoped instance latAct (h : V →ₗ⋆[K] V →ₗ[K] K) :
    MulAction (Formalism.HermitianLatticesTheory.isom h) (Submodule (𝓞 K) V) where
  smul g Λ := Formalism.HermitianLatticesTheory.gmap g.1 Λ
  one_smul := autSub_gmap_one
  mul_smul a b Λ := autSub_gmap_mul a.1 b.1 Λ
variable {h : V →ₗ⋆[K] V →ₗ[K] K}
theorem smul_pair (g : Formalism.HermitianLatticesTheory.isom h) (p : Submodule (𝓞 K) V × V) :
    g • p = (Formalism.HermitianLatticesTheory.gmap g.1 p.1, g.1 p.2) := rfl
def stabLatEquiv (Λ : Submodule (𝓞 K) V) :
    MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) Λ ≃ Formalism.ThetaLiftIndependence.autL h Λ where
  toFun a := ⟨a.1.1, a.1.2, MulAction.mem_stabilizer_iff.mp a.2⟩
  invFun b := ⟨⟨b.1, b.2.1⟩, MulAction.mem_stabilizer_iff.mpr b.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
def pairs (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (n : K) :
    Set (Submodule (𝓞 K) V × V) :=
  {p | p.1 ∈ Formalism.HermitianLatticesTheory.genus h L ∧ p.2 ∈ p.1 ∧ h p.2 p.2 = n}
def perpO (h : V →ₗ⋆[K] V →ₗ[K] K) (x : V) : Submodule (𝓞 K) V :=
  (LinearMap.ker (h x)).restrictScalars (𝓞 K)
def proj (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Submodule (𝓞 K) V × V) : Submodule (𝓞 K) V × V :=
  (p.1 ⊓ perpO h p.2, p.2)
end One
section Two
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open SplitBAux
def emb (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') : Submodule (𝓞 K) V :=
  Λ'.map (S.ι.restrictScalars (𝓞 K))
theorem cut_emb (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') : S.cut (emb S Λ') = Λ' :=
  Submodule.comap_map_eq_of_injective (f := S.ι.restrictScalars (𝓞 K)) S.inj Λ'
theorem gmap_extOf_emb (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (C : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') (emb S C) = emb S (Formalism.HermitianLatticesTheory.gmap g' C) := by
  unfold Formalism.HermitianLatticesTheory.gmap emb
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext a
  exact extOf_ι S g' a
theorem stab_pair_iff (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') (g : Formalism.HermitianLatticesTheory.isom h) :
    g ∈ MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) ((emb S Λ', S.x₀) : Submodule (𝓞 K) V × V) ↔
      Formalism.HermitianLatticesTheory.gmap g.1 (emb S Λ') = emb S Λ' ∧ g.1 S.x₀ = S.x₀ := by
  rw [MulAction.mem_stabilizer_iff, smul_pair, Prod.ext_iff]
def stabPairEquiv (hs : h.IsSymm) (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') :
    MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) ((emb S Λ', S.x₀) : Submodule (𝓞 K) V × V) ≃
      Formalism.ThetaLiftIndependence.autL h' Λ' where
  toFun a := ⟨res S a.1.1 a.1.2 ((stab_pair_iff S Λ' a.1).mp a.2).2,
    res_mem_isom S _ _ _, by
      have := gmap_res S a.1.1 a.1.2 ((stab_pair_iff S Λ' a.1).mp a.2).2
        ((stab_pair_iff S Λ' a.1).mp a.2).1
      rwa [cut_emb] at this⟩
  invFun b := ⟨⟨extOf S b.1, extOf_mem_isom hs S b.2.1⟩, (stab_pair_iff S Λ' _).mpr
    ⟨by rw [gmap_extOf_emb, b.2.2], extOf_x₀ S _⟩⟩
  left_inv a := Subtype.ext (Subtype.ext (LinearEquiv.toLinearMap_injective
    (linearMap_ext S (by simp [extOf_x₀, ((stab_pair_iff S Λ' a.1).mp a.2).2])
      (fun v => by simp [extOf_ι, res_spec]))))
  right_inv b := Subtype.ext (LinearEquiv.ext fun v => S.inj (by simp [res_spec, extOf_ι]))
end Two
end StabilizerLattices
end Formalism.HermitianLattices.Ext.L3


