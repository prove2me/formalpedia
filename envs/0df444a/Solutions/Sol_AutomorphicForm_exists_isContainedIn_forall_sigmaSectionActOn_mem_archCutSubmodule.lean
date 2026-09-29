-- Prove2me | solution 1 for AutomorphicForm.exists_isContainedIn_forall_sigmaSectionActOn_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/84872d98-b05d-5261-aa90-3325bcb790b5

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_NumberField_InfinitePlaceTransport_transport_one
import Theorems.Thm_NumberField_InfinitePlaceTransport_transport_trans_transport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_isContainedIn_forall_sigmaSectionActOn_mem_archCutSubmodule

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open AutomorphicForm
open scoped NumberField.PlaceTransport

noncomputable section

namespace Q09StabA

section Transport

variable {K L : Type} [Field K] [Field L] [Algebra K L]

private theorem norm_transport (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w') (x : w.Completion) :
    ‖InfinitePlaceTransport.transport σ h x‖ = ‖x‖ := by
  have hc : Isometry (WithAbs.congr w.1 w'.1 ((σ : L ≃ₐ[K] L) : L ≃+* L)) :=
    AddMonoidHomClass.isometry_of_norm _ fun y => by
      rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
      exact InfinitePlaceTransport.apply_apply_of_smul_eq h _
  have hT : Isometry (InfinitePlaceTransport.transport σ h) := by
    have hfun : (InfinitePlaceTransport.transport σ h : w.Completion → w'.Completion) =
        NumberField.InfinitePlace.Completion.ofCompletion ∘ UniformSpace.Completion.map _ ∘
          NumberField.InfinitePlace.Completion.toCompletion :=
      funext (InfinitePlaceTransport.transport_apply σ h)
    rw [hfun]
    exact (NumberField.InfinitePlace.Completion.isometryEquivCompletion w').symm.isometry.comp
      (hc.completion_map.comp (NumberField.InfinitePlace.Completion.isometry_toCompletion w))
  have hd := hT.dist_eq x 0
  rwa [map_zero, dist_zero_right, dist_zero_right] at hd

private def placeHom (σ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    rowIsometrySubgroup₀ w.Completion →* rowIsometrySubgroup₀ (σ • w).Completion :=
  rowIsometrySubgroup₀Map (InfinitePlaceTransport.transport σ rfl) (norm_transport σ rfl)

private theorem placeHom_entry (σ : L ≃ₐ[K] L) (w : InfinitePlace L) (k : rowIsometrySubgroup₀ w.Completion)
    (i j : Fin 2) :
    (((placeHom σ w k : rowIsometrySubgroup₀ (σ • w).Completion) : GL (Fin 2) (σ • w).Completion) :
        Matrix (Fin 2) (Fin 2) (σ • w).Completion) i j
      = InfinitePlaceTransport.transport σ rfl
          (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) := rfl

private theorem rowIsometrySubgroup₀Map_congr {A B : Type*} [NormedField A] [NormedField B] {e e' : A ≃+* B}
    (hee : e = e') (he : ∀ x, ‖e x‖ = ‖x‖) (he' : ∀ x, ‖e' x‖ = ‖x‖) :
    rowIsometrySubgroup₀Map e he = rowIsometrySubgroup₀Map e' he' := by
  subst hee; rfl

private theorem rowIsometrySubgroup₀Map_refl {A : Type*} [NormedField A] (he : ∀ x : A, ‖RingEquiv.refl A x‖ = ‖x‖) :
    rowIsometrySubgroup₀Map (RingEquiv.refl A) he = MonoidHom.id _ :=
  MonoidHom.ext fun _ => Subtype.ext (Units.ext (Matrix.ext fun _ _ => rfl))

private theorem rowIsometrySubgroup₀Map_trans {A B C : Type*} [NormedField A] [NormedField B] [NormedField C]
    (e : A ≃+* B) (f : B ≃+* C) (he : ∀ x, ‖e x‖ = ‖x‖) (hf : ∀ x, ‖f x‖ = ‖x‖)
    (hef : ∀ x, ‖(e.trans f) x‖ = ‖x‖) :
    rowIsometrySubgroup₀Map (e.trans f) hef = (rowIsometrySubgroup₀Map f hf).comp (rowIsometrySubgroup₀Map e he) :=
  MonoidHom.ext fun _ => Subtype.ext (Units.ext (Matrix.ext fun _ _ => rfl))

private theorem placeHom_one (w : InfinitePlace L) : placeHom (1 : L ≃ₐ[K] L) w = MonoidHom.id _ :=
  (rowIsometrySubgroup₀Map_congr (InfinitePlaceTransport.transport_one K L w rfl) _
    (fun _ => rfl)).trans (rowIsometrySubgroup₀Map_refl _)

private theorem placeHom_mul (γ σ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    placeHom (γ * σ) w = (placeHom γ (σ • w)).comp (placeHom σ w) :=
  (rowIsometrySubgroup₀Map_congr
      (InfinitePlaceTransport.transport_trans_transport K L γ σ rfl rfl rfl).symm _
      (fun x => by rw [RingEquiv.trans_apply, norm_transport, norm_transport])).trans
    (rowIsometrySubgroup₀Map_trans _ _ _ _ _)

end Transport

section Datum

variable {K L : Type} [Field K] [Field L] [Algebra K L]

private def transportDatum (σ : L ≃ₐ[K] L) (w : InfinitePlace L) (τ : ArchRepAt L (σ • w)) : ArchRepAt L w :=
  ⟨τ.n, τ.ρ.comp (placeHom σ w)⟩

private theorem transportDatum_one (w : InfinitePlace L) (τ : ArchRepAt L w) :
    transportDatum (1 : L ≃ₐ[K] L) w τ = τ := by
  obtain ⟨n, ρ⟩ := τ
  show (⟨n, ρ.comp (placeHom (1 : L ≃ₐ[K] L) w)⟩ : ArchRepAt L w) = ⟨n, ρ⟩
  rw [placeHom_one, MonoidHom.comp_id]

private theorem transportDatum_comp (γ σ : L ≃ₐ[K] L) (w : InfinitePlace L) (τ : ArchRepAt L (γ • (σ • w))) :
    transportDatum σ w (transportDatum γ (σ • w) τ) = transportDatum (γ * σ) w τ := by
  obtain ⟨n, ρ⟩ := τ
  show (⟨n, (ρ.comp (placeHom γ (σ • w))).comp (placeHom σ w)⟩ : ArchRepAt L w)
    = ⟨n, ρ.comp (placeHom (γ * σ) w)⟩
  rw [placeHom_mul, MonoidHom.comp_assoc]

end Datum

section Twist

variable {H₁ H₂ G : Type*} [Group H₁] [Group H₂] [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]

private def compLin (α : G →* G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u := u ∘ α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem comp_mem_typeSubmodule {ι₁ : H₁ →* G} {ι₂ : H₂ →* G} (α : G →* G) (m : H₁ →* H₂)
    (hαι : ∀ k : H₁, α (ι₁ k) = ι₂ (m k)) (ρ : Representation ℂ H₂ W) {u : G → ℂ}
    (hu : u ∈ typeSubmodule ι₂ ρ) : (u ∘ α) ∈ typeSubmodule ι₁ (ρ.comp m) := by
  refine Submodule.span_induction (p := fun f _ => (f ∘ α) ∈ typeSubmodule ι₁ (ρ.comp m)) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨T, hT, v, rfl⟩
    have hS : IsRightEquivariant ι₁ (ρ.comp m) (compLin α ∘ₗ T) := by
      intro k v' x
      show T (ρ (m k) v') (α x) = T v' (α (x * ι₁ k))
      rw [hT (m k) v' (α x), map_mul α, hαι]
    exact mem_typeSubmodule_of_isRightEquivariant hS v
  · exact (typeSubmodule ι₁ (ρ.comp m)).zero_mem
  · exact fun _ _ _ _ hf hg => (typeSubmodule ι₁ (ρ.comp m)).add_mem hf hg
  · exact fun c _ _ hf => (typeSubmodule ι₁ (ρ.comp m)).smul_mem c hf

end Twist

section Placement

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private theorem entry_fst (w : InfinitePlace L) (g : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt L w g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1
      = archMatrixUpdate L w (g : Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl

private theorem entry_snd (w : InfinitePlace L) (g : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt L w g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2
      = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j := rfl

private theorem fa_one_apply (v : HeightOneSpectrum (𝓞 L)) : (1 : FiniteAdeleRing (𝓞 L) L) v = 1 := rfl

private theorem fa_zero_apply (v : HeightOneSpectrum (𝓞 L)) : (0 : FiniteAdeleRing (𝓞 L) L) v = 0 := rfl

omit [NumberField K] in
private theorem act_toRingHom_apply (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    (D.act σ).toRingHom x = D.act σ x := rfl

private theorem sigmaAdelicAct_rowIsometryInclAt₀ (σ : L ≃ₐ[K] L) (w : InfinitePlace L)
    (k : rowIsometrySubgroup₀ w.Completion) :
    sigmaAdelicAct K L D σ (rowIsometryInclAt₀ L w k) = rowIsometryInclAt₀ L (σ • w) (placeHom σ w k) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  ext i j
  rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply, sigmaAdelicAct, Matrix.GeneralLinearGroup.map_apply,
    act_toRingHom_apply]
  refine Prod.ext ?_ ?_
  · funext v
    by_cases hv : v = σ • w
    · subst hv
      rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ _ (rfl : σ • w = σ • w),
        entry_fst, entry_fst, archMatrixUpdate_apply_self, archMatrixUpdate_apply_self]
      rfl
    · have hne : σ⁻¹ • v ≠ w := fun h0 => hv (by rw [← h0, smul_inv_smul])
      rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ _ (smul_inv_smul σ v),
        entry_fst, entry_fst, archMatrixUpdate_apply_of_ne _ _ _ _ _ hne, archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · refine FiniteAdeleRing.ext L fun v => ?_
    rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ (smul_inv_smul σ v),
      entry_snd, entry_snd]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, fa_one_apply, fa_zero_apply]

private theorem sigmaSectionActOn_mem_archTypeSubmoduleAt (σ : L ≃ₐ[K] L) (w : InfinitePlace L)
    (τ : ArchRepAt L (σ • w)) {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : u ∈ archTypeSubmoduleAt L (σ • w) τ) :
    sigmaSectionActOn K L D σ u ∈ archTypeSubmoduleAt L w (transportDatum σ w τ) :=
  comp_mem_typeSubmodule (sigmaAdelicAct K L D σ) (placeHom σ w) (sigmaAdelicAct_rowIsometryInclAt₀ K L D σ w)
    τ.ρ hu

end Placement

section Head

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private abbrev SatIndex (tys : ArchTypeFamily L) (w : InfinitePlace L) : Type :=
  Σ γ : L ≃ₐ[K] L, Fin (tys.card (γ • w))

private def satRep (tys : ArchTypeFamily L) (w : InfinitePlace L) (p : SatIndex K L tys w) : ArchRepAt L w :=
  transportDatum p.1 w (tys.rep (p.1 • w) p.2)

private def satEquiv (tys : ArchTypeFamily L) (w : InfinitePlace L) :
    SatIndex K L tys w ≃ Fin (Fintype.card (SatIndex K L tys w)) :=
  Fintype.equivFin _

private def saturate (tys : ArchTypeFamily L) : ArchTypeFamily L where
  card w := Fintype.card (SatIndex K L tys w)
  rep w j := satRep K L tys w ((satEquiv K L tys w).symm j)

private theorem saturate_rep (tys : ArchTypeFamily L) (w : InfinitePlace L) (j : Fin ((saturate K L tys).card w)) :
    (saturate K L tys).rep w j = satRep K L tys w ((satEquiv K L tys w).symm j) := rfl

private theorem saturate_rep_satEquiv (tys : ArchTypeFamily L) (w : InfinitePlace L) (p : SatIndex K L tys w) :
    (saturate K L tys).rep w (satEquiv K L tys w p) = satRep K L tys w p := by
  rw [saturate_rep, Equiv.symm_apply_apply]

private theorem isContainedIn_saturate (tys : ArchTypeFamily L) :
    ArchTypeFamily.IsContainedIn L tys (saturate K L tys) := by
  intro w i
  refine ⟨satEquiv K L tys w ⟨1, i⟩, ?_⟩
  rw [saturate_rep_satEquiv]
  exact transportDatum_one (K := K) w (tys.rep w i)

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private theorem sigmaSectionActOn_mem_archCutSubmodule_saturate (σ : L ≃ₐ[K] L) (tys : ArchTypeFamily L)
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : u ∈ archCutSubmodule L (saturate K L tys)) :
    sigmaSectionActOn K L D σ u ∈ archCutSubmodule L (saturate K L tys) := by
  rw [mem_archCutSubmodule_iff] at hu ⊢
  intro w
  have key : ∀ (p : SatIndex K L tys (σ • w)) (v : AdelicGL2 (𝓞 L) L → ℂ),
      v ∈ archTypeSubmoduleAt L (σ • w) (satRep K L tys (σ • w) p) →
        sigmaSectionActOn K L D σ v ∈
          ⨆ j : Fin ((saturate K L tys).card w), archTypeSubmoduleAt L w ((saturate K L tys).rep w j) := by
    rintro ⟨γ, i⟩ v hv
    have h1 := sigmaSectionActOn_mem_archTypeSubmoduleAt K L D σ w _ hv
    rw [show satRep K L tys (σ • w) ⟨γ, i⟩ = transportDatum γ (σ • w) (tys.rep (γ • (σ • w)) i) from rfl,
      transportDatum_comp] at h1
    have h2 : (saturate K L tys).rep w (satEquiv K L tys w ⟨γ * σ, i⟩)
        = transportDatum (γ * σ) w (tys.rep (γ • (σ • w)) i) :=
      saturate_rep_satEquiv K L tys w ⟨γ * σ, i⟩
    refine Submodule.mem_iSup_of_mem (satEquiv K L tys w ⟨γ * σ, i⟩) ?_
    rw [h2]
    exact h1
  have hmap : (⨆ j : Fin ((saturate K L tys).card (σ • w)),
        archTypeSubmoduleAt L (σ • w) ((saturate K L tys).rep (σ • w) j)).map (compLin (sigmaAdelicAct K L D σ))
      ≤ ⨆ j : Fin ((saturate K L tys).card w), archTypeSubmoduleAt L w ((saturate K L tys).rep w j) := by
    rw [Submodule.map_iSup]
    refine iSup_le fun j => ?_
    rintro _ ⟨v, hv, rfl⟩
    exact key _ v hv
  exact hmap (Submodule.mem_map_of_mem (hu (σ • w)))

end Head

end Q09StabA

end

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (tys : ArchTypeFamily L) :
    ∃ tys' : ArchTypeFamily L, ArchTypeFamily.IsContainedIn L tys tys' ∧
      ∀ u ∈ archCutSubmodule L tys', sigmaSectionActOn K L D σ u ∈ archCutSubmodule L tys' := by
  haveI : CharZero K := (algebraMap K L).charZero
  haveI : NumberField K := NumberField.of_tower ℚ L K
  exact ⟨Q09StabA.saturate K L tys, Q09StabA.isContainedIn_saturate K L tys,
    fun _ hu => Q09StabA.sigmaSectionActOn_mem_archCutSubmodule_saturate K L D σ tys hu⟩

end S_AutomorphicForm_exists_isContainedIn_forall_sigmaSectionActOn_mem_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_isContainedIn_forall_sigmaSectionActOn_mem_archCutSubmodule (solution)
