-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/655c4bb9-a1a3-5c67-8d12-9d4567d0a168

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_supportedIn_idealPowQuot
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPow
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace P2mFiltQ

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

section Topology

include π in
private theorem _root_.P2mFiltQ.isLocallyNoetherian [IsNoetherianRing R] [IsProper π] : IsLocallyNoetherian V :=
  LocallyOfFiniteType.isLocallyNoetherian π

p2m_export "P2mFiltQ" "isLocallyNoetherian"
include π in
theorem compactSpace [IsProper π] : CompactSpace V :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := π)).mp inferInstance

end Topology

theorem isCoherent_zero : (zero π).IsCoherent := fun U =>
  Module.Finite.of_surjective (M := Γ(V, U.1)) (0 : Γ(V, U.1) →ₗ[Γ(V, U.1)] (zero π).obj U.1)
    fun _ => ⟨0, Subsingleton.elim _ _⟩

theorem isQuasicoherent_zero : (zero π).IsQuasicoherent := fun _ _ =>
  ⟨fun _ => ⟨0, 0, Subsingleton.elim _ _⟩, fun _ _ => ⟨0, Subsingleton.elim _ _⟩⟩

theorem isCoherent_idealPow [IsLocallyNoetherian V] (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    (hFc : F.IsCoherent) : (idealPow π I F k).IsCoherent := by
  intro U
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule
  haveI := F.isScalarTower U.1
  haveI : Module.Finite Γ(V, U.1) (F.obj U.1) := hFc U
  haveI : IsNoetherianRing Γ(V, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI : IsNoetherian Γ(V, U.1) (F.obj U.1) := isNoetherian_of_isNoetherianRing_of_finite _ _
  show Module.Finite Γ(V, U.1)
    ((idealSections I U.1 ^ k • (⊤ : Submodule Γ(V, U.1) (F.obj U.1))).restrictScalars R)
  haveI : Module.Finite Γ(V, U.1) ↥(idealSections I U.1 ^ k • (⊤ : Submodule Γ(V, U.1) (F.obj U.1))) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  exact Module.Finite.equiv
    (Submodule.restrictScalarsEquiv R Γ(V, U.1) (F.obj U.1) (idealSections I U.1 ^ k • ⊤)).symm

section Uniform

theorem subsingleton_basicOpen_of_subsingleton (G : OModulePresheaf π) (hGq : G.IsQuasicoherent)
    (W : V.affineOpens) [Subsingleton (G.obj W.1)] (g : Γ(V, W.1)) :
    Subsingleton (G.obj (V.basicOpen g)) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨n, y, hy⟩ := (hGq W g).1 z
  rw [Subsingleton.elim y 0, map_zero] at hy
  have hu : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom (g ^ n)) := by
    rw [map_pow]
    exact (V.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen g).pow n
  exact (hu.smul_eq_zero.mp hy.symm)

variable [IsNoetherianRing R] [IsProper π]

theorem exists_forall_subsingleton_idealPow (Y : Closeds V) (F : OModulePresheaf π) (hFc : F.IsCoherent)
    (hFq : F.IsQuasicoherent) (hFs : F.SupportedIn Y) :
    ∃ N : ℕ, ∀ U : V.affineOpens,
      Subsingleton ((idealPow π (Scheme.IdealSheafData.vanishingIdeal Y) F N).obj U.1) := by
  haveI : IsLocallyNoetherian V := isLocallyNoetherian π
  haveI : CompactSpace V := compactSpace π

  have hcover : (Set.univ : Set V) ⊆ ⋃ W : V.affineOpens, (W.1 : Set V) := by
    intro x _
    obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (X := V) (x := x) (U := ⊤) trivial
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun W : V.affineOpens => (W.1 : Set V))
    (fun W => W.1.isOpen) hcover

  choose N hN using fun W : V.affineOpens =>
    exists_idealPowSub_eq_bot π Y F hFc hFq hFs W
  refine ⟨t.sup N, fun U => ?_⟩
  set G := idealPow π (Scheme.IdealSheafData.vanishingIdeal Y) F (t.sup N) with hG
  have hGq : G.IsQuasicoherent := isQuasicoherent_idealPow π _ F _ hFq

  have hchart : ∀ W ∈ t, Subsingleton (G.obj W.1) := by
    intro W hW
    refine subsingleton_of_forall_eq 0 fun y => Subtype.ext ?_
    have hle : idealPowSub π (Scheme.IdealSheafData.vanishingIdeal Y) F (t.sup N) W.1 ≤ ⊥ :=
      (hN W) ▸ idealPowSub_antitone π _ F (Finset.le_sup hW) W.1
    exact (Submodule.mem_bot R).mp (hle y.2)

  have hloc : ∀ p : U.1, ∃ f : Γ(V, U.1), (p : V) ∈ V.basicOpen f ∧ Subsingleton (G.obj (V.basicOpen f)) := by
    intro p
    have hp : (p : V) ∈ ⋃ W ∈ t, (W.1 : Set V) := ht (Set.mem_univ _)
    simp only [Set.mem_iUnion] at hp
    obtain ⟨W, hWt, hpW⟩ := hp
    obtain ⟨f, g, hfg, hpf⟩ := exists_basicOpen_le_affine_inter U.2 W.2 (p : V) ⟨p.2, hpW⟩
    haveI := hchart W hWt
    refine ⟨f, hpf, ?_⟩
    rw [hfg]
    exact subsingleton_basicOpen_of_subsingleton π G hGq W g
  choose f hpf hsub using hloc

  have hUcov : (U.1 : Set V) ⊆ ⋃ p : U.1, (V.basicOpen (f p) : Set V) :=
    fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpf ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := U.2.isCompact.elim_finite_subcover (fun p : U.1 => (V.basicOpen (f p) : Set V))
    (fun p => (V.basicOpen (f p)).isOpen) hUcov
  have hcov : U.1 ≤ ⨆ j : s, V.basicOpen (f j.1) := by
    intro x hx
    have hx' := hs hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨p, hps, hxp⟩ := hx'
    exact Opens.mem_iSup.mpr ⟨⟨p, hps⟩, hxp⟩

  refine subsingleton_of_forall_eq 0 fun x => ?_
  exact eq_zero_of_forall_res_basicOpen_eq_zero hGq U (fun j : s => f j.1) hcov x
    fun j => by haveI := hsub j.1; exact Subsingleton.elim _ _

end Uniform

section Main

variable [IsNoetherianRing R] [IsProper π]
variable (Y : Closeds V) (Q : OModulePresheaf π → Prop)
  (h0 : ∀ G : OModulePresheaf π, (∀ U : V.affineOpens, Subsingleton (G.obj U.1)) → Q G)
  (hext : ∀ (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃) →
    G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
    G₃.IsCoherent → G₃.IsQuasicoherent →
    (Q G₁ → Q G₃ → Q G₂) ∧ (Q G₁ → Q G₂ → Q G₃) ∧ (Q G₂ → Q G₃ → Q G₁))
  (hann : ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y →
    OModulePresheaf.IdealAnnihilates π (Scheme.IdealSheafData.vanishingIdeal Y) G → Q G)

include h0 hext hann in
theorem main : ∀ F : OModulePresheaf π, F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → Q F := by
  intro F hFc hFq hFs
  haveI : IsLocallyNoetherian V := isLocallyNoetherian π
  obtain ⟨N, hN⟩ := exists_forall_subsingleton_idealPow π Y F hFc hFq hFs

  have hPc : ∀ k, (idealPow π (Scheme.IdealSheafData.vanishingIdeal Y) F k).IsCoherent :=
    fun k => isCoherent_idealPow π _ F k hFc
  have hPq : ∀ k, (idealPow π (Scheme.IdealSheafData.vanishingIdeal Y) F k).IsQuasicoherent :=
    fun k => isQuasicoherent_idealPow π _ F k hFq
  have hQ : ∀ k, Q (idealPowQuot π (Scheme.IdealSheafData.vanishingIdeal Y) F k) := fun k =>
    hann _ (isCoherent_idealPowQuot π _ F k hFc) (isQuasicoherent_idealPowQuot π _ F k hFq)
      (supportedIn_idealPowQuot π _ F k hFs) (idealAnnihilates_idealPowQuot π _ F k)

  have hpow : ∀ d k : ℕ, k + d = N → Q (idealPow π (Scheme.IdealSheafData.vanishingIdeal Y) F k) := by
    intro d
    induction d with
    | zero =>
      intro k hk
      rw [add_zero] at hk
      subst hk
      exact h0 _ hN
    | succ d ih =>
      intro k hk
      have h1 : Q (idealPow π (Scheme.IdealSheafData.vanishingIdeal Y) F (k + 1)) := ih (k + 1) (by omega)
      exact (hext _ _ _ ⟨idealPowSES π (Scheme.IdealSheafData.vanishingIdeal Y) F k⟩ (hPc (k + 1)) (hPq (k + 1))
        (hPc k) (hPq k) (isCoherent_idealPowQuot π _ F k hFc) (isQuasicoherent_idealPowQuot π _ F k hFq)).1
        h1 (hQ k)

  exact (hext (zero π) _ F ⟨idealPowZeroSES π (Scheme.IdealSheafData.vanishingIdeal Y) F⟩ (isCoherent_zero π)
    (isQuasicoherent_zero π) (hPc 0) (hPq 0) hFc hFq).2.1 (h0 _ fun _ => inferInstance) (hpow N 0 (zero_add N))

end Main

end P2mFiltQ

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (Y : Closeds V) (Q : OModulePresheaf π → Prop)
    (h0 : ∀ G : OModulePresheaf π, (∀ U : V.affineOpens, Subsingleton (G.obj U.1)) → Q G)
    (hext : ∀ (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃) →
      G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
      G₃.IsCoherent → G₃.IsQuasicoherent →
      (Q G₁ → Q G₃ → Q G₂) ∧ (Q G₁ → Q G₂ → Q G₃) ∧ (Q G₂ → Q G₃ → Q G₁))
    (hann : ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y →
      OModulePresheaf.IdealAnnihilates π (Scheme.IdealSheafData.vanishingIdeal Y) G → Q G) :
    ∀ F : OModulePresheaf π, F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → Q F :=
  P2mFiltQ.main π Y Q h0 hext hann

end S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates (solution)
