-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_pow_eq_zero_of_preimage_basicOpen_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/217459c4-8096-5cf8-8fb6-db5478bf6d3f

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_eq_zero_of_preimage_basicOpen_eq_bot

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace NilpSol

open Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.GradedOAlgebra

variable {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {L : X.Modules}
  {R : Type u} [CommRing R] [Algebra S R] {𝓡 : ℕ → Submodule S R} [GradedAlgebra 𝓡]
  {ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)}

lemma app_map {N N' : X.Modules} (φ : N ⟶ N') {W W' : X.Opens} (i : W' ⟶ W) (x : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op x) = N'.presheaf.map i.op (φ.app W x) := by
  have h := φ.mapPresheaf.naturality i.op
  exact ConcreteCategory.congr_hom h x

lemma map_map (N : X.Modules) {W W' W'' : X.Opens} (i : W' ⟶ W) (j : W'' ⟶ W') (k : W'' ⟶ W)
    (x : Γ(N, W)) :
    N.presheaf.map j.op (N.presheaf.map i.op x) = N.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  obtain rfl : k = j ≫ i := Subsingleton.elim _ _
  rfl

abbrev rs (L : X.Modules) (d : ℕ) (W : X.Opens) (s : Γ(L.tensorPow d, ⊤)) : Γ(L.tensorPow d, W) :=
  (L.tensorPow d).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s

theorem exists_mem_basicOpen (p : Proj 𝓡) :
    ∃ (m : ℕ) (hm : 0 < m) (τ : 𝓡 m), p ∈ Proj.basicOpen 𝓡 (τ : R) := by
  have hp := (Proj.affineOpenCover 𝓡).covers p
  change p ∈ (Proj.awayι 𝓡 _ _ _).opensRange at hp
  rw [Proj.opensRange_awayι] at hp
  exact ⟨_, ((Proj.affineOpenCover 𝓡).idx p).1.2, _, hp⟩

theorem isNilpotent_of_basicOpen_eq_bot {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W))
    (h : X.basicOpen g = ⊥) : IsNilpotent g := by
  have h1 := hW.fromSpec_preimage_basicOpen g
  rw [h] at h1
  have h2 : PrimeSpectrum.basicOpen g = ⊥ := by
    rw [← h1]
    exact le_bot_iff.mp fun x hx => by simp at hx; exact hx
  exact (PrimeSpectrum.basicOpen_eq_bot_iff g).mp h2

section Alg

variable (hR : IsSectionRing f L R 𝓡 ι) (W : X.Opens)
include hR

theorem rs_mul (d d' : ℕ) (a : 𝓡 d) (b : 𝓡 d') :
    rs L (d + d') W (ι (d + d') ⟨(a : R) * (b : R), SetLike.GradedMul.mul_mem a.2 b.2⟩) =
      (tensorPowAdd L d d').hom.app W (tensorSections (rs L d W (ι d a)) (rs L d' W (ι d' b))) := by
  rw [hR.map_mul]
  unfold rs
  rw [← map_homOfLE_tensorSections, app_map]

theorem rs_mul_eq_zero (d d' : ℕ) (a : 𝓡 d) (b : 𝓡 d') (ha : rs L d W (ι d a) = 0) :
    rs L (d + d') W (ι (d + d') ⟨(a : R) * (b : R), SetLike.GradedMul.mul_mem a.2 b.2⟩) = 0 := by
  rw [rs_mul hR W, ha, tensorSections_zero_left, map_zero]

theorem rs_eq_zero_of_factor (D : ℕ) (c : 𝓡 D) (d d' : ℕ) (a : 𝓡 d) (b : 𝓡 d') (hD : d + d' = D)
    (hc : (a : R) * (b : R) = (c : R)) (ha : rs L d W (ι d a) = 0) : rs L D W (ι D c) = 0 := by
  subst hD
  obtain rfl : c = ⟨(a : R) * (b : R), SetLike.GradedMul.mul_mem a.2 b.2⟩ := Subtype.ext hc.symm
  exact rs_mul_eq_zero hR W d d' a b ha

theorem rs_pow (d : ℕ) (a : 𝓡 d) (g : Γ(X, W)) (y : Γ(L.tensorPow d, W)) (h : rs L d W (ι d a) = g • y)
    (k : ℕ) :
    ∃ (dk : ℕ) (ak : 𝓡 dk) (yk : Γ(L.tensorPow dk, W)),
      (ak : R) = (a : R) ^ k ∧ dk = d * k ∧ rs L dk W (ι dk ak) = g ^ k • yk := by
  induction k with
  | zero =>
    exact ⟨0, ⟨1, SetLike.GradedOne.one_mem⟩, rs L 0 W (ι 0 ⟨1, SetLike.GradedOne.one_mem⟩),
      by simp, by simp, by rw [pow_zero, one_smul]⟩
  | succ k ih =>
    obtain ⟨dk, ak, yk, hak, hdk, hrs⟩ := ih
    refine ⟨dk + d, ⟨(ak : R) * (a : R), SetLike.GradedMul.mul_mem ak.2 a.2⟩,
      (tensorPowAdd L dk d).hom.app W (tensorSections yk y), ?_, ?_, ?_⟩
    · change (ak : R) * (a : R) = (a : R) ^ (k + 1)
      rw [hak, pow_succ]
    · rw [hdk, Nat.mul_succ]
    · rw [rs_mul hR W, hrs, h, tensorSections_smul_left, tensorSections_smul_right, ← mul_smul,
        Scheme.Modules.Hom.app_smul, ← pow_succ]

theorem coe_eq_zero_of_ι_eq_zero (d : ℕ) (c : 𝓡 d) (h : ι d c = 0) : (c : R) = 0 := by
  have h0 : ι d 0 = 0 := by
    have h1 := hR.map_add d 0 0
    rw [add_zero] at h1
    have h2 : ι d 0 + ι d 0 = ι d 0 + 0 := by rw [add_zero]; exact h1.symm
    exact add_left_cancel h2
  have : c = 0 := (hR.bijective d).1 (h.trans h0.symm)
  rw [this]; rfl

end Alg

section Chart

variable {θ : X ⟶ Proj 𝓡} (hθ : IsCanonicalToProj f L R 𝓡 ι θ) {n : ℕ} (hn : 0 < n) (σ : 𝓡 n)
include hθ hn

theorem exists_chartFun {m : ℕ} (hm : 0 < m) (τ : 𝓡 m) (W : X.Opens)
    (hW : W ≤ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) :
    ∃ (g : Γ(X, W)) (hσm : (σ : R) ^ m ∈ 𝓡 (n • m)),
      rs L (n • m) W (ι (n • m) ⟨(σ : R) ^ m, hσm⟩) =
        g • rs L (n • m) W (ι (n • m) ⟨(τ : R) ^ n, SetLike.pow_mem_graded n τ.2⟩) ∧
      X.basicOpen g ≤ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) := by
  have hσm : (σ : R) ^ m ∈ 𝓡 (n • m) := by
    rw [smul_eq_mul, Nat.mul_comm]; exact SetLike.pow_mem_graded m σ.2
  set M : X.Modules := L.tensorPow (n • m) with hM
  set U₁ : (Proj 𝓡).Opens := Proj.basicOpen 𝓡 (τ : R) with hU₁
  set V₁ : X.Opens := θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) with hV₁
  set s₁ : 𝓡 (n • m) := ⟨(σ : R) ^ m, hσm⟩ with hs₁
  set t₁ : 𝓡 (n • m) := ⟨(τ : R) ^ n, SetLike.pow_mem_graded n τ.2⟩ with ht₁
  set g : Γ(X, V₁) := θ.appLE U₁ V₁ le_rfl
      (Proj.awayToSection 𝓡 (τ : R) (Away.mk 𝓡 τ.2 n ((σ : R) ^ m) hσm)) with hg
  have key : g • M.presheaf.map (homOfLE (le_top : V₁ ≤ ⊤)).op (ι (n • m) t₁) =
      M.presheaf.map (homOfLE (le_top : V₁ ≤ ⊤)).op (ι (n • m) s₁) :=
    hθ.appLE_awayToSection_smul m hm τ n s₁
  set gW : Γ(X, W) := X.presheaf.map (homOfLE hW).op g with hgW
  refine ⟨gW, hσm, ?_, ?_⟩
  · have := congrArg (M.presheaf.map (homOfLE hW).op) key
    rw [Scheme.Modules.map_smul, map_map M _ _ (homOfLE (le_top : W ≤ ⊤)),
      map_map M _ _ (homOfLE (le_top : W ≤ ⊤))] at this
    exact this.symm
  · have h52 := AlgebraicGeometry.Proj.basicOpen_mul_eq_basicOpen_awayToSection 𝓡 τ.2 hm σ.2 hn
    change Proj.basicOpen 𝓡 ((τ : R) * σ) =
      (Proj 𝓡).basicOpen (Proj.awayToSection 𝓡 (τ : R) (Away.mk 𝓡 τ.2 n ((σ : R) ^ m) hσm)) at h52
    rw [hgW, Scheme.basicOpen_res, hg, Scheme.basicOpen_appLE, ← h52, Proj.basicOpen_mul,
      Scheme.Hom.preimage_inf]
    exact inf_le_right.trans (inf_le_right.trans inf_le_right)

end Chart

end NilpSol

end

theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) (hσ : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = ⊥) :
    ∃ k : ℕ, (σ : R) ^ k = 0 := by
  classical
  open NilpSol in

  obtain ⟨N, 𝔓, hci⟩ := hva
  haveI : CompactSpace X := by
    haveI : QuasiCompact (𝔓.toProj ≫ ProjSpace.π S N) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (𝔓.toProj ≫ ProjSpace.π S N)

  have haff : ∀ x : X, ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧
      ∃ (m : ℕ) (hm : 0 < m) (τ : 𝓡 m), W ≤ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) := by
    intro x
    obtain ⟨m, hm, τ, hτ⟩ := NilpSol.exists_mem_basicOpen (𝓡 := 𝓡) (θ.base x)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (show x ∈ (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) : X.Opens) from hτ)
        (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)).2
    exact ⟨W, hW, hxW, m, hm, τ, hWV⟩
  choose W hWaff hxW hWch using haff

  have hloc : ∀ x : X, ∃ e : ℕ, ∀ E : ℕ, e ≤ E →
      NilpSol.rs L (E • n) (W x) (ι (E • n) ⟨(σ : R) ^ E, SetLike.pow_mem_graded E σ.2⟩) = 0 := by
    intro x
    obtain ⟨m, hm, τ, hWV⟩ := hWch x
    obtain ⟨g, hσm, hkey, hle⟩ := NilpSol.exists_chartFun hθ hn σ hm τ (W x) hWV
    have hbot : X.basicOpen g = ⊥ := le_bot_iff.mp (hle.trans_eq hσ)
    obtain ⟨k, hk⟩ := NilpSol.isNilpotent_of_basicOpen_eq_bot (hWaff x) g hbot
    obtain ⟨dk, ak, yk, hak, hdk, hrs⟩ := NilpSol.rs_pow hR (W x) (n • m) ⟨(σ : R) ^ m, hσm⟩ g _ hkey k
    rw [hk, zero_smul] at hrs
    refine ⟨m * k, fun E hE => ?_⟩
    refine NilpSol.rs_eq_zero_of_factor hR (W x) (E • n) _ dk ((E - m * k) • n) ak
      ⟨(σ : R) ^ (E - m * k), SetLike.pow_mem_graded (E - m * k) σ.2⟩ ?_ ?_ hrs
    · obtain ⟨E', rfl⟩ : ∃ E', E = m * k + E' := ⟨E - m * k, (Nat.add_sub_cancel' hE).symm⟩
      rw [hdk, Nat.add_sub_cancel_left]
      simp only [smul_eq_mul]
      ring
    · change (ak : R) * (σ : R) ^ (E - m * k) = (σ : R) ^ E
      rw [hak, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hE]
  choose e he using hloc

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ((W x : X.Opens) : Set X))
    (fun x => (W x).2) (fun y _ => Set.mem_iUnion.mpr ⟨y, hxW y⟩)

  let E : ℕ := ∑ x ∈ t, e x
  have hEe : ∀ x ∈ t, e x ≤ E := fun x hx => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
  set s : Γ(L.tensorPow (E • n), ⊤) := ι (E • n) ⟨(σ : R) ^ E, SetLike.pow_mem_graded E σ.2⟩ with hs
  have hsW : ∀ x ∈ t, NilpSol.rs L (E • n) (W x) s = 0 := fun x hx => he x E (hEe x hx)

  have hs0 : s = 0 := by
    let F : TopCat.Sheaf Ab X := ⟨(L.tensorPow (E • n)).presheaf, Scheme.Modules.isSheaf _⟩
    refine F.eq_of_locally_eq' (fun j : t => W j.1) ⊤ (fun j => homOfLE le_top) ?_ s 0 ?_
    · intro y _
      obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨j, hj⟩, hy⟩
    · intro j
      change NilpSol.rs L (E • n) (W j.1) s = NilpSol.rs L (E • n) (W j.1) 0
      rw [hsW j.1 j.2]
      simp
  exact ⟨E, NilpSol.coe_eq_zero_of_ι_eq_zero hR (E • n) ⟨(σ : R) ^ E, SetLike.pow_mem_graded E σ.2⟩
    (hs ▸ hs0)⟩

end S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_eq_zero_of_preimage_basicOpen_eq_bot
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_eq_zero_of_preimage_basicOpen_eq_bot (solution)
