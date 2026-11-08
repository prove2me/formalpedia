-- Prove2me | solution 1 for AlgebraicGeometry.exists_closedImmersion_proj_of_twisted_affine_chart_ratios
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-07T20:47:54.258726+00:00
-- url     : https://prove2.me/submissions/b0476483-2daf-4ac5-8dcd-2f950ac8a83a

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top

universe u v
noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

namespace PhilipponFiniteCocycle
variable {X : Scheme.{u}} {r : ℕ}

/-- A finite chart cocycle, without equating the index and scheme universes. -/
structure UnitCocycle (V : Fin r → X.Opens) where
  u : ∀ i j, Γ(X, V i ⊓ V j)
  refl : ∀ i, u i i = 1
  cocycle : ∀ i j k,
    rO (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
      V i ⊓ V j ⊓ V k ≤ V i ⊓ V j) (u i j) *
    rO (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      V i ⊓ V j ⊓ V k ≤ V j ⊓ V k) (u j k) =
    rO (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      V i ⊓ V j ⊓ V k ≤ V i ⊓ V k) (u i k)

variable {V : Fin r → X.Opens}

def UnitCocycle.lift (c : UnitCocycle V) :
    Scheme.Modules.UnitCocycle (fun i : ULift.{u} (Fin r) => V i.down) where
  u i j := c.u i.down j.down
  refl i := c.refl i.down
  cocycle i j k := c.cocycle i.down j.down k.down

noncomputable abbrev glueOfCocycle (c : UnitCocycle V) : X.Modules :=
  Scheme.Modules.glueOfCocycle c.lift

noncomputable abbrev glueComponent (c : UnitCocycle V) (T : X.Opens) (i : Fin r) :=
  Scheme.Modules.glueComponent c.lift T (ULift.up i)

lemma leij (T : X.Opens) (i j : Fin r) : T ⊓ (V i ⊓ V j) ≤ V i ⊓ V j := inf_le_right

noncomputable abbrev glueMk (c : UnitCocycle V) (T : X.Opens)
    (x : ∀ i, Γ(X, T ⊓ V i))
    (hx : ∀ i j,
      rO (inf_le_inf_left T inf_le_left : T ⊓ (V i ⊓ V j) ≤ T ⊓ V i) (x i) =
      rO (leij T i j) (c.u i j) *
      rO (inf_le_inf_left T inf_le_right : T ⊓ (V i ⊓ V j) ≤ T ⊓ V j) (x j)) :
    Γ(glueOfCocycle c, T) :=
  Scheme.Modules.glueMk c.lift T (fun i => x i.down) (fun i j => hx i.down j.down)

noncomputable abbrev glueFrame (c : UnitCocycle V) (i : Fin r) :=
  Scheme.Modules.glueFrame c.lift (ULift.up i)

lemma glue_ext (c : UnitCocycle V) {T : X.Opens} {p q : Γ(glueOfCocycle c, T)}
    (h : ∀ i, glueComponent c T i p = glueComponent c T i q) : p = q :=
  Scheme.Modules.glue_ext c.lift (fun i => h i.down)

lemma glueComponent_map (c : UnitCocycle V) {T T' : X.Opens} (h : T' ≤ T)
    (i : Fin r) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T' i ((glueOfCocycle c).presheaf.map (homOfLE h).op p) =
      rO (inf_le_inf_right (V i) h) (glueComponent c T i p) := rfl

lemma glueComponent_smul (c : UnitCocycle V) {T : X.Opens} (g : Γ(X, T))
    (i : Fin r) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T i (g • p) = rO inf_le_left g * glueComponent c T i p := rfl

lemma glueComponent_glueFrame (c : UnitCocycle V) (i k : Fin r) :
    glueComponent c (V i) k (glueFrame c i) =
      rO (le_of_eq (inf_comm (V i) (V k))) (c.u k i) := rfl

lemma isFrameOn_glueFrame (c : UnitCocycle V) (i : Fin r) :
    Scheme.Modules.IsFrameOn (glueFrame c i) (V i) :=
  Scheme.Modules.isFrameOn_glueFrame c.lift (ULift.up i)

end PhilipponFiniteCocycle
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem solution
    {Z : Scheme.{u}} {r : ℕ} (V : Fin r → Z.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (w : ∀ i j : Fin r, Γ(Z, V i))
    (hW1 : ∀ i, w i i = 1)
    (hW2 : ∀ i j k : Fin r,
      Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Z.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hW3 : ∀ i j : Fin r, Z.basicOpen (w i j) = V i ⊓ V j)
    (i₀ : Fin r) (g : Γ(Z, V i₀)) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ t : ∀ j : Fin r, Γ(Z, V j), t i₀ = g ∧
      ∀ j m : Fin r,
        Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (t j) =
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (t m) := by
  classical

  have res_res : ∀ {A B C : Z.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C) (x : Γ(Z, C)),
      Z.presheaf.map (homOfLE h₁).op (Z.presheaf.map (homOfLE h₂).op x) =
        Z.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
    intro A B C h₁ h₂ x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

  have stepA : ∀ j : Fin r, ∃ (a : Γ(Z, V j)) (n : ℕ),
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op a =
        Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ n *
          Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    letI : Algebra Γ(Z, V j) Γ(Z, V j ⊓ V i₀) :=
      (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op).hom.toAlgebra
    haveI : IsLocalization.Away (w j i₀) Γ(Z, V j ⊓ V i₀) :=
      (hV j).isLocalization_of_eq_basicOpen (w j i₀) (homOfLE inf_le_left) (hW3 j i₀).symm
    obtain ⟨⟨a, ⟨s, ⟨n, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (w j i₀))
      (Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g)
    refine ⟨a, n, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow] at h
    rw [← h, mul_comm]
  choose a₀ n₀ ha₀ using stepA

  let a : ∀ j : Fin r, Γ(Z, V j) := Function.update a₀ i₀ g
  let n : Fin r → ℕ := Function.update n₀ i₀ 0
  have ha : ∀ j, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (a j) =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ n j *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      simp only [a, n, Function.update_self, pow_zero, one_mul]
    · simp only [a, n, Function.update_of_ne hj]
      exact ha₀ j

  let k₁ : ℕ := Finset.univ.sup n
  have hn : ∀ j, n j ≤ k₁ := fun j => Finset.le_sup (f := n) (Finset.mem_univ j)
  let b : ∀ j : Fin r, Γ(Z, V j) := fun j => a j * w j i₀ ^ (k₁ - n j)
  have hb : ∀ j, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (b j) =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ k₁ *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    simp only [b, map_mul, map_pow, ha]
    rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' (hn j)]
  have hbi₀ : b i₀ = g := by
    simp only [b, a, n, Function.update_self, hW1, one_pow, mul_one]

  have stepB : ∀ j m : Fin r, ∃ e : ℕ,
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀) ^ e *
        (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (b j) -
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k₁ *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (b m)) = 0 := by
    intro j m
    have hjm : IsAffineOpen (V j ⊓ V m) := by rw [← hW3 j m]; exact (hV j).basicOpen (w j m)

    have hT : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) =
        Z.basicOpen (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀)) := by
      rw [Scheme.basicOpen_res, hW3]
    letI : Algebra Γ(Z, V j ⊓ V m) Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) :=
      (Z.presheaf.map (homOfLE (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op).hom.toAlgebra
    haveI : IsLocalization.Away (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀))
        Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) :=
      hjm.isLocalization_of_eq_basicOpen _ (homOfLE inf_le_left) hT

    have hvan : Z.presheaf.map (homOfLE (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op
        (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (b j) -
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k₁ *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (b m)) = 0 := by
      have e1 := congrArg (Z.presheaf.map (homOfLE
        (inf_le_right : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V i₀)).op) (hb j)
      have e2 := congrArg (Z.presheaf.map (homOfLE
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V m ⊓ V i₀)).op) (hb m)
      have e3 := congrArg (Z.presheaf.map (homOfLE
        (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op) (hW2 j m i₀)
      simp only [map_sub, map_mul, map_pow, res_res] at e1 e2 e3 ⊢
      rw [e1, e2, e3]
      ring
    obtain ⟨⟨_, ⟨e, rfl⟩⟩, he⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀)))
      Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) _).mp hvan
    exact ⟨e, he⟩
  choose e he using stepB

  let E : ℕ := Finset.univ.sup (fun jm : Fin r × Fin r => e jm.1 jm.2)
  have hE : ∀ j m, e j m ≤ E := fun j m =>
    Finset.le_sup (f := fun jm : Fin r × Fin r => e jm.1 jm.2) (Finset.mem_univ (j, m))
  refine ⟨k₁ + E, fun k hk => ⟨fun j => b j * w j i₀ ^ (k - k₁), ?_, ?_⟩⟩
  ·
    simp only [hbi₀, hW1, one_pow, mul_one]
  · intro j m
    obtain ⟨E', hE'⟩ : ∃ E', k = k₁ + (e j m + E') := ⟨k - k₁ - e j m, by have := hE j m; omega⟩
    have hkk : k - k₁ = e j m + E' := by omega
    have c := hW2 j m i₀
    have d := he j m
    simp only [map_mul, map_pow, hkk]
    rw [hE']
    rw [c] at d ⊢
    linear_combination ((Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) *
      Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (w m i₀)) ^ E') * d

end S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf
end P2MW

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace QPC2


theorem isImmersion_respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf => by haveI := hi; haveI := hf; infer_instance⟩

theorem surjective_app_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) (e : V = U)
    (hs : Function.Surjective (f.app U)) : Function.Surjective (f.app V) := by
  subst e; exact hs

theorem isClosedImmersion_morphismRestrict_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) (hfU : IsAffineOpen (f ⁻¹ᵁ U))
    (hs : Function.Surjective (f.app U)) : IsClosedImmersion (f ∣_ U) := by
  haveI : IsAffine U := hU
  haveI : IsAffine (f ⁻¹ᵁ U) := hfU
  rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)]
  refine ⟨hfU, ?_⟩
  rw [morphismRestrict_appTop]
  have e : U.ι ''ᵁ ⊤ = U := by simp [Scheme.Hom.image_top_eq_opensRange]
  have h1 : Function.Surjective (f.app (U.ι ''ᵁ ⊤)) := surjective_app_of_eq f U _ e hs
  have h2 : Function.Surjective
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) :=
    (ConcreteCategory.bijective_of_isIso _).2
  intro y
  obtain ⟨z, rfl⟩ := h2 y
  obtain ⟨x, rfl⟩ := h1 z
  exact ⟨x, ConcreteCategory.comp_apply _ _ _⟩

theorem isImmersion_of_affine_charts {Y P : Scheme.{u}} (φ : Y ⟶ P) {J : Type*} (W : J → P.Opens)
    (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen (φ ⁻¹ᵁ W j))
    (hcov : ⨆ j, φ ⁻¹ᵁ W j = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
    IsImmersion φ := by
  haveI := isImmersion_respectsRight_isOpenImmersion
  have hrange : Set.range φ.base ⊆ ((⨆ j, W j : P.Opens) : Set P) := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ (⨆ j, φ ⁻¹ᵁ W j : Y.Opens) := by rw [hcov]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨j, hj⟩ := hy
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨j, hj⟩
  exact IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) W hrange
    (fun j => by
      haveI := isClosedImmersion_morphismRestrict_of_surjective φ (W j) (hWaff j) (hYaff j) (hsurj j)
      infer_instance)

end QPC2

theorem solution
    {Y P : Scheme.{u}} (φ : Y ⟶ P) {J : Type v} (W : J → P.Opens)
    (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen (φ ⁻¹ᵁ W j))
    (hcov : ⨆ j, φ ⁻¹ᵁ W j = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
    IsImmersion φ :=
  QPC2.isImmersion_of_affine_charts φ W hWaff hYaff hcov hsurj

end S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app
end P2MW

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GluedPres

variable {Y : Scheme.{u}} {r : ℕ} {V : Fin r → Y.Opens} (c : PhilipponFiniteCocycle.UnitCocycle V)

def Compat (x : ∀ j : Fin r, Γ(Y, V j)) : Prop :=
  ∀ i j, rO (inf_le_left : V i ⊓ V j ≤ V i) (x i) = c.u i j * rO (inf_le_right : V i ⊓ V j ≤ V j) (x j)

noncomputable def sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤) :=
  PhilipponFiniteCocycle.glueMk c ⊤ (fun j => rO (inf_le_right : ⊤ ⊓ V j ≤ V j) (x j)) fun i j => by
    rw [rO_rO, rO_rO]
    have h := congrArg (rO (PhilipponFiniteCocycle.leij ⊤ i j)) (hx i j)
    rw [map_mul, rO_rO, rO_rO] at h
    exact h

theorem glueComponent_sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (j : Fin r) :
    PhilipponFiniteCocycle.glueComponent c ⊤ j (sec c x hx) = rO (inf_le_right : ⊤ ⊓ V j ≤ V j) (x j) := rfl

theorem glueComponent_map_sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) {W : Y.Opens} (j : Fin r) :
    PhilipponFiniteCocycle.glueComponent c W j ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (sec c x hx)) =
      rO (inf_le_right : W ⊓ V j ≤ V j) (x j) := by
  rw [PhilipponFiniteCocycle.glueComponent_map, glueComponent_sec, rO_rO]

theorem map_sec_eq_glueFrame (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (i : Fin r)
    (hxi : ∀ j, rO (inf_le_left : V j ⊓ V i ≤ V j) (x j) = c.u j i) :
    (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (sec c x hx) = PhilipponFiniteCocycle.glueFrame c i := by
  apply PhilipponFiniteCocycle.glue_ext
  intro j
  rw [glueComponent_map_sec, PhilipponFiniteCocycle.glueComponent_glueFrame, ← hxi j, rO_rO]

theorem bijective_smul_of_map_eq_glueFrame (s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤)) (i : Fin r)
    (hs : (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op s = PhilipponFiniteCocycle.glueFrame c i)
    (W : Y.Opens) (hW : W ≤ V i) :
    Function.Bijective fun g : Γ(Y, W) => g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W)) := by
  have key : (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s =
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE hW).op (PhilipponFiniteCocycle.glueFrame c i) := by
    rw [← hs]
    change _ = ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op ≫
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE hW).op) s
    rw [← Functor.map_comp]; rfl
  rw [key]
  exact PhilipponFiniteCocycle.isFrameOn_glueFrame c i hW hW

theorem subsingleton_sections_bot (M : Y.Modules) : Subsingleton (M.val.obj (op (⊥ : Y.Opens))) := by
  have hbot : (⊥ : Sieve (⊥ : Y.Opens)) ∈ (Opens.grothendieckTopology ↥Y) (⊥ : Y.Opens) :=
    fun x hx => (Opens.mem_bot.1 hx).elim
  have hT : Limits.IsTerminal (M.val.presheaf.obj (op (⊥ : Y.Opens))) :=
    Sheaf.isTerminalOfBotCover ⟨M.val.presheaf, M.isSheaf⟩ (⊥ : Y.Opens) hbot
  have h0 : (𝟙 (M.val.presheaf.obj (op (⊥ : Y.Opens))) : _ ⟶ _) = 0 := hT.hom_ext _ _
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) a) h0
    simp at this
    exact this
  have hb : b = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) b) h0
    simp at this
    exact this
  rw [ha, hb]

theorem subsingleton_functions_bot : Subsingleton (Γ(Y, (⊥ : Y.Opens)) : Type _) := by
  have hbot : (⊥ : Sieve (⊥ : Y.Opens)) ∈ (Opens.grothendieckTopology ↥Y) (⊥ : Y.Opens) :=
    fun x hx => (Opens.mem_bot.1 hx).elim
  have hT : Limits.IsTerminal (Y.sheaf.val.obj (op (⊥ : Y.Opens))) :=
    Sheaf.isTerminalOfBotCover Y.sheaf (⊥ : Y.Opens) hbot
  let e := hT.uniqueUpToIso CommRingCat.punitIsTerminal
  refine ⟨fun a b => ?_⟩
  have h1 : ∀ x : Γ(Y, (⊥ : Y.Opens)), e.inv.hom (e.hom.hom x) = x := fun x => by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) x) e.hom_inv_id
    simpa using this
  rw [← h1 a, ← h1 b, Subsingleton.elim (e.hom.hom a) (e.hom.hom b)]

theorem bijective_smul_bot (M : Y.Modules) (s : Γ(M, ⊤)) (W : Y.Opens) (hW : W ≤ ⊥) :
    Function.Bijective fun g : Γ(Y, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s : Γ(M, W)) := by
  have hW' : W = ⊥ := le_bot_iff.1 hW
  subst hW'
  haveI : Subsingleton (Γ(M, (⊥ : Y.Opens)) : Type _) := subsingleton_sections_bot M
  haveI : Subsingleton (Γ(Y, (⊥ : Y.Opens)) : Type _) := subsingleton_functions_bot
  exact ⟨fun a b _ => Subsingleton.elim a b, fun m => ⟨0, Subsingleton.elim _ _⟩⟩

theorem isUnit_of_frames {M : Y.Modules} {W : Y.Opens} (s t : Γ(M, W))
    (hs : Function.Bijective fun g : Γ(Y, W) => g • s) (ht : Function.Bijective fun g : Γ(Y, W) => g • t)
    (f : Γ(Y, W)) (h : s = f • t) : IsUnit f := by
  obtain ⟨f', hf'⟩ := hs.2 t
  have hf'' : f' • s = t := hf'
  have h1 : (f * f') • s = (1 : Γ(Y, W)) • s := by
    rw [one_smul, mul_smul, hf'', ← h]
  exact isUnit_iff_exists_inv.2 ⟨f', hs.1 h1⟩

theorem inf_le_basicOpen_of_frame (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (W : Y.Opens)
    (hW : ∀ W' : Y.Opens, W' ≤ W → Function.Bijective fun g : Γ(Y, W') =>
      g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (sec c x hx) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W')))
    (j : Fin r) : W ⊓ V j ≤ Y.basicOpen (x j) := by

  set W' : Y.Opens := W ⊓ V j with hW'
  let s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W') := (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (sec c x hx)
  let t : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W') := (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (inf_le_right : W' ≤ V j)).op (PhilipponFiniteCocycle.glueFrame c j)
  have hs : Function.Bijective fun g : Γ(Y, W') => g • s := hW W' inf_le_left
  have ht : Function.Bijective fun g : Γ(Y, W') => g • t := PhilipponFiniteCocycle.isFrameOn_glueFrame c j (inf_le_right : W' ≤ V j) inf_le_right
  obtain ⟨f, hf⟩ := ht.2 s
  have hfu : IsUnit f := isUnit_of_frames s t hs ht f hf.symm

  have hcomp : rO (inf_le_right : W' ⊓ V j ≤ V j) (x j) = rO (inf_le_left : W' ⊓ V j ≤ W') f := by
    have h1 := congrArg (PhilipponFiniteCocycle.glueComponent c W' j) hf
    rw [PhilipponFiniteCocycle.glueComponent_smul, PhilipponFiniteCocycle.glueComponent_map, PhilipponFiniteCocycle.glueComponent_glueFrame, rO_rO,
      show rO ((inf_le_inf_right (V j) (inf_le_right : W' ≤ V j)).trans (le_of_eq (inf_comm (V j) (V j)))) (c.u j j) = 1 by
        rw [c.refl, map_one], mul_one] at h1
    rw [h1]
    exact (glueComponent_map_sec c x hx j).symm
  have hu : IsUnit (rO (inf_le_right : W' ⊓ V j ≤ V j) (x j)) := by rw [hcomp]; exact hfu.map _
  have hb := Y.basicOpen_of_isUnit hu
  rw [show rO (inf_le_right : W' ⊓ V j ≤ V j) (x j) = Y.presheaf.map (homOfLE (inf_le_right : W' ⊓ V j ≤ V j)).op (x j) from rfl,
    Scheme.basicOpen_res] at hb
  calc W ⊓ V j = W' ⊓ V j := by rw [hW', inf_assoc, inf_idem]
    _ = W' ⊓ V j ⊓ Y.basicOpen (x j) := hb.symm
    _ ≤ Y.basicOpen (x j) := inf_le_right

theorem eq_of_smul_sec_eq {x x' : ∀ j : Fin r, Γ(Y, V j)} (hx : Compat c x) (hx' : Compat c x') (i : Fin r)
    (hxi : x i = 1) {D : Y.Opens} (hD : V i ≤ D) (g : Γ(Y, D))
    (h : g • (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op (sec c x hx) =
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op (sec c x' hx')) :
    rO hD g = x' i := by

  have h2 := congrArg (PhilipponFiniteCocycle.glueComponent c D i) h
  rw [PhilipponFiniteCocycle.glueComponent_smul, glueComponent_map_sec, glueComponent_map_sec, hxi, map_one, mul_one] at h2

  have hinj := (rO_bijective_of_le_le (inf_le_right : D ⊓ V i ≤ V i) (le_inf hD le_rfl)).1
  apply hinj
  rw [rO_rO]
  exact h2

end GluedPres

open GluedPres in
theorem solution
    (B : Type u) [CommRing B] (Y : Scheme.{u}) (πY : Y ⟶ Spec (CommRingCat.of B))
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j)
    (k : ℕ) (hk : 0 < k) (c : PhilipponFiniteCocycle.UnitCocycle V)
    (hc : ∀ i j : Fin r, c.u i j = Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) ^ k)
    (N : ℕ) (a : Fin (N + 1) → ∀ j : Fin r, Γ(Y, V j))
    (ha : ∀ (α : Fin (N + 1)) (j m : Fin r),
      Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (a α j) =
        Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
          Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (a α m))
    (e : Fin r → Fin (N + 1)) (he : Function.Injective e) (hae : ∀ i j : Fin r, a (e i) j = w j i ^ k) :
    ∃ 𝔓 : (PhilipponFiniteCocycle.glueOfCocycle c).ProjPresentation πY N,
      (∀ (α : Fin (N + 1)) (j : Fin r), PhilipponFiniteCocycle.glueComponent c ⊤ j (𝔓.σ α) =
        Y.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V j ≤ V j)).op (a α j)) ∧
      ∃ hV : ∀ i : Fin r, V i ≤ 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)),
        (∀ i : Fin r, 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)) = V i) ∧
        (∀ (i : Fin r) (α : Fin (N + 1)),
          𝔓.toProj.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)))
              (V i) (hV i)
            (Proj.awayToSection _ (MvPolynomial.X (e i)) (ProjSpace.ratio B N (e i) α)) = a α i) := by
  classical

  have hx : ∀ α : Fin (N + 1), Compat c (a α) := by
    intro α i j
    show rO _ (a α i) = c.u i j * rO _ (a α j)
    rw [hc]
    exact ha α i j
  let σ : Fin (N + 1) → Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤) := fun α => sec c (a α) (hx α)

  have hσe : ∀ i : Fin r,
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (σ (e i)) = PhilipponFiniteCocycle.glueFrame c i := by
    intro i
    refine map_sec_eq_glueFrame c (a (e i)) (hx _) i fun j => ?_
    show rO _ (a (e i) j) = c.u j i
    rw [hae, map_pow, hc]

  let U' : Fin (N + 1) → Y.Opens := fun α => if h : ∃ i, e i = α then V h.choose else ⊥
  have hU'e : ∀ i, U' (e i) = V i := by
    intro i
    have h : ∃ i', e i' = e i := ⟨i, rfl⟩
    simp only [U', dif_pos h]
    rw [he h.choose_spec]
  have hU' : iSup U' = ⊤ := by
    apply top_le_iff.1
    rw [← hcov]
    exact iSup_le fun i => (hU'e i).symm.le.trans (le_iSup U' (e i))
  have hframe : ∀ (α : Fin (N + 1)) (W : Y.Opens), W ≤ U' α →
      Function.Bijective fun g : Γ(Y, W) =>
        g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (σ α) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W)) := by
    intro α W hW
    by_cases h : ∃ i, e i = α
    · obtain ⟨i, rfl⟩ := h
      rw [hU'e] at hW
      exact bijective_smul_of_map_eq_glueFrame c (σ (e i)) i (hσe i) W hW
    · have hbot : U' α = ⊥ := dif_neg h
      rw [hbot] at hW
      exact bijective_smul_bot _ _ W hW
  obtain ⟨𝔓, h𝔓σ, h𝔓U⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top πY (PhilipponFiniteCocycle.glueOfCocycle c) N σ U' hU' hframe
  have hV : ∀ i : Fin r, V i ≤ 𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)) :=
    fun i => (hU'e i).symm.le.trans (h𝔓U (e i))
  refine ⟨𝔓, ?_, hV, ?_, ?_⟩
  ·
    intro α j
    rw [h𝔓σ]
    exact glueComponent_sec c (a α) (hx α) j
  ·
    intro i
    refine le_antisymm ?_ (hV i)
    intro y hy
    have hy' : y ∈ (⊤ : Y.Opens) := trivial
    rw [← hcov] at hy'
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hy'
    have hle := inf_le_basicOpen_of_frame c (a (e i)) (hx (e i))
      (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)))
      (fun W' hW' => by have hf := 𝔓.frame (e i) W' hW'; rw [h𝔓σ] at hf; exact hf) j
    have hyj : y ∈ Y.basicOpen (a (e i) j) := hle ⟨hy, hj⟩
    rw [hae, Y.basicOpen_pow _ hk, hw3] at hyj
    exact hyj.2
  ·
    intro i α
    have hr := 𝔓.app_ratio_smul (e i) α
    rw [h𝔓σ] at hr
    have h1 := eq_of_smul_sec_eq c (hx (e i)) (hx α) i (by rw [hae, hw1, one_pow]) (hV i) _ hr
    exact h1

end S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf
end P2MW

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

namespace AmpleChartsAux

theorem exists_finset_forall_surjective {B C : Type u} [CommRing B] [CommRing C] (f : B →+* C) (hf : f.FiniteType) :
    ∃ s : Finset C, ∀ (D : Type u) [CommRing D] (ψ : D →+* C) (θ : B →+* D), ψ.comp θ = f →
      (∀ x ∈ s, x ∈ Set.range ψ) → Function.Surjective ψ := by
  letI : Algebra B C := f.toAlgebra
  obtain ⟨s, hs⟩ := hf
  refine ⟨s, fun D _ ψ θ hcomp hsub => ?_⟩
  let S : Subalgebra B C :=
    { carrier := Set.range ψ
      mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul ψ a b⟩
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add ψ a b⟩
      algebraMap_mem' := fun r => ⟨θ r, by rw [← RingHom.comp_apply, hcomp]; rfl⟩ }
  have hle : Algebra.adjoin B (s : Set C) ≤ S := Algebra.adjoin_le hsub
  intro c
  have hc : c ∈ Algebra.adjoin B (s : Set C) := by rw [hs]; trivial
  exact hle hc

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

noncomputable def φ (U : X.affineOpens) : CommRingCat.of R ⟶ Γ(X, U.1) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.1 (by simp)

lemma fromSpec_comp (U : X.affineOpens) : U.2.fromSpec ≫ f = Spec.map (φ f U) := by
  rw [φ, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp)).symm

lemma finiteType_φ [LocallyOfFiniteType f] (U : X.affineOpens) : (φ f U).hom.FiniteType := by
  have h := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  rw [φ, CommRingCat.hom_comp]
  exact RingHom.FiniteType.comp h
    (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2)

lemma SpecMap_awayToSection_comp_awayι {n : ℕ} (i : Fin (n + 1)) :
    Spec.map (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) (ProjSpace.X_mem_one R n i) one_pos =
    (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (ProjSpace.X_mem_one R n i) one_pos).fromSpec := by
  have hU := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (ProjSpace.X_mem_one R n i) one_pos
  haveI : IsAffine (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) := hU
  rw [Proj.awayι, IsAffineOpen.fromSpec, ← Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Iso.eq_inv_comp, Proj.basicOpenIsoSpec_hom, IsAffineOpen.isoSpec_hom, Proj.basicOpenToSpec]

end AmpleChartsAux

open AmpleChartsAux in
theorem solution
    (B : Type u) [CommRing B] (Y : Scheme.{u}) (πY : Y ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType πY]
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw2 : ∀ i j k : Fin r,
      Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j) :
    ∃ (qpn : ℕ) (qpι : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) B)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpn = πY := by
  classical

  let Va : Fin r → Y.affineOpens := fun i => ⟨V i, hVaff i⟩

  have hgen := fun i => exists_finset_forall_surjective (φ πY (Va i)).hom (finiteType_φ πY (Va i))
  choose s hs using hgen

  let I : Type u := Σ i : Fin r, ↥(s i)
  haveI : Fintype I := inferInstance
  have hC1 := fun x : I => P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.solution
    V hVaff w hw1 hw2 hw3 x.1 (x.2 : Γ(Y, V x.1))
  choose k₀ hk₀ using hC1
  let k : ℕ := (Finset.univ.sup k₀) + 1
  have hk : 0 < k := Nat.succ_pos _
  have hkx : ∀ x : I, k₀ x ≤ k := fun x => (Finset.le_sup (Finset.mem_univ x)).trans (Nat.le_succ _)
  have ht := fun x : I => hk₀ x k (hkx x)
  choose t ht₁ ht₂ using ht

  let M : ℕ := Fintype.card I
  let eI : I ≃ Fin M := Fintype.equivFin I
  let N : ℕ := r + M
  let a : Fin (N + 1) → ∀ j : Fin r, Γ(Y, V j) := fun α =>
    if h : α.val < r then (fun j => w j ⟨α.val, h⟩ ^ k)
    else if h' : α.val - r < M then t (eI.symm ⟨α.val - r, h'⟩) else fun _ => 0
  let e : Fin r → Fin (N + 1) := fun i => ⟨i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j h; exact Fin.ext (by simpa [e] using congrArg Fin.val h)
  have hae : ∀ i j : Fin r, a (e i) j = w j i ^ k := by
    intro i j; simp only [a, e, dif_pos i.isLt]
  have a_ext : ∀ (x : I) (j : Fin r), a ⟨r + (eI x).val, by omega⟩ j = t x j := by
    intro x j
    simp only [a]
    rw [dif_neg (by omega), dif_pos (by simp)]
    congr 1
    have : (⟨r + (eI x).val - r, by omega⟩ : Fin M) = eI x := Fin.ext (by simp)
    rw [this, Equiv.symm_apply_apply]
  have ha : ∀ (α : Fin (N + 1)) (j m : Fin r),
      Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (a α j) =
        Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
          Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (a α m) := by
    intro α j m
    by_cases h : α.val < r
    · simp only [a, dif_pos h, map_pow]
      rw [hw2 j m ⟨α.val, h⟩, mul_pow]
    · by_cases h' : α.val - r < M
      · simp only [a, dif_neg h, dif_pos h']
        exact ht₂ _ j m
      · simp only [a, dif_neg h, dif_neg h', map_zero, mul_zero]

  let c : PhilipponFiniteCocycle.UnitCocycle V :=
    { u := fun i j => rO (inf_le_left : V i ⊓ V j ≤ V i) (w i j) ^ k
      refl := fun i => by simp only [hw1, map_one, one_pow]
      cocycle := fun i j l => by
        simp only [map_pow, rO_rO, ← mul_pow]
        congr 1
        have h := congrArg (rO (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
          V i ⊓ V j ⊓ V l ≤ V i ⊓ V j)) (hw2 i j l)
        rw [map_mul, rO_rO, rO_rO, rO_rO] at h
        exact h.symm }
  have hc : ∀ i j : Fin r, c.u i j = Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) ^ k :=
    fun _ _ => rfl

  obtain ⟨𝔓, -, hVle, hpre, happ⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.solution
      B Y πY r V hVaff hcov w hw1 hw3 k hk c hc N a ha e he hae

  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B
  let W : Fin r → (Proj 𝒜).Opens := fun i => Proj.basicOpen 𝒜 (MvPolynomial.X (e i))
  have hWaff : ∀ i, IsAffineOpen (W i) := fun i =>
    Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X (e i)) (ProjSpace.X_mem_one B N (e i)) one_pos
  have hYaff : ∀ i, IsAffineOpen (𝔓.toProj ⁻¹ᵁ W i) := fun i => by rw [hpre i]; exact hVaff i
  have hcov' : (⨆ i, 𝔓.toProj ⁻¹ᵁ W i) = ⊤ := by
    have : (fun i => 𝔓.toProj ⁻¹ᵁ W i) = V := funext hpre
    rw [this]; exact hcov
  have hsurj : ∀ i, Function.Surjective (𝔓.toProj.app (W i)) := by
    intro i

    let ψ : HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)) →+* Γ(Y, V i) :=
      (𝔓.toProj.appLE (W i) (V i) (hVle i)).hom.comp (Proj.awayToSection 𝒜 (MvPolynomial.X (e i))).hom

    have hψB : ψ.comp (algebraMap B (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)))) = (φ πY (Va i)).hom := by
      have key : CommRingCat.ofHom (algebraMap B (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)))) ≫
          Proj.awayToSection 𝒜 (MvPolynomial.X (e i)) ≫ 𝔓.toProj.appLE (W i) (V i) (hVle i) = φ πY (Va i) := by
        apply Spec.map_injective
        have h' : ∀ (Z : Scheme.{u}) (g : Proj 𝒜 ⟶ Z),
            Spec.map (Proj.awayToSection 𝒜 (MvPolynomial.X (e i))) ≫
              Proj.awayι 𝒜 (MvPolynomial.X (e i)) (ProjSpace.X_mem_one B N (e i)) one_pos ≫ g = (hWaff i).fromSpec ≫ g :=
          fun Z g => by rw [← Category.assoc, SpecMap_awayToSection_comp_awayι]
        rw [Spec.map_comp, Spec.map_comp, ← fromSpec_comp, ← ProjSpace.awayι_comp_π, Category.assoc, h',
          ← Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec 𝔓.toProj (hWaff i) (hVaff i) (hVle i), Category.assoc,
          𝔓.toProj_π]
      have := congrArg CommRingCat.Hom.hom key
      simp [CommRingCat.hom_comp, RingHom.comp_assoc] at this
      exact this

    have hgen : ∀ x ∈ s i, x ∈ Set.range ψ := by
      intro x hx
      refine ⟨ProjSpace.ratio B N (e i) ⟨r + (eI ⟨i, ⟨x, hx⟩⟩).val, by omega⟩, ?_⟩
      change (𝔓.toProj.appLE (W i) (V i) (hVle i)) (Proj.awayToSection 𝒜 (MvPolynomial.X (e i)) _) = x
      rw [happ i, a_ext ⟨i, ⟨x, hx⟩⟩ i, ht₁]
    have hψ : Function.Surjective ψ := hs i _ ψ _ hψB hgen

    have h1 : Function.Surjective (𝔓.toProj.appLE (W i) (V i) (hVle i)) := Function.Surjective.of_comp hψ
    have h2 : 𝔓.toProj.appLE (W i) (V i) (hVle i) = 𝔓.toProj.app (W i) ≫ Y.presheaf.map (homOfLE (hVle i)).op := rfl
    rw [h2] at h1
    have hbij := rO_bijective_of_le_le (X := Y) (hVle i) (le_of_eq (hpre i))
    intro y
    obtain ⟨x, hx⟩ := h1 (rO (hVle i) y)
    exact ⟨x, hbij.1 hx⟩
  refine ⟨N, 𝔓.toProj, ?_, 𝔓.toProj_π⟩
  exact P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.solution
    𝔓.toProj W hWaff hYaff hcov' hsurj

end S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
end P2MW


set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory Opposite


namespace PhilipponAffineSectionExtension

variable {X : Scheme.{u}}

abbrev res {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

/-- Clearing denominators with one additional positive power preserves
the exact nonvanishing open of the original section. -/
theorem exists_extension {U V : X.Opens} (hU : IsAffineOpen U) (hVU : V ≤ U)
    (f : Γ(X, U)) (hf : X.basicOpen f = V) (s : Γ(X, V)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ t : Γ(X, U),
      res hVU t = res hVU f ^ n * s ∧ X.basicOpen t = X.basicOpen s := by
  letI : Algebra Γ(X, U) Γ(X, V) := (res hVU).toAlgebra
  haveI : IsLocalization.Away f Γ(X, V) :=
    hU.isLocalization_of_eq_basicOpen f (homOfLE hVU) hf.symm
  obtain ⟨⟨a, ⟨_, ⟨m, rfl⟩⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers f) s
  have ha' : res hVU a = res hVU f ^ m * s := by
    simpa only [RingHom.algebraMap_toAlgebra, map_pow, mul_comm] using ha.symm
  refine ⟨m + 1, fun n hn => ⟨a * f ^ (n - m), ?_, ?_⟩⟩
  · rw [map_mul, map_pow, ha', mul_right_comm, ← pow_add, Nat.add_sub_cancel' (by omega : m ≤ n)]
  · have hpos : 0 < n - m := by omega
    have ht : X.basicOpen (a * f ^ (n - m)) ≤ V := by
      rw [X.basicOpen_mul, X.basicOpen_pow _ hpos, hf]
      exact inf_le_right
    have he : res hVU (a * f ^ (n - m)) = res hVU f ^ n * s := by
      rw [map_mul, map_pow, ha', mul_right_comm, ← pow_add, Nat.add_sub_cancel' (by omega : m ≤ n)]
    have hresf : X.basicOpen (res hVU f) = V := by
      change X.basicOpen (X.presheaf.map (homOfLE hVU).op f) = V
      rw [X.basicOpen_res, hf, inf_idem]
    calc
      X.basicOpen (a * f ^ (n - m)) = V ⊓ X.basicOpen (a * f ^ (n - m)) :=
        (inf_eq_right.mpr ht).symm
      _ = X.basicOpen (res hVU (a * f ^ (n - m))) :=
        (X.basicOpen_res (a * f ^ (n - m)) (homOfLE hVU).op).symm
      _ = X.basicOpen (res hVU f ^ n * s) := congrArg (fun z : Γ(X, V) => X.basicOpen z) he
      _ = X.basicOpen (res hVU f) ⊓ X.basicOpen s := by
        rw [X.basicOpen_mul, X.basicOpen_pow _ (by omega : 0 < n)]
      _ = X.basicOpen s := by rw [hresf, inf_eq_right.mpr (X.basicOpen_le s)]

end PhilipponAffineSectionExtension



set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PhilipponAffineSectionExtension


namespace PhilipponTwistedChartCocycle

variable {X : Scheme.{u}} {r : ℕ}

lemma res_res {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (s : Γ(X, U)) :
    res k (res h s) = res (k.trans h) s := by
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE k).op).hom s = _
  rw [← X.presheaf.map_comp]
  rfl

lemma res_injective_of_le {U V : X.Opens} (h : V ≤ U) (h' : U ≤ V) :
    Function.Injective (res h) := by
  intro a b hab
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  change X.presheaf.germ U x hx a = X.presheaf.germ U x hx b
  have hg := congrArg (X.presheaf.germ V x (h' hx)) hab
  simpa only [res, TopCat.Presheaf.germ_res_apply] using hg

/-- Ratios of local frame sections on an affine refinement, together
with the transition functions of the line bundle pulled back from the
base. The ratios are initially defined only over the larger base-chart
overlap. -/
structure LocalData (V O : Fin r → X.Opens) where
  le : ∀ i, V i ≤ O i
  affine : ∀ i, IsAffineOpen (V i)
  weight : ∀ i j, Γ(X, V i)
  weight_self : ∀ i, weight i i = 1
  weight_open : ∀ i j, X.basicOpen (weight i j) = V i ⊓ O j
  weight_mul : ∀ i j k,
    res (inf_le_left : V i ⊓ V j ≤ V i) (weight i k) =
      res (inf_le_left : V i ⊓ V j ≤ V i) (weight i j) *
        res (inf_le_right : V i ⊓ V j ≤ V j) (weight j k)
  ratio : ∀ i j, Γ(X, V i ⊓ O j)
  ratio_self : ∀ i, ratio i i = res (inf_le_left : V i ⊓ O i ≤ V i) 1
  ratio_open : ∀ i j, X.basicOpen (ratio i j) = V i ⊓ V j
  ratio_mul : ∀ i j k,
    res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      (V i ⊓ V j) ⊓ O k ≤ V i ⊓ O k) (ratio i k) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right |>.trans (le j)) :
        (V i ⊓ V j) ⊓ O k ≤ V i ⊓ O j) (ratio i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (V i ⊓ V j) ⊓ O k ≤ V j ⊓ O k) (ratio j k)

variable {V O : Fin r → X.Opens} (d : LocalData V O)

theorem exists_cleared : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ w : ∀ i j, Γ(X, V i), ∀ i j,
      res (inf_le_left : V i ⊓ O j ≤ V i) (w i j) =
        res (inf_le_left : V i ⊓ O j ≤ V i) (d.weight i j) ^ n * d.ratio i j ∧
      X.basicOpen (w i j) = V i ⊓ V j := by
  classical
  have h (i j : Fin r) := exists_extension (d.affine i) inf_le_left
    (d.weight i j) (d.weight_open i j) (d.ratio i j)
  choose N hN using h
  let bound := Finset.univ.sup (fun ij : Fin r × Fin r => N ij.1 ij.2)
  refine ⟨bound, fun n hn => ?_⟩
  have hlarge (i j : Fin r) : N i j ≤ n :=
    (Finset.le_sup (f := fun ij : Fin r × Fin r => N ij.1 ij.2) (Finset.mem_univ (i, j))).trans hn
  choose w hw hO using fun i j => hN i j n (hlarge i j)
  exact ⟨w, fun i j => ⟨hw i j, (hO i j).trans (d.ratio_open i j)⟩⟩

theorem cleared_self (n : ℕ) (w : ∀ i j, Γ(X, V i))
    (hw : ∀ i j, res (inf_le_left : V i ⊓ O j ≤ V i) (w i j) =
      res (inf_le_left : V i ⊓ O j ≤ V i) (d.weight i j) ^ n * d.ratio i j)
    (i : Fin r) : w i i = 1 := by
  apply res_injective_of_le (inf_le_left : V i ⊓ O i ≤ V i) (le_inf le_rfl (d.le i))
  rw [hw, d.weight_self, d.ratio_self, map_one, one_pow, one_mul]

theorem cleared_mul [IsIntegral X] (n : ℕ) (w : ∀ i j, Γ(X, V i))
    (hw : ∀ i j, res (inf_le_left : V i ⊓ O j ≤ V i) (w i j) =
      res (inf_le_left : V i ⊓ O j ≤ V i) (d.weight i j) ^ n * d.ratio i j)
    (hopen : ∀ i j, X.basicOpen (w i j) = V i ⊓ V j) (i j k : Fin r) :
    res (inf_le_left : V i ⊓ V j ≤ V i) (w i k) =
      res (inf_le_left : V i ⊓ V j ≤ V i) (w i j) *
        res (inf_le_right : V i ⊓ V j ≤ V j) (w j k) := by
  classical
  by_cases hk : O k = ⊥
  · have hvk : V k = ⊥ := bot_unique (hk ▸ d.le k)
    have hi : w i k = 0 := (basicOpen_eq_bot_iff (s := w i k)).mp (by rw [hopen, hvk, inf_bot_eq])
    have hj : w j k = 0 := (basicOpen_eq_bot_iff (s := w j k)).mp (by rw [hopen, hvk, inf_bot_eq])
    rw [hi, hj, map_zero, map_zero, mul_zero]
  by_cases hij : V i ⊓ V j = ⊥
  · apply TopCat.Presheaf.section_ext X.sheaf (V i ⊓ V j)
    intro x hx
    have hfalse : x ∈ (⊥ : X.Opens) := hij ▸ hx
    exact hfalse.elim
  have hη (U : X.Opens) (hU : U ≠ ⊥) : genericPoint X ∈ U := by
    apply (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr
    have hnon : (U : Set X).Nonempty := by
      by_contra h
      exact hU ((Opens.not_nonempty_iff_eq_bot U).mp h)
    simpa only [Set.univ_inter] using hnon
  apply map_injective_of_isIntegral X (homOfLE (inf_le_left :
    (V i ⊓ V j) ⊓ O k ≤ V i ⊓ V j)) (H := ⟨⟨genericPoint X, hη _ hij, hη _ hk⟩⟩)
  have hi := congrArg (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    (V i ⊓ V j) ⊓ O k ≤ V i ⊓ O k)) (hw i k)
  have hj := congrArg (res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
    (V i ⊓ V j) ⊓ O k ≤ V j ⊓ O k)) (hw j k)
  have hij' := congrArg (res (le_inf (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right |>.trans (d.le j)) :
    (V i ⊓ V j) ⊓ O k ≤ V i ⊓ O j)) (hw i j)
  have hb := congrArg (res (inf_le_left : (V i ⊓ V j) ⊓ O k ≤ V i ⊓ V j))
    (d.weight_mul i j k)
  simp only [map_mul, map_pow, res_res] at hi hj hij' hb
  change res (inf_le_left : (V i ⊓ V j) ⊓ O k ≤ V i ⊓ V j)
    (res (inf_le_left : V i ⊓ V j ≤ V i) (w i k)) =
    res (inf_le_left : (V i ⊓ V j) ⊓ O k ≤ V i ⊓ V j)
      (res (inf_le_left : V i ⊓ V j ≤ V i) (w i j) *
        res (inf_le_right : V i ⊓ V j ≤ V j) (w j k))
  simp only [map_mul, res_res]
  rw [hi, hij', hj, hb, d.ratio_mul]
  ring

theorem exists_cocycle [IsIntegral X] :
    ∃ (n : ℕ) (w : ∀ i j, Γ(X, V i)),
      (∀ i, w i i = 1) ∧
      (∀ i j k, res (inf_le_left : V i ⊓ V j ≤ V i) (w i k) =
        res (inf_le_left : V i ⊓ V j ≤ V i) (w i j) *
          res (inf_le_right : V i ⊓ V j ≤ V j) (w j k)) ∧
      (∀ i j, X.basicOpen (w i j) = V i ⊓ V j) ∧
      ∀ i j, res (inf_le_left : V i ⊓ O j ≤ V i) (w i j) =
        res (inf_le_left : V i ⊓ O j ≤ V i) (d.weight i j) ^ n * d.ratio i j := by
  obtain ⟨n, hn⟩ := exists_cleared d
  obtain ⟨w, hw⟩ := hn n le_rfl
  exact ⟨n, w, cleared_self d n w (fun i j => (hw i j).1),
    cleared_mul d n w (fun i j => (hw i j).1) (fun i j => (hw i j).2),
    (fun i j => (hw i j).2), (fun i j => (hw i j).1)⟩

end PhilipponTwistedChartCocycle



set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory
open PhilipponTwistedChartCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponTwistedChartProjectivity

theorem exists_immersion {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType π]
    {r : ℕ} {V O : Fin r → X.Opens} (d : LocalData V O) (hV : iSup V = ⊤) :
    ∃ (n : ℕ) (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)),
      IsImmersion j ∧ j ≫ ProjSpace.π R n = π := by
  obtain ⟨n, w, hself, hmul, hopen, -⟩ := exists_cocycle d
  exact P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.solution
    R X π r V d.affine hV w hself hmul hopen

/-- Properness upgrades the constructed immersion to a closed embedding
of the same source with its original structure morphism. -/
theorem exists_closedImmersion {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (CommRingCat.of R)) [IsProper π]
    {r : ℕ} {V O : Fin r → X.Opens} (d : LocalData V O) (hV : iSup V = ⊤) :
    ∃ (n : ℕ) (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)),
      IsClosedImmersion j ∧ j ≫ ProjSpace.π R n = π := by
  obtain ⟨n, j, hj, hover⟩ := exists_immersion π d hV
  letI := hj
  haveI : IsProper (j ≫ ProjSpace.π R n) := by rw [hover]; infer_instance
  haveI : IsProper j := IsProper.of_comp j (ProjSpace.π R n)
  exact ⟨n, j, IsClosedImmersion.of_isPreimmersion j j.isClosedMap.isClosed_range, hover⟩

end PhilipponTwistedChartProjectivity


end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
theorem solution {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (CommRingCat.of R)) [IsProper π]
    {r : ℕ} (V O : Fin r → X.Opens) (hVO : ∀ i, V i ≤ O i)
    (hAffine : ∀ i, IsAffineOpen (V i)) (hCover : iSup V = ⊤)
    (b : ∀ i j, Γ(X, V i)) (hbself : ∀ i, b i i = 1)
    (hbopen : ∀ i j, X.basicOpen (b i j) = V i ⊓ O j)
    (hbmul : ∀ i j k,
      X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b i k) =
        X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b i j) *
          X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b j k))
    (a : ∀ i j, Γ(X, V i ⊓ O j))
    (haself : ∀ i, a i i = X.presheaf.map (homOfLE (inf_le_left : V i ⊓ O i ≤ V i)).op 1)
    (haopen : ∀ i j, X.basicOpen (a i j) = V i ⊓ V j)
    (hamul : ∀ i j k,
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        (V i ⊓ V j) ⊓ O k ≤ V i ⊓ O k)).op (a i k) =
        X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
          ((inf_le_left.trans inf_le_right).trans (hVO j)) :
          (V i ⊓ V j) ⊓ O k ≤ V i ⊓ O j)).op (a i j) *
        X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          (V i ⊓ V j) ⊓ O k ≤ V j ⊓ O k)).op (a j k)) :
    ∃ (n : ℕ) (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)),
      IsClosedImmersion j ∧ j ≫ ProjSpace.π R n = π := by
  let d : PhilipponTwistedChartCocycle.LocalData V O :=
    { le := hVO, affine := hAffine, weight := b, weight_self := hbself,
      weight_open := hbopen, weight_mul := hbmul,
      ratio := a, ratio_self := haself, ratio_open := haopen, ratio_mul := hamul }
  exact PhilipponTwistedChartProjectivity.exists_closedImmersion π d hCover
