-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitVanishingDetection
-- name    : AlgebraicGeometry_EtaleAffineLimitVanishingDetection
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T06:39:17.53757+00:00
-- url     : https://prove2.me/theorems/8c1845bf-466d-4690-a914-8bfaffb4162b
-- title:
--   Detection of vanishing of étale classes by a finite stage
-- statement:
--   Finite-stage detection of zero sections and of sections in the image of a coefficient map implies detection of vanishing in every cohomological degree. Acyclicity of limit sheaves of stagewise injectives supplies dimension shifting.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitAcyclicity
import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitBoundaryMaps
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open PhilipponCompatibleInjectiveSystems PhilipponCompatibleSystemCokernel


namespace PhilipponCompatibleInjectiveResolution

universe u v w

variable {I : Type u} [Category.{u} I]
  {C : I → Type v} [∀ i, Category.{w} (C i)] [∀ i, Abelian (C i)]
  {R : DirectImages C}
  [∀ i, HasProducts.{u} (C i)] [∀ i, EnoughInjectives (C i)]
  [∀ {i j : I} (a : i ⟶ j), PreservesLimitsOfSize.{u, u} (R.functor a)]
  [∀ {i j : I} (a : i ⟶ j), (R.functor a).PreservesInjectiveObjects]
  [∀ {i j : I} (a : i ⟶ j), (R.functor a).PreservesZeroMorphisms]

private structure Embedding (F : System R) where
  target : System R
  incl : Hom F target
  mono (i : I) : Mono (incl.app i)
  injective (i : I) : Injective (target.obj i)

omit [∀ i, Abelian (C i)]
  [∀ {i j : I} (a : i ⟶ j), (R.functor a).PreservesZeroMorphisms] in
private theorem nonempty_embedding (F : System R) : Nonempty (Embedding F) := by
  obtain ⟨G, m, h, hm⟩ := exists_injective_extension R F
  exact ⟨⟨G, ⟨m, hm⟩, fun i => (h i).1, fun i => (h i).2⟩⟩

private def embedding (F : System R) : Embedding F := (nonempty_embedding F).some

variable (F : System R)

private def quotients : ℕ → System R
  | 0 => F
  | n + 1 => cokernelSystem (embedding (quotients n)).incl

/-- The terms of the compatible resolution, before evaluating at a stage. -/
def terms (n : ℕ) : System R := (embedding (quotients F n)).target

private abbrev inclusion (n : ℕ) : Hom (quotients F n) (terms F n) :=
  (embedding (quotients F n)).incl

private abbrev projection (n : ℕ) : Hom (terms F n) (quotients F (n + 1)) :=
  cokernelProjection (inclusion F n)

/-- The differential of the resolution is a map of systems. -/
def differential (n : ℕ) : Hom (terms F n) (terms F (n + 1)) where
  app i := (projection F n).app i ≫ (inclusion F (n + 1)).app i
  naturality {i j} a := by
    rw [Category.assoc, (inclusion F (n + 1)).naturality a, ← Category.assoc,
      (projection F n).naturality a, Category.assoc, Functor.map_comp]

private theorem inclusion_differential (i : I) (n : ℕ) :
    (inclusion F n).app i ≫ (differential F n).app i = 0 := by
  change (inclusion F n).app i ≫ cokernel.π ((inclusion F n).app i) ≫
    (inclusion F (n + 1)).app i = 0
  rw [cokernel.condition_assoc, zero_comp]

private theorem differential_sq (i : I) (n : ℕ) :
    (differential F n).app i ≫ (differential F (n + 1)).app i = 0 := by
  change ((projection F n).app i ≫ (inclusion F (n + 1)).app i) ≫
    (differential F (n + 1)).app i = _
  rw [Category.assoc, inclusion_differential, comp_zero]

/-- The compatible resolution as a single cochain complex of systems. -/
def systemCocomplex : CochainComplex (System R) ℕ :=
  CochainComplex.of (terms F) (differential F) (fun n => Hom.ext (fun i => differential_sq F i n))

@[simp]
theorem systemCocomplex_succ_d (n : ℕ) :
    (systemCocomplex F).d n (n + 1) = differential F n := by
  simp [systemCocomplex]

/-- The augmentation together with the first differential. -/
def initialShortComplex : ShortComplex (System R) :=
  ShortComplex.mk (inclusion F 0) (differential F 0)
    (Hom.ext (fun i => inclusion_differential F i 0))

theorem initial_mono (i : I) : Mono ((initialShortComplex F).f.app i) :=
  (embedding (quotients F 0)).mono i

instance terms_injective (n : ℕ) (i : I) : Injective ((terms F n).obj i) :=
  (embedding (quotients F n)).injective i

end PhilipponCompatibleInjectiveResolution

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponCompatibleSystemCokernel (cokernelProjection)
open PhilipponCompatibleInjectiveResolution (initialShortComplex initial_mono terms terms_injective)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleLimitExactness (atStageSheaf)
open PhilipponEtaleLimitSheaf (limitSheaf)
open PhilipponEtaleLimitFunctor (limitFunctor)
open PhilipponEtaleLimitShortExact (shortExact_limit)
open PhilipponEtaleLimitCohomologyTransport (stageRestriction stageRestriction_boundary)
open PhilipponEtaleStageCohomology (transition transition_boundary)
open PhilipponEtaleLimitAcyclicity (acyclic)


namespace PhilipponEtaleLimitVanishingDetection

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)

private abbrev Sys := System (directImages D)

private def embeddingSequence (F : Sys (D := D)) : ShortComplex (Sys (D := D)) :=
  let f := (initialShortComplex F).f
  ShortComplex.mk f (cokernelProjection f) (by
    apply PhilipponCompatibleSystemCokernel.Hom.ext
    intro i
    exact cokernel.condition (f.app i))

private theorem embeddingSequence_shortExact (F : Sys (D := D)) (i : I) :
    ((embeddingSequence F).map (atStageSheaf i)).ShortExact := by
  let f := (initialShortComplex F).f
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (f.app i))
    (initial_mono F i) (inferInstanceAs (Epi (cokernel.π (f.app i))))

/-- Detection in degree zero, including detection of a section in the
image, implies finite-stage detection in every cohomological degree. -/
theorem exists_transition_eq_zero
    (h₀ : ∀ (F : Sys (D := D)) (i : I) (x : (F.obj i).H 0),
      stageRestriction c hc F i 0 x = 0 → ∃ (j : I) (a : j ⟶ i), transition a F 0 x = 0)
    (hImage : ∀ {F G : Sys (D := D)} (f : F ⟶ G) (i : I) (x : (G.obj i).H 0)
      (y : (limitSheaf c hc F).H 0),
      stageRestriction c hc G i 0 x = Sheaf.H.map ((limitFunctor c hc).map f) 0 y →
      ∃ (j : I) (a : j ⟶ i) (z : (F.obj j).H 0), transition a G 0 x = Sheaf.H.map (f.app j) 0 z)
    (q : ℕ) (F : Sys (D := D)) (i : I) (x : (F.obj i).H q)
    (hx : stageRestriction c hc F i q x = 0) :
    ∃ (j : I) (a : j ⟶ i), transition a F q x = 0 := by
  induction q generalizing F i with
  | zero => exact h₀ F i x hx
  | succ n ih =>
    let S := embeddingSequence F
    let hS (k : I) : (S.map (atStageSheaf k)).ShortExact := embeddingSequence_shortExact F k
    let hs := shortExact_limit c hc S hS
    let : ∀ k, Injective (S.X₂.obj k) := fun k => terms_injective F 0 k
    have hxi : x.comp (Ext.mk₀ (S.f.app i)) (add_zero (n + 1)) = 0 :=
      Ext.eq_zero_of_injective _
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ (hS i) x hxi rfl
    have hy₀ : (stageRestriction c hc S.X₃ i n y).comp hs.extClass rfl = 0 := by
      rw [← stageRestriction_boundary c hc S hS i n y, hy]
      exact hx
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hs (stageRestriction c hc S.X₃ i n y) rfl hy₀
    cases n with
    | zero =>
      obtain ⟨j, a, w, hw⟩ := hImage S.g i y z hz.symm
      refine ⟨j, a, ?_⟩
      change transition a S.X₁ (0 + 1) x = 0
      calc
        _ = transition a S.X₁ (0 + 1) (y.comp (hS i).extClass rfl) := congrArg _ hy.symm
        _ = (transition a S.X₃ 0 y).comp (hS j).extClass rfl := transition_boundary a S hS 0 y
        _ = (Sheaf.H.map (S.g.app j) 0 w).comp (hS j).extClass rfl := by rw [hw]
        _ = 0 := by
          change (w.comp (Ext.mk₀ (S.map (atStageSheaf j)).g) (add_zero 0)).comp (hS j).extClass rfl = _
          simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
    | succ n =>
      have hz₀ : z = 0 := (acyclic c hc S.X₂ n).elim _ _
      rw [hz₀, Ext.zero_comp] at hz
      obtain ⟨j, a, ha⟩ := ih S.X₃ i y hz.symm
      refine ⟨j, a, ?_⟩
      change transition a S.X₁ ((n + 1) + 1) x = 0
      calc
        _ = transition a S.X₁ ((n + 1) + 1) (y.comp (hS i).extClass rfl) := congrArg _ hy.symm
        _ = (transition a S.X₃ (n + 1) y).comp (hS j).extClass rfl := transition_boundary a S hS (n + 1) y
        _ = 0 := by rw [ha, Ext.zero_comp]

end PhilipponEtaleLimitVanishingDetection

end

end


