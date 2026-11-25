-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitResolution
-- name    : AlgebraicGeometry_EtaleAffineLimitResolution
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T05:13:34.306365+00:00
-- url     : https://prove2.me/theorems/2d68bd82-a1b1-428a-a0eb-9d59f130b46a
-- title:
--   Compatible resolutions for étale cohomology of affine inverse limits
-- statement:
--   Compatible systems admit resolutions by systems of injective sheaves. Taking the limit sheaf gives an acyclic resolution, and its global sections are the filtered colimit of the sections of the stage resolutions.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitAcyclicity
import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitFunctor
import Definitions.Def_AlgebraicGeometry_EtaleModeledCech
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
namespace PhilipponEtaleAcyclicCohomology
universe u
private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

/-- The identity chart is terminal in the small étale site. -/
def isTerminal (X : Scheme.{u}) : IsTerminal (terminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

/-- The base change of the terminal chart is the terminal chart. -/
def terminalComparison {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (baseChange f).obj (terminal X) ≅ terminal Y := by
  have : PreservesFiniteLimits (baseChange f) :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ f))
  exact (IsTerminal.isTerminalObj (baseChange f) _ (isTerminal X)).uniqueUpToIso (isTerminal Y)

end PhilipponEtaleAcyclicCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleBaseChangeMap (stalkToFiberSections stalkOfHigherImageIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)


namespace PhilipponEtalePullbackResolution

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

local instance (X : Scheme.{u}) : (globalSections X).Additive where
  map_add := rfl

local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullbackSheaves f).Additive :=
  (pullbackAdjunction f).left_adjoint_additive

private theorem extLarge (X : Scheme.{u}) : HasExt.{u + 1} (Ab X) := by
  have h (P Q : Ab X) (n : ℕ) : Small.{u + 1} (Ext.{u} P Q n) :=
    small_succ (Ext.{u} P Q n)
  exact (hasExt_iff_small_ext.{u + 1, u} (Ab X)).mpr h

private def extLift {X : Scheme.{u}} [HasExt.{u + 1} (Ab X)] (P Q : Ab X) (n : ℕ) :
    Ext.{u} P Q n ≃+ Ext.{u + 1} P Q n :=
  letI := HasDerivedCategory.standard (Ab X)
  Ext.homAddEquiv.trans Ext.homAddEquiv.symm

/-- An acyclic resolution computes positive étale cohomology by the
homology of its global sections. -/
def cohomologyEquivAcyclicResolution {X : Scheme.{u}} (F : Ab X)
    (K : CochainComplex (Ab X) ℕ) (e₀ : F ≅ K.cycles 0)
    (hExact : ∀ j : ℕ, K.ExactAt (j + 1))
    (hAcyclic : ∀ j k : ℕ, Subsingleton ((K.X j).H (k + 1)))
    (n : ℕ) : F.H (n + 1) ≃+
      (((globalSections X).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology (n + 1) := by
  letI : HasExt.{u + 1} (Ab X) := extLarge X
  let P := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  have hExt (j k : ℕ) : Subsingleton (Ext.{u + 1} P (K.X j) (k + 1)) := by
    have : Subsingleton (Ext.{u} P (K.X j) (k + 1)) := hAcyclic j k
    exact (extLift P (K.X j) (k + 1)).symm.injective.subsingleton
  let e := PhilipponAcyclicResolution.extEquivAcyclicComplex P F K e₀ hExact hExt n
  exact (extLift P F (n + 1)).trans
    (e.trans (PhilipponEtaleDerivedSections.homologyEquivGlobalSections K (n + 1)))

end PhilipponEtalePullbackResolution

end

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

private theorem exact_inclusion (i : I) (n : ℕ) :
    (ShortComplex.mk ((inclusion F n).app i) ((differential F n).app i)
      (inclusion_differential F i n)).Exact := by
  let σ := ShortComplex.mk ((inclusion F n).app i) ((projection F n).app i) (cokernel.condition _)
  let τ := ShortComplex.mk ((inclusion F n).app i) ((differential F n).app i)
    (inclusion_differential F i n)
  let φ : σ ⟶ τ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (inclusion F (n + 1)).app i
      comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
      comm₂₃ := by simp [σ, τ, differential] }
  let : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
  let : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  let : Mono φ.τ₃ := (embedding (quotients F (n + 1))).mono i
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp (ShortComplex.exact_cokernel _)

/-- The first pair is exact at every stage. -/
theorem initial_exact (i : I) :
    (ShortComplex.mk ((initialShortComplex F).f.app i) ((initialShortComplex F).g.app i)
      (inclusion_differential F i 0)).Exact :=
  exact_inclusion F i 0

/-- The differentials are exact at every stage in positive degrees. -/
theorem exact_differential (i : I) (n : ℕ) :
    (ShortComplex.mk ((differential F n).app i) ((differential F (n + 1)).app i)
      (differential_sq F i n)).Exact := by
  let σ := ShortComplex.mk ((differential F n).app i) ((differential F (n + 1)).app i)
    (differential_sq F i n)
  let τ := ShortComplex.mk ((inclusion F (n + 1)).app i) ((differential F (n + 1)).app i)
    (inclusion_differential F i (n + 1))
  let φ : σ ⟶ τ :=
    { τ₁ := (projection F n).app i
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  let : Epi φ.τ₁ := inferInstanceAs (Epi (cokernel.π ((inclusion F n).app i)))
  let : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  let : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr (exact_inclusion F i (n + 1))

/-- The cochain complex at each stage of the compatible resolution. -/
def cocomplex (i : I) : CochainComplex (C i) ℕ :=
  CochainComplex.of (fun n => (terms F n).obj i) (fun n => (differential F n).app i)
    (differential_sq F i)

@[simp]
theorem cocomplex_succ_d (i : I) (n : ℕ) :
    (cocomplex F i).d n (n + 1) = (differential F n).app i := by
  simp [cocomplex]

/-- A transition acts on the compatible cochain complexes term by term. -/
def transition {i j : I} (a : i ⟶ j) :
    cocomplex F j ⟶ ((R.functor a).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cocomplex F i) :=
  CochainComplex.ofHom (fun n => (terms F n).map a) (fun n => by
    change (terms F n).map a ≫ (R.functor a).map ((cocomplex F i).d n (n + 1)) =
      (cocomplex F j).d n (n + 1) ≫ (terms F (n + 1)).map a
    rw [cocomplex_succ_d, cocomplex_succ_d]
    exact ((differential F n).naturality a).symm)

private def augmentation (i : I) :
    (CochainComplex.single₀ (C i)).obj (F.obj i) ⟶ cocomplex F i :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨(inclusion F 0).app i, by
    rw [cocomplex_succ_d]
    exact inclusion_differential F i 0⟩

private theorem exactAt_succ (i : I) (n : ℕ) :
    (cocomplex F i).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  let σ := ShortComplex.mk ((differential F n).app i) ((differential F (n + 1)).app i)
    (differential_sq F i n)
  let e : σ ≅ (cocomplex F i).sc' n (n + 1) (n + 2) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', σ])
      (by simp [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', σ])
  exact ShortComplex.exact_of_iso e (exact_differential F i n)

set_option maxHeartbeats 1000000 in
/-- The compatible complex resolves the original object at every stage. -/
def resolution (i : I) : InjectiveResolution (F.obj i) where
  cocomplex := cocomplex F i
  injective n := (embedding (quotients F n)).injective i
  ι := augmentation F i
  quasiIso := ⟨fun n => by
    cases n
    · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
          ⟨exact_inclusion F i 0, (embedding (quotients F 0)).mono i⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [augmentation]) (by simp)
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt]
      · apply exactAt_succ
      · apply CochainComplex.exactAt_succ_single_obj⟩

@[simp]
theorem resolution_ι_f_zero (i : I) :
    (resolution F i).ι.f 0 = (inclusion F 0).app i :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero ..

end PhilipponCompatibleInjectiveResolution

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponCompatibleSystemCokernel (Hom)
open PhilipponCompatibleInjectiveResolution (terms differential systemCocomplex
  systemCocomplex_succ_d initialShortComplex initial_exact initial_mono exact_differential)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleLimitFunctor (limitFunctor)
open PhilipponEtaleLimitExactness (atStageSheaf exact_limit mono_limitMap)
open PhilipponEtaleLimitSheaf (limitSheaf)
open PhilipponEtaleLimitAcyclicity (acyclic)
open PhilipponEtaleAcyclicCohomology (globalSections)


namespace PhilipponEtaleLimitResolution

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}

/-- Evaluating the system resolution recovers the chosen injective
resolution at a stage. -/
def atStageIso (F : System (directImages D)) (i : I) :
    ((atStageSheaf i).mapHomologicalComplex (ComplexShape.up ℕ)).obj (systemCocomplex F) ≅
      (PhilipponCompatibleInjectiveResolution.resolution F i).cocomplex := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro n m h
  have hm : n + 1 = m := h
  subst m
  simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  change (PhilipponCompatibleInjectiveResolution.cocomplex F i).d n (n + 1) = _
  rw [PhilipponCompatibleInjectiveResolution.cocomplex_succ_d]
  exact (congrArg (fun f => (atStageSheaf i).map f) (systemCocomplex_succ_d F n)).symm

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
  (F : System (directImages D))

/-- The compatible injective resolution after forming limit sheaves. -/
def cocomplex : CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) ℕ :=
  ((limitFunctor c hc).mapHomologicalComplex (ComplexShape.up ℕ)).obj (systemCocomplex F)

@[simp]
theorem d_succ (n : ℕ) :
    (cocomplex c hc F).d n (n + 1) = (limitFunctor c hc).map (differential F n) :=
  congrArg (fun f => (limitFunctor c hc).map f) (systemCocomplex_succ_d F n)

/-- The limit resolution is exact in positive degrees. -/
theorem exactAt (n : ℕ) : (cocomplex c hc F).ExactAt (n + 1) := by
  let B := systemCocomplex F
  let S := B.sc' n (n + 1) (n + 2)
  have hS (i : I) : (S.map (atStageSheaf i)).Exact := by
    have hz : (differential F n).app i ≫ (differential F (n + 1)).app i = 0 := by
      simpa only [PhilipponCompatibleInjectiveResolution.cocomplex_succ_d] using
        (PhilipponCompatibleInjectiveResolution.cocomplex F i).d_comp_d n (n + 1) (n + 2)
    let T := ShortComplex.mk ((differential F n).app i) ((differential F (n + 1)).app i) hz
    let e : T ≅ S.map (atStageSheaf i) :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [S, B, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', T, atStageSheaf])
        (by simp [S, B, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', T, atStageSheaf])
    exact ShortComplex.exact_of_iso e (exact_differential F i n)
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  exact exact_limit c hc S hS

/-- The degree-zero cycles recover the original limit sheaf. -/
def toCycles : limitSheaf c hc F ≅ (cocomplex c hc F).cycles 0 := by
  let S := initialShortComplex F
  let T := S.map (limitFunctor c hc)
  let K := cocomplex c hc F
  have hS (i : I) : (S.map (atStageSheaf i)).Exact := initial_exact F i
  let hm : Mono T.f := mono_limitMap c hc S.f (initial_mono F)
  have hT := (exact_limit c hc S hS).fIsKernel
  have hg : T.g = K.d 0 1 := (d_succ c hc F 0).symm
  have hi : K.iCycles 0 ≫ T.g = 0 := by rw [hg]; exact K.iCycles_d 0 1
  have hK (g : K.X 0 ⟶ K.X 1) (e : g = K.d 0 1) (hz : K.iCycles 0 ≫ g = 0) :
      IsLimit (KernelFork.ofι (K.iCycles 0) hz) := by
    subst g
    exact K.cyclesIsKernel (j := 1) 0 (by simp)
  exact hT.conePointUniqueUpToIso (hK T.g hg hi)

/-- The cohomology of the limit sheaf is computed by the global sections
of the limit resolution. -/
def cohomologyEquiv (n : ℕ) :
    (limitSheaf c hc F).H (n + 1) ≃+
      (((globalSections c.pt).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cocomplex c hc F)).homology (n + 1) :=
  PhilipponEtalePullbackResolution.cohomologyEquivAcyclicResolution _
    (cocomplex c hc F) (toCycles c hc F) (exactAt c hc F)
    (fun j k => acyclic c hc (terms F j) k) n

end PhilipponEtaleLimitResolution

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (StageChart toLimit)
open PhilipponEtaleChartLimitDiagram (stageCharts)
open PhilipponEtaleLimitAffinePresheaf (affineCharts AffineModel)
open PhilipponEtaleLimitRepresentatives (modelFunctor modelLimitSectionsIso)
open PhilipponEtaleLimitFunctor (limitFunctor)
open PhilipponEtaleLimitExactness (atStageSheaf)
open PhilipponEtaleModeledSections (reversedBaseChangeIso)
open PhilipponEtaleAcyclicCohomology (globalSections terminalComparison)


namespace PhilipponEtaleLimitGlobalSections

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (i : I)

private def terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

private def limitTerminal : (affineCharts c.pt).FullSubcategory :=
  ⟨terminal c.pt, Scheme.isAffine_of_isLimit c hc⟩

private def terminalModel : AffineModel c (limitTerminal c hc).obj where
  chart := ⟨i, terminal (D.obj i)⟩
  affine := inferInstanceAs (IsAffine (D.obj i))
  comparison := (terminalComparison (c.π.app i)).symm

/-- The diagram computing global sections on the limit. -/
def sectionsDiagram : System (directImages D) ⥤ (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  modelFunctor c (limitTerminal c hc) (terminalModel c hc i)

instance : (sectionsDiagram c hc i).PreservesZeroMorphisms :=
  inferInstanceAs ((modelFunctor c (limitTerminal c hc) (terminalModel c hc i)).PreservesZeroMorphisms)

/-- The global sections of the limit sheaf are the colimit of this
diagram, naturally in the system. -/
def colimIso : sectionsDiagram c hc i ⋙ colim ≅ limitFunctor c hc ⋙ globalSections c.pt :=
  modelLimitSectionsIso c (limitTerminal c hc) (terminalModel c hc i) hc

/-- Each term of the diagram is the corresponding stage's global sections. -/
def evalIso (j : (Over i)ᵒᵖ) :
    sectionsDiagram c hc i ⋙ (evaluation _ _).obj j ≅
      atStageSheaf j.unop.left ⋙ globalSections (D.obj j.unop.left) := by
  let A : StageChart D := ⟨i, terminal (D.obj i)⟩
  let B := (stageCharts A).obj j.unop
  let r := D.map j.unop.hom
  let e : B.etale ≅ terminal (D.obj j.unop.left) :=
    (reversedBaseChangeIso r).app A.etale ≪≫ terminalComparison r
  refine NatIso.ofComponents (fun F => (F.obj j.unop.left).obj.mapIso e.symm.op) ?_
  intro F G f
  exact ((f.app j.unop.left).hom.naturality e.symm.op.hom).symm

end PhilipponEtaleLimitGlobalSections

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponCompatibleInjectiveResolution (systemCocomplex resolution)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleAcyclicCohomology (globalSections isTerminal)
open PhilipponEtaleLimitSheaf (limitSheaf)
open PhilipponEtaleLimitGlobalSections (sectionsDiagram)
open PhilipponEtaleLimitResolution (atStageIso cohomologyEquiv)


namespace PhilipponEtaleLimitCohomology

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (i : I) (F : System (directImages D))

private abbrev shape := ComplexShape.up ℕ

private abbrev sectionComplex : CochainComplex ((Over i)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  ((sectionsDiagram c hc i).mapHomologicalComplex shape).obj (systemCocomplex F)

/-- The cohomology diagram obtained from a compatible injective resolution. -/
def cohomologyDiagram (q : ℕ) : (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (sectionComplex c hc i F).homology q

/-- Its value at a stage is the usual étale cohomology at that stage. -/
def cohomologyStageIso (j : (Over i)ᵒᵖ) (q : ℕ) :
    (cohomologyDiagram c hc i F q).obj j ≅ AddCommGrpCat.of ((F.obj j.unop.left).H q) := by
  let K := sectionComplex c hc i F
  let E := (evaluation (Over i)ᵒᵖ AddCommGrpCat.{u}).obj j
  let e₀ := ((K.sc q).mapHomologyIso E).symm
  let X := D.obj j.unop.left
  let B := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} shape q
  let e₁ := (NatIso.mapHomologicalComplex (PhilipponEtaleLimitGlobalSections.evalIso c hc i j)
    shape).app (systemCocomplex F)
  let e₂ := ((globalSections X).mapHomologicalComplex shape).mapIso (atStageIso F j.unop.left)
  let e₃ : B.obj (((globalSections X).mapHomologicalComplex shape).obj
        (resolution F j.unop.left).cocomplex) ≅ AddCommGrpCat.of ((F.obj j.unop.left).H q) :=
    (PhilipponEtaleDerivedSections.cohomologyEquivResolution
      (F.obj j.unop.left) (resolution F j.unop.left) q).symm.toAddCommGrpIso
  exact e₀ ≪≫ B.mapIso (e₁ ≪≫ e₂) ≪≫ e₃

/-- The positive cohomology of the limit sheaf is the colimit of the
stage cohomology diagram. -/
def cohomologyColimIso (q : ℕ) :
    colimit (cohomologyDiagram c hc i F (q + 1)) ≅
      AddCommGrpCat.of ((limitSheaf c hc F).H (q + 1)) := by
  let K := sectionComplex c hc i F
  let E := colim (J := (Over i)ᵒᵖ) (C := AddCommGrpCat.{u})
  let e₀ := ((K.sc (q + 1)).mapHomologyIso E).symm
  let B := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} shape (q + 1)
  let e₁ := (NatIso.mapHomologicalComplex (PhilipponEtaleLimitGlobalSections.colimIso c hc i)
    shape).app (systemCocomplex F)
  let e₂ : B.obj (((globalSections c.pt).mapHomologicalComplex shape).obj
        (PhilipponEtaleLimitResolution.cocomplex c hc F)) ≅
      AddCommGrpCat.of ((limitSheaf c hc F).H (q + 1)) :=
    (cohomologyEquiv c hc F q).symm.toAddCommGrpIso
  exact e₀ ≪≫ B.mapIso e₁ ≪≫ e₂

/-- If positive-degree cohomology vanishes at every stage, it vanishes
on the limit sheaf of the compatible system. -/
theorem subsingleton_H (q : ℕ) (h : ∀ j, Subsingleton ((F.obj j).H (q + 1))) :
    Subsingleton ((limitSheaf c hc F).H (q + 1)) := by
  let i := (IsCofiltered.nonempty (C := I)).some
  let G := cohomologyDiagram c hc i F (q + 1)
  have hG : IsZero G := Functor.isZero G (fun j => by
    let : Subsingleton ((F.obj j.unop.left).H (q + 1)) := h j.unop.left
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr
      (cohomologyStageIso c hc i F j (q + 1)).addCommGroupIsoToAddEquiv.injective.subsingleton)
  have hz : IsZero (colimit G) :=
    (colim (J := (Over i)ᵒᵖ) (C := AddCommGrpCat.{u})).map_isZero hG
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (hz.of_iso (cohomologyColimIso c hc i F q).symm)

/-- Vanishing in any fixed degree passes from the stages to the limit. -/
theorem subsingleton_H_all (q : ℕ) (h : ∀ j, Subsingleton ((F.obj j).H q)) :
    Subsingleton ((limitSheaf c hc F).H q) := by
  cases q with
  | succ q => exact subsingleton_H c hc F q h
  | zero =>
    let i := (IsCofiltered.nonempty (C := I)).some
    let G := (sectionsDiagram c hc i).obj F
    have hG : IsZero G := Functor.isZero G (fun j => by
      let X := D.obj j.unop.left
      let T := F.obj j.unop.left
      let : Subsingleton (T.H 0) := h j.unop.left
      let e := (Sheaf.H.equiv₀ T (isTerminal X)).symm
      let : Subsingleton ((PhilipponEtaleLimitExactness.atStageSheaf j.unop.left ⋙ globalSections X).obj F) :=
        e.injective.subsingleton
      let a := ((PhilipponEtaleLimitGlobalSections.evalIso c hc i j).app F).addCommGroupIsoToAddEquiv
      exact AddCommGrpCat.isZero_iff_subsingleton.mpr a.injective.subsingleton)
    let a := (PhilipponEtaleLimitGlobalSections.colimIso c hc i).app F
    have hz : IsZero (colimit G) := (colim (J := (Over i)ᵒᵖ) (C := AddCommGrpCat.{u})).map_isZero hG
    let : Subsingleton ((limitSheaf c hc F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))) :=
      AddCommGrpCat.isZero_iff_subsingleton.mp (hz.of_iso a.symm)
    exact (Sheaf.H.equiv₀ (limitSheaf c hc F) (isTerminal c.pt)).injective.subsingleton

end PhilipponEtaleLimitCohomology

end

end


