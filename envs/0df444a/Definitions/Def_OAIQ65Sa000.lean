-- Prove2me | Definitions.Def_OAIQ65Sa000
-- name    : OAIQ65Sa000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:25:47.498203+00:00
-- url     : https://prove2.me/theorems/d9e6855d-e95a-4aa1-bdf3-0ff18b80bca5
-- title:
--   Definitions bundle OAIQ65Sa000 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 525 declarations of OpenAI's Lean: 238 definitions, 3 inductive types or structures, 46 instances and 238 theorems. The definitions and types are `OAI.AdditiveFinite.I`, `OAI.AdditiveFinite.basis`, `OAI.AdditiveFinite.incl`, `OAI.AdditiveFinite.proj`, `OAI.AugmentedSplit.U`, `OAI.BarFinitePower.LowConnected`, `OAI.BarFinitePower.coefficientReindex`, `OAI.BarFinitePower.coordinateSplit`, `OAI.BarFinitePower.coordinates`, `OAI.BarFinitePower.doubleProject`, `OAI.BarFinitePower.evaluate`, `OAI.BarFinitePower.finSuccIso`, `OAI.BarFinitePower.finZeroIso`, `OAI.BarFinitePower.lift`, `OAI.BarFinitePower.liftRows`, `OAI.BarFinitePower.nervePiIso`, `OAI.BarFinitePower.power`, `OAI.BarFinitePower.project`, `OAI.BarFinitePower.reindexIso`, `OAI.BarFinitePower.swap`, `OAI.BarFinitePower.swapEquiv`, `OAI.BarFinitePower.vectorSplit`, `OAI.BiResolution.augmentation`, `OAI.BiResolution.augmentedAt`, `OAI.BiResolution.aug₀`, `OAI.BiResolution.c`, `OAI.BiResolution.chains`, `OAI.BiResolution.chainsAt`, `OAI.BiResolution.complex`, `OAI.BiResolution.complexAt`, `OAI.BiResolution.complexAtEquiv`, `OAI.BiResolution.complexAtIso`, `OAI.BiResolution.evalComplexIso`, `OAI.BiResolution.evalTotalIso`, `OAI.BiResolution.extra`, `OAI.BiResolution.pi`, `OAI.BiResolution.point`, `OAI.BiResolution.pointAugmentation`, `OAI.BiResolution.pointAugmented`, `OAI.BiResolution.pointExtra` and 201 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Configurations_FiberAddition`, `SimpleAmenable_Homology_AssemblyMap`, `SimpleAmenable_Homology_BiProjective`, `SimpleAmenable_Homology_BiResolution`, `SimpleAmenable_Homology_CanonicalProduct`, `SimpleAmenable_Homology_CoefficientUCT`, `SimpleAmenable_Homology_ConcreteHomology`, `SimpleAmenable_Homology_ConeHomology`, `SimpleAmenable_Homology_ConnectedProduct`, `SimpleAmenable_Homology_ConstantSplit`, `SimpleAmenable_Homology_E2Boundary`, `SimpleAmenable_Homology_FilteredHomology`, `SimpleAmenable_Homology_FreeChains`, `SimpleAmenable_Homology_ModelAssembly`, `SimpleAmenable_Homology_PowerEquivalence`, `SimpleAmenable_Homology_ProductChains`, `SimpleAmenable_Homology_ProductNatural`, `SimpleAmenable_Homology_TensorJoint`, `SimpleAmenable_Homology_TotalComparison`, `SimpleAmenable_Homology_TotalFiltration`, `SimpleAmenable_Homology_TotalFiniteness`, `SimpleAmenable_Homology_TotalProjection`, `SimpleAmenable_Homology_TotalSingle`, `SimpleAmenable_Simplicial_DiagonalComparison`, `SimpleAmenable_Simplicial_DiagonalResolution`, `SimpleAmenable_Simplicial_EZNatural`, `SimpleAmenable_Simplicial_EilenbergZilber`, `SimpleAmenable_Simplicial_FiberSum`, `SimpleAmenable_Simplicial_FinitePowerConnected`, `SimpleAmenable_Simplicial_FinitePowerGeneral`, `SimpleAmenable_Simplicial_FinitePowerLow`, `SimpleAmenable_Simplicial_IntervalBar`, `SimpleAmenable_Simplicial_IntervalEquivalence`, `SimpleAmenable_Simplicial_IntervalExtension`, `SimpleAmenable_Simplicial_IntervalFunctor`, `SimpleAmenable_Simplicial_IntervalMap`, `SimpleAmenable_Simplicial_IntervalPullback`, `SimpleAmenable_Simplicial_IntervalTensor`, `SimpleAmenable_Simplicial_IteratedBarMaps`, `SimpleAmenable_Simplicial_PowerDiagonal`, `SimpleAmenable_Simplicial_RestrictedMonoidal`, `SimpleAmenable_Simplicial_SimplicialAugment`, `SimpleAmenable_Simplicial_SimplicialConnectedProduct`, `SimpleAmenable_Simplicial_SimplicialH0`, `SimpleAmenable_Simplicial_StageCoordinateMaps`, `SimpleAmenable_Simplicial_StageTripleHomology`, `SimpleAmenable_Simplicial_TripleComposition`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa004`, `OAIQ65Sa005` and `OAIQ65Sa006`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ065_SA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ConcreteHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits HomologicalComplex
namespace ConcreteHomology

universe u
variable {R : Type u} [CommRing R]
abbrev c := ComplexShape.down ℕ
abbrev CC := ChainComplex (ModuleCat.{u} R) ℕ
variable (K L : CC (R:=R)) (n : ℕ)
def S := K.sc' (n+1) n (n-1)
abbrev Cycles := LinearMap.ker ((K.d n (n-1)).hom)
abbrev boundary := (S K n).moduleCatToCycles
abbrev H := Cycles K n ⧸ LinearMap.range (boundary K n)
def π : Cycles K n →ₗ[R] H K n := (LinearMap.range (boundary K n)).mkQ

@[simp] lemma π_eq_zero (x : Cycles K n) : π K n x=0 ↔ ∃ y, boundary K n y=x :=
  Submodule.Quotient.mk_eq_zero _

lemma π_surjective : Function.Surjective (π K n) :=
  Submodule.mkQ_surjective (LinearMap.range (boundary K n))

noncomputable def sFunctor : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R where
  obj T := T.moduleCatLeftHomologyData.H
  map f := ShortComplex.leftHomologyMap' f _ _
  map_id _ := ShortComplex.leftHomologyMap'_id _
  map_comp _ _ := ShortComplex.leftHomologyMap'_comp _ _ _ _ _

noncomputable def sIso : ShortComplex.homologyFunctor (ModuleCat.{u} R) ≅ sFunctor (R:=R) :=
  NatIso.ofComponents (fun T => T.moduleCatHomologyIso) (fun f =>
    (ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality f _ _).symm)

noncomputable def functor (n : ℕ) : CC (R:=R) ⥤ ModuleCat.{u} R :=
  shortComplexFunctor' _ c (n+1) n (n-1) ⋙ sFunctor

instance instAdditiveCCModuleCatFunctor : (functor (R:=R) n).Additive where
  map_add {X Y} f g := by
    change ShortComplex.leftHomologyMap' ((shortComplexFunctor' (ModuleCat.{u} R) c (n+1) n (n-1)).map (f+g)) (S X n).moduleCatLeftHomologyData (S Y n).moduleCatLeftHomologyData = _
    have h : (shortComplexFunctor' (ModuleCat.{u} R) c (n+1) n (n-1)).map (f+g) =
        (shortComplexFunctor' (ModuleCat.{u} R) c (n+1) n (n-1)).map f +
        (shortComplexFunctor' (ModuleCat.{u} R) c (n+1) n (n-1)).map g := by
      ext <;> rfl
    rw [h]
    exact ShortComplex.leftHomologyMap'_add (S X n).moduleCatLeftHomologyData
      (S Y n).moduleCatLeftHomologyData

lemma prev (n : ℕ) : c.prev n=n+1 := c.prev_eq' rfl
lemma next (n : ℕ) : c.next n=n-1 := by
  cases n with
  | zero => exact c.next_eq_self' 0 (by intro k; change ¬k+1=0; omega)
  | succ n => exact c.next_eq' rfl

noncomputable def naturalIso (n : ℕ) : homologyFunctor (ModuleCat.{u} R) c n ≅ functor n :=
  homologyFunctorIso' _ c (n+1) n (n-1) (prev n) (next n) ≪≫
    Functor.isoWhiskerLeft _ sIso

noncomputable def iso : K.homology n ≅ ModuleCat.of R (H K n) := (naturalIso n).app K

variable {K L}
noncomputable def cyclesMap (f : K ⟶ L) (n : ℕ) : Cycles K n →ₗ[R] Cycles L n :=
  (ShortComplex.cyclesMap' ((shortComplexFunctor' _ c (n+1) n (n-1)).map f)
    (S K n).moduleCatLeftHomologyData (S L n).moduleCatLeftHomologyData).hom

@[simp] lemma cyclesMap_val (f : K ⟶ L) (n : ℕ) (x : Cycles K n) :
    (cyclesMap f n x).val=(f.f n).hom x := by
  have h := ShortComplex.cyclesMap'_i ((shortComplexFunctor' _ c (n+1) n (n-1)).map f)
    (S K n).moduleCatLeftHomologyData (S L n).moduleCatLeftHomologyData
  exact congrArg (fun g : ModuleCat.of R (Cycles K n) ⟶ L.X n => g.hom x) h

@[simp] lemma map_π (f : K ⟶ L) (n : ℕ) (x : Cycles K n) :
    ((functor n).map f).hom (π K n x)=π L n (cyclesMap f n x) := by
  have h := ShortComplex.leftHomologyπ_naturality' ((shortComplexFunctor' _ c (n+1) n (n-1)).map f)
    (S K n).moduleCatLeftHomologyData (S L n).moduleCatLeftHomologyData
  exact congrArg (fun g : ModuleCat.of R (Cycles K n) ⟶ ModuleCat.of R (H L n) => g.hom x) h

end ConcreteHomology

end

section
open _root_.CategoryTheory Limits HomologicalComplex
namespace ConeCoordinates

universe u
variable {R : Type u} [CommRing R]
open ConcreteHomology
variable {F G : CC (R:=R)} (φ : F ⟶ G)
noncomputable abbrev C := homotopyCofiber φ
noncomputable abbrev left (n : ℕ) : F.X n ⟶ (C φ).X (n+1) := homotopyCofiber.inlX φ n (n+1) rfl
noncomputable abbrev right (n : ℕ) : G.X n ⟶ (C φ).X n := homotopyCofiber.inrX φ n
noncomputable abbrev fst (n : ℕ) : (C φ).X (n+1) ⟶ F.X n := homotopyCofiber.fstX φ (n+1) n rfl
noncomputable abbrev snd (n : ℕ) : (C φ).X n ⟶ G.X n := homotopyCofiber.sndX φ n
lemma zero_next : ¬ c.Rel 0 (c.next 0) := by change ¬ c.next 0+1=0; omega
@[simp] lemma fst_left (n : ℕ) (x : F.X n) : fst φ n (left φ n x)=x := by
  exact congrArg (fun f : F.X n ⟶ F.X n => f x) (homotopyCofiber.inlX_fstX φ n (n+1) rfl)
@[simp] lemma snd_right (n : ℕ) (x : G.X n) : snd φ n (right φ n x)=x := by
  exact congrArg (fun f : G.X n ⟶ G.X n => f x) (homotopyCofiber.inrX_sndX φ n)
@[simp] lemma fst_right (n : ℕ) (x : G.X (n+1)) : fst φ n (right φ (n+1) x)=0 := by
  exact congrArg (fun f : G.X (n+1) ⟶ F.X n => f x) (homotopyCofiber.inrX_fstX φ (n+1) n rfl)
@[simp] lemma snd_left (n : ℕ) (x : F.X n) : snd φ (n+1) (left φ n x)=0 := by
  exact congrArg (fun f : F.X n ⟶ G.X (n+1) => f x) (homotopyCofiber.inlX_sndX φ n (n+1) rfl)
lemma ext {n : ℕ} {x y : (C φ).X (n+1)} (hfst : fst φ n x=fst φ n y)
    (hsnd : snd φ (n+1) x=snd φ (n+1) y) : x=y := by
  have hrel : c.Rel (n+1) n := rfl
  apply (homotopyCofiber.XIsoBiprod φ (n+1) n hrel).toLinearEquiv.injective
  apply (ModuleCat.biprodIsoProd (F.X n) (G.X (n+1))).toLinearEquiv.injective
  apply Prod.ext
  · exact hfst
  · change (biprod.snd : F.X n ⊞ G.X (n+1) ⟶ G.X (n+1)) ((homotopyCofiber.XIsoBiprod φ (n+1) n hrel).hom x) =
      (biprod.snd : F.X n ⊞ G.X (n+1) ⟶ G.X (n+1)) ((homotopyCofiber.XIsoBiprod φ (n+1) n hrel).hom y)
    have he : (homotopyCofiber.XIsoBiprod φ (n+1) n hrel).hom ≫ biprod.snd = snd φ (n+1) := by
      apply homotopyCofiber.ext_from_X φ n (n+1) hrel
      · simp only [homotopyCofiber.inlX_XIsoBiprod_hom_assoc,biprod.inl_snd,
          homotopyCofiber.inlX_sndX]
      · simp only [homotopyCofiber.inrX_XIsoBiprod_hom_assoc,biprod.inr_snd,
          homotopyCofiber.inrX_sndX]
    change ((homotopyCofiber.XIsoBiprod φ (n+1) n hrel).hom ≫ biprod.snd) x =
      ((homotopyCofiber.XIsoBiprod φ (n+1) n hrel).hom ≫ biprod.snd) y
    rw [he]; exact hsnd
lemma ext_zero {x y : (C φ).X 0} (h : snd φ 0 x=snd φ 0 y) : x=y :=
  (homotopyCofiber.XIso φ 0 zero_next).toLinearEquiv.injective h
lemma decomp_zero (x : (C φ).X 0) : right φ 0 (snd φ 0 x)=x := by
  apply ext_zero φ; exact snd_right φ 0 _
lemma d_snd (n : ℕ) (x : (C φ).X (n+1)) :
    snd φ n ((C φ).d (n+1) n x)=φ.f n (fst φ n x)+G.d (n+1) n (snd φ (n+1) x) := by
  exact congrArg (fun f : (C φ).X (n+1) ⟶ G.X n => f x)
    (homotopyCofiber.d_sndX φ (n+1) n rfl)
lemma d_fst (n : ℕ) (x : (C φ).X (n+2)) :
    fst φ n ((C φ).d (n+2) (n+1) x) = -F.d (n+1) n (fst φ (n+1) x) := by
  exact congrArg (fun f : (C φ).X (n+2) ⟶ F.X n => f x)
    (homotopyCofiber.d_fstX φ (n+2) (n+1) n rfl rfl)
lemma d_right (n m : ℕ) (x : G.X n) :
    (C φ).d n m (right φ n x)=right φ m (G.d n m x) := by
  exact congrArg (fun f : G.X n ⟶ (C φ).X m => f x)
    (homotopyCofiber.inrX_d φ n m)
lemma d_left (n : ℕ) (x : F.X (n+1)) :
    (C φ).d (n+2) (n+1) (left φ (n+1) x) =
      -left φ n (F.d (n+1) n x)+right φ (n+1) (φ.f (n+1) x) := by
  apply ext φ
  · rw [d_fst φ n, fst_left φ (n+1)]
    simp only [map_add,map_neg,fst_left φ n _,fst_right φ n _,add_zero]
  · rw [d_snd φ (n+1),fst_left φ (n+1),snd_left φ (n+1)]
    simp only [map_add,map_neg,map_zero,snd_left φ n _,snd_right φ (n+1) _,neg_zero,zero_add,add_zero]
lemma d_left_zero (x : F.X 0) : (C φ).d 1 0 (left φ 0 x)=right φ 0 (φ.f 0 x) := by
  apply ext_zero φ
  rw [d_snd φ 0,fst_left φ 0,snd_left φ 0,map_zero,add_zero,snd_right φ 0]
lemma d_left_cycle (n : ℕ) (x : Cycles F n) :
    (C φ).d (n+1) n (left φ n x)=right φ n (φ.f n x) := by
  cases n with
  | zero => exact d_left_zero φ x
  | succ n =>
    rw [d_left]
    have hx : F.d (n+1) n x=0 := x.property
    rw [hx,map_zero,neg_zero,zero_add]
end ConeCoordinates

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_DiagonalResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
namespace DiagonalResolution

abbrev D := SimplexCategory × SimplexCategory
abbrev A := ModuleCat.{0} ℤ
noncomputable abbrev Z : A := ModuleCat.of ℤ ℤ
noncomputable abbrev free (d : D) : D ⥤ A := (evaluationLeftAdjoint A d).obj Z

noncomputable def pre {a b : D} (k : a ⟶ b) : free b ⟶ free a where
  app d := Sigma.desc (fun f => Sigma.ι (fun _ : a ⟶ d => Z) (k ≫ f))
  naturality d e f := by
    apply Sigma.hom_ext
    intro g
    simp [free,evaluationLeftAdjoint,Category.assoc]

@[reassoc (attr := simp)] lemma ι_pre {a b : D} (k : a ⟶ b) (d : D) (f : b ⟶ d) :
    Sigma.ι (fun _ : b ⟶ d => Z) f ≫ (pre k).app d =
      Sigma.ι (fun _ : a ⟶ d => Z) (k ≫ f) := by
  exact Sigma.ι_desc _ _

@[simp] lemma pre_id (a : D) : pre (𝟙 a) = 𝟙 (free a) := by
  apply NatTrans.ext
  funext d
  apply Sigma.hom_ext
  intro f
  simp only [ι_pre, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm
@[simp] lemma pre_comp {a b c : D} (f : a ⟶ b) (g : b ⟶ c) :
    pre (f ≫ g) = pre g ≫ pre f := by
  apply NatTrans.ext
  funext d
  apply Sigma.hom_ext
  intro h
  simp only [NatTrans.comp_app]
  erw [← Category.assoc, ι_pre, ι_pre, ι_pre]
  rw [Category.assoc]

noncomputable def preDiag {a b : SimplexCategory} (f : a ⟶ b) : free (b,b) ⟶ free (a,a) :=
  pre (a := (a,a)) (b := (b,b)) (f,f)

noncomputable def chains : SimplicialObject (D ⥤ A) where
  obj n := free (n.unop,n.unop)
  map f := pre (f.unop,f.unop)
  map_id n := pre_id _
  map_comp {X Y W} f g := by
    simpa only [unop_comp, prod_comp, Prod.mkHom] using (pre_comp (a := (W.unop,W.unop))
      (b := (Y.unop,Y.unop)) (c := (X.unop,X.unop)) (g.unop,g.unop) (f.unop,f.unop))
noncomputable def augmentation : chains ⟶ (SimplicialObject.const _).obj ((Functor.const D).obj Z) where
  app n :=
    { app d := Sigma.desc (fun _ : (n.unop,n.unop) ⟶ d => 𝟙 Z)
      naturality d e f := by
        apply Sigma.hom_ext
        intro g
        simp [chains,free,evaluationLeftAdjoint] }
  naturality n m f := by
    apply NatTrans.ext
    funext d
    apply Sigma.hom_ext
    intro g
    simp only [NatTrans.comp_app, chains, pre, Functor.const_obj_map]
    erw [Sigma.ι_desc_assoc, Sigma.ι_desc, Sigma.ι_desc_assoc,
      NatTrans.id_app, Category.id_comp]
    rfl

noncomputable def augmented : SimplicialObject.Augmented (D ⥤ A) where
  left := chains
  right := (Functor.const D).obj Z
  hom := augmentation

noncomputable def complex : ChainComplex (D ⥤ A) ℕ :=
  AlternatingFaceMapComplex.obj chains

instance projective (n : ℕ) : Projective (complex.X n) := by
  change Projective (free (⦋n⦌,⦋n⦌))
  exact (evaluationAdjunctionRight A (⦋n⦌,⦋n⦌)).map_projective Z inferInstance

open SSet.Augmented.StandardSimplex

def zeroSimplex (a : SimplexCategory) : ⦋0⦌ ⟶ a := SimplexCategory.Hom.mk (OrderHom.const _ 0)

@[simp] lemma shift_δ₀ {n : ℕ} {a : SimplexCategory} (f : ⦋n⦌ ⟶ a) :
    SimplexCategory.δ 0 ≫ shift f = f := by
  exact congrArg SSet.stdSimplex.objEquiv.{0}
    (ConcreteCategory.congr_hom ((SSet.Augmented.StandardSimplex.extraDegeneracy a).s_comp_δ₀ n)
      (SSet.stdSimplex.objEquiv.symm f))

@[simp] lemma shift_δ_succ {n : ℕ} {a : SimplexCategory} (f : ⦋n+1⦌ ⟶ a) (i : Fin (n+2)) :
    SimplexCategory.δ i.succ ≫ shift f = shift (SimplexCategory.δ i ≫ f) := by
  exact congrArg SSet.stdSimplex.objEquiv.{0}
    (ConcreteCategory.congr_hom ((SSet.Augmented.StandardSimplex.extraDegeneracy a).s_comp_δ n i)
      (SSet.stdSimplex.objEquiv.symm f))

@[simp] lemma shift_σ_succ {n : ℕ} {a : SimplexCategory} (f : ⦋n⦌ ⟶ a) (i : Fin (n+1)) :
    SimplexCategory.σ i.succ ≫ shift f = shift (SimplexCategory.σ i ≫ f) := by
  exact congrArg SSet.stdSimplex.objEquiv.{0}
    (ConcreteCategory.congr_hom ((SSet.Augmented.StandardSimplex.extraDegeneracy a).s_comp_σ n i)
      (SSet.stdSimplex.objEquiv.symm f))

@[simp] lemma shift_δ₁ {a : SimplexCategory} (f : ⦋0⦌ ⟶ a) :
    SimplexCategory.δ 1 ≫ shift f = zeroSimplex a := by
  exact congrArg SSet.stdSimplex.objEquiv.{0}
    (ConcreteCategory.congr_hom ((SSet.Augmented.StandardSimplex.extraDegeneracy a).s₀_comp_δ₁)
      (SSet.stdSimplex.objEquiv.symm f))

noncomputable abbrev augmentedAt (d : D) : SimplicialObject.Augmented A :=
  ((SimplicialObject.Augmented.whiskering _ _).obj ((evaluation D A).obj d)).obj augmented
noncomputable def extraAt (d : D) : (augmentedAt d).ExtraDegeneracy where
  s' := Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z) (zeroSimplex d.1,zeroSimplex d.2)
  s n := Sigma.desc (fun f : (⦋n⦌,⦋n⦌) ⟶ d =>
    Sigma.ι (fun _ : (⦋n+1⦌,⦋n+1⦌) ⟶ d => Z) (shift f.1,shift f.2))
  s'_comp_ε := by
    change Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z) (zeroSimplex d.1,zeroSimplex d.2) ≫
      Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z) = 𝟙 Z
    simp
  s₀_comp_δ₁ := by
    change Sigma.desc _ ≫ (preDiag (SimplexCategory.δ 1)).app d =
      Sigma.desc _ ≫ Sigma.ι _ _
    apply Sigma.hom_ext
    intro f
    dsimp only [preDiag]
    erw [Sigma.ι_desc_assoc, ι_pre, Sigma.ι_desc_assoc]
    simp only [prod_comp, Prod.mkHom, shift_δ₁]
    exact (Category.id_comp _).symm
  s_comp_δ₀ n := by
    change Sigma.desc _ ≫ (preDiag (SimplexCategory.δ 0)).app d = 𝟙 _
    apply Sigma.hom_ext
    intro f
    dsimp only [preDiag]
    erw [Sigma.ι_desc_assoc, ι_pre]
    simp only [prod_comp, Prod.mkHom, shift_δ₀, Prod.eta]
    exact (Category.comp_id _).symm
  s_comp_δ n i := by
    change Sigma.desc _ ≫ (preDiag (SimplexCategory.δ i.succ)).app d =
      (preDiag (SimplexCategory.δ i)).app d ≫ Sigma.desc _
    apply Sigma.hom_ext
    intro f
    dsimp only [preDiag]
    erw [Sigma.ι_desc_assoc, ι_pre, ι_pre_assoc, Sigma.ι_desc]
    simp only [prod_comp, Prod.mkHom, shift_δ_succ]
    rfl
  s_comp_σ n i := by
    change Sigma.desc _ ≫ (preDiag (SimplexCategory.σ i.succ)).app d =
      (preDiag (SimplexCategory.σ i)).app d ≫ Sigma.desc _
    apply Sigma.hom_ext
    intro f
    dsimp only [preDiag]
    erw [Sigma.ι_desc_assoc, ι_pre, ι_pre_assoc, Sigma.ι_desc]
    simp only [prod_comp, Prod.mkHom, shift_σ_succ]
    rfl

noncomputable def pi : complex ⟶ (ChainComplex.single₀ (D ⥤ A)).obj ((Functor.const D).obj Z) :=
  AlternatingFaceMapComplex.ε.app augmented

noncomputable def atIso (d : D) :
    (((evaluation D A).obj d).mapHomologicalComplex (ComplexShape.down ℕ)).obj complex ≅
      AlternatingFaceMapComplex.obj (augmentedAt d).left :=
  eqToIso (congrArg (fun F => F.obj chains)
    (map_alternatingFaceMapComplex ((evaluation D A).obj d)))

noncomputable def singleAtIso (d : D) :
    (((evaluation D A).obj d).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((ChainComplex.single₀ (D ⥤ A)).obj ((Functor.const D).obj Z)) ≅
      (ChainComplex.single₀ A).obj Z :=
  (HomologicalComplex.singleMapHomologicalComplex ((evaluation D A).obj d)
    (ComplexShape.down ℕ) 0).app ((Functor.const D).obj Z)
instance pi_quasiIso : QuasiIso pi := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro d
  let f := (((evaluation D A).obj d).mapHomologicalComplex (ComplexShape.down ℕ)).map pi
  have h : f ≫ (singleAtIso d).hom = (atIso d).hom ≫ (extraAt d).homotopyEquiv.hom := by
    apply HomologicalComplex.to_single_hom_ext
    dsimp [f,pi,atIso,singleAtIso]
    simp [HomologicalComplex.singleMapHomologicalComplex,
      SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
      Functor.mapHomologicalComplex, augmentedAt, augmented, augmentation]
    dsimp only [NatIso.ofComponents, SimplicialObject.Augmented.whiskering,
      SimplicialObject.Augmented.whiskeringObj, CategoryTheory.eqToIso]
    erw [HomologicalComplex.eqToHom_f]
    rfl
  change QuasiIso f
  rw [← quasiIso_iff_comp_right f (singleAtIso d).hom, h]
  have : QuasiIso (extraAt d).homotopyEquiv.hom :=
    (extraAt d).homotopyEquiv.quasiIso_hom
  have hcomp := quasiIso_comp (atIso d).hom (extraAt d).homotopyEquiv.hom
  exact hcomp

noncomputable def resolution : ProjectiveResolution ((Functor.const D).obj Z) where
  complex := complex
  π := pi
  quasiIso := pi_quasiIso

end DiagonalResolution

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ModelAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open _root_.CategoryTheory Limits Opposite
namespace ModelAssembly

open DiagonalResolution
variable (X : Dᵒᵖ ⥤ Type)

abbrev projection : X.Elementsᵒᵖ ⥤ D := (CategoryOfElements.π X).leftOp

noncomputable def assembly : (D ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft _ _ _).obj (projection X) ⋙ colim

instance assembly_additive : (assembly X).Additive := by
  unfold assembly
  infer_instance

instance assembly_preservesColimits : PreservesColimitsOfSize.{0,0} (assembly X) := by
  unfold assembly
  infer_instance
noncomputable def freeCocone (d : D) : Cocone (projection X ⋙ free d) where
  pt := ∐ (fun _ : X.obj (op d) => Z)
  ι :=
    { app e := Sigma.desc (fun f : d ⟶ e.unop.1.unop =>
        Sigma.ι (fun _ : X.obj (op d) => Z) (X.map f.op e.unop.2))
      naturality e e' f := by
        apply Sigma.hom_ext
        intro g
        simp only [Functor.const_obj_obj,Functor.const_obj_map,Category.comp_id,
          Functor.comp_map,projection,Functor.leftOp_map,CategoryOfElements.π_map,
          free,evaluationLeftAdjoint]
        simp only [← Category.assoc,Sigma.ι_desc]
        erw [Sigma.ι_desc, Sigma.ι_desc]
        congr 1
        change X.map (g ≫ f.unop.val.unop).op e'.unop.2 = X.map g.op e.unop.2
        erw [op_comp, X.map_comp]
        change X.map g.op (X.map f.unop.val e'.unop.2) = _
        erw [f.unop.property] }

noncomputable def forward (d : D) : (assembly X).obj (free d) ⟶ ∐ (fun _ : X.obj (op d) => Z) :=
  colimit.desc _ (freeCocone X d)

noncomputable def backward (d : D) : (∐ (fun _ : X.obj (op d) => Z)) ⟶ (assembly X).obj (free d) :=
  Sigma.desc (fun x => Sigma.ι (fun _ : d ⟶ d => Z) (𝟙 d) ≫
    colimit.ι (projection X ⋙ free d) (op (X.elementsMk (op d) x)))

@[reassoc (attr := simp)] lemma ι_to (d : D) (e : X.Elementsᵒᵖ) :
    colimit.ι (projection X ⋙ free d) e ≫ forward X d = (freeCocone X d).ι.app e := by
  apply colimit.ι_desc
lemma from_to (d : D) : backward X d ≫ forward X d = 𝟙 _ := by
  apply Sigma.hom_ext
  intro x
  dsimp only [backward]
  erw [Sigma.ι_desc_assoc, Category.assoc, ι_to]
  change Sigma.ι (fun _ : d ⟶ d => Z) (𝟙 d) ≫ Sigma.desc
    (fun f : d ⟶ d => Sigma.ι (fun _ : X.obj (op d) => Z) (X.map f.op x)) = _
  simp
lemma to_from (d : D) : forward X d ≫ backward X d = 𝟙 _ := by
  apply colimit.hom_ext
  intro e
  apply Sigma.hom_ext
  intro f
  change Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) f ≫
    colimit.ι (projection X ⋙ free d) e ≫ forward X d ≫ backward X d =
    Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) f ≫ colimit.ι (projection X ⋙ free d) e ≫ 𝟙 _
  erw [← Category.assoc (colimit.ι (projection X ⋙ free d) e) (forward X d)
    (backward X d), ι_to]
  dsimp only [freeCocone]
  dsimp only [backward]
  erw [Sigma.ι_desc_assoc, Sigma.ι_desc, Category.comp_id]
  let k := (show e.unop ⟶ X.elementsMk (op d) (X.map f.op e.unop.2) from
    ⟨f.op, rfl⟩).op
  have h := congrArg (fun g => Sigma.ι (fun _ : d ⟶ d => Z) (𝟙 d) ≫ g)
    (colimit.w (projection X ⋙ free d) k)
  change Sigma.ι (fun _ : d ⟶ d => Z) (𝟙 d) ≫
    (Sigma.desc (fun g : d ⟶ d => Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) (g ≫ f))) ≫
      colimit.ι (projection X ⋙ free d) e =
    Sigma.ι (fun _ : d ⟶ d => Z) (𝟙 d) ≫
      colimit.ι (projection X ⋙ free d) (op (X.elementsMk (op d) (X.map f.op e.unop.2))) at h
  erw [Sigma.ι_desc_assoc, Category.id_comp] at h
  change _ = _ at h
  exact h.symm

noncomputable def freeIso (d : D) : (assembly X).obj (free d) ≅ ∐ (fun _ : X.obj (op d) => Z) where
  hom := forward X d
  inv := backward X d
  hom_inv_id := to_from X d
  inv_hom_id := from_to X d

end ModelAssembly

end

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalHomotopy

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
abbrev c := ComplexShape.down ℕ
variable {K L : HomologicalComplex₂ C c c} {f g : K ⟶ L}

@[simp] lemma sign₁ (p q : ℕ) : ComplexShape.ε₁ c c c (p,q)=1 := rfl
@[simp] lemma sign₂ (p q : ℕ) : ComplexShape.ε₂ c c c (p,q)=(-1 : ℤˣ)^p := rfl
@[simp] lemma π_add (p q : ℕ) : ComplexShape.π c c c (p,q)=p+q := rfl

noncomputable def step (h : Homotopy f g) (n : ℕ) : (K.total c).X n ⟶ (L.total c).X (n+1) :=
  K.totalDesc (fun p q hpq => (h.hom p (p+1)).f q ≫ L.ιTotal c (p+1) q (n+1) (by
    dsimp at hpq ⊢; omega))

@[reassoc (attr := simp)] lemma ι_step (h : Homotopy f g) (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal c p q n hpq ≫ step h n =
      (h.hom p (p+1)).f q ≫ L.ιTotal c (p+1) q (n+1) (by dsimp; omega) := by
  apply ι_totalDesc

lemma ι_d₁_zero (q n : ℕ) : K.ιTotal c 0 q q (by simp) ≫ K.D₁ c q n=0 := by
  rw [ι_D₁]
  apply d₁_eq_zero
  simp [c]

lemma ι_d₂_zero (p n : ℕ) : K.ιTotal c p 0 p (by simp) ≫ K.D₂ c p n=0 := by
  rw [ι_D₂]
  apply d₂_eq_zero
  simp [c]

@[reassoc] lemma ι_d₁_succ (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal c (p+1) q (n+1) (by dsimp; omega) ≫ K.D₁ c (n+1) n =
      (K.d (p+1) p).f q ≫ K.ιTotal c p q n hpq := by
  rw [ι_D₁, d₁_eq K c (by rfl : c.Rel (p+1) p) q n hpq,sign₁,one_smul]

@[reassoc] lemma ι_d₂_succ (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal c p (q+1) (n+1) (by dsimp; omega) ≫ K.D₂ c (n+1) n =
      ((-1 : ℤˣ)^p) • ((K.X p).d (q+1) q ≫ K.ιTotal c p q n hpq) := by
  rw [ι_D₂,d₂_eq K c p (by rfl : c.Rel (q+1) q) n hpq,sign₂]

@[reassoc] lemma ι_d (p q n m : ℕ) (hpq : p+q=n) :
    K.ιTotal c p q n hpq ≫ (K.total c).d n m = K.d₁ c p q m+K.d₂ c p q m := by
  change _ ≫ (_+_)=_
  rw [Preadditive.comp_add,ι_D₁,ι_D₂]

omit [HasCoproducts C] in
lemma comm_zero (h : Homotopy f g) (q : ℕ) :
    (f.f 0).f q = (h.hom 0 1).f q ≫ (L.d 1 0).f q +(g.f 0).f q := by
  have e := congrArg (fun k : K.X 0 ⟶ L.X 0 => k.f q) (h.comm 0)
  simpa only [Homotopy.dNext_zero_chainComplex,Homotopy.prevD_chainComplex,
    zero_add, HomologicalComplex.comp_f,HomologicalComplex.add_f_apply] using e

omit [HasCoproducts C] in
lemma comm_succ (h : Homotopy f g) (p q : ℕ) :
    (f.f (p+1)).f q = (K.d (p+1) p).f q ≫ (h.hom p (p+1)).f q +
      (h.hom (p+1) (p+2)).f q ≫ (L.d (p+2) (p+1)).f q +(g.f (p+1)).f q := by
  have e := congrArg (fun k : K.X (p+1) ⟶ L.X (p+1) => k.f q) (h.comm (p+1))
  simpa only [Homotopy.dNext_succ_chainComplex,Homotopy.prevD_chainComplex,
    HomologicalComplex.comp_f,HomologicalComplex.add_f_apply] using e

noncomputable def hom (h : Homotopy f g) :
    ∀ n m, (K.total c).X n ⟶ (L.total c).X m :=
  fun n => Pi.single (n+1) (step h n)

@[simp] lemma hom_diag (h : Homotopy f g) (n : ℕ) : hom h n (n+1)=step h n := by
  simp [hom]

@[reassoc] lemma ι_d_rightZero (p : ℕ) :
    K.ιTotal c (p+1) 0 (p+1) (by simp) ≫ (K.total c).d (p+1) p =
      (K.d (p+1) p).f 0 ≫ K.ιTotal c p 0 p (by simp) := by
  rw [ι_d,d₁_eq K c (by rfl : c.Rel (p+1) p) 0 p (by simp),sign₁,one_smul,
    d₂_eq_zero K c (p+1) 0 p (by simp [c]),add_zero]

@[reassoc] lemma ι_d_leftZero (q : ℕ) :
    K.ιTotal c 0 (q+1) (q+1) (by simp) ≫ (K.total c).d (q+1) q =
      (K.X 0).d (q+1) q ≫ K.ιTotal c 0 q q (by simp) := by
  rw [ι_d,d₁_eq_zero K c 0 (q+1) q (by simp [c]),zero_add,
    d₂_eq K c 0 (by rfl : c.Rel (q+1) q) q (by simp),sign₂,pow_zero,one_smul]

@[reassoc] lemma ι_d_both (p q n : ℕ) (hpq : p+q+1=n) :
    K.ιTotal c (p+1) (q+1) (n+1) (by dsimp; omega) ≫ (K.total c).d (n+1) n =
      (K.d (p+1) p).f (q+1) ≫ K.ιTotal c p (q+1) n (by dsimp; omega) +
        ((-1 : ℤˣ)^(p+1)) • ((K.X (p+1)).d (q+1) q ≫ K.ιTotal c (p+1) q n (by dsimp; omega)) := by
  rw [ι_d,d₁_eq K c (by rfl : c.Rel (p+1) p) (q+1) n (by dsimp; omega),
    d₂_eq K c (p+1) (by rfl : c.Rel (q+1) q) n (by dsimp; omega),sign₁,one_smul,sign₂]

lemma total_comm_zero (h : Homotopy f g) :
    (total.map f c).f 0 = dNext 0 (hom h) + prevD 0 (hom h) +
      (total.map g c).f 0 := by
  rw [Homotopy.dNext_zero_chainComplex,Homotopy.prevD_chainComplex,hom_diag,zero_add]
  apply total.hom_ext
  intro p q hpq
  obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hpq
  simp only [Preadditive.comp_add,←Category.assoc,ι_step,ιTotal_map]
  rw [Category.assoc,ι_d_rightZero,←Category.assoc,comm_zero h 0,Preadditive.add_comp]

lemma neg_pow_smul_succ {A : Type*} [AddCommGroup A] (p : ℕ) (a : A) :
    ((-1 : ℤˣ)^(p+1)) • a = - (((-1 : ℤˣ)^p) • a) := by
  rw [pow_succ',mul_smul,Units.neg_smul,one_smul]

lemma total_comm_succ (h : Homotopy f g) (n : ℕ) :
    (total.map f c).f (n+1) = (K.total c).d (n+1) n ≫ step h n +
      step h (n+1) ≫ (L.total c).d (n+2) (n+1) + (total.map g c).f (n+1) := by
  apply total.hom_ext
  intro p q hpq
  change p+q=n+1 at hpq
  cases p with
  | zero =>
    cases q with
    | zero => omega
    | succ q =>
      have : q=n := by omega
      subst q
      simp only [Preadditive.comp_add,←Category.assoc,ι_d_leftZero,ι_step,ιTotal_map]
      simp only [Category.assoc,ι_step,ι_d_both 0 n (n+1) (by omega)]
      simp only [Preadditive.comp_add,Linear.comp_units_smul]
      rw [←Category.assoc, ←Category.assoc, ←(h.hom 0 1).comm]
      rw [comm_zero h (n+1),Preadditive.add_comp]
      simp only [Nat.zero_add, pow_one, Units.neg_smul, one_smul, Category.assoc]
      abel
  | succ p =>
    cases q with
    | zero =>
      have : p=n := by omega
      subst p
      simp only [Preadditive.comp_add,←Category.assoc,ι_d_rightZero,ι_step,ιTotal_map]
      simp only [Category.assoc,ι_step,ι_d_rightZero]
      rw [comm_succ h n 0]
      simp only [Preadditive.add_comp,Category.assoc]
    | succ q =>
      have hn : p+q+1=n := by omega
      simp only [Preadditive.comp_add,←Category.assoc,
        ι_d_both p q n hn,Preadditive.add_comp,Linear.units_smul_comp,
        ι_step,ιTotal_map]
      simp only [Category.assoc,ι_step,ι_d_both (p+1) q (n+1) (by omega)]
      simp only [Preadditive.comp_add,Linear.comp_units_smul]
      rw [←Category.assoc, ←Category.assoc, ←(h.hom (p+1) (p+2)).comm]
      rw [comm_succ h p (q+1)]
      simp only [Preadditive.add_comp,Category.assoc,neg_pow_smul_succ,neg_neg]
      abel

noncomputable def total (h : Homotopy f g) : Homotopy (total.map f c) (total.map g c) where
  hom := hom h
  zero i j hij := by
    have hne : i+1 ≠ j := by simpa [c,eq_comm] using hij
    exact Pi.single_eq_of_ne hne.symm _
  comm i := by
    cases i with
    | zero => exact total_comm_zero h
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex,Homotopy.prevD_chainComplex,hom_diag,hom_diag]
      exact total_comm_succ h n

end TotalHomotopy

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ConeHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits HomologicalComplex
namespace ConeCoordinates

universe u
variable {R : Type u} [CommRing R]
open ConcreteHomology
variable {F G : CC (R:=R)} (φ : F ⟶ G)
lemma right_cycle (n : ℕ) (y : Cycles G n) :
    (C φ).d n (n-1) (right φ n y)=0 := by
  rw [d_right φ n (n-1),y.property,map_zero]
lemma fst_cycle (n : ℕ) (w : (C φ).X (n+1)) (y : G.X n)
    (hw : (C φ).d (n+1) n w=right φ n y) : F.d n (n-1) (fst φ n w)=0 := by
  cases n with
  | zero => rw [F.shape 0 (0-1) (by decide)]; rfl
  | succ n =>
    have h := congrArg (fst φ n) hw
    rw [d_fst φ n,fst_right φ n] at h
    exact neg_eq_zero.mp h
lemma surjective_of_cone_zero (n : ℕ) [Subsingleton (H (C φ) n)] :
    Function.Surjective ((functor n).map φ).hom := by
  intro z
  obtain ⟨y,rfl⟩ := π_surjective G n z
  let yc : Cycles (C φ) n := ⟨right φ n y,right_cycle φ n y⟩
  obtain ⟨w,hw⟩ := (π_eq_zero (C φ) n yc).mp (Subsingleton.elim _ _)
  change (C φ).X (n+1) at w
  have hw' : (C φ).d (n+1) n w=right φ n y := congrArg Subtype.val hw
  let x : Cycles F n := ⟨fst φ n w,fst_cycle φ n w y hw'⟩
  refine ⟨π F n x,?_⟩
  rw [map_π]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-snd φ (n+1) w,?_⟩
  apply Subtype.ext
  have hs := congrArg (snd φ n) hw'
  rw [d_snd φ n,snd_right φ n] at hs
  change G.d (n+1) n (-snd φ (n+1) w)=φ.f n x-y
  rw [map_neg]
  change -(G.d (n+1) n (snd φ (n+1) w))=φ.f n (fst φ n w)-y
  rw [←hs]
  abel
lemma injective_of_cone_zero (n : ℕ) [Subsingleton (H (C φ) (n+1))] :
    Function.Injective ((functor n).map φ).hom := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨x,rfl⟩ := π_surjective F n z
  have hz' : π G n (cyclesMap φ n x)=0 := by
    rw [←map_π]; exact hz
  obtain ⟨y,hy⟩ := (π_eq_zero G n _).mp hz'
  change G.X (n+1) at y
  have hy' : G.d (n+1) n y=φ.f n x := by
    have hh := congrArg Subtype.val hy
    change G.d (n+1) n y=(cyclesMap φ n x).val at hh
    rw [cyclesMap_val] at hh
    exact hh
  let w := left φ n x-right φ (n+1) y
  have hw : (C φ).d (n+1) n w=0 := by
    change (C φ).d (n+1) n (left φ n x-right φ (n+1) y)=0
    rw [map_sub,d_left_cycle φ n x,d_right φ (n+1) n,hy',sub_self]
  let wc : Cycles (C φ) (n+1) := ⟨w,hw⟩
  obtain ⟨a,ha⟩ := (π_eq_zero (C φ) (n+1) wc).mp (Subsingleton.elim _ _)
  change (C φ).X (n+2) at a
  have ha' : (C φ).d (n+2) (n+1) a=w := congrArg Subtype.val ha
  have hf := congrArg (fst φ n) ha'
  rw [d_fst φ n] at hf
  change -F.d (n+1) n (fst φ (n+1) a)=fst φ n (left φ n x-right φ (n+1) y) at hf
  rw [map_sub,fst_left φ n,fst_right φ n,sub_zero] at hf
  apply (Submodule.mem_bot R).mpr
  apply (π_eq_zero F n x).mpr
  refine ⟨-fst φ (n+1) a,?_⟩
  apply Subtype.ext
  change F.d (n+1) n (-fst φ (n+1) a)=x
  rw [map_neg]; exact hf
lemma cone_subsingleton_of_iso [IsIso φ] (n : ℕ) : Subsingleton (H (C φ) n) := by
  apply subsingleton_of_forall_eq 0
  intro z
  obtain ⟨x,rfl⟩ := π_surjective (C φ) n z
  apply (π_eq_zero (C φ) n x).mpr
  refine ⟨left φ n ((inv φ).f n (snd φ n x)),?_⟩
  apply Subtype.ext
  change (C φ).d (n+1) n (left φ n ((inv φ).f n (snd φ n x)))=x
  cases n with
  | zero =>
    rw [d_left_zero φ]
    have hi : φ.f 0 ((inv φ).f 0 (snd φ 0 x))=snd φ 0 x := by
      have h := congrArg (fun f : G ⟶ G => f.f 0 (snd φ 0 x)) (IsIso.inv_hom_id φ)
      exact h
    rw [hi]; exact decomp_zero φ x
  | succ n =>
    rw [d_left φ]
    apply ext φ
    · simp only [map_add,map_neg,fst_left φ n _,fst_right φ n _,add_zero]
      have hx : (C φ).d (n+1) n x=0 := x.property
      have hs := congrArg (snd φ n) hx
      rw [d_snd φ n,map_zero] at hs
      have hc := congrArg (fun f : G.X (n+1) ⟶ F.X n => f (snd φ (n+1) x))
        ((inv φ).comm (n+1) n)
      have hi : (inv φ).f n (φ.f n (fst φ n x))=fst φ n x := by
        exact congrArg (fun f : F ⟶ F => f.f n (fst φ n x)) (IsIso.hom_inv_id φ)
      have hs' := congrArg ((inv φ).f n) hs
      rw [map_add,hi,map_zero] at hs'
      change -(F.d (n+1) n ((inv φ).f (n+1) (snd φ (n+1) x)))=fst φ n x
      change F.d (n+1) n ((inv φ).f (n+1) (snd φ (n+1) x)) =
        (inv φ).f n (G.d (n+1) n (snd φ (n+1) x)) at hc
      rw [hc]
      exact (eq_neg_of_add_eq_zero_left hs').symm
    · simp only [map_add,map_neg,snd_left φ n _,snd_right φ (n+1) _,neg_zero,zero_add]
      exact congrArg (fun f : G ⟶ G => f.f (n+1) (snd φ (n+1) x)) (IsIso.inv_hom_id φ)
end ConeCoordinates

end

section
open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalCone

universe u
variable {R : Type u} [CommRing R]
abbrev c := ComplexShape.down ℕ
variable {K L : HomologicalComplex₂ (ModuleCat.{u} R) c c} (φ : K ⟶ L)
noncomputable abbrev B : HomologicalComplex₂ (ModuleCat.{u} R) c c := homotopyCofiber φ
noncomputable abbrev f := total.map φ c
noncomputable abbrev inr := total.map (homotopyCofiber.inr φ) c
end TotalCone

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FreeChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits MonoidalCategory SimplicialObject AlgebraicTopology
namespace FreeChains

abbrev A := ModuleCat.{0} ℤ
abbrev Z : A := ModuleCat.of ℤ ℤ
abbrev c := ComplexShape.down ℕ

noncomputable def forward (X : Type) : (sigmaConst.obj Z).obj X ⟶ (ModuleCat.free ℤ).obj X :=
  Sigma.desc (fun x => ModuleCat.ofHom (Finsupp.lsingle x))
noncomputable def backward (X : Type) : (ModuleCat.free ℤ).obj X ⟶ (sigmaConst.obj Z).obj X :=
  ModuleCat.freeDesc (↾fun x => (Sigma.ι (fun _ : X => Z) x) (1:ℤ))
@[reassoc (attr := simp)] lemma ι_forward (X : Type) (x : X) :
    Sigma.ι (fun _ : X => Z) x ≫ forward X = ModuleCat.ofHom (Finsupp.lsingle x) :=
  Sigma.ι_desc _ _
@[simp] lemma backward_mk (X : Type) (x : X) :
    backward X (ModuleCat.freeMk x)=(Sigma.ι (fun _ : X => Z) x) (1:ℤ) := by
  simp [backward]

noncomputable def iso (X : Type) : (sigmaConst.obj Z).obj X ≅ (ModuleCat.free ℤ).obj X where
  hom := forward X
  inv := backward X
  hom_inv_id := by
    apply Sigma.hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    have h := congrArg (fun f : Z ⟶ (ModuleCat.free ℤ).obj X => f (1:ℤ)) (ι_forward X x)
    change backward X (forward X ((Sigma.ι (fun _ : X => Z) x) (1:ℤ))) = _
    rw [show forward X ((Sigma.ι (fun _ : X => Z) x) (1:ℤ))=ModuleCat.freeMk x from h]
    exact backward_mk X x
  inv_hom_id := by
    apply ModuleCat.free_hom_ext
    intro x
    change forward X (backward X (ModuleCat.freeMk x)) = ModuleCat.freeMk x
    rw [backward_mk]
    exact congrArg (fun f : Z ⟶ (ModuleCat.free ℤ).obj X => f (1:ℤ)) (ι_forward X x)

noncomputable def naturalIso : sigmaConst.obj Z ≅ ModuleCat.free ℤ :=
  NatIso.ofComponents iso (by
    intro X Y f
    apply Sigma.hom_ext
    intro x
    dsimp only [iso,sigmaConst]
    erw [Sigma.ι_comp_map'_assoc]
    rw [Category.id_comp,ι_forward,ι_forward_assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change Finsupp.single (f x) 1 = (ModuleCat.free ℤ).map f (ModuleCat.freeMk x)
    exact (ModuleCat.free_map_apply f x).symm)

noncomputable def complex (X : SSet) : ChainComplex A ℕ :=
  AlternatingFaceMapComplex.obj (X ⋙ ModuleCat.free ℤ)
noncomputable def complexIso (X : SSet) : SSet.chainComplex X Z ≅ complex X :=
  (alternatingFaceMapComplex A).mapIso (Functor.isoWhiskerLeft X naturalIso)

end FreeChains

end

section

open _root_.CategoryTheory Limits Classical
namespace AdditiveFinite

variable {R : Type} [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    (F : ModuleCat R ⥤ ModuleCat R) [F.Additive]
    (A : ModuleCat R) [Module.Free R A] [Module.Finite R A]

noncomputable abbrev basis := Module.finBasis R A
noncomputable abbrev I := Fin (Module.finrank R A)
noncomputable def incl (i : I A) : ModuleCat.of R R ⟶ A :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R A (basis A i))
noncomputable def proj (i : I A) : A ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom ((basis A).coord i)

end AdditiveFinite

end

section

open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace TensorCoefficient

variable {R : Type} [CommRing R]
abbrev c := ComplexShape.down ℕ
variable (K : ChainComplex (ModuleCat.{0} R) ℕ)

noncomputable def functor : ModuleCat.{0} R ⥤ ChainComplex (ModuleCat.{0} R) ℕ where
  obj A := ((tensorRight A).mapHomologicalComplex c).obj K
  map f := (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{0} R)).map f) c).app K
  map_id A := by apply HomologicalComplex.Hom.ext; funext n; change K.X n ◁ 𝟙 A=𝟙 _; simp
  map_comp f g := by apply HomologicalComplex.Hom.ext; funext n; change K.X n ◁ (f≫g)=(K.X n ◁ f)≫(K.X n ◁ g); simp

instance instAdditiveModuleCatChainComplexNatFunctor : (functor K).Additive where
  map_add := by
    intros
    apply HomologicalComplex.Hom.ext
    funext n
    exact MonoidalPreadditive.whiskerLeft_add _ _

noncomputable def homologyFunctor (n : ℕ) : ModuleCat.{0} R ⥤ ModuleCat.{0} R :=
  functor K ⋙ HomologicalComplex.homologyFunctor _ c n

instance instAdditiveModuleCatHomologyFunctor (n : ℕ) : (homologyFunctor K n).Additive := by
  unfold homologyFunctor
  infer_instance

lemma shortExact [∀n,Module.Flat R (K.X n)] {S : ShortComplex (ModuleCat.{0} R)}
    (hS : S.ShortExact) : (S.map (functor K)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  change (S.map (tensorLeft (K.X n))).ShortExact
  exact hS.map_of_exact _

end TensorCoefficient

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalProjection

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
abbrev c := ComplexShape.down ℕ
variable (K : HomologicalComplex₂ C c c)

noncomputable def projection (p q n : ℕ) : (K.total c).X n ⟶ (K.X p).X q :=
  K.totalDesc (fun i j _ => if hi : i=p then if hj : j=q then
    eqToHom (by subst i; subst j; rfl) else 0 else 0)

@[reassoc (attr := simp)] lemma inclusion_projection (p q n : ℕ) (h : p+q=n) :
    K.ιTotal c p q n h ≫ projection K p q n = 𝟙 _ := by
  simp [projection]

@[reassoc] lemma inclusion_projection_of_ne (i j p q n : ℕ) (h : i+j=n)
    (hne : (i,j) ≠ (p,q)) :
    K.ιTotal c i j n h ≫ projection K p q n = 0 := by
  simp only [projection,ι_totalDesc]
  split_ifs with hi hj
  · exact False.elim (hne (Prod.ext hi hj))
  all_goals rfl

abbrev Index (n : ℕ) := ↥(Finset.HasAntidiagonal.antidiagonal n)
noncomputable abbrev inclusion (n : ℕ) (i : Index n) :=
  K.ιTotal c i.val.1 i.val.2 n (Finset.HasAntidiagonal.mem_antidiagonal.mp i.property)
noncomputable abbrev proj (n : ℕ) (i : Index n) := projection K i.val.1 i.val.2 n

lemma sum_projection_inclusion (n : ℕ) :
    (∑ i : Index n,proj K n i ≫ inclusion K n i) = 𝟙 _ := by
  apply total.hom_ext
  intro p q hpq
  let j : Index n := ⟨(p,q),Finset.HasAntidiagonal.mem_antidiagonal.mpr hpq⟩
  rw [Preadditive.comp_sum]
  rw [Finset.sum_eq_single j]
  · change K.ιTotal c p q n hpq ≫ (proj K n j ≫ inclusion K n j) = _
    simp [j,←Category.assoc]
  · intro i _ hij
    rw [←Category.assoc,inclusion_projection_of_ne]
    · simp
    · exact fun h => hij (Subtype.ext h.symm)
  · simp

@[reassoc] lemma D₁_projection (p q : ℕ) :
    K.D₁ c (p+q+1) (p+q) ≫ projection K p q (p+q) =
      projection K (p+1) q (p+q+1) ≫ (K.d (p+1) p).f q := by
  apply total.hom_ext
  intro i j hij
  change i+j=p+q+1 at hij
  cases i with
  | zero =>
    have hj : j=p+q+1 := by omega
    subst j
    rw [←Category.assoc,TotalHomotopy.ι_d₁_zero,zero_comp,
      inclusion_projection_of_ne_assoc K 0 (p+q+1) (p+1) q _ _ (by intro h; have := congrArg Prod.fst h; omega),zero_comp]
  | succ i =>
    rw [←Category.assoc,TotalHomotopy.ι_d₁_succ i j (p+q) (by omega),Category.assoc]
    by_cases hi : i=p
    · subst i
      have : j=q := by omega
      subst j
      simp
    · rw [inclusion_projection_of_ne K i j p q _ _ (by intro h; exact hi (congrArg Prod.fst h)),comp_zero,
        inclusion_projection_of_ne_assoc K (i+1) j (p+1) q _ _ (by intro h; have := congrArg Prod.fst h; omega),zero_comp]

@[reassoc] lemma D₂_projection (p q : ℕ) :
    K.D₂ c (p+q+1) (p+q) ≫ projection K p q (p+q) =
      ((-1 : ℤˣ)^p) • (projection K p (q+1) (p+q+1) ≫ (K.X p).d (q+1) q) := by
  apply total.hom_ext
  intro i j hij
  change i+j=p+q+1 at hij
  cases j with
  | zero =>
    have hi : i=p+q+1 := by omega
    subst i
    rw [←Category.assoc,TotalHomotopy.ι_d₂_zero,zero_comp,Linear.comp_units_smul,←Category.assoc,
      inclusion_projection_of_ne K (p+q+1) 0 p (q+1) _ _ (by intro h; have := congrArg Prod.snd h; omega),zero_comp,smul_zero]
  | succ j =>
    rw [←Category.assoc,TotalHomotopy.ι_d₂_succ i j (p+q) (by omega)]
    simp only [Linear.units_smul_comp,Linear.comp_units_smul,Category.assoc]
    by_cases hi : i=p
    · subst i
      have : j=q := by omega
      subst j
      simp
    · rw [inclusion_projection_of_ne K i j p q _ _ (by intro h; exact hi (congrArg Prod.fst h)),comp_zero,smul_zero,
        inclusion_projection_of_ne_assoc K i (j+1) p (q+1) _ _ (by intro h; exact hi (congrArg Prod.fst h)),zero_comp,smul_zero]

@[reassoc] lemma d_projection (p q : ℕ) :
    (K.total c).d (p+q+1) (p+q) ≫ projection K p q (p+q) =
      projection K (p+1) q (p+q+1) ≫ (K.d (p+1) p).f q +
      ((-1 : ℤˣ)^p) • (projection K p (q+1) (p+q+1) ≫ (K.X p).d (q+1) q) := by
  change (K.D₁ _ _ _ + K.D₂ _ _ _) ≫ _ = _
  rw [Preadditive.add_comp,D₁_projection,D₂_projection]

end TotalProjection

end

section

namespace FilteredFiniteness

universe u
variable {R : Type u} [CommRing R]
variable {A B C E : Type u} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [AddCommGroup E] [Module R E]

structure Data where
  d : A →ₗ[R] B
  e : B →ₗ[R] C
  de : e.comp d=0
  FA : ℤ → Submodule R A
  FB : ℤ → Submodule R B
  FC : ℤ → Submodule R C
  monoB : Monotone FB

namespace Data
variable (K : Data (R:=R) (A:=A) (B:=B) (C:=C))

def dCycles : A →ₗ[R] LinearMap.ker K.e :=
  K.d.codRestrict _ (fun x => by
    change K.e (K.d x)=0
    exact congrArg (fun f : A →ₗ[R] C => f x) K.de)

abbrev H := LinearMap.ker K.e ⧸ LinearMap.range K.dCycles

def π : LinearMap.ker K.e →ₗ[R] K.H := (LinearMap.range K.dCycles).mkQ

def cycles (p : ℤ) : Submodule R (LinearMap.ker K.e) :=
  (K.FB p).comap (LinearMap.ker K.e).subtype

def πp (p : ℤ) : K.cycles p →ₗ[R] K.H := K.π.comp (K.cycles p).subtype

def filtration (p : ℤ) : Submodule R K.H := LinearMap.range (K.πp p)

def Z₂ (p : ℤ) : Submodule R B := K.FB p ⊓ (K.FC (p-2)).comap K.e

def B₂ (p : ℤ) : Submodule R B :=
  (K.FB (p-1) ⊓ (K.FC (p-2)).comap K.e) ⊔ ((K.FA (p+1)).map K.d ⊓ K.FB p)

abbrev E₂ (p : ℤ) := K.Z₂ p ⧸ (K.B₂ p).comap (K.Z₂ p).subtype

def lead (p : ℤ) : K.cycles p →ₗ[R] K.E₂ p :=
  ((K.B₂ p).comap (K.Z₂ p).subtype).mkQ.comp
    (((LinearMap.ker K.e).subtype.comp (K.cycles p).subtype).codRestrict _ (fun x => by
      refine ⟨x.property,?_⟩
      change K.e x.val.val∈K.FC (p-2)
      rw [x.val.property]
      exact (K.FC _).zero_mem))

lemma lead_eq_zero {p : ℤ} (x : K.cycles p) :
    K.lead p x=0 ↔ x.val.val∈K.B₂ p := by
  exact Submodule.Quotient.mk_eq_zero ((K.B₂ p).comap (K.Z₂ p).subtype)

lemma lower_of_lead_zero {p : ℤ} (x : K.cycles p) (hx : K.lead p x=0) :
    K.πp p x∈K.filtration (p-1) := by
  obtain ⟨y,hy,z,hz,hyz⟩ := Submodule.mem_sup.mp ((K.lead_eq_zero x).mp hx)
  obtain ⟨a,ha,haz⟩ := hz.1
  have hza : K.e z=0 := by
    rw [←haz]
    exact congrArg (fun f : A →ₗ[R] C => f a) K.de
  have hey : K.e y=0 := by
    have he := congrArg K.e hyz
    rw [map_add,hza,add_zero,x.val.property] at he
    exact he
  let y' : K.cycles (p-1) := ⟨⟨y,hey⟩,hy.1⟩
  refine ⟨y',?_⟩
  change K.π ⟨y,hey⟩=K.π x.val
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-a,?_⟩
  apply Subtype.ext
  change K.d (-a)=y-x.val.val
  rw [map_neg,haz,←hyz]
  abel

end Data
end FilteredFiniteness

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalProjection

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma projection_eq_zero (p q n : ℕ) (h : p+q≠n) : projection K p q n = 0 := by
  apply total.hom_ext
  intro i j hij
  rw [inclusion_projection_of_ne]
  · simp
  · intro h'
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj h'
    exact h hij

lemma element_ext {n : ℕ} {x y : (K.total c).X n}
    (h : ∀ i : Index n,proj K n i x = proj K n i y) : x=y := by
  have hx := congrArg (fun f : (K.total c).X n ⟶ (K.total c).X n => f x)
    (sum_projection_inclusion K n)
  have hy := congrArg (fun f : (K.total c).X n ⟶ (K.total c).X n => f y)
    (sum_projection_inclusion K n)
  simp only [ModuleCat.hom_sum,LinearMap.sum_apply,ModuleCat.comp_apply,ModuleCat.id_apply] at hx hy
  rw [←hx,←hy]
  exact Finset.sum_congr rfl (fun i _ => congrArg (inclusion K n i) (h i))

def filtration (n : ℕ) (p : ℤ) : Submodule R ((K.total c).X n) where
  carrier := { x | ∀ i : Index n, p ≤ (i.val.1:ℤ) → proj K n i x=0 }
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [map_add,hx i hi,hy i hi]
  smul_mem' := by intro r x hx i hi; simp [map_smul,hx i hi]

lemma filtration_mono (n : ℕ) : Monotone (filtration K n) := by
  intro p q hpq x hx i hi
  exact hx i (hpq.trans hi)

lemma filtration_zero (n : ℕ) : filtration K n 0=⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply (Submodule.mem_bot R).mpr
  apply element_ext K
  intro i
  simpa using hx i (by omega)

lemma filtration_top (n : ℕ) : filtration K n (n+1)=⊤ := by
  apply top_unique
  intro x _ i hi
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp i.property
  omega

lemma entry_zero {n p q : ℕ} {k : ℤ} {x : (K.total c).X n}
    (hx : x∈filtration K n k) (hp : k≤(p:ℤ)) : projection K p q n x=0 := by
  by_cases h : p+q=n
  · exact hx ⟨(p,q),Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩ hp
  · rw [projection_eq_zero K p q n h]; rfl

lemma inclusion_mem {p q n : ℕ} (h : p+q=n) (x : (K.X p).X q) {k : ℤ}
    (hp : (p:ℤ)<k) : K.ιTotal c p q n h x ∈ filtration K n k := by
  intro i hi
  have he := inclusion_projection_of_ne K p q i.val.1 i.val.2 n h (by
    intro h'
    have he := congrArg Prod.fst h'
    dsimp at he
    omega)
  exact congrArg (fun f : (K.X p).X q ⟶ (K.X i.val.1).X i.val.2 => f x) he

lemma d_filtration {n m : ℕ} {k : ℤ} {x : (K.total c).X n}
    (hx : x∈filtration K n k) : (K.total c).d n m x∈filtration K m k := by
  by_cases h : m+1=n
  · subst n
    intro i hi
    obtain ⟨⟨p,q⟩,hpq⟩ := i
    have hpq' : p+q=m := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
    subst m
    have hd := congrArg (fun f : (K.total c).X (p+q+1) ⟶ (K.X p).X q => f x)
      (d_projection K p q)
    change projection K p q (p+q) ((K.total c).d (p+q+1) (p+q) x)=0
    simp only [ModuleCat.comp_apply] at hd
    rw [hd]
    change (projection K (p+1) q (p+q+1) ≫ (K.d (p+1) p).f q +
      ((-1 : ℤˣ)^p) • (projection K p (q+1) (p+q+1) ≫ (K.X p).d (q+1) q)).hom x=0
    simp only [ModuleCat.hom_add,LinearMap.add_apply,ModuleCat.hom_comp,LinearMap.comp_apply,Units.smul_def,ModuleCat.hom_zsmul,LinearMap.smul_apply,
      entry_zero K hx (by dsimp at hi; omega : k≤((p+1:ℕ):ℤ)),entry_zero K hx hi,map_zero,smul_zero,add_zero]
  · rw [(K.total c).shape n m (by exact h)]
    exact (filtration K m k).zero_mem

noncomputable def filteredData (n : ℕ) : FilteredFiniteness.Data
    (R:=R) (A:=(K.total c).X (n+1)) (B:=(K.total c).X n) (C:=(K.total c).X (n-1)) where
  d := ((K.total c).d (n+1) n).hom
  e := ((K.total c).d n (n-1)).hom
  de := by exact ModuleCat.hom_ext_iff.mp ((K.total c).d_comp_d (n+1) n (n-1))
  FA := filtration K (n+1)
  FB := filtration K n
  FC := filtration K (n-1)
  monoB := filtration_mono K n

end TotalProjection

end

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading

universe u
variable {R : Type u} [CommRing R]
open TotalProjection
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma d_entry (p q : ℕ) (x : (K.total c).X (p+q+1)) :
    projection K p q (p+q) ((K.total c).d (p+q+1) (p+q) x) =
      (K.d (p+1) p).f q (projection K (p+1) q (p+q+1) x) +
      ((-1 : ℤˣ)^p) • (K.X p).d (q+1) q (projection K p (q+1) (p+q+1) x) := by
  have h := congrArg (fun f : (K.total c).X (p+q+1) ⟶ (K.X p).X q => f.hom x)
    (d_projection K p q)
  simpa only [ModuleCat.hom_add,ModuleCat.hom_comp,LinearMap.comp_apply,LinearMap.add_apply,
    Units.smul_def,ModuleCat.hom_zsmul,LinearMap.smul_apply] using h

lemma d_entry' (p q n m : ℕ) (hn : p+q+1=n) (hm : p+q=m) (x : (K.total c).X n) :
    projection K p q m ((K.total c).d n m x) =
      (K.d (p+1) p).f q (projection K (p+1) q n x) +
      ((-1 : ℤˣ)^p) • (K.X p).d (q+1) q (projection K p (q+1) n x) := by
  subst n; subst m; exact d_entry K p q x

lemma z₂_top_cycle (p q : ℕ) (x : (filteredData K (p+q)).Z₂ ((p:ℤ)+1)) :
    (K.X p).d q (q-1) (projection K p q (p+q) x)=0 := by
  cases q with
  | zero => rw [(K.X p).shape 0 (0-1) (by decide)]; rfl
  | succ q =>
    rw [show q+1-1=q by omega]
    have hd := d_entry K p q x.val
    have hz : projection K p q (p+q) ((K.total c).d (p+q+1) (p+q) x.val)=0 := by
      apply entry_zero K x.property.2
      omega
    have hf : projection K (p+1) q (p+q+1) x.val=0 := entry_zero K x.property.1 (by omega)
    rw [hz,hf,map_zero,zero_add] at hd
    have hs : ((-1 : ℤˣ)^p) • (K.X p).d (q+1) q (projection K p (q+1) (p+q+1) x.val)=0 := hd.symm
    have hh := congrArg (fun z => (((-1 : ℤˣ)^p)⁻¹) • z) hs
    rw [inv_smul_smul,smul_zero] at hh
    exact hh

noncomputable def topCycle (p q : ℕ) : (filteredData K (p+q)).Z₂ ((p:ℤ)+1) →ₗ[R]
    ConcreteHomology.Cycles (K.X p) q :=
  ((projection K p q (p+q)).hom.comp ((filteredData K (p+q)).Z₂ ((p:ℤ)+1)).subtype).codRestrict
    _ (z₂_top_cycle K p q)

noncomputable def row (q : ℕ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((ConcreteHomology.functor q).mapHomologicalComplex c).obj K

lemma z₂_top_horizontal (p q : ℕ) (x : (filteredData K (p+q)).Z₂ ((p:ℤ)+1)) :
    (row K q).d p (p-1) (ConcreteHomology.π (K.X p) q (topCycle K p q x))=0 := by
  cases p with
  | zero => rw [(row K q).shape 0 (0-1) (by decide)]; rfl
  | succ p =>
    change ((ConcreteHomology.functor q).map (K.d (p+1) p)).hom
      (ConcreteHomology.π (K.X (p+1)) q (topCycle K (p+1) q x))=0
    rw [ConcreteHomology.map_π]
    apply (ConcreteHomology.π_eq_zero (K.X p) q _).mpr
    have hd := d_entry' K p q (p+1+q) (p+1+q-1) (by omega) (by omega) x.val
    have hz : projection K p q (p+1+q-1) ((K.total c).d (p+1+q) (p+1+q-1) x.val)=0 := by
      apply entry_zero K x.property.2
      omega
    rw [hz] at hd
    refine ⟨- ((-1 : ℤˣ)^p) • (projection K p (q+1) (p+1+q) x.val),?_⟩
    apply Subtype.ext
    rw [ConcreteHomology.cyclesMap_val]
    change (K.X p).d (q+1) q (- ((-1 : ℤˣ)^p) • (projection K p (q+1) (p+1+q) x.val))=
      (K.d (p+1) p).f q (projection K (p+1) q (p+1+q) x.val)
    simp only [Units.smul_def,map_zsmul,Units.val_neg,neg_smul,map_neg]
    simpa only [Units.smul_def] using (eq_neg_of_add_eq_zero_left hd.symm).symm

noncomputable def topRowCycle (p q : ℕ) : (filteredData K (p+q)).Z₂ ((p:ℤ)+1) →ₗ[R]
    ConcreteHomology.Cycles (row K q) p :=
  ((ConcreteHomology.π (K.X p) q).comp (topCycle K p q)).codRestrict _ (z₂_top_horizontal K p q)

noncomputable def lead (p q : ℕ) : (filteredData K (p+q)).Z₂ ((p:ℤ)+1) →ₗ[R]
    ConcreteHomology.H (row K q) p :=
  (ConcreteHomology.π (row K q) p).comp (topRowCycle K p q)

end E2Leading

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_E2Boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading

universe u
variable {R : Type u} [CommRing R]
open TotalProjection
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma entry_inclusion (p q n : ℕ) (h : p+q=n) (x : (K.X p).X q) :
    projection K p q n (K.ιTotal c p q n h x)=x :=
  congrArg (fun f : (K.X p).X q ⟶ (K.X p).X q => f.hom x) (inclusion_projection K p q n h)

lemma entry_inclusion_ne (i j p q n : ℕ) (h : i+j=n) (hne : (i,j)≠(p,q)) (x : (K.X i).X j) :
    projection K p q n (K.ιTotal c i j n h x)=0 :=
  congrArg (fun f : (K.X i).X j ⟶ (K.X p).X q => f.hom x)
    (inclusion_projection_of_ne K i j p q n h hne)

lemma lower_filtration (p q : ℕ) {x : (K.total c).X (p+q)}
    (hx : x∈filtration K (p+q) ((p:ℤ)+1)) (htop : projection K p q (p+q) x=0) :
    x∈filtration K (p+q) p := by
  intro i hi
  by_cases he : i.val.1=p
  · obtain ⟨⟨i,j⟩,hij⟩ := i
    dsimp at he
    subst i
    have hj : j=q := by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij; omega
    subst j
    exact htop
  · exact hx i (by omega)

lemma lower_filtration' (p q n : ℕ) (hn : p+q=n) {x : (K.total c).X n}
    (hx : x∈filtration K n ((p:ℤ)+1)) (htop : projection K p q n x=0) :
    x∈filtration K n p := by
  subst n
  exact lower_filtration K p q hx htop

lemma linear_units_smul {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (f : A →ₗ[R] B) (a : ℤˣ) (x : A) :
    f (a • x)=a • f x := by simp [Units.smul_def]

noncomputable def lift (p q : ℕ) (y : (K.X (p+1)).X q) (z : (K.X p).X (q+1)) :
    (K.total c).X (p+q+1) :=
  K.ιTotal c (p+1) q (p+q+1) (by dsimp; omega) y +
    ((-1 : ℤˣ)^p) • K.ιTotal c p (q+1) (p+q+1) (by dsimp; omega) z

lemma lift_mem (p q : ℕ) (y : (K.X (p+1)).X q) (z : (K.X p).X (q+1)) :
    lift K p q y z ∈ filtration K (p+q+1) ((p:ℤ)+2) := by
  apply Submodule.add_mem
  · exact inclusion_mem K (by omega) y (by omega)
  · change ((-1 : ℤˣ)^p) • _ ∈ _
    rw [Units.smul_def]
    exact (filtration K (p+q+1) ((p:ℤ)+2)).toAddSubgroup.zsmul_mem
      (inclusion_mem K (by omega) z (by omega)) _

@[simp] lemma lift_left (p q : ℕ) (y : (K.X (p+1)).X q) (z : (K.X p).X (q+1)) :
    projection K (p+1) q (p+q+1) (lift K p q y z)=y := by
  simp only [lift,map_add,Units.smul_def,map_zsmul,entry_inclusion,
    entry_inclusion_ne K p (q+1) (p+1) q _ _ (by intro h; have := congrArg Prod.fst h; omega),
    smul_zero,add_zero]

@[simp] lemma lift_right (p q : ℕ) (y : (K.X (p+1)).X q) (z : (K.X p).X (q+1)) :
    projection K p (q+1) (p+q+1) (lift K p q y z)=((-1 : ℤˣ)^p) • z := by
  simp only [lift,map_add,Units.smul_def,map_zsmul,entry_inclusion,
    entry_inclusion_ne K (p+1) q p (q+1) _ _ (by intro h; have := congrArg Prod.fst h; omega),
    zero_add]

lemma neg_pow_smul_twice {A : Type*} [AddCommGroup A] (p : ℕ) (a : A) :
    ((-1 : ℤˣ)^p) • (((-1 : ℤˣ)^p) • a)=a := by
  rw [smul_smul,←mul_pow]
  simp

lemma d_lift_top (p q : ℕ) (y : (K.X (p+1)).X q) (z : (K.X p).X (q+1)) :
    projection K p q (p+q) ((K.total c).d (p+q+1) (p+q) (lift K p q y z))=
      (K.d (p+1) p).f q y + (K.X p).d (q+1) q z := by
  rw [d_entry,lift_left,lift_right]
  congr 1
  change ((-1 : ℤˣ)^p) • ((K.X p).d (q+1) q).hom (((-1 : ℤˣ)^p) • z) = _
  rw [linear_units_smul,neg_pow_smul_twice]

lemma d_lift_mem (p q : ℕ) (y : ConcreteHomology.Cycles (K.X (p+1)) q)
    (z : (K.X p).X (q+1)) :
    (K.total c).d (p+q+1) (p+q) (lift K p q y.val z) ∈ filtration K (p+q) ((p:ℤ)+1) := by
  cases q with
  | zero =>
    simpa only [Nat.add_zero,filtration_top] using
      (show (K.total c).d (p+1) p (lift K p 0 y.val z)∈(⊤ : Submodule R _) from trivial)
  | succ q =>
    apply lower_filtration' K (p+1) q (p+(q+1)) (by omega)
    · exact d_filtration K (lift_mem K p (q+1) y.val z)
    · have he := d_entry' K (p+1) q (p+(q+1)+1) (p+(q+1)) (by omega) (by omega) (lift K p (q+1) y.val z)
      have hz : projection K (p+1+1) q (p+(q+1)+1) (lift K p (q+1) y.val z)=0 :=
        entry_zero K (lift_mem K p (q+1) y.val z) (by omega)
      rw [hz,map_zero,zero_add] at he
      have hy : projection K (p+1) (q+1) (p+(q+1)+1) (lift K p (q+1) y.val z)=y.val :=
        lift_left K p (q+1) y.val z
      rw [hy] at he
      have hcyc : (K.X (p+1)).d (q+1) q y.val=0 := y.property
      rw [hcyc,smul_zero] at he
      exact he

end E2Leading

end

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading

universe u
variable {R : Type u} [CommRing R]
open TotalProjection
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma lead_zero_boundary (p q : ℕ) (x : (filteredData K (p+q)).Z₂ ((p:ℤ)+1))
    (hx : lead K p q x=0) : x.val∈(filteredData K (p+q)).B₂ ((p:ℤ)+1) := by
  obtain ⟨u,hu⟩ := (ConcreteHomology.π_eq_zero (row K q) p (topRowCycle K p q x)).mp hx
  obtain ⟨y,rfl⟩ := ConcreteHomology.π_surjective (K.X (p+1)) q u
  have he : ConcreteHomology.π (K.X p) q (ConcreteHomology.cyclesMap (K.d (p+1) p) q y)=
      ConcreteHomology.π (K.X p) q (topCycle K p q x) := by
    have h := congrArg Subtype.val hu
    change ((ConcreteHomology.functor q).map (K.d (p+1) p)).hom
      (ConcreteHomology.π (K.X (p+1)) q y)= _ at h
    rw [ConcreteHomology.map_π] at h
    exact h
  have hπ : ConcreteHomology.π (K.X p) q
      (topCycle K p q x - ConcreteHomology.cyclesMap (K.d (p+1) p) q y)=0 := by
    rw [map_sub,he,sub_self]
  obtain ⟨z,hz⟩ := (ConcreteHomology.π_eq_zero _ _ _).mp hπ
  have hzval : (K.X p).d (q+1) q z = projection K p q (p+q) x.val - (K.d (p+1) p).f q y.val := by
    have h := congrArg Subtype.val hz
    change (K.X p).d (q+1) q z = (topCycle K p q x).val - (ConcreteHomology.cyclesMap (K.d (p+1) p) q y).val at h
    rw [ConcreteHomology.cyclesMap_val] at h
    exact h
  let w := lift K p q y.val z
  have hw : w∈(filteredData K (p+q)).FA (((p:ℤ)+1)+1) := by
    change w∈filtration K (p+q+1) (((p:ℤ)+1)+1)
    simpa only [Int.add_assoc,Int.reduceAdd] using lift_mem K p q y.val z
  have hdw := d_lift_mem K p q y z
  have htop : projection K p q (p+q) ((K.total c).d (p+q+1) (p+q) w) =
      projection K p q (p+q) x.val := by
    calc
      _ = (K.d (p+1) p).f q y.val + (K.X p).d (q+1) q z := d_lift_top K p q y.val z
      _ = _ := by rw [hzval]; abel
  have hlower : x.val - (K.total c).d (p+q+1) (p+q) w∈filtration K (p+q) p := by
    apply lower_filtration K p q ((filtration K _ _).sub_mem x.property.1 hdw)
    rw [map_sub,htop,sub_self]
  refine Submodule.mem_sup.mpr ⟨x.val-(K.total c).d (p+q+1) (p+q) w,⟨?_,?_⟩,
    (K.total c).d (p+q+1) (p+q) w,⟨⟨w,hw,rfl⟩,hdw⟩,sub_add_cancel _ _⟩
  · change x.val-(K.total c).d (p+q+1) (p+q) w∈filtration K (p+q) (((p:ℤ)+1)-1)
    simpa using hlower
  · change (K.total c).d (p+q) (p+q-1) (x.val-(K.total c).d (p+q+1) (p+q) w)∈
      filtration K (p+q-1) (((p:ℤ)+1)-2)
    rw [map_sub]
    have hd : (K.total c).d (p+q) (p+q-1) ((K.total c).d (p+q+1) (p+q) w)=0 :=
      congrArg (fun f : (K.total c).X (p+q+1) ⟶ (K.total c).X (p+q-1) => f.hom w)
        ((K.total c).d_comp_d _ _ _)
    rw [hd,sub_zero]
    exact x.property.2

end E2Leading

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_BiResolution
attribute [-instance] _root_.OAI.ModelAssembly.assembly_additive _root_.OAI.ModelAssembly.assembly_preservesColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace BiResolution

open DiagonalResolution

noncomputable def row (p : SimplexCategory) : SimplicialObject (D ⥤ A) where
  obj q := free (p,q.unop)
  map f := pre (Prod.mkHom (𝟙 p) f.unop)
  map_id q := by simpa only [unop_id,←prod_id] using pre_id (p,q.unop)
  map_comp f g := by
    simpa only [prod_comp, Prod.mkHom, unop_comp, Category.id_comp] using
      pre_comp (Prod.mkHom (𝟙 p) g.unop) (Prod.mkHom (𝟙 p) f.unop)

noncomputable def rowMap {p p' : SimplexCategory} (f : p ⟶ p') : row p' ⟶ row p where
  app q := pre (Prod.mkHom f (𝟙 q.unop))
  naturality q q' g := by
    dsimp [row]
    rw [←pre_comp,←pre_comp]
    congr 1

noncomputable def chains : SimplicialObject (SimplicialObject (D ⥤ A)) where
  obj p := row p.unop
  map f := rowMap f.unop
  map_id p := by
    apply NatTrans.ext
    funext q
    dsimp [rowMap]
    simpa only [unop_id,←prod_id,row] using pre_id (p.unop,q.unop)
  map_comp f g := by
    apply NatTrans.ext
    funext q
    dsimp [rowMap, row]
    simpa only [prod_comp,Prod.mkHom,unop_comp,Category.id_comp] using
      pre_comp (Prod.mkHom g.unop (𝟙 q.unop)) (Prod.mkHom f.unop (𝟙 q.unop))

noncomputable def complex : HomologicalComplex₂ (D ⥤ A) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  AlternatingFaceMapComplex.obj (chains ⋙ alternatingFaceMapComplex (D ⥤ A))

noncomputable def total : ChainComplex (D ⥤ A) ℕ := complex.total (ComplexShape.down ℕ)

instance projective (n : ℕ) : Projective (total.X n) := by
  change Projective (∐ (fun ij : {ij : ℕ × ℕ // ij.1+ij.2=n} => free (⦋ij.1.1⦌,⦋ij.1.2⦌)))
  have (ij : {ij : ℕ × ℕ // ij.1+ij.2=n}) : Projective (free (⦋ij.1.1⦌,⦋ij.1.2⦌)) :=
    (evaluationAdjunctionRight A _).map_projective Z inferInstance
  infer_instance

noncomputable def chainsAt (d : D) : SimplicialObject (SimplicialObject A) :=
  chains ⋙ (SimplicialObject.whiskering _ _).obj ((evaluation D A).obj d)

noncomputable def point (d : D) : SimplicialObject A where
  obj q := ∐ (fun _ : q.unop ⟶ d.2 => Z)
  map f := Sigma.desc (fun g => Sigma.ι (fun _ : _ ⟶ d.2 => Z) (f.unop ≫ g))
  map_id q := by apply Sigma.hom_ext; intro g; simp
  map_comp f g := by apply Sigma.hom_ext; intro h; simp [Category.assoc]

@[simp] lemma chainsAt_obj_map (d : D) (p : SimplexCategoryᵒᵖ)
    {q q' : SimplexCategoryᵒᵖ} (f : q ⟶ q') :
    ((chainsAt d).obj p).map f = (pre (Prod.mkHom (𝟙 p.unop) f.unop)).app d := rfl
@[simp] lemma chainsAt_map_app (d : D) {p p' : SimplexCategoryᵒᵖ} (f : p ⟶ p')
    (q : SimplexCategoryᵒᵖ) :
    ((chainsAt d).map f).app q = (pre (Prod.mkHom f.unop (𝟙 q.unop))).app d := rfl
noncomputable def augmentation (d : D) : chainsAt d ⟶ (SimplicialObject.const _).obj (point d) where
  app p :=
    { app q := Sigma.desc (fun f : (p.unop,q.unop) ⟶ d => Sigma.ι (fun _ : q.unop ⟶ d.2 => Z) f.2)
      naturality q q' f := by
        apply Sigma.hom_ext
        intro g
        simp [point,pre]
        erw [Sigma.ι_desc_assoc, Sigma.ι_desc,
          Sigma.ι_desc_assoc, Sigma.ι_desc] }
  naturality p p' f := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro g
    simp [pre]
    erw [Sigma.ι_desc_assoc, Sigma.ι_desc]
    rfl

noncomputable def augmentedAt (d : D) : SimplicialObject.Augmented (SimplicialObject A) where
  left := chainsAt d
  right := point d
  hom := augmentation d
noncomputable def section_ (d : D) : point d ⟶ (chainsAt d).obj (op ⦋0⦌) where
  app q := Sigma.desc (fun f : q.unop ⟶ d.2 =>
    Sigma.ι (fun _ : (⦋0⦌,q.unop) ⟶ d => Z) (zeroSimplex d.1,f))
  naturality q q' f := by
    apply Sigma.hom_ext
    intro g
    simp [point,pre]
    erw [Sigma.ι_desc_assoc, Sigma.ι_desc]
    rfl

open SSet.Augmented.StandardSimplex in
noncomputable def shift_ (d : D) (n : ℕ) :
    (chainsAt d).obj (op ⦋n⦌) ⟶ (chainsAt d).obj (op ⦋n+1⦌) where
  app q := Sigma.desc (fun f : (⦋n⦌,q.unop) ⟶ d =>
    Sigma.ι (fun _ : (⦋n+1⦌,q.unop) ⟶ d => Z) (shift f.1,f.2))
  naturality q q' f := by
    apply Sigma.hom_ext
    intro g
    simp [pre]
    erw [Sigma.ι_desc_assoc, Sigma.ι_desc,
      Sigma.ι_desc_assoc, Sigma.ι_desc]
noncomputable def extra (d : D) : (augmentedAt d).ExtraDegeneracy where
  s' := section_ d
  s := shift_ d
  s'_comp_ε := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro f
    dsimp only [augmentedAt,section_,shift_,augmentation,SimplicialObject.δ,SimplicialObject.σ,NatTrans.comp_app,NatTrans.id_app]
    simp
    erw [Sigma.ι_desc_assoc, Sigma.ι_desc, Category.comp_id]
  s₀_comp_δ₁ := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro f
    dsimp only [augmentedAt,section_,shift_,augmentation,SimplicialObject.δ,SimplicialObject.σ,NatTrans.comp_app,NatTrans.id_app]
    simp only [Quiver.Hom.unop_op, chainsAt_map_app, pre, prod_comp, Prod.mkHom, Category.id_comp]
    erw [Sigma.ι_desc_assoc, Sigma.ι_desc,
      Sigma.ι_desc_assoc, Sigma.ι_desc]
    simp only [shift_δ₁]
    rfl
  s_comp_δ₀ n := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro f
    dsimp only [augmentedAt,section_,shift_,augmentation,SimplicialObject.δ,SimplicialObject.σ,NatTrans.comp_app,NatTrans.id_app]
    simp only [Quiver.Hom.unop_op, chainsAt_map_app, pre, prod_comp, Prod.mkHom, Category.id_comp]
    erw [Sigma.ι_desc_assoc, Sigma.ι_desc]
    simp only [shift_δ₀, Prod.eta]
    exact (Category.comp_id _).symm
  s_comp_δ n i := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro f
    dsimp only [augmentedAt,section_,shift_,augmentation,SimplicialObject.δ,SimplicialObject.σ,NatTrans.comp_app,NatTrans.id_app]
    simp only [Quiver.Hom.unop_op, chainsAt_map_app, pre, prod_comp, Prod.mkHom, Category.id_comp]
    erw [Sigma.ι_desc_assoc, Sigma.ι_desc,
      Sigma.ι_desc_assoc, Sigma.ι_desc]
    simp only [shift_δ_succ]
    rfl
  s_comp_σ n i := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro f
    dsimp only [augmentedAt,section_,shift_,augmentation,SimplicialObject.δ,SimplicialObject.σ,NatTrans.comp_app,NatTrans.id_app]
    simp only [Quiver.Hom.unop_op, chainsAt_map_app, pre, prod_comp, Prod.mkHom, Category.id_comp]
    erw [Sigma.ι_desc_assoc, Sigma.ι_desc,
      Sigma.ι_desc_assoc, Sigma.ι_desc]
    simp only [shift_σ_succ]
    rfl

end BiResolution

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalSingle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalHomotopy

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasCoproducts.{0} C]

noncomputable def equiv {K L : HomologicalComplex₂ C c c} (e : HomotopyEquiv K L) :
    HomotopyEquiv (K.total c) (L.total c) where
  hom := HomologicalComplex₂.total.map e.hom c
  inv := HomologicalComplex₂.total.map e.inv c
  homotopyHomInvId := by simpa using total e.homotopyHomInvId
  homotopyInvHomId := by simpa using total e.homotopyInvHomId

noncomputable abbrev single (K : ChainComplex C ℕ) : HomologicalComplex₂ C c c := (ChainComplex.single₀ (ChainComplex C ℕ)).obj K

noncomputable def singleIn (K : ChainComplex C ℕ) : K ⟶ (single K).total c where
  f n := (single K).ιTotal c 0 n n (by simp)
  comm' i j h := by
    change j+1=i at h
    subst i
    exact ι_d_leftZero (K := single K) j

noncomputable def singleOutF (K : ChainComplex C ℕ) (n : ℕ) :
    ((single K).total c).X n ⟶ K.X n :=
  (single K).totalDesc (fun p q hpq => if hp : p=0 then by
    subst p
    have hq : q=n := by simpa using hpq
    subst q
    exact 𝟙 _
    else 0)
@[reassoc, simp] lemma singleIn_out (K : ChainComplex C ℕ) (n : ℕ) :
    (singleIn K).f n ≫ singleOutF K n = 𝟙 _ := by
  dsimp only [singleIn, singleOutF]
  erw [ι_totalDesc]
  simp
@[reassoc, simp] lemma singleOut_in (K : ChainComplex C ℕ) (n : ℕ) :
    singleOutF K n ≫ (singleIn K).f n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [←Category.assoc,singleOutF,ι_totalDesc]
  split_ifs with hp
  · subst p
    have : q=n := by simpa using hpq
    subst q
    dsimp only [singleIn]
    erw [Category.id_comp, Category.comp_id]
  · have hz : IsZero (((single K).X p).X q) := by
      exact ((eval C c q).map_isZero
        (isZero_single_obj_X c 0 K p hp))
    exact hz.eq_of_src _ _

instance singleIn_isIso (K : ChainComplex C ℕ) : IsIso (singleIn K) := by
  have (n : ℕ) : IsIso ((singleIn K).f n) :=
    ⟨⟨singleOutF K n, singleIn_out K n, singleOut_in K n⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components (singleIn K)

noncomputable def singleIso (K : ChainComplex C ℕ) : (single K).total c ≅ K :=
  (asIso (singleIn K)).symm

end TotalHomotopy

end

section

open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace BiResolution

open DiagonalResolution SSet.Augmented.StandardSimplex
abbrev c := ComplexShape.down ℕ

noncomputable def pointAugmentation (d : D) : point d ⟶ (SimplicialObject.const A).obj Z where
  app q := Sigma.desc (fun _ : q.unop ⟶ d.2 => 𝟙 Z)
  naturality q q' f := by apply Sigma.hom_ext; intro g; simp [point]

noncomputable def pointAugmented (d : D) : SimplicialObject.Augmented A where
  left := point d
  right := Z
  hom := pointAugmentation d

noncomputable def pointExtra (d : D) : (pointAugmented d).ExtraDegeneracy where
  s' := Sigma.ι (fun _ : ⦋0⦌ ⟶ d.2 => Z) (zeroSimplex d.2)
  s n := Sigma.desc (fun f : ⦋n⦌ ⟶ d.2 => Sigma.ι (fun _ : ⦋n+1⦌ ⟶ d.2 => Z) (shift f))
  s'_comp_ε := by exact Sigma.ι_desc _ _
  s₀_comp_δ₁ := by
    apply Sigma.hom_ext
    intro f
    dsimp only [pointAugmented,pointAugmentation,SimplicialObject.δ,point]
    simp only [Sigma.ι_desc_assoc,Sigma.ι_desc,Quiver.Hom.unop_op,shift_δ₁,Category.id_comp]
  s_comp_δ₀ n := by
    apply Sigma.hom_ext
    intro f
    dsimp only [pointAugmented,pointAugmentation,SimplicialObject.δ,point]
    simp only [Sigma.ι_desc_assoc,Sigma.ι_desc,Quiver.Hom.unop_op,shift_δ₀,Category.comp_id]
  s_comp_δ n i := by
    apply Sigma.hom_ext
    intro f
    dsimp only [pointAugmented,pointAugmentation,SimplicialObject.δ,point]
    simp only [Sigma.ι_desc_assoc,Sigma.ι_desc,Quiver.Hom.unop_op,shift_δ_succ]
  s_comp_σ n i := by
    apply Sigma.hom_ext
    intro f
    dsimp only [pointAugmented,pointAugmentation,SimplicialObject.σ,point]
    simp only [Sigma.ι_desc_assoc,Sigma.ι_desc,Quiver.Hom.unop_op,shift_σ_succ]

noncomputable def complexAt (d : D) : HomologicalComplex₂ A c c :=
  AlternatingFaceMapComplex.obj (chainsAt d ⋙ alternatingFaceMapComplex A)

noncomputable def complexAtIso (d : D) :
    (((alternatingFaceMapComplex A).mapHomologicalComplex c).obj
      (AlternatingFaceMapComplex.obj (chainsAt d))) ≅ complexAt d :=
  eqToIso (congrArg (fun F => F.obj (chainsAt d))
    (map_alternatingFaceMapComplex (alternatingFaceMapComplex A)))

noncomputable def complexAtEquiv (d : D) : HomotopyEquiv (complexAt d)
    (TotalHomotopy.single (AlternatingFaceMapComplex.obj (point d))) :=
  (HomotopyEquiv.ofIso (complexAtIso d).symm).trans
    (((alternatingFaceMapComplex A).mapHomotopyEquiv (extra d).homotopyEquiv).trans
      (HomotopyEquiv.ofIso ((HomologicalComplex.singleMapHomologicalComplex
        (alternatingFaceMapComplex A) c 0).app (point d))))

noncomputable def totalAtEquiv (d : D) : HomotopyEquiv ((complexAt d).total c)
    ((ChainComplex.single₀ A).obj Z) :=
  (TotalHomotopy.equiv (complexAtEquiv d)).trans
    ((HomotopyEquiv.ofIso (TotalHomotopy.singleIso _)).trans (pointExtra d).homotopyEquiv)

end BiResolution

end

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalFunctor

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
  {E : Type u'} [Category.{v'} E] [Preadditive E] [HasCoproducts.{0} E]
open TotalHomotopy
variable (F : C ⥤ E) [F.Additive]
noncomputable abbrev map₂ (K : HomologicalComplex₂ C c c) : HomologicalComplex₂ E c c :=
  ((F.mapHomologicalComplex c).mapHomologicalComplex c).obj K

noncomputable def comparisonF (K : HomologicalComplex₂ C c c) (n : ℕ) :
    ((map₂ F K).total c).X n ⟶ F.obj ((K.total c).X n) :=
  (map₂ F K).totalDesc (fun p q hpq => F.map (K.ιTotal c p q n hpq))

@[reassoc (attr := simp)] lemma ι_comparisonF (K : HomologicalComplex₂ C c c)
    (p q n : ℕ) (hpq : p+q=n) :
    (map₂ F K).ιTotal c p q n hpq ≫ comparisonF F K n = F.map (K.ιTotal c p q n hpq) := by
  apply ι_totalDesc

noncomputable def comparison (K : HomologicalComplex₂ C c c) :
    (map₂ F K).total c ⟶ (F.mapHomologicalComplex c).obj (K.total c) where
  f := comparisonF F K
  comm' i j h := by
    change j+1=i at h
    subst i
    apply total.hom_ext
    intro p q hpq
    change p+q=j+1 at hpq
    cases p with
    | zero =>
      have hq : q=j+1 := by omega
      subst q
      simp only [←Category.assoc,Functor.mapHomologicalComplex_obj_d]
      erw [← Category.assoc, ← Category.assoc, ι_comparisonF,←F.map_comp,ι_d_leftZero,ι_d_leftZero,
        F.map_comp,Category.assoc,ι_comparisonF]
      rfl
    | succ p =>
      cases q with
      | zero =>
        have hp : p=j := by omega
        subst p
        simp only [←Category.assoc,Functor.mapHomologicalComplex_obj_d]
        erw [← Category.assoc, ← Category.assoc, ι_comparisonF,←F.map_comp,ι_d_rightZero,ι_d_rightZero,
          F.map_comp,Category.assoc,ι_comparisonF]
        rfl
      | succ q =>
        have h : p+q+1=j := by omega
        simp only [←Category.assoc,Functor.mapHomologicalComplex_obj_d]
        erw [← Category.assoc, ← Category.assoc, ι_comparisonF,←F.map_comp,ι_d_both p q j h,ι_d_both p q j h]
        simp only [F.map_add,F.map_units_smul,F.map_comp,Preadditive.add_comp,
          Linear.units_smul_comp,Category.assoc,ι_comparisonF]
        erw [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, Category.assoc, ι_comparisonF, ι_comparisonF]
        rfl

instance comparisonF_isIso [PreservesColimitsOfSize.{0,0} F]
    (K : HomologicalComplex₂ C c c) (n : ℕ) : IsIso (comparisonF F K n) := by
  change IsIso (sigmaComparison F (fun ij : {ij : ℕ×ℕ // ij.1+ij.2=n} => (K.X ij.1.1).X ij.1.2))
  infer_instance

instance comparison_isIso [PreservesColimitsOfSize.{0,0} F]
    (K : HomologicalComplex₂ C c c) : IsIso (comparison F K) := by
  have (n : ℕ) : IsIso ((comparison F K).f n) := comparisonF_isIso F K n
  exact HomologicalComplex.Hom.isIso_of_components _

noncomputable def iso [PreservesColimitsOfSize.{0,0} F] (K : HomologicalComplex₂ C c c) :
    (F.mapHomologicalComplex c).obj (K.total c) ≅ (map₂ F K).total c :=
  (asIso (comparison F K)).symm

end TotalFunctor

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_BiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace BiResolution

open DiagonalResolution TotalHomotopy

noncomputable def aug₀ : total.X 0 ⟶ (Functor.const D).obj Z :=
  complex.totalDesc (fun p q hpq => eqToHom (by
    change p+q=0 at hpq
    obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hpq
    rfl) ≫ DiagonalResolution.augmentation.app (op ⦋0⦌))

@[reassoc (attr := simp)] lemma ι_aug₀ :
    complex.ιTotal c 0 0 0 (by simp) ≫ aug₀ =
      DiagonalResolution.augmentation.app (op ⦋0⦌) := by
  simp [aug₀,ι_totalDesc]
  change (𝟙 _) ≫ DiagonalResolution.augmentation.app (op ⦋0⦌) = _
  exact Category.id_comp _

lemma d_aug₀ : total.d 1 0 ≫ aug₀=0 := by
  change (complex.total c).d 1 0 ≫ aug₀=0
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p+q=1 at hpq
  have hpq' : (p=0 ∧ q=1) ∨ (p=1 ∧ q=0) := by omega
  rcases hpq' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    simp only [comp_zero]
    erw [←Category.assoc]
    first | erw [ι_d_leftZero] | erw [ι_d_rightZero]
    erw [Category.assoc,ι_aug₀]
    apply NatTrans.ext
    funext d
    apply Sigma.hom_ext
    intro f
    simp [complex,chains,row,rowMap,AlternatingFaceMapComplex.objD,
      DiagonalResolution.augmentation,pre,SimplicialObject.δ]
    erw [NatTrans.comp_app,NatTrans.app_add,NatTrans.app_neg]
  · change Sigma.ι (fun _ : (⦋0⦌,⦋1⦌) ⟶ d => Z) f ≫
      ((Limits.Sigma.desc (fun index : (⦋0⦌,⦋1⦌) ⟶ d =>
        Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z)
          (Prod.mkHom index.1 (SimplexCategory.δ 0 ≫ index.2))) +
        -Limits.Sigma.desc (fun index : (⦋0⦌,⦋1⦌) ⟶ d =>
          Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z)
            (Prod.mkHom index.1 (SimplexCategory.δ 1 ≫ index.2)))) ≫
        Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z)) = 0
    simp [Preadditive.add_comp,Preadditive.comp_add,Preadditive.neg_comp,
      Preadditive.comp_neg]
  · change Sigma.ι (fun _ : (⦋1⦌,⦋0⦌) ⟶ d => Z) f ≫
      ((Limits.Sigma.desc (fun index : (⦋1⦌,⦋0⦌) ⟶ d =>
        Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z)
          (Prod.mkHom (SimplexCategory.δ 0 ≫ index.1) index.2)) +
        -Limits.Sigma.desc (fun index : (⦋1⦌,⦋0⦌) ⟶ d =>
          Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z)
            (Prod.mkHom (SimplexCategory.δ 1 ≫ index.1) index.2))) ≫
        Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z)) = 0
    simp [Preadditive.add_comp,Preadditive.comp_add,Preadditive.neg_comp,
      Preadditive.comp_neg]

noncomputable def pi : total ⟶ (ChainComplex.single₀ (D ⥤ A)).obj ((Functor.const D).obj Z) :=
  (ChainComplex.toSingle₀Equiv total ((Functor.const D).obj Z)).symm ⟨aug₀,d_aug₀⟩

@[simp] lemma pi_f_zero : pi.f 0 = aug₀ := ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

noncomputable def evalComplexIso (d : D) :
    TotalFunctor.map₂ ((evaluation D A).obj d) complex ≅ complexAt d := by
  let E := (evaluation D A).obj d
  let F := E.mapHomologicalComplex c
  refine eqToIso ?_
  change ((alternatingFaceMapComplex (ChainComplex (D ⥤ A) ℕ) ⋙ F.mapHomologicalComplex c).obj
    (chains ⋙ alternatingFaceMapComplex (D ⥤ A))) = _
  rw [map_alternatingFaceMapComplex F]
  change AlternatingFaceMapComplex.obj (chains ⋙ alternatingFaceMapComplex (D ⥤ A) ⋙ F) = _
  rw [map_alternatingFaceMapComplex E]
  rfl

noncomputable def evalTotalIso (d : D) :
    (((evaluation D A).obj d).mapHomologicalComplex c).obj total ≅ (complexAt d).total c :=
  TotalFunctor.iso ((evaluation D A).obj d) complex ≪≫ total.mapIso (evalComplexIso d) c

end BiResolution

end

section

open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace BiResolution

open DiagonalResolution TotalHomotopy

lemma contraction_aug (d : D) :
    (complexAt d).ιTotal c 0 0 0 (by simp) ≫ ((totalAtEquiv d).hom.f 0) =
      Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z) := by
  change (complexAt d).ιTotal c 0 0 0 (by simp) ≫
    (total.map (complexAtEquiv d).hom c).f 0 ≫
    (TotalHomotopy.singleIso (AlternatingFaceMapComplex.obj (point d))).hom.f 0 ≫
    (pointExtra d).homotopyEquiv.hom.f 0 = _
  rw [ιTotal_map_assoc]
  have hs : (TotalHomotopy.single (AlternatingFaceMapComplex.obj (point d))).ιTotal c 0 0 0 (by simp) ≫
      (TotalHomotopy.singleIso (AlternatingFaceMapComplex.obj (point d))).hom.f 0 = 𝟙 _ := by
    change (TotalHomotopy.singleIn _).f 0 ≫ _ = _
    have h := congrArg (fun f : AlternatingFaceMapComplex.obj (point d) ⟶ _ => f.f 0)
      (Iso.inv_hom_id (TotalHomotopy.singleIso (AlternatingFaceMapComplex.obj (point d))))
    exact h
  erw [←Category.assoc _ ((TotalHomotopy.singleIso (AlternatingFaceMapComplex.obj (point d))).hom.f 0)
    ((pointExtra d).homotopyEquiv.hom.f 0),hs,Category.id_comp]
  dsimp [complexAtEquiv,complexAtIso,pointExtra]
  simp [HomotopyEquiv.ofIso,CategoryTheory.eqToIso,HomologicalComplex.eqToHom_f,HomologicalComplex.singleMapHomologicalComplex,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
    extra,augmentedAt,augmentation,pointAugmented,pointAugmentation]
  apply Sigma.hom_ext
  intro f
  erw [eqToHom_refl,Category.id_comp]
  change Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z) f ≫
    Sigma.desc (fun index : (⦋0⦌,⦋0⦌) ⟶ d =>
      Sigma.ι (fun _ : ⦋0⦌ ⟶ d.2 => Z) index.2) ≫
    Sigma.desc (fun _ : ⦋0⦌ ⟶ d.2 => 𝟙 Z) =
    Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z) f ≫
      Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z)
  simp

lemma eval_inverse_aug (d : D) :
    (complexAt d).ιTotal c 0 0 0 (by simp) ≫ (evalTotalIso d).inv.f 0 ≫
      ((((evaluation D A).obj d).mapHomologicalComplex c).map pi).f 0 =
      Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z) := by
  change (complexAt d).ιTotal c 0 0 0 (by simp) ≫
    (total.map (evalComplexIso d).inv c).f 0 ≫
    TotalFunctor.comparisonF ((evaluation D A).obj d) complex 0 ≫ (pi.f 0).app d = _
  rw [ιTotal_map_assoc]
  simp only [evalComplexIso,CategoryTheory.eqToIso,HomologicalComplex.eqToHom_f]
  change _ ≫ (TotalFunctor.comparisonF ((evaluation D A).obj d) complex 0) ≫ (pi.f 0).app d = _
  erw [←Category.assoc,TotalFunctor.ι_comparisonF,pi_f_zero]
  change (complex.ιTotal c 0 0 0 (by simp)).app d ≫ aug₀.app d = _
  erw [←NatTrans.comp_app,ι_aug₀]
  rfl

instance pi_quasiIso : QuasiIso pi := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro d
  let f := (((evaluation D A).obj d).mapHomologicalComplex c).map pi
  have h : (evalTotalIso d).inv ≫ f ≫ (DiagonalResolution.singleAtIso d).hom =
      (totalAtEquiv d).hom := by
    apply HomologicalComplex.to_single_hom_ext
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change p+q=0 at hpq
    obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hpq
    simp only [HomologicalComplex.comp_f,←Category.assoc,contraction_aug]
    dsimp only [f]
    rw [Category.assoc ((complexAt d).ιTotal c 0 0 0 hpq),eval_inverse_aug]
    simp [DiagonalResolution.singleAtIso,HomologicalComplex.singleMapHomologicalComplex]
    change (Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z)) ≫ 𝟙 Z = _
    exact Category.comp_id _
  change QuasiIso f
  rw [←quasiIso_iff_comp_left (evalTotalIso d).inv f,
    ←quasiIso_iff_comp_right ((evalTotalIso d).inv ≫ f) (DiagonalResolution.singleAtIso d).hom,
    Category.assoc,h]
  infer_instance

noncomputable def resolution : ProjectiveResolution ((Functor.const D).obj Z) where
  complex := total
  π := pi
  quasiIso := pi_quasiIso

end BiResolution

end

section

open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace ModelAssembly

open DiagonalResolution
variable (X : Dᵒᵖ ⥤ Type)

@[reassoc (attr := simp)] lemma pre_forward {a b : D} (k : a ⟶ b) :
    (assembly X).map (pre k) ≫ forward X a =
      forward X b ≫ (sigmaConst.obj Z).map (X.map k.op) := by
  apply colimit.hom_ext
  intro e
  apply Sigma.hom_ext
  intro f
  change Sigma.ι (fun _ : b ⟶ e.unop.1.unop => Z) f ≫
    colimit.ι (projection X ⋙ free b) e ≫
      colim.map (Functor.whiskerLeft (projection X) (pre k)) ≫ forward X a = _
  erw [colimit.ι_map_assoc]
  change Sigma.ι (fun _ : b ⟶ e.unop.1.unop => Z) f ≫
    (pre k).app e.unop.1.unop ≫ colimit.ι (projection X ⋙ free a) e ≫ forward X a = _
  erw [←Category.assoc,ι_pre,ι_to]
  erw [ι_to_assoc]
  dsimp [freeCocone,sigmaConst]
  erw [Sigma.ι_desc,←Category.assoc,Sigma.ι_desc,Sigma.ι_comp_map',Category.id_comp]
  congr 1
  change X.map (k ≫ f).op e.unop.2 = X.map k.op (X.map f.op e.unop.2)
  rw [op_comp,X.map_comp]
  rfl

noncomputable def models : Dᵒᵖ ⥤ (D ⥤ A) where
  obj d := free d.unop
  map f := pre f.unop
  map_id d := pre_id _
  map_comp f g := by simp only [unop_comp,pre_comp]

noncomputable def freeNatIso : models ⋙ assembly X ≅ X ⋙ sigmaConst.obj Z :=
  NatIso.ofComponents (fun d => freeIso X d.unop) (fun f => pre_forward X f.unop)

noncomputable def modelEquiv : HomotopyEquiv DiagonalResolution.complex BiResolution.total :=
  ProjectiveResolution.homotopyEquiv DiagonalResolution.resolution BiResolution.resolution

noncomputable def assembledEquiv : HomotopyEquiv
    (((assembly X).mapHomologicalComplex (ComplexShape.down ℕ)).obj DiagonalResolution.complex)
    (((assembly X).mapHomologicalComplex (ComplexShape.down ℕ)).obj BiResolution.total) :=
  (assembly X).mapHomotopyEquiv modelEquiv

end ModelAssembly

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_EilenbergZilber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace EilenbergZilber

open DiagonalResolution ModelAssembly
abbrev c := ComplexShape.down ℕ

def diag : SimplexCategoryᵒᵖ ⥤ Dᵒᵖ := (Functor.diag SimplexCategory).op

def bisimplicial {C : Type*} [Category C] (F : Dᵒᵖ ⥤ C) :
    SimplicialObject (SimplicialObject C) :=
  Functor.curry.obj ((CategoryTheory.prodOpEquiv SimplexCategory (D := SimplexCategory)).inverse ⋙ F)

variable (X : Dᵒᵖ ⥤ Type)
noncomputable def diagonalIso :
    (((assembly X).mapHomologicalComplex c).obj DiagonalResolution.complex) ≅
      SSet.chainComplex (diag ⋙ X) Z := by
  refine (CategoryTheory.eqToIso (congrArg (fun F => F.obj DiagonalResolution.chains)
    (map_alternatingFaceMapComplex (assembly X)))) ≪≫ ?_
  change AlternatingFaceMapComplex.obj (diag ⋙ models ⋙ assembly X) ≅
    AlternatingFaceMapComplex.obj (diag ⋙ X ⋙ sigmaConst.obj Z)
  exact (alternatingFaceMapComplex A).mapIso
    (Functor.isoWhiskerLeft diag (freeNatIso X))

noncomputable def rowIso (p : SimplexCategoryᵒᵖ) :
    ((BiResolution.chains.obj p) ⋙ assembly X) ≅
      (bisimplicial (X ⋙ sigmaConst.obj Z)).obj p := by
  refine NatIso.ofComponents (fun q => freeIso X (p.unop,q.unop)) ?_
  intro q q' f
  change (assembly X).map (pre (a:=(p.unop,q'.unop)) (b:=(p.unop,q.unop))
      (𝟙 p.unop,f.unop)) ≫ forward X (p.unop,q'.unop) =
    forward X (p.unop,q.unop) ≫
      (sigmaConst.obj Z).map (X.map (show (p.unop,q'.unop) ⟶ (p.unop,q.unop) from
        (𝟙 p.unop,f.unop)).op)
  exact pre_forward X (a:=(p.unop,q'.unop)) (b:=(p.unop,q.unop)) (𝟙 p.unop,f.unop)

noncomputable def bisimplicialIso :
    BiResolution.chains ⋙ (Functor.whiskeringRight _ _ _).obj (assembly X) ≅
      bisimplicial (X ⋙ sigmaConst.obj Z) := by
  refine NatIso.ofComponents (rowIso X) ?_
  intro p p' f
  apply NatTrans.ext
  funext q
  change (assembly X).map (pre (a:=(p'.unop,q.unop)) (b:=(p.unop,q.unop))
      (f.unop,𝟙 q.unop)) ≫ forward X (p'.unop,q.unop) =
    forward X (p.unop,q.unop) ≫
      (sigmaConst.obj Z).map (X.map (show (p'.unop,q.unop) ⟶ (p.unop,q.unop) from
        (f.unop,𝟙 q.unop)).op)
  exact pre_forward X (a:=(p'.unop,q.unop)) (b:=(p.unop,q.unop)) (f.unop,𝟙 q.unop)

noncomputable def twoComplex : HomologicalComplex₂ A c c :=
  AlternatingFaceMapComplex.obj (bisimplicial (X ⋙ sigmaConst.obj Z) ⋙ alternatingFaceMapComplex A)

end EilenbergZilber

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalFiniteness

universe u
variable {R : Type u} [CommRing R]
abbrev c := ComplexShape.down ℕ
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

noncomputable def row (q : ℕ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((homologyFunctor (ModuleCat.{u} R) c q).mapHomologicalComplex c).obj K

noncomputable def rowIso (q : ℕ) : row K q ≅ E2Leading.row K q :=
  (NatIso.mapHomologicalComplex (ConcreteHomology.naturalIso q) c).app K

noncomputable def rowHomologyIso (p q : ℕ) : (row K q).homology p ≅
    ModuleCat.of R (ConcreteHomology.H (E2Leading.row K q) p) :=
  (homologyFunctor _ c p).mapIso (rowIso K q) ≪≫ ConcreteHomology.iso _ _

end TotalFiniteness

end

section

namespace FilteredFiniteness.Data

universe u
variable {R : Type u} [CommRing R]
variable {A B C : Type u} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
variable (K : FilteredFiniteness.Data (R:=R) (A:=A) (B:=B) (C:=C))

lemma subsingleton_H (N : ℕ) (hzero : K.FB 0=⊥) (htop : K.FB (N+1)=⊤)
    (hzeroE : ∀ p : ℕ, p≤N → Subsingleton (K.E₂ (p+1))) : Subsingleton K.H := by
  have hz : K.filtration 0=⊥ := by
    apply le_antisymm _ bot_le
    rintro y ⟨x,rfl⟩
    have hx : x=0 := by
      apply Subtype.ext; apply Subtype.ext
      exact (Submodule.mem_bot R).mp (hzero ▸ x.property)
    rw [hx,map_zero]
    exact Submodule.zero_mem _
  have hf : ∀ p : ℕ, p≤N+1 → K.filtration p=⊥ := by
    intro p hp
    induction p with
    | zero => exact hz
    | succ p ih =>
      have hl := ih (by omega)
      have := hzeroE p (by omega)
      apply le_antisymm _ bot_le
      rintro y ⟨x,rfl⟩
      have he : K.lead ((p:ℤ)+1) x=0 := Subsingleton.elim _ _
      have hh := K.lower_of_lead_zero x he
      change K.π x.val∈K.filtration (((p+1:ℕ):ℤ)-1) at hh
      have hidx : ((p+1:ℕ):ℤ)-1=(p:ℤ) := by omega
      rw [hidx,hl] at hh
      exact hh
  apply subsingleton_of_forall_eq 0
  intro y
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range K.dCycles) y
  have hy : K.π z∈K.filtration ((N+1:ℕ):ℤ) := by
    refine ⟨⟨z,?_⟩,rfl⟩
    change z.val∈K.FB ((N+1:ℕ):ℤ)
    rw [Nat.cast_add,Nat.cast_one,htop]; trivial
  rw [hf (N+1) le_rfl] at hy
  exact hy
end FilteredFiniteness.Data

open _root_.CategoryTheory HomologicalComplex HomologicalComplex₂
namespace E2Leading

universe u
variable {R : Type u} [CommRing R]
open TotalProjection
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma subsingleton_E₂ (p q : ℕ) [Subsingleton (ConcreteHomology.H (row K q) p)] :
    Subsingleton ((filteredData K (p+q)).E₂ ((p:ℤ)+1)) := by
  apply subsingleton_of_forall_eq 0
  intro y
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective _ y
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (lead_zero_boundary K p q x (Subsingleton.elim _ _))

lemma subsingleton_total_concrete (n : ℕ)
    (hzero : ∀ p q, p+q=n → Subsingleton (ConcreteHomology.H (row K q) p)) :
    Subsingleton (ConcreteHomology.H (K.total c) n) := by
  change Subsingleton (filteredData K n).H
  apply FilteredFiniteness.Data.subsingleton_H _ n (filtration_zero K n) (filtration_top K n)
  intro p hp
  have hn : p+(n-p)=n := Nat.add_sub_of_le hp
  have := hzero p (n-p) hn
  have h := subsingleton_E₂ K p (n-p)
  rwa [hn] at h
end E2Leading

namespace TotalFiniteness

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma subsingleton (n : ℕ)
    (hzero : ∀ p q, p+q=n → Subsingleton ((row K q).homology p)) :
    Subsingleton ((K.total c).homology n) := by
  have : Subsingleton (ConcreteHomology.H (K.total c) n) := by
    apply E2Leading.subsingleton_total_concrete K n
    intro p q hpq
    have := hzero p q hpq
    exact (rowHomologyIso K p q).toLinearEquiv.symm.injective.subsingleton
  exact (ConcreteHomology.iso (K.total c) n).toLinearEquiv.injective.subsingleton
end TotalFiniteness

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_CoefficientUCT
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace TensorProductHomology

variable {R : Type} [CommRing R]
abbrev c := ComplexShape.down ℕ
variable (K L : ChainComplex (ModuleCat.{0} R) ℕ)
noncomputable def bicomplex : HomologicalComplex₂ (ModuleCat.{0} R) c c :=
  (((curriedTensor (ModuleCat.{0} R)).mapBifunctorHomologicalComplex c c).obj K).obj L

noncomputable def rowIso [∀n,Module.Flat R (K.X n)] (q : ℕ) :
    TotalFiniteness.row (bicomplex K L) q ≅ (TensorCoefficient.functor K).obj (L.homology q) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p => (L.sc q).mapHomologyIso (tensorLeft (K.X p))) ?_
  intro p p' _
  symm
  change ShortComplex.homologyMap ((L.sc q).mapNatTrans
      ((tensoringLeft (ModuleCat R)).map (K.d p p'))) ≫ _ = _
  apply (Iso.eq_comp_inv ((L.sc q).mapHomologyIso (tensorLeft (K.X p')))).mp
  exact (ShortComplex.homologyMap_mapNatTrans (L.sc q)
    ((tensoringLeft (ModuleCat R)).map (K.d p p'))).trans (Category.assoc _ _ _).symm

end TensorProductHomology

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ProductChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits MonoidalCategory SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace ProductChains

open FreeChains
lemma sum_f {K L : ChainComplex A ℕ} {ι : Type} (s : Finset ι) (f : ι → (K ⟶ L)) (q : ℕ) :
    (∑ i∈s,f i).f q=∑ i∈s,(f i).f q := map_sum (HomologicalComplex.Hom.fAddMonoidHom q) f s
abbrev D := SimplexCategory × SimplexCategory
variable (X Y : SSet)
def product : Dᵒᵖ ⥤ Type where
  obj a := X.obj (op a.unop.1) × Y.obj (op a.unop.2)
  map f := ↾fun z => (X.map f.unop.1.op z.1,Y.map f.unop.2.op z.2)
  map_id _ := by ext z <;> simp
  map_comp f g := by ext z <;> simp

noncomputable def twoFree : HomologicalComplex₂ A c c :=
  AlternatingFaceMapComplex.obj (EilenbergZilber.bisimplicial (product X Y ⋙ ModuleCat.free ℤ) ⋙
    alternatingFaceMapComplex A)

noncomputable def freeIso : EilenbergZilber.twoComplex (product X Y) ≅ twoFree X Y :=
  (alternatingFaceMapComplex (ChainComplex A ℕ)).mapIso
    (Functor.isoWhiskerRight
      ((Functor.curry.mapIso (Functor.isoWhiskerLeft
        (CategoryTheory.prodOpEquiv SimplexCategory (D:=SimplexCategory)).inverse
        (Functor.isoWhiskerLeft (product X Y) FreeChains.naturalIso))))
      (alternatingFaceMapComplex A))

noncomputable def rowIso (p : ℕ) :
    (TensorProductHomology.bicomplex (complex X) (complex Y)).X p ≅ (twoFree X Y).X p := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun q => Functor.Monoidal.μIso (ModuleCat.free ℤ) (X.obj (op ⦋p⦌)) (Y.obj (op ⦋q⦌))) ?_
  intro q q' h
  obtain rfl : q=q'+1 := h.symm
  change Functor.LaxMonoidal.μ (ModuleCat.free ℤ) (X.obj (op ⦋p⦌)) (Y.obj (op ⦋q'+1⦌)) ≫
      (AlternatingFaceMapComplex.obj ((EilenbergZilber.bisimplicial (product X Y ⋙ ModuleCat.free ℤ)).obj (op ⦋p⦌))).d (q'+1) q' =
    (tensorLeft ((ModuleCat.free ℤ).obj (X.obj (op ⦋p⦌)))).map ((AlternatingFaceMapComplex.obj (Y ⋙ ModuleCat.free ℤ)).d (q'+1) q') ≫
      Functor.LaxMonoidal.μ (ModuleCat.free ℤ) (X.obj (op ⦋p⦌)) (Y.obj (op ⦋q'⦌))
  simp only [AlternatingFaceMapComplex.obj_d_eq,
    Functor.map_sum,Functor.map_zsmul,Preadditive.sum_comp,Preadditive.zsmul_comp]
  refine (Preadditive.comp_sum _ _ _).trans ?_
  apply Finset.sum_congr rfl
  intro _ _
  refine (Preadditive.comp_zsmul _ _ _).trans ?_
  congr 1
  simp [EilenbergZilber.bisimplicial,product,SimplicialObject.δ]
  rfl

noncomputable def tensorIso :
    TensorProductHomology.bicomplex (complex X) (complex Y) ≅ twoFree X Y := by
  refine HomologicalComplex.Hom.isoOfComponents (rowIso X Y) ?_
  intro p p' h
  obtain rfl : p=p'+1 := h.symm
  apply HomologicalComplex.Hom.ext
  funext q
  change Functor.LaxMonoidal.μ (ModuleCat.free ℤ) (X.obj (op ⦋p'+1⦌)) (Y.obj (op ⦋q⦌)) ≫
      ((twoFree X Y).d (p'+1) p').f q =
    (tensorRight ((ModuleCat.free ℤ).obj (Y.obj (op ⦋q⦌)))).map ((complex X).d (p'+1) p') ≫
      Functor.LaxMonoidal.μ (ModuleCat.free ℤ) (X.obj (op ⦋p'⦌)) (Y.obj (op ⦋q⦌))
  simp only [twoFree,complex,AlternatingFaceMapComplex.obj_d_eq,
    sum_f,HomologicalComplex.zsmul_f_apply,
    Functor.map_sum,Functor.map_zsmul,Preadditive.sum_comp,Preadditive.zsmul_comp]
  refine (Preadditive.comp_sum _ _ _).trans ?_
  apply Finset.sum_congr rfl
  intro _ _
  refine (Preadditive.comp_zsmul _ _ _).trans ?_
  congr 1
  simp [EilenbergZilber.bisimplicial,product,SimplicialObject.δ]
  rfl

end ProductChains

end

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace AugmentedSplit
open FreeChains
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

noncomputable abbrev U : ChainComplex A ℕ := 𝟙_ (ChainComplex A ℕ)
variable {K : ChainComplex A ℕ} (e : K ⟶ U) (s : U ⟶ K) (hs : s ≫ e=𝟙 U)

lemma uni_isZero (n : ℕ) (hn : n≠0) : IsZero (U.homology n) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  exact HomologicalComplex.isZero_single_obj_X c 0 _ n hn

end AugmentedSplit

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_SimplicialAugment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialAugment
open FreeChains AugmentedSplit

variable (X : SSet)
noncomputable def aug0 : (ModuleCat.free ℤ).obj (X.obj (op ⦋0⦌)) ⟶ Z := ModuleCat.freeDesc (M:=Z) (↾fun _ => (1:ℤ))
@[simp] lemma aug0_mk (x : X.obj (op ⦋0⦌)) : aug0 X (ModuleCat.freeMk x)=1 :=
  ModuleCat.freeDesc_apply (M:=Z) (↾fun _ => (1:ℤ)) x
lemma d_aug0 : (complex X).d 1 0 ≫ aug0 X=0 := by
  change (∑ i : Fin 2, (-1:ℤ)^i.val • (ModuleCat.free ℤ).map (X.δ i)) ≫ aug0 X=0
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one,
    pow_zero,pow_one,one_smul,neg_smul,Preadditive.add_comp,Preadditive.neg_comp]
  apply ModuleCat.free_hom_ext
  intro x
  change aug0 X ((ModuleCat.free ℤ).map (X.δ 0) (ModuleCat.freeMk x)) -
    aug0 X ((ModuleCat.free ℤ).map (X.δ 1) (ModuleCat.freeMk x)) = 0
  simp only [ModuleCat.free_map_apply]
  rw [aug0_mk,aug0_mk,sub_self]
noncomputable def aug : complex X ⟶ U :=
  (ChainComplex.toSingle₀Equiv _ Z).symm ⟨aug0 X,d_aug0 X⟩
@[simp] lemma aug_f_zero : (aug X).f 0=aug0 X := ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
instance flat (n : ℕ) : Module.Flat ℤ ((complex X).X n) := by
  change Module.Flat ℤ (X.obj (op ⦋n⦌) →₀ ℤ)
  infer_instance

lemma lift_homology (x : X.obj (op ⦋0⦌)) :
    (X.chainComplex Z).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
      (X.chainComplex Z).homologyπ 0 ≫
        homologyMap ((complexIso X).hom ≫ aug X) 0 ≫
          (singleObjHomologySelfIso c 0 Z).hom=𝟙 Z := by
  rw [homologyπ_naturality_assoc,liftCycles_comp_cyclesMap_assoc]
  change liftCycles ((single A c 0).obj Z) _ 0 _ _ ≫
    ((single A c 0).obj Z).homologyπ 0 ≫ (singleObjHomologySelfIso c 0 Z).hom = _
  rw [homologyπ_singleObjHomologySelfIso_hom]
  rw [singleObjCyclesSelfIso_hom,←Category.assoc,liftCycles_i]
  simp only [HomologicalComplex.comp_f,aug_f_zero]
  change Sigma.ι (fun _ : X.obj (op ⦋0⦌) => Z) x ≫ forward _ ≫ aug0 X=𝟙 Z
  rw [ι_forward_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (ModuleCat.freeDesc (M:=Z) (↾fun _ : X.obj (op ⦋0⦌) => (1:ℤ))) (ModuleCat.freeMk x)=1
  exact ModuleCat.freeDesc_apply (M:=Z) (↾fun _ => (1:ℤ)) x

lemma homology_aug :
    homologyMap ((complexIso X).hom ≫ aug X) 0 ≫
      (singleObjHomologySelfIso c 0 Z).hom = X.homology₀ε Z := by
  apply (cancel_epi ((X.chainComplex Z).homologyπ 0)).mp
  apply (cancel_epi (X.chainComplex Z).cycles₀Iso.inv).mp
  apply Sigma.hom_ext
  intro x
  have he : X.ιChainComplex x ≫ (X.chainComplex Z).cycles₀Iso.inv =
      (X.chainComplex Z).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
    apply (cancel_mono ((X.chainComplex Z).iCycles 0)).mp
    simp
  change X.ιChainComplex x ≫ _ = X.ιChainComplex x ≫ _
  simp only [←Category.assoc]
  rw [he]
  simp only [Category.assoc]
  rw [lift_homology,X.liftCycles_ιChainComplex_homologyπ_homology₀ε]

instance homology_aug_isIso [X.IsConnected] : IsIso (homologyMap (aug X) 0) := by
  have h := homology_aug X
  rw [homologyMap_comp,Category.assoc] at h
  have : IsIso (homologyMap (complexIso X).hom 0 ≫
    homologyMap (aug X) 0 ≫ (singleObjHomologySelfIso c 0 Z).hom) := by rw [h]; infer_instance
  have : IsIso (homologyMap (aug X) 0 ≫ (singleObjHomologySelfIso c 0 Z).hom) :=
    (isIso_comp_left_iff (homologyMap (complexIso X).hom 0) _).mp inferInstance
  exact (isIso_comp_right_iff _ (singleObjHomologySelfIso c 0 Z).hom).mp inferInstance
end SimplicialAugment

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ConnectedProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace ConnectedProduct
open FreeChains AugmentedSplit

variable (X : SSet) [X.IsConnected]
noncomputable def point : X.obj (op ⦋0⦌) := Classical.arbitrary _
end ConnectedProduct

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_SimplicialConnectedProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite AlgebraicTopology
namespace ConnectedProduct

variable (X Y : SSet)
def pairLeft (y : Y.obj (op ⦋0⦌)) : X ⟶ X ⊗ Y :=
  CartesianMonoidalCategory.lift (𝟙 X) (SSet.const y)
def pairRight (x : X.obj (op ⦋0⦌)) : Y ⟶ X ⊗ Y :=
  CartesianMonoidalCategory.lift (SSet.const x) (𝟙 Y)
lemma const_zero {X Y : SSet} (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌)) :
    (SSet.const (X:=X) y).app (op ⦋0⦌) x=y := by
  change Y.map _ y=y
  rw [Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (𝟙 _)]
  simp
lemma pairLeft_zero (y : Y.obj (op ⦋0⦌)) (x : X.obj (op ⦋0⦌)) :
    (pairLeft X Y y).app (op ⦋0⦌) x=(x,y) := by
  change (x,(SSet.const y).app (op ⦋0⦌) x)=(x,y)
  rw [const_zero]
lemma pairRight_zero (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌)) :
    (pairRight X Y x).app (op ⦋0⦌) y=(x,y) := by
  change ((SSet.const x).app (op ⦋0⦌) y,y)=(x,y)
  rw [const_zero]
instance connected_tensor [X.IsConnected] [Y.IsConnected] : (X⊗Y).IsConnected where
  allEq u v := by
    obtain ⟨⟨x,y⟩,rfl⟩ := SSet.π₀.mk_surjective u
    obtain ⟨⟨x',y'⟩,rfl⟩ := SSet.π₀.mk_surjective v
    have h₁ := congrArg (SSet.mapπ₀ (pairLeft X Y y))
      (Subsingleton.elim (SSet.π₀.mk x) (SSet.π₀.mk x'))
    have h₂ := congrArg (SSet.mapπ₀ (pairRight X Y x'))
      (Subsingleton.elim (SSet.π₀.mk y) (SSet.π₀.mk y'))
    simp only [SSet.mapπ₀_mk,pairLeft_zero,pairRight_zero] at h₁ h₂
    exact h₁.trans h₂
  nonempty := ⟨(Classical.arbitrary _,Classical.arbitrary _)⟩
end ConnectedProduct

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_CanonicalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace ConnectedProduct
open FreeChains AugmentedSplit

abbrev one : SSet := (Functor.const SimplexCategoryᵒᵖ).obj PUnit
lemma one_homology_zero (n : ℕ) (hn : n≠0) : IsZero (one.homology Z n) := by
  let V := (sigmaConst.obj Z).obj PUnit
  let e := (SimplicialObject.Augmented.ExtraDegeneracy.const V).homotopyEquiv
  have hz : IsZero (((ChainComplex.single₀ A).obj V).homology n) := by
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact HomologicalComplex.isZero_single_obj_X c 0 V n hn
  let ei : one.chainComplex Z ≅ AlternatingFaceMapComplex.obj ((Functor.const SimplexCategoryᵒᵖ).obj V) :=
    (alternatingFaceMapComplex A).mapIso
      (Functor.constComp SimplexCategoryᵒᵖ PUnit (sigmaConst.obj Z))
  exact IsZero.of_iso hz (((homologyFunctor A c n).mapIso ei) ≪≫ e.toHomologyIso n)
lemma const_homology_zero {X Y : SSet} (y : Y.obj (op ⦋0⦌)) (n : ℕ) (hn : n≠0) :
    SSet.homologyMap (SSet.const (X:=X) y) Z n = 0 := by
  have hh : SSet.const (X:=X) y = SSet.const (X:=X) (Y:=one) PUnit.unit ≫ SSet.const y := by simp
  rw [hh,SSet.homologyMap_comp]
  have hz := one_homology_zero n hn
  rw [hz.eq_of_src (SSet.homologyMap (SSet.const (X:=one) y) Z n) 0,comp_zero]
variable (X Y : SSet)
noncomputable def projection (n : ℕ) : (X⊗Y).homology Z n ⟶ X.homology Z n ⊞ Y.homology Z n :=
  biprod.lift (SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n)
    (SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n)
noncomputable def inclusion (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌)) (n : ℕ) :
    X.homology Z n ⊞ Y.homology Z n ⟶ (X⊗Y).homology Z n :=
  biprod.desc (SSet.homologyMap (pairLeft X Y y) Z n) (SSet.homologyMap (pairRight X Y x) Z n)
lemma inclusion_projection (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌)) (n : ℕ) (hn : n≠0) :
    inclusion X Y x y n ≫ projection X Y n=𝟙 _ := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext
  all_goals simp only [inclusion,projection,Category.assoc,biprod.inl_desc_assoc,
    biprod.inr_desc_assoc,biprod.lift_fst,biprod.lift_snd,biprod.inl_fst,biprod.inl_snd,
    biprod.inr_fst,biprod.inr_snd,Category.comp_id,←SSet.homologyMap_comp]
  all_goals simp [pairLeft,pairRight,CartesianMonoidalCategory.lift_fst,
    CartesianMonoidalCategory.lift_snd,const_homology_zero _ n hn]
end ConnectedProduct

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalComparison
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalComparison

universe u
variable {R : Type u} [CommRing R]
abbrev c := ComplexShape.down ℕ
end TotalComparison

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_AssemblyMap
attribute [-instance] _root_.OAI.BiResolution.pi_quasiIso _root_.OAI.ConnectedProduct.connected_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace ModelAssembly

open DiagonalResolution
variable {X Y : Dᵒᵖ ⥤ Type} (φ : X ⟶ Y)
noncomputable def mapCocone (F : D ⥤ A) : Cocone (projection X ⋙ F) where
  pt := (assembly Y).obj F
  ι := {
    app e := colimit.ι (projection Y ⋙ F) (φ.mapElements.op.obj e)
    naturality e e' f := by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
      exact colimit.w (projection Y ⋙ F) (φ.mapElements.op.map f) }
noncomputable def assemblyMapF (F : D ⥤ A) : (assembly X).obj F ⟶ (assembly Y).obj F :=
  colimit.desc (projection X ⋙ F) (mapCocone φ F)
@[reassoc (attr := simp)] lemma ι_assemblyMapF (F : D ⥤ A) (e : X.Elementsᵒᵖ) :
    colimit.ι (projection X ⋙ F) e ≫ assemblyMapF φ F =
      colimit.ι (projection Y ⋙ F) (φ.mapElements.op.obj e) :=
  colimit.ι_desc _ _
noncomputable def assemblyMap : assembly X ⟶ assembly Y where
  app := assemblyMapF φ
  naturality F G α := by
    apply colimit.hom_ext
    intro e
    change colimit.ι (projection X ⋙ F) e ≫
      colim.map (Functor.whiskerLeft (projection X) α) ≫ assemblyMapF φ G =
      colimit.ι (projection X ⋙ F) e ≫ assemblyMapF φ F ≫
        colim.map (Functor.whiskerLeft (projection Y) α)
    erw [colimit.ι_map_assoc,ι_assemblyMapF,←Category.assoc,ι_assemblyMapF,colimit.ι_map]
    rfl
@[reassoc (attr := simp)] lemma ι_assemblyMap (F : D ⥤ A) (e : X.Elementsᵒᵖ) :
    colimit.ι (projection X ⋙ F) e ≫ (assemblyMap φ).app F =
      colimit.ι (projection Y ⋙ F) (φ.mapElements.op.obj e) :=
  ι_assemblyMapF φ F e
@[reassoc] lemma map_forward (d : D) :
    (assemblyMap φ).app (free d) ≫ forward Y d =
      forward X d ≫ (sigmaConst.obj Z).map (φ.app (op d)) := by
  apply colimit.hom_ext
  intro e
  apply Sigma.hom_ext
  intro f
  change Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) f ≫ colimit.ι (projection X ⋙ free d) e ≫ _ = _
  erw [← Category.assoc (colimit.ι (projection X ⋙ free d) e)
    ((assemblyMap φ).app (free d)) (forward Y d), ι_assemblyMap, ι_to]
  change Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) f ≫
    (freeCocone Y d).ι.app (φ.mapElements.op.obj e) =
    Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) f ≫
    colimit.ι (projection X ⋙ free d) e ≫ forward X d ≫ _
  erw [← Category.assoc (colimit.ι (projection X ⋙ free d) e) (forward X d)
    ((sigmaConst.obj Z).map (φ.app (op d))), ι_to]
  dsimp only [freeCocone]
  erw [Sigma.ι_desc, Sigma.ι_desc_assoc]
  dsimp only [sigmaConst]
  erw [Sigma.ι_comp_map', Category.id_comp]
  congr 1
  exact (ConcreteCategory.congr_hom (φ.naturality f.op) e.unop.2).symm
end ModelAssembly

end

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalFunctor

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
  {E : Type u'} [Category.{v'} E] [Preadditive E] [HasCoproducts.{0} E]
open TotalHomotopy
variable {F G : C ⥤ E} [F.Additive] [G.Additive] (α : F ⟶ G)
noncomputable abbrev nat₂ (K : HomologicalComplex₂ C c c) : map₂ F K ⟶ map₂ G K :=
  ((α.mapHomologicalComplex c).mapHomologicalComplex c).app K
@[reassoc] lemma comparison_natural (K : HomologicalComplex₂ C c c) :
    total.map (nat₂ α K) c ≫ comparison G K =
      comparison F K ≫ (α.mapHomologicalComplex c).app (K.total c) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply total.hom_ext
  intro p q hpq
  change (map₂ F K).ιTotal c p q n hpq ≫ (total.map (nat₂ α K) c).f n ≫ comparisonF G K n =
    (map₂ F K).ιTotal c p q n hpq ≫ comparisonF F K n ≫ α.app _
  rw [ιTotal_map_assoc,ι_comparisonF,ι_comparisonF_assoc]
  exact (α.naturality _).symm
@[reassoc] lemma iso_natural [PreservesColimitsOfSize.{0,0} F] [PreservesColimitsOfSize.{0,0} G]
    (K : HomologicalComplex₂ C c c) :
    (α.mapHomologicalComplex c).app (K.total c) ≫ (iso G K).hom =
      (iso F K).hom ≫ total.map (nat₂ α K) c := by
  apply (cancel_mono (comparison G K)).mp
  simp only [Category.assoc]
  change _ ≫ inv (comparison G K) ≫ comparison G K =
    inv (comparison F K) ≫ total.map (nat₂ α K) c ≫ comparison G K
  rw [IsIso.inv_hom_id,Category.comp_id,comparison_natural,←Category.assoc,
    IsIso.inv_hom_id,Category.id_comp]
end TotalFunctor

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_EZNatural
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace EilenbergZilber

open DiagonalResolution ModelAssembly
variable {X Y : Dᵒᵖ ⥤ Type} (φ : X ⟶ Y)
noncomputable def diagonalMap : SSet.chainComplex (diag ⋙ X) Z ⟶ SSet.chainComplex (diag ⋙ Y) Z :=
  (alternatingFaceMapComplex A).map
    (Functor.whiskerRight (Functor.whiskerLeft diag φ) (sigmaConst.obj Z))
noncomputable def twoMap : twoComplex X ⟶ twoComplex Y :=
  (alternatingFaceMapComplex (ChainComplex A ℕ)).map
    (Functor.whiskerRight
      (Functor.curry.map (Functor.whiskerLeft
        (CategoryTheory.prodOpEquiv SimplexCategory (D:=SimplexCategory)).inverse
        (Functor.whiskerRight φ (sigmaConst.obj Z)))) (alternatingFaceMapComplex A))
noncomputable def twoIsoN (X : Dᵒᵖ ⥤ Type) :
    TotalFunctor.map₂ (assembly X) BiResolution.complex ≅ twoComplex X := by
  let F := assembly X
  let FC := F.mapHomologicalComplex c
  refine (CategoryTheory.eqToIso (congrArg (fun G => G.obj
    (BiResolution.chains ⋙ alternatingFaceMapComplex (D ⥤ A)))
      (map_alternatingFaceMapComplex FC))) ≪≫ ?_
  refine (alternatingFaceMapComplex (ChainComplex A ℕ)).mapIso
    (Functor.isoWhiskerLeft BiResolution.chains
      (CategoryTheory.eqToIso (map_alternatingFaceMapComplex F))) ≪≫ ?_
  exact (alternatingFaceMapComplex (ChainComplex A ℕ)).mapIso
    (Functor.isoWhiskerRight (bisimplicialIso X) (alternatingFaceMapComplex A))
noncomputable def equivN (X : Dᵒᵖ ⥤ Type) :
    HomotopyEquiv (SSet.chainComplex (diag ⋙ X) Z) ((twoComplex X).total c) :=
  (HomotopyEquiv.ofIso (diagonalIso X).symm).trans
    ((assembledEquiv X).trans (HomotopyEquiv.ofIso
      (TotalFunctor.iso (assembly X) BiResolution.complex ≪≫ total.mapIso (twoIsoN X) c)))
lemma diagonalIso_f (n : ℕ) : (diagonalIso X).hom.f n = forward X (SimplexCategory.mk n,SimplexCategory.mk n) := by
  simp only [diagonalIso, Iso.trans_hom, HomologicalComplex.comp_f]
  dsimp only [CategoryTheory.eqToIso]
  erw [HomologicalComplex.eqToHom_f]
  erw [eqToHom_refl, Category.id_comp]
  rfl
lemma twoIso_f (p q : ℕ) : ((twoIsoN X).hom.f p).f q = forward X (SimplexCategory.mk p,SimplexCategory.mk q) := by
  simp only [twoIsoN, Iso.trans_hom, HomologicalComplex.comp_f]
  dsimp only [CategoryTheory.eqToIso]
  erw [HomologicalComplex.eqToHom_f, HomologicalComplex.eqToHom_f]
  erw [eqToHom_refl, Category.id_comp]
  erw [Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom, alternatingFaceMapComplex_map_f, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  dsimp only [CategoryTheory.eqToIso]
  erw [eqToHom_app, HomologicalComplex.eqToHom_f, eqToHom_refl, Category.id_comp]
  rfl
@[reassoc] lemma diagonal_natural :
    ((assemblyMap φ).mapHomologicalComplex c).app DiagonalResolution.complex ≫
      (diagonalIso Y).hom = (diagonalIso X).hom ≫ diagonalMap φ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (assemblyMap φ).app (free (SimplexCategory.mk n,SimplexCategory.mk n)) ≫
    (diagonalIso Y).hom.f n = (diagonalIso X).hom.f n ≫ _
  rw [diagonalIso_f,diagonalIso_f]
  exact map_forward φ _
@[reassoc] lemma two_natural :
    TotalFunctor.nat₂ (assemblyMap φ) BiResolution.complex ≫ (twoIsoN Y).hom =
      (twoIsoN X).hom ≫ twoMap φ := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply HomologicalComplex.Hom.ext
  funext q
  change (assemblyMap φ).app (free (SimplexCategory.mk p,SimplexCategory.mk q)) ≫
    ((twoIsoN Y).hom.f p).f q = ((twoIsoN X).hom.f p).f q ≫ _
  rw [twoIso_f,twoIso_f]
  exact map_forward φ _
@[reassoc] lemma equiv_natural :
    diagonalMap φ ≫ (equivN Y).hom = (equivN X).hom ≫ total.map (twoMap φ) c := by
  change diagonalMap φ ≫ (diagonalIso Y).inv ≫ (assembledEquiv Y).hom ≫
    (TotalFunctor.iso (assembly Y) BiResolution.complex).hom ≫ (total.mapIso (twoIsoN Y) c).hom =
      ((diagonalIso X).inv ≫ (assembledEquiv X).hom ≫
      (TotalFunctor.iso (assembly X) BiResolution.complex).hom ≫ (total.mapIso (twoIsoN X) c).hom) ≫ _
  apply (cancel_epi (diagonalIso X).hom).mp
  simp only [←Category.assoc]
  rw [←diagonal_natural]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  have hn := ((assemblyMap φ).mapHomologicalComplex c).naturality modelEquiv.hom
  have hn' : ((assemblyMap φ).mapHomologicalComplex c).app DiagonalResolution.complex ≫
      (assembledEquiv Y).hom = (assembledEquiv X).hom ≫
      ((assemblyMap φ).mapHomologicalComplex c).app BiResolution.total := hn.symm
  rw [←Category.assoc,hn']
  simp only [Category.assoc]
  have ht := TotalFunctor.iso_natural (assemblyMap φ) BiResolution.complex
  change ((assemblyMap φ).mapHomologicalComplex c).app BiResolution.total ≫
    (TotalFunctor.iso (assembly Y) BiResolution.complex).hom = _ at ht
  erw [reassoc_of% ht]
  have htwo : total.map (TotalFunctor.nat₂ (assemblyMap φ) BiResolution.complex) c ≫
      total.map (twoIsoN Y).hom c = total.map (twoIsoN X).hom c ≫ total.map (twoMap φ) c := by
    rw [←total.map_comp,←total.map_comp,two_natural]
  exact congrArg (fun k => (assembledEquiv X).hom ≫
    (TotalFunctor.iso (assembly X) BiResolution.complex).hom ≫ k) htwo
noncomputable def homologyIsoN (X : Dᵒᵖ ⥤ Type) (n : ℕ) :
    SSet.homology (diag ⋙ X) Z n ≅ (((twoComplex X).total c).homology n) :=
  (equivN X).toHomologyIso n
@[reassoc] lemma homology_natural (n : ℕ) :
    homologyMap (diagonalMap φ) n ≫ (homologyIsoN Y n).hom =
      (homologyIsoN X n).hom ≫ homologyMap (total.map (twoMap φ) c) n := by
  change homologyMap (diagonalMap φ) n ≫ homologyMap (equivN Y).hom n =
    homologyMap (equivN X).hom n ≫ homologyMap (total.map (twoMap φ) c) n
  rw [←homologyMap_comp,←homologyMap_comp,equiv_natural]
end EilenbergZilber

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_DiagonalComparison
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace EilenbergZilber

open DiagonalResolution ModelAssembly
variable {X Y : Dᵒᵖ ⥤ Type} (φ : X ⟶ Y)
noncomputable def bisimplicialMap : bisimplicial X ⟶ bisimplicial Y :=
  Functor.curry.map (Functor.whiskerLeft
    (CategoryTheory.prodOpEquiv SimplexCategory (D:=SimplexCategory)).inverse φ)
end EilenbergZilber

end

section

open _root_.CategoryTheory MonoidalCategory Simplicial Opposite
namespace NerveHomotopy

universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {F G : C ⥤ D}

def cylinder (α : F ⟶ G) : C × Fin 2 ⥤ D :=
  CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ α).flip

noncomputable def homotopyMap (α : F ⟶ G) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app n := ↾fun x => x.1.prod' ((SSet.stdSimplex.objEquiv x.2).toOrderHom.toFunctor) ⋙ cylinder α
  naturality _ _ f := by ext x; rfl
@[simp] lemma homotopyMap_zero (α : F ⟶ G) : SSet.ι₀ ≫ homotopyMap α=nerveMap F := by
  ext n x
  apply CategoryTheory.Functor.ext
  · intro i j f
    erw [eqToHom_refl, Category.id_comp, Category.comp_id]
    change F.map (x.map f) ≫ 𝟙 _=F.map (x.map f)
    simp
  · intro i
    rfl
@[simp] lemma homotopyMap_one (α : F ⟶ G) : SSet.ι₁ ≫ homotopyMap α=nerveMap G := by
  ext n x
  apply CategoryTheory.Functor.ext
  · intro i j f
    erw [eqToHom_refl, Category.id_comp, Category.comp_id]
    change G.map (x.map f) ≫ 𝟙 _=G.map (x.map f)
    simp
  · intro i
    rfl

noncomputable def ofNatTrans (α : F ⟶ G) : SSet.Homotopy (nerveMap F) (nerveMap G) where
  h := homotopyMap α
  h₀ := homotopyMap_zero α
  h₁ := homotopyMap_one α
  rel := by ext n x; exact x.1.property.elim

universe w
variable {A : Type w} [Category A] [Preadditive A]
  [Limits.HasCoproducts.{max u v} A] [CategoryWithHomology A]

noncomputable def homologyIso (e : C ≌ D) (R : A) (n : ℕ) :
    (nerve C).homology R n ≅ (nerve D).homology R n where
  hom := SSet.homologyMap (nerveMap e.functor) R n
  inv := SSet.homologyMap (nerveMap e.inverse) R n
  hom_inv_id := by
    rw [←SSet.homologyMap_comp]
    have h := (ofNatTrans e.unitIso.hom).congr_homologyMap R n
    change SSet.homologyMap (nerveMap (e.functor ⋙ e.inverse)) R n = _
    rw [←h]
    exact SSet.homologyMap_id _ _ _
  inv_hom_id := by
    rw [←SSet.homologyMap_comp]
    have h := (ofNatTrans e.counitIso.hom).congr_homologyMap R n
    change SSet.homologyMap (nerveMap (e.inverse ⋙ e.functor)) R n = _
    rw [h]
    exact SSet.homologyMap_id _ _ _

noncomputable instance homologyMap_isIso (F : C ⥤ D) [F.IsEquivalence]
    (R : A) (n : ℕ) : IsIso (SSet.homologyMap (nerveMap F) R n) :=
  (homologyIso F.asEquivalence R n).isIso_hom

end NerveHomotopy

end

open _root_.CategoryTheory SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialDiagonal
open DiagonalResolution

abbrev I := SimplexCategoryᵒᵖ
def uncurry (X : I ⥤ SSet) : DiagonalResolution.Dᵒᵖ ⥤ Type :=
  (prodOpEquiv SimplexCategory (D:=SimplexCategory)).functor ⋙ Functor.uncurry.obj X
def diagonal : (I ⥤ SSet) ⥤ SSet where
  obj X := EilenbergZilber.diag ⋙ uncurry X
  map f := Functor.whiskerLeft EilenbergZilber.diag
    (Functor.whiskerLeft (prodOpEquiv SimplexCategory (D:=SimplexCategory)).functor (Functor.uncurry.map f))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

def nerveDiagonal : (I ⥤ Cat.{0,0}) ⥤ SSet :=
  (Functor.whiskeringRight I Cat SSet).obj nerveFunctor ⋙ diagonal
end SimplicialDiagonal

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalBar
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.NerveHomotopy.homologyMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory MonoidalCategory
universe u v w
namespace IntervalBar
variable (C : Type u) [Groupoid.{v} C] [MonoidalCategory C]
variable (I : Type w) [Preorder I]

structure Diagram where
  obj : ∀ i j : I, i ≤ j → C
  unit : ∀ i, obj i i le_rfl ≅ 𝟙_ C
  cut : ∀ i j k (hij : i≤j) (hjk : j≤k), obj i j hij ⊗ obj j k hjk ≅ obj i k (hij.trans hjk)
  left_unit : ∀ i j (h : i≤j), (cut i i j le_rfl h).hom =
    (unit i).hom ▷ obj i j h ≫ (λ_ (obj i j h)).hom
  right_unit : ∀ i j (h : i≤j), (cut i j j h le_rfl).hom =
    obj i j h ◁ (unit j).hom ≫ (ρ_ (obj i j h)).hom
  associativity : ∀ i j k l (hij : i≤j) (hjk : j≤k) (hkl : k≤l),
    (cut i j k hij hjk).hom ▷ obj k l hkl ≫ (cut i k l (hij.trans hjk) hkl).hom =
    (α_ (obj i j hij) (obj j k hjk) (obj k l hkl)).hom ≫
      obj i j hij ◁ (cut j k l hjk hkl).hom ≫ (cut i j l hij (hjk.trans hkl)).hom

namespace Diagram
variable {C I}
structure Hom (D E : Diagram C I) where
  app : ∀ i j (h : i≤j), D.obj i j h ⟶ E.obj i j h
  unit : ∀i, app i i le_rfl ≫ (E.unit i).hom = (D.unit i).hom
  cut : ∀i j k (hij : i≤j) (hjk : j≤k),
    (app i j hij ⊗ₘ app j k hjk) ≫ (E.cut i j k hij hjk).hom =
      (D.cut i j k hij hjk).hom ≫ app i k (hij.trans hjk)

@[ext] lemma Hom.ext {D E : Diagram C I} {f g : Hom D E}
    (h : ∀i j hij,f.app i j hij=g.app i j hij) : f=g := by
  cases f; cases g
  simp_all only [mk.injEq]
  funext i j hij
  exact h i j hij

def Hom.id (D : Diagram C I) : Hom D D where
  app i j h := 𝟙 _
  unit i := by simp
  cut i j k hij hjk := by simp

def Hom.comp {D E F : Diagram C I} (f : Hom D E) (g : Hom E F) : Hom D F where
  app i j h := f.app i j h ≫ g.app i j h
  unit i := by rw [Category.assoc,g.unit,f.unit]
  cut i j k hij hjk := by
    rw [←tensorHom_comp_tensorHom,Category.assoc,g.cut,←Category.assoc,f.cut,Category.assoc]

noncomputable def Hom.inv {D E : Diagram C I} (f : Hom D E) : Hom E D where
  app i j h := CategoryTheory.inv (f.app i j h)
  unit i := by rw [←f.unit,←Category.assoc,IsIso.inv_hom_id,Category.id_comp]
  cut i j k hij hjk := by
    apply (cancel_epi (f.app i j hij ⊗ₘ f.app j k hjk)).mp
    simp only [←Category.assoc,tensorHom_comp_tensorHom,IsIso.hom_inv_id,id_tensorHom_id,
      Category.id_comp]
    rw [f.cut,Category.assoc,IsIso.hom_inv_id,Category.comp_id]

noncomputable instance instGroupoid : Groupoid (Diagram C I) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext; simp [Hom.comp,Hom.id]
  comp_id f := by ext; simp [Hom.comp,Hom.id]
  assoc f g h := by ext; simp [Hom.comp,Category.assoc]
  inv := Hom.inv
  inv_comp f := by ext; simp [Hom.comp,Hom.inv,Hom.id]
  comp_inv f := by ext; simp [Hom.comp,Hom.inv,Hom.id]

@[simp] lemma id_app (D : Diagram C I) (i j : I) (h : i≤j) :
    (𝟙 D : D ⟶ D).app i j h=𝟙 _ := rfl
@[simp] lemma comp_app {D E F : Diagram C I} (f : D ⟶ E) (g : E ⟶ F)
    (i j : I) (h : i≤j) : (f≫g).app i j h=f.app i j h≫g.app i j h := rfl

variable {J : Type w} [Preorder J]
def reindexObj (f : I →o J) (D : Diagram C J) : Diagram C I where
  obj i j h := D.obj (f i) (f j) (f.monotone h)
  unit i := D.unit (f i)
  cut i j k hij hjk := D.cut (f i) (f j) (f k) (f.monotone hij) (f.monotone hjk)
  left_unit i j h := D.left_unit (f i) (f j) (f.monotone h)
  right_unit i j h := D.right_unit (f i) (f j) (f.monotone h)
  associativity i j k l hij hjk hkl :=
    D.associativity (f i) (f j) (f k) (f l) (f.monotone hij) (f.monotone hjk) (f.monotone hkl)

noncomputable def reindex (f : I →o J) : Diagram C J ⥤ Diagram C I where
  obj := reindexObj f
  map g := {
    app i j h := g.app (f i) (f j) (f.monotone h)
    unit i := g.unit (f i)
    cut i j k hij hjk := g.cut (f i) (f j) (f k) (f.monotone hij) (f.monotone hjk) }

@[simp] lemma reindex_id : reindex (C:=C) (OrderHom.id : I →o I)=𝟭 _ := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro D; cases D; rfl
  case h_map => intro D E f; change _ = (𝟙 _ ≫ f ≫ 𝟙 _); simp only [Category.id_comp,Category.comp_id]; rfl

variable {K : Type w} [Preorder K]
@[simp] lemma reindex_comp (f : I →o J) (g : J →o K) :
    reindex (C:=C) (g.comp f)=reindex g ⋙ reindex f := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro D; rfl
  case h_map => intro D E h; change _ = (𝟙 _ ≫ (reindex g ⋙ reindex f).map h ≫ 𝟙 _); simp only [Category.id_comp,Category.comp_id]; rfl

noncomputable def eval (n : ℕ) : Diagram C (Fin (n+1)) ⥤ (Fin n → C) where
  obj D i := D.obj i.castSucc i.succ (Fin.castSucc_le_succ i)
  map f i := f.app i.castSucc i.succ (Fin.castSucc_le_succ i)

lemma hom_ext_elementary {n : ℕ} {D E : Diagram C (Fin (n+1))} (f g : D ⟶ E)
    (h : ∀ i : Fin n, f.app i.castSucc i.succ (Fin.castSucc_le_succ i) =
      g.app i.castSucc i.succ (Fin.castSucc_le_succ i)) : f=g := by
  have diag (i : Fin (n+1)) : f.app i i le_rfl=g.app i i le_rfl := by
    apply (cancel_mono (E.unit i).hom).mp
    rw [f.unit,g.unit]
  apply Hom.ext
  suffices ∀ j : Fin (n+1), ∀ i (hij : i≤j), f.app i j hij=g.app i j hij by
    intro i j hij; exact this j i hij
  apply Fin.induction
  · intro i hi
    have : i=0 := Fin.eq_of_val_eq (by simpa using hi)
    subst i
    exact diag 0
  · intro j ih i hij
    by_cases he : i=j.succ
    · subst i; exact diag j.succ
    · have hi : i≤j.castSucc := by
        simp only [Fin.le_def,Fin.ext_iff,Fin.val_succ,Fin.val_castSucc] at *
        omega
      apply (cancel_epi (D.cut i j.castSucc j.succ hi (Fin.castSucc_le_succ j)).hom).mp
      rw [←f.cut,←g.cut,ih i hi,h j]

noncomputable instance instFaithfulFinHAddNatOfNatForallEval (n : ℕ) : (eval (C:=C) n).Faithful where
  map_injective {_ _} f g h := hom_ext_elementary f g (fun i => congrFun h i)

open scoped Simplicial
noncomputable def simplicial : SimplicialObject Cat.{v,max u v} where
  obj n := Cat.of (Diagram C (Fin (n.unop.len+1)))
  map f := (reindex f.unop.toOrderHom).toCatHom
  map_id n := by
    apply Cat.ext
    exact reindex_id
  map_comp f g := by
    apply Cat.ext
    exact reindex_comp g.unop.toOrderHom f.unop.toOrderHom

end Diagram
end IntervalBar

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalExtension
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.NerveHomotopy.homologyMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory MonoidalCategory
universe u v w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]
variable {I : Type w} [Preorder I]

lemma cut_propagate (D E : Diagram C I) (i j k l : I)
    (hij : i≤j) (hjk : j≤k) (hkl : k≤l)
    (x : D.obj i j hij ⟶ E.obj i j hij)
    (y : D.obj j k hjk ⟶ E.obj j k hjk)
    (z : D.obj k l hkl ⟶ E.obj k l hkl)
    (xy : D.obj i k (hij.trans hjk) ⟶ E.obj i k (hij.trans hjk))
    (yz : D.obj j l (hjk.trans hkl) ⟶ E.obj j l (hjk.trans hkl))
    (xyz : D.obj i l (hij.trans (hjk.trans hkl)) ⟶ E.obj i l (hij.trans (hjk.trans hkl)))
    (hxy : (x⊗ₘy) ≫ (E.cut i j k hij hjk).hom = (D.cut i j k hij hjk).hom ≫ xy)
    (hyz : (y⊗ₘz) ≫ (E.cut j k l hjk hkl).hom = (D.cut j k l hjk hkl).hom ≫ yz)
    (hxyz : (xy⊗ₘz) ≫ (E.cut i k l (hij.trans hjk) hkl).hom =
      (D.cut i k l (hij.trans hjk) hkl).hom ≫ xyz) :
    (x⊗ₘyz) ≫ (E.cut i j l hij (hjk.trans hkl)).hom =
      (D.cut i j l hij (hjk.trans hkl)).hom ≫ xyz := by
  apply (cancel_epi ((α_ (D.obj i j hij) (D.obj j k hjk) (D.obj k l hkl)).hom ≫
      (𝟙 _ ⊗ₘ (D.cut j k l hjk hkl).hom))).mp
  calc
    _ = (α_ _ _ _).hom ≫ (x⊗ₘ((D.cut j k l hjk hkl).hom≫yz)) ≫
        (E.cut i j l hij (hjk.trans hkl)).hom := by
      simp only [Category.assoc,tensorHom_comp_tensorHom_assoc,Category.id_comp]
    _ = (α_ _ _ _).hom ≫ (x⊗ₘ((y⊗ₘz)≫(E.cut j k l hjk hkl).hom)) ≫
        (E.cut i j l hij (hjk.trans hkl)).hom := by rw [hyz]
    _ = (α_ _ _ _).hom ≫ (x⊗ₘ(y⊗ₘz)) ≫ (𝟙 _ ⊗ₘ (E.cut j k l hjk hkl).hom) ≫
        (E.cut i j l hij (hjk.trans hkl)).hom := by
      simp only [tensorHom_comp_tensorHom_assoc,Category.comp_id]
    _ = ((x⊗ₘy)⊗ₘz) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ₘ (E.cut j k l hjk hkl).hom) ≫
        (E.cut i j l hij (hjk.trans hkl)).hom := by rw [associator_naturality_assoc]
    _ = ((x⊗ₘy)⊗ₘz) ≫ ((E.cut i j k hij hjk).hom ⊗ₘ 𝟙 _) ≫
        (E.cut i k l (hij.trans hjk) hkl).hom := by
      rw [id_tensorHom,←E.associativity,tensorHom_id]
    _ = (((x⊗ₘy)≫(E.cut i j k hij hjk).hom)⊗ₘz) ≫
        (E.cut i k l (hij.trans hjk) hkl).hom := by
      simp only [tensorHom_comp_tensorHom_assoc,Category.comp_id]
    _ = (((D.cut i j k hij hjk).hom≫xy)⊗ₘz) ≫
        (E.cut i k l (hij.trans hjk) hkl).hom := by rw [hxy]
    _ = ((D.cut i j k hij hjk).hom⊗ₘ𝟙 _) ≫ (xy⊗ₘz) ≫
        (E.cut i k l (hij.trans hjk) hkl).hom := by
      simp only [tensorHom_comp_tensorHom_assoc,Category.id_comp]
    _ = ((D.cut i j k hij hjk).hom⊗ₘ𝟙 _) ≫ (D.cut i k l (hij.trans hjk) hkl).hom ≫ xyz := by rw [hxyz]
    _ = _ := by rw [tensorHom_id,←Category.assoc,D.associativity]; simp only [Category.assoc,id_tensorHom]

variable {n : ℕ} {D E : Diagram C (Fin (n+1))}

noncomputable def extendApp
    (f : ∀j : Fin n, D.obj j.castSucc j.succ (Fin.castSucc_le_succ j) ⟶
      E.obj j.castSucc j.succ (Fin.castSucc_le_succ j)) :
    ∀i j (hij : i≤j), D.obj i j hij ⟶ E.obj i j hij := fun i j hij =>
  (Fin.induction
    (motive := fun j => ∀i (h : i≤j), D.obj i j h ⟶ E.obj i j h)
    (fun i hi => by
      have he : i=0 := Fin.eq_of_val_eq (by simpa using hi)
      subst i
      exact (D.unit 0).hom ≫ (E.unit 0).inv)
    (fun k prev i hi => by
      by_cases he : i=k.succ
      · subst i
        exact (D.unit k.succ).hom ≫ (E.unit k.succ).inv
      · have hik : i≤k.castSucc := by
          simp only [Fin.le_def,Fin.ext_iff,Fin.val_succ,Fin.val_castSucc] at *
          omega
        exact (D.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).inv ≫
          (prev i hik ⊗ₘ f k) ≫ (E.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).hom)
    j) i hij

@[simp] lemma extendApp_self (f : ∀j : Fin n, D.obj j.castSucc j.succ (Fin.castSucc_le_succ j) ⟶
      E.obj j.castSucc j.succ (Fin.castSucc_le_succ j)) (i : Fin (n+1)) :
    extendApp f i i le_rfl = (D.unit i).hom ≫ (E.unit i).inv := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih => simp [extendApp,Fin.induction_succ]

lemma extendApp_succ (f : ∀j : Fin n, D.obj j.castSucc j.succ (Fin.castSucc_le_succ j) ⟶
      E.obj j.castSucc j.succ (Fin.castSucc_le_succ j))
    (i : Fin (n+1)) (k : Fin n) (hik : i≤k.castSucc) :
    extendApp f i k.succ (hik.trans (Fin.castSucc_le_succ k)) =
      (D.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).inv ≫
      (extendApp f i k.castSucc hik ⊗ₘ f k) ≫
        (E.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).hom := by
  have he : i≠k.succ := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_succ] at hh
    have hi : i.val≤k.val := hik
    omega
  simp only [extendApp,Fin.induction_succ,dite_eq_right he]

lemma extendApp_succ_square
    (f : ∀j : Fin n, D.obj j.castSucc j.succ (Fin.castSucc_le_succ j) ⟶
      E.obj j.castSucc j.succ (Fin.castSucc_le_succ j))
    (i : Fin (n+1)) (k : Fin n) (hik : i≤k.castSucc) :
    (extendApp f i k.castSucc hik ⊗ₘ f k) ≫
        (E.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).hom =
      (D.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).hom ≫
        extendApp f i k.succ (hik.trans (Fin.castSucc_le_succ k)) := by
  rw [extendApp_succ f i k hik]
  simp

lemma unit_left_square (D E : Diagram C I) (i j : I) (hij : i≤j)
    (f : D.obj i j hij ⟶ E.obj i j hij) :
    (((D.unit i).hom ≫ (E.unit i).inv)⊗ₘf) ≫ (E.cut i i j le_rfl hij).hom =
      (D.cut i i j le_rfl hij).hom ≫ f := by
  rw [D.left_unit,E.left_unit,tensorHom_comp_whiskerRight_assoc]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [MonoidalCategory.tensorHom_def,Category.assoc,leftUnitor_naturality]

lemma unit_right_square (D E : Diagram C I) (i j : I) (hij : i≤j)
    (f : D.obj i j hij ⟶ E.obj i j hij) :
    (f⊗ₘ((D.unit j).hom ≫ (E.unit j).inv)) ≫ (E.cut i j j hij le_rfl).hom =
      (D.cut i j j hij le_rfl).hom ≫ f := by
  rw [D.right_unit,E.right_unit,tensorHom_comp_whiskerLeft_assoc]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [MonoidalCategory.tensorHom_def',Category.assoc,rightUnitor_naturality]

lemma extendApp_cut
    (f : ∀j : Fin n, D.obj j.castSucc j.succ (Fin.castSucc_le_succ j) ⟶
      E.obj j.castSucc j.succ (Fin.castSucc_le_succ j)) :
    ∀k (j i : Fin (n+1)) (hij : i≤j) (hjk : j≤k),
      (extendApp f i j hij ⊗ₘ extendApp f j k hjk) ≫ (E.cut i j k hij hjk).hom =
        (D.cut i j k hij hjk).hom ≫ extendApp f i k (hij.trans hjk) := by
  apply Fin.induction
  · intro j i hij hjk
    have hj : j=0 := Fin.eq_of_val_eq (by simpa using hjk)
    subst j
    rw [extendApp_self]
    exact unit_right_square D E i 0 hij (extendApp f i 0 hij)
  · intro k ih j i hij hjk
    by_cases he : j=k.succ
    · subst j
      rw [extendApp_self]
      exact unit_right_square D E i k.succ hij (extendApp f i k.succ hij)
    · have hj : j≤k.castSucc := by
        simp only [Fin.le_def,Fin.ext_iff,Fin.val_succ,Fin.val_castSucc] at *
        omega
      exact cut_propagate D E i j k.castSucc k.succ hij hj (Fin.castSucc_le_succ k)
        (extendApp f i j hij) (extendApp f j k.castSucc hj) (f k)
        (extendApp f i k.castSucc (hij.trans hj)) (extendApp f j k.succ hjk)
        (extendApp f i k.succ (hij.trans hjk)) (ih j i hij hj)
        (extendApp_succ_square f j k hj) (extendApp_succ_square f i k (hij.trans hj))

noncomputable def extend (f : (eval n).obj D ⟶ (eval n).obj E) : D ⟶ E where
  app := extendApp f
  unit i := by rw [extendApp_self f i]; simp
  cut i j k hij hjk := extendApp_cut f k j i hij hjk

lemma extend_elementary (f : (eval n).obj D ⟶ (eval n).obj E) (i : Fin n) :
    (extend f).app i.castSucc i.succ (Fin.castSucc_le_succ i) = f i := by
  change extendApp f i.castSucc i.succ _ = f i
  apply (cancel_epi (D.cut i.castSucc i.castSucc i.succ le_rfl (Fin.castSucc_le_succ i)).hom).mp
  rw [←extendApp_succ_square f i.castSucc i le_rfl,extendApp_self f i.castSucc]
  exact unit_left_square D E i.castSucc i.succ (Fin.castSucc_le_succ i) (f i)

noncomputable instance instFullFinHAddNatOfNatForallEval : (eval (C:=C) n).Full where
  map_surjective f := ⟨extend f,by funext i; exact extend_elementary f i⟩

end IntervalBar.Diagram

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalMap
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.IntervalBar.Diagram.instFullFinHAddNatOfNatForallEval _root_.OAI.NerveHomotopy.homologyMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v u' v' w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D]
variable {I : Type w} [Preorder I]

noncomputable def mapObj (F : C ⥤ D) [F.Monoidal] (A : Diagram C I) : Diagram D I where
  obj i j h := F.obj (A.obj i j h)
  unit i := F.mapIso (A.unit i) ≪≫ (Functor.Monoidal.εIso F).symm
  cut i j k hij hjk := Functor.Monoidal.μIso F _ _ ≪≫ F.mapIso (A.cut i j k hij hjk)
  left_unit i j h := by
    simp only [Iso.trans_hom,Functor.mapIso_hom,Functor.Monoidal.μIso_hom,
      Iso.symm_hom,Functor.Monoidal.εIso_inv]
    rw [A.left_unit,Functor.map_comp,Functor.Monoidal.map_whiskerRight,
      Functor.Monoidal.map_leftUnitor]
    simp only [Category.assoc,Functor.Monoidal.μ_δ_assoc,comp_whiskerRight]
  right_unit i j h := by
    simp only [Iso.trans_hom,Functor.mapIso_hom,Functor.Monoidal.μIso_hom,
      Iso.symm_hom,Functor.Monoidal.εIso_inv]
    rw [A.right_unit,Functor.map_comp,Functor.Monoidal.map_whiskerLeft,
      Functor.Monoidal.map_rightUnitor]
    simp only [Category.assoc,Functor.Monoidal.μ_δ_assoc,whiskerLeft_comp]
  associativity i j k l hij hjk hkl := by
    simp only [Iso.trans_hom,Functor.mapIso_hom,Functor.Monoidal.μIso_hom]
    simp only [comp_whiskerRight,whiskerLeft_comp,Category.assoc]
    rw [μ_natural_left_assoc,←F.map_comp, A.associativity]
    simp only [Functor.map_comp]
    rw [Functor.LaxMonoidal.associativity_assoc, μ_natural_right_assoc]

noncomputable def map (F : C ⥤ D) [F.Monoidal] : Diagram C I ⥤ Diagram D I where
  obj := mapObj F
  map f := {
    app i j h := F.map (f.app i j h)
    unit i := by
      simp only [mapObj,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,Functor.Monoidal.εIso_inv]
      rw [←Category.assoc,←F.map_comp,f.unit]
    cut i j k hij hjk := by
      simp only [mapObj,Iso.trans_hom,Functor.mapIso_hom,Functor.Monoidal.μIso_hom]
      rw [μ_natural_assoc,←F.map_comp,f.cut,F.map_comp,Category.assoc] }
  map_id A := by apply Hom.ext; intro i j h; exact F.map_id _
  map_comp f g := by apply Hom.ext; intro i j h; exact F.map_comp _ _

noncomputable def pair (A : Diagram C I) (B : Diagram D I) : Diagram (C×D) I where
  obj i j h := (A.obj i j h,B.obj i j h)
  unit i := (A.unit i).prod (B.unit i)
  cut i j k hij hjk := (A.cut i j k hij hjk).prod (B.cut i j k hij hjk)
  left_unit i j h := by ext; exacts [A.left_unit i j h,B.left_unit i j h]
  right_unit i j h := by ext; exacts [A.right_unit i j h,B.right_unit i j h]
  associativity i j k l hij hjk hkl := by
    ext; exacts [A.associativity i j k l hij hjk hkl,B.associativity i j k l hij hjk hkl]

noncomputable def pairHom {A A' : Diagram C I} {B B' : Diagram D I}
    (f : A ⟶ A') (g : B ⟶ B') : pair A B ⟶ pair A' B' where
  app i j h := (f.app i j h,g.app i j h)
  unit i := by ext; exacts [f.unit i,g.unit i]
  cut i j k hij hjk := by ext; exacts [f.cut i j k hij hjk,g.cut i j k hij hjk]

noncomputable def constantUnit : Diagram C I where
  obj _ _ _ := 𝟙_ C
  unit _ := Iso.refl _
  cut _ _ _ _ _ := λ_ _
  left_unit _ _ _ := by simp
  right_unit _ _ _ := by simp; exact unitors_equal
  associativity _ _ _ _ _ _ _ := by monoidal

end IntervalBar.Diagram

end

section
open _root_.CategoryTheory MonoidalCategory BraidedCategory
universe u v
namespace IntervalBar
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

lemma tensorμ_braiding (W X Y Z : C) :
    ((β_ W X).hom ⊗ₘ (β_ Y Z).hom) ≫ tensorμ X W Z Y =
      tensorμ W X Y Z ≫ (β_ (W⊗Y) (X⊗Z)).hom := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding Y X,
    MonoidalCategory.tensorHom_def]
end IntervalBar

end

section

open _root_.CategoryTheory MonoidalCategory
universe u v w
namespace IntervalBar
namespace Normal

variable {A : Type u}
open FreeMonoidalCategory

def fold : List A → FreeMonoidalCategory A
  | [] => .unit
  | a::l => .tensor (.of a) (fold l)

def appendIso : ∀ l r : List A, fold l ⊗ fold r ≅ fold (l++r)
  | [],_ => λ_ _
  | a::l,r => (α_ _ _ _ ) ≪≫ (whiskerLeftIso (.of a) (appendIso l r))

lemma segment_append (l : List A) (i j k : ℕ) (hij : i≤j) (hjk : j≤k) :
    (l.drop i).take (j-i) ++ (l.drop j).take (k-j) = (l.drop i).take (k-i) := by
  have hji : j=i+(j-i) := by omega
  have hki : k-i=(j-i)+(k-j) := by omega
  rw [hki,List.take_add,List.drop_drop,←hji]

def segment (l : List A) (i j : ℕ) : List A := (l.drop i).take (j-i)
@[simp] lemma segment_self (l : List A) (i : ℕ) : segment l i i=[] := by
  simp [segment]

def diagram {n : ℕ} (l : List A) : Diagram (FreeMonoidalCategory A) (Fin (n+1)) where
  obj i j _ := fold (segment l i.val j.val)
  unit i := eqToIso (by simp [fold])
  cut i j k hij hjk := appendIso _ _ ≪≫ eqToIso (congrArg fold (segment_append l i j k hij hjk))
  left_unit _ _ _ := Subsingleton.elim _ _
  right_unit _ _ _ := Subsingleton.elim _ _
  associativity _ _ _ _ _ _ _ := Subsingleton.elim _ _

variable {C : Type v} [Groupoid.{w} C] [MonoidalCategory C]

@[simp] lemma project_whiskerLeft (f : A → C) (X : FreeMonoidalCategory A)
    {Y Z : FreeMonoidalCategory A} (h : Y ⟶ Z) :
    (project f).map (X ◁ h) = (project f).obj X ◁ (project f).map h := by
  induction h using Quotient.inductionOn with | h h => rfl
@[simp] lemma project_whiskerRight (f : A → C) {Y Z : FreeMonoidalCategory A}
    (h : Y ⟶ Z) (X : FreeMonoidalCategory A) :
    (project f).map (h ▷ X) = (project f).map h ▷ (project f).obj X := by
  induction h using Quotient.inductionOn with | h h => rfl

@[simp] lemma project_leftUnitor (f : A → C) (X : FreeMonoidalCategory A) :
    (project f).map (λ_ X).hom = (λ_ ((project f).obj X)).hom := rfl
@[simp] lemma project_rightUnitor (f : A → C) (X : FreeMonoidalCategory A) :
    (project f).map (ρ_ X).hom = (ρ_ ((project f).obj X)).hom := rfl
@[simp] lemma project_associator (f : A → C) (X Y Z : FreeMonoidalCategory A) :
    (project f).map (α_ X Y Z).hom =
      (α_ ((project f).obj X) ((project f).obj Y) ((project f).obj Z)).hom := rfl

variable {I : Type u} [Preorder I]
def projectDiagram (f : A → C) (D : Diagram (FreeMonoidalCategory A) I) : Diagram C I where
  obj i j h := (project f).obj (D.obj i j h)
  unit i := (project f).mapIso (D.unit i)
  cut i j k hij hjk := (project f).mapIso (D.cut i j k hij hjk)
  left_unit i j h := by
    have he := congrArg ((project f).map) (D.left_unit i j h)
    simp only [Functor.map_comp,project_whiskerRight,project_leftUnitor] at he
    exact he
  right_unit i j h := by
    have he := congrArg ((project f).map) (D.right_unit i j h)
    simp only [Functor.map_comp,project_whiskerLeft,project_rightUnitor] at he
    exact he
  associativity i j k l hij hjk hkl := by
    have he := congrArg ((project f).map) (D.associativity i j k l hij hjk hkl)
    simp only [Functor.map_comp,project_whiskerLeft,project_whiskerRight,project_associator] at he
    exact he

lemma segment_finRange {n : ℕ} (i : Fin n) :
    segment (List.finRange n) i.val (i.val+1) = [i] := by
  simp only [segment,Nat.add_sub_cancel_left]
  rw [List.take_one_drop_eq_of_lt_length (by simp)]
  congr 1
  apply Fin.ext
  simp

noncomputable def elementaryDiagram {n : ℕ} (f : Fin n → C) : Diagram C (Fin (n+1)) :=
  projectDiagram f (diagram (List.finRange n))

noncomputable def elementaryIso {n : ℕ} (f : Fin n → C) :
    (Diagram.eval n).obj (elementaryDiagram f) ≅ f where
  hom i := (eqToIso (by
    change (project f).obj (fold (segment (List.finRange n) i.val (i.val+1))) = _
    rw [segment_finRange]
    rfl) ≪≫ ρ_ (f i)).hom
  inv i := (eqToIso (by
    change (project f).obj (fold (segment (List.finRange n) i.val (i.val+1))) = _
    rw [segment_finRange]
    rfl) ≪≫ ρ_ (f i)).inv
  hom_inv_id := by funext i; exact Iso.hom_inv_id _
  inv_hom_id := by funext i; exact Iso.inv_hom_id _

noncomputable instance instEssSurjDiagramFinHAddNatOfNatForallEval {n : ℕ} : (Diagram.eval (C:=C) n).EssSurj where
  mem_essImage f := ⟨elementaryDiagram f,⟨elementaryIso f⟩⟩

end Normal
end IntervalBar

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalTensor
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.NerveHomotopy.homologyMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I : Type w} [Preorder I]

noncomputable def tensorObj (A B : Diagram C I) : Diagram C I :=
  mapObj (tensor C) (pair A B)

noncomputable def tensorHom {A A' B B' : Diagram C I} (f : A ⟶ A') (g : B ⟶ B') :
    tensorObj A B ⟶ tensorObj A' B' := (map (tensor C)).map (pairHom f g)

@[simp] lemma tensorObj_obj (A B : Diagram C I) (i j : I) (h : i≤j) :
    (tensorObj A B).obj i j h = A.obj i j h ⊗ B.obj i j h := rfl
@[simp] lemma tensorObj_unit (A B : Diagram C I) (i : I) :
    ((tensorObj A B).unit i).hom = ((A.unit i).hom ⊗ₘ (B.unit i).hom) ≫ (λ_ (𝟙_ C)).hom := rfl
@[simp] lemma tensorObj_cut (A B : Diagram C I) (i j k : I) (hij : i≤j) (hjk : j≤k) :
    ((tensorObj A B).cut i j k hij hjk).hom =
      tensorμ (A.obj i j hij) (B.obj i j hij) (A.obj j k hjk) (B.obj j k hjk) ≫
        ((A.cut i j k hij hjk).hom ⊗ₘ (B.cut i j k hij hjk).hom) := rfl
@[simp] lemma tensorHom_app {A A' B B' : Diagram C I} (f : A ⟶ A') (g : B ⟶ B')
    (i j : I) (h : i≤j) : (tensorHom f g).app i j h = f.app i j h ⊗ₘ g.app i j h := rfl

omit [SymmetricCategory C] in
lemma associator_unit_square {X Y Z : C} (f : X ⟶ 𝟙_ C) (g : Y ⟶ 𝟙_ C) (h : Z ⟶ 𝟙_ C) :
    (α_ X Y Z).hom ≫ (f ⊗ₘ ((g ⊗ₘ h) ≫ (λ_ (𝟙_ C)).hom)) ≫ (λ_ (𝟙_ C)).hom =
      (((f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom) ⊗ₘ h) ≫ (λ_ (𝟙_ C)).hom := by
  rw [←tensorHom_comp_whiskerLeft,←tensorHom_comp_whiskerRight]
  simp only [Category.assoc]
  rw [←associator_naturality_assoc]
  congr 1
  monoidal

lemma associator_cut_square {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ Z₃ : C}
    (f : X₁ ⊗ Y₁ ⟶ Z₁) (g : X₂ ⊗ Y₂ ⟶ Z₂) (h : X₃ ⊗ Y₃ ⟶ Z₃) :
    ((α_ X₁ X₂ X₃).hom ⊗ₘ (α_ Y₁ Y₂ Y₃).hom) ≫
      tensorμ X₁ (X₂ ⊗ X₃) Y₁ (Y₂ ⊗ Y₃) ≫
        (f ⊗ₘ (tensorμ X₂ X₃ Y₂ Y₃ ≫ (g ⊗ₘ h))) =
      (tensorμ (X₁ ⊗ X₂) X₃ (Y₁ ⊗ Y₂) Y₃ ≫
        ((tensorμ X₁ X₂ Y₁ Y₂ ≫ (f ⊗ₘ g)) ⊗ₘ h)) ≫ (α_ Z₁ Z₂ Z₃).hom := by
  rw [←whiskerLeft_comp_tensorHom,←whiskerRight_comp_tensorHom]
  simp only [Category.assoc]
  rw [←associator_monoidal_assoc,associator_naturality]

lemma leftUnitor_cut_square {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    ((λ_ X).hom ⊗ₘ (λ_ Y).hom) ≫ f =
      (tensorμ (𝟙_ C) X (𝟙_ C) Y ≫ ((λ_ (𝟙_ C)).hom ⊗ₘ f)) ≫ (λ_ Z).hom := by
  rw [leftUnitor_monoidal_assoc]
  simp only [MonoidalCategory.tensorHom_def,Category.assoc,leftUnitor_naturality]

lemma rightUnitor_cut_square {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    ((ρ_ X).hom ⊗ₘ (ρ_ Y).hom) ≫ f =
      (tensorμ X (𝟙_ C) Y (𝟙_ C) ≫ (f ⊗ₘ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ Z).hom := by
  rw [rightUnitor_monoidal_assoc]
  simp only [MonoidalCategory.tensorHom_def',Category.assoc,rightUnitor_naturality]

noncomputable def associatorHom (A B D : Diagram C I) :
    tensorObj (tensorObj A B) D ⟶ tensorObj A (tensorObj B D) where
  app i j h := (α_ (A.obj i j h) (B.obj i j h) (D.obj i j h)).hom
  unit i := associator_unit_square (A.unit i).hom (B.unit i).hom (D.unit i).hom
  cut i j k hij hjk := associator_cut_square (A.cut i j k hij hjk).hom
    (B.cut i j k hij hjk).hom (D.cut i j k hij hjk).hom

noncomputable def leftUnitorHom (A : Diagram C I) : tensorObj constantUnit A ⟶ A where
  app i j h := (λ_ (A.obj i j h)).hom
  unit i := by
    change (λ_ _).hom ≫ (A.unit i).hom = (𝟙 _ ⊗ₘ (A.unit i).hom) ≫ (λ_ _).hom
    rw [id_tensorHom,leftUnitor_naturality]
  cut i j k hij hjk := leftUnitor_cut_square (A.cut i j k hij hjk).hom

noncomputable def rightUnitorHom (A : Diagram C I) : tensorObj A constantUnit ⟶ A where
  app i j h := (ρ_ (A.obj i j h)).hom
  unit i := by
    change (ρ_ _).hom ≫ (A.unit i).hom = ((A.unit i).hom ⊗ₘ 𝟙 _) ≫ (λ_ _).hom
    rw [tensorHom_id,unitors_equal,rightUnitor_naturality]
  cut i j k hij hjk := rightUnitor_cut_square (A.cut i j k hij hjk).hom

noncomputable instance monoidalStruct : MonoidalCategoryStruct (Diagram C I) where
  tensorObj := tensorObj
  tensorHom := tensorHom
  whiskerLeft A _ _ f := tensorHom (𝟙 A) f
  whiskerRight f A := tensorHom f (𝟙 A)
  tensorUnit := constantUnit
  associator A B D := asIso (associatorHom A B D)
  leftUnitor A := asIso (leftUnitorHom A)
  rightUnitor A := asIso (rightUnitorHom A)

@[simp] lemma whiskerLeft_app (A : Diagram C I) {B D : Diagram C I} (f : B ⟶ D)
    (i j : I) (h : i≤j) : (A ◁ f).app i j h = A.obj i j h ◁ f.app i j h := by
  change (𝟙 (A.obj i j h) ⊗ₘ f.app i j h) = _
  exact MonoidalCategory.id_tensorHom (A.obj i j h) (f.app i j h)
@[simp] lemma whiskerRight_app {A B : Diagram C I} (f : A ⟶ B) (D : Diagram C I)
    (i j : I) (h : i≤j) : (f ▷ D).app i j h = f.app i j h ▷ D.obj i j h := by
  change (f.app i j h ⊗ₘ 𝟙 (D.obj i j h)) = _
  exact MonoidalCategory.tensorHom_id (f.app i j h) (D.obj i j h)
@[simp] lemma associator_app (A B D : Diagram C I) (i j : I) (h : i≤j) :
    (α_ A B D).hom.app i j h = (α_ (A.obj i j h) (B.obj i j h) (D.obj i j h)).hom := rfl
@[simp] lemma leftUnitor_app (A : Diagram C I) (i j : I) (h : i≤j) :
    (λ_ A).hom.app i j h = (λ_ (A.obj i j h)).hom := rfl
@[simp] lemma rightUnitor_app (A : Diagram C I) (i j : I) (h : i≤j) :
    (ρ_ A).hom.app i j h = (ρ_ (A.obj i j h)).hom := rfl
@[simp] lemma tensor_app {A A' B B' : Diagram C I} (f : A ⟶ A') (g : B ⟶ B')
    (i j : I) (h : i≤j) : (f ⊗ₘ g).app i j h = f.app i j h ⊗ₘ g.app i j h := rfl
@[simp] lemma tensor_obj (A B : Diagram C I) (i j : I) (h : i≤j) :
    (A⊗B).obj i j h = A.obj i j h ⊗ B.obj i j h := rfl
@[simp] lemma tensorUnit_obj (i j : I) (h : i≤j) :
    (𝟙_ (Diagram C I)).obj i j h = 𝟙_ C := rfl

noncomputable instance monoidal : MonoidalCategory (Diagram C I) where
  tensorHom_def f g := by apply Hom.ext; intro i j h; simp [MonoidalCategory.tensorHom_def]
  id_tensorHom_id A B := by apply Hom.ext; intro i j h; simp
  tensorHom_comp_tensorHom f g h k := by apply Hom.ext; intro i j hij; simp
  whiskerLeft_id A B := by apply Hom.ext; intro i j h; simp
  id_whiskerRight A B := by apply Hom.ext; intro i j h; simp
  associator_naturality f g h := by apply Hom.ext; intro i j hij; simp
  leftUnitor_naturality f := by apply Hom.ext; intro i j h; simp
  rightUnitor_naturality f := by apply Hom.ext; intro i j h; simp
  pentagon A B D E := by apply Hom.ext; intro i j h; simp
  triangle A B := by apply Hom.ext; intro i j h; simp

lemma braiding_unit_square {X Y : C} (f : X ⟶ 𝟙_ C) (g : Y ⟶ 𝟙_ C) :
    (β_ X Y).hom ≫ (g ⊗ₘ f) ≫ (λ_ (𝟙_ C)).hom =
      (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom := by
  rw [←braiding_naturality_assoc]
  simp only [braiding_tensorUnit_right,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [←unitors_equal]

lemma braiding_cut_square {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    (f : X₁ ⊗ Y₁ ⟶ Z₁) (g : X₂ ⊗ Y₂ ⟶ Z₂) :
    ((β_ X₁ X₂).hom ⊗ₘ (β_ Y₁ Y₂).hom) ≫
      (tensorμ X₂ X₁ Y₂ Y₁ ≫ (g ⊗ₘ f)) =
      (tensorμ X₁ X₂ Y₁ Y₂ ≫ (f ⊗ₘ g)) ≫ (β_ Z₁ Z₂).hom := by
  rw [←Category.assoc,IntervalBar.tensorμ_braiding,Category.assoc,
    ←braiding_naturality,Category.assoc]

noncomputable def braidingHom (A B : Diagram C I) : A⊗B ⟶ B⊗A where
  app i j h := (β_ (A.obj i j h) (B.obj i j h)).hom
  unit i := braiding_unit_square (A.unit i).hom (B.unit i).hom
  cut i j k hij hjk := braiding_cut_square (A.cut i j k hij hjk).hom (B.cut i j k hij hjk).hom

omit [SymmetricCategory C] in
@[simp] lemma inv_app {A B : Diagram C I} (f : A ⟶ B) (i j : I) (h : i≤j) :
    (CategoryTheory.inv f).app i j h = CategoryTheory.inv (f.app i j h) := by
  rw [←Groupoid.inv_eq_inv]
  rfl

@[simp] lemma associator_inv_app (A B D : Diagram C I) (i j : I) (h : i≤j) :
    (α_ A B D).inv.app i j h = (α_ (A.obj i j h) (B.obj i j h) (D.obj i j h)).inv := by
  change (CategoryTheory.inv (associatorHom A B D)).app i j h = _
  rw [inv_app]
  apply IsIso.inv_eq_of_hom_inv_id
  exact Iso.hom_inv_id _

noncomputable instance braided : BraidedCategory (Diagram C I) where
  braiding A B := asIso (braidingHom A B)
  braiding_naturality_right A B D f := by
    apply Hom.ext; intro i j h
    change (𝟙 _ ⊗ₘ f.app i j h) ≫ (β_ _ _).hom = (β_ _ _).hom ≫ (f.app i j h ⊗ₘ 𝟙 _)
    simp
  braiding_naturality_left f D := by
    apply Hom.ext; intro i j h
    change (f.app i j h ⊗ₘ 𝟙 _) ≫ (β_ _ _).hom = (β_ _ _).hom ≫ (𝟙 _ ⊗ₘ f.app i j h)
    simp
  hexagon_forward A B D := by
    apply Hom.ext; intro i j h
    change (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ (α_ _ _ _).hom =
      ((β_ _ _).hom ⊗ₘ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ₘ (β_ _ _).hom)
    simp only [tensorHom_id,id_tensorHom]
    exact hexagon_forward _ _ _
  hexagon_reverse A B D := by
    apply Hom.ext; intro i j h
    simp only [comp_app,associator_inv_app,whiskerLeft_app,whiskerRight_app]
    change (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (α_ _ _ _).inv =
      (_ ◁ (β_ _ _).hom) ≫ (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _)
    exact hexagon_reverse _ _ _

@[simp] lemma braiding_app (A B : Diagram C I) (i j : I) (h : i≤j) :
    (β_ A B).hom.app i j h = (β_ (A.obj i j h) (B.obj i j h)).hom := rfl

noncomputable instance symmetric : SymmetricCategory (Diagram C I) where
  symmetry A B := by apply Hom.ext; intro i j h; simp

noncomputable instance evalEquivalence (n : ℕ) : (eval (C:=C) n).IsEquivalence where

end IntervalBar.Diagram

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalFunctor
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.NerveHomotopy.homologyMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open _root_.CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v u' v' w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I : Type w} [Preorder I]
noncomputable instance reindexMonoidal {J : Type w} [Preorder J] (f : I →o J) :
    (reindex (C:=C) f).Monoidal := Functor.CoreMonoidal.toMonoidal {
  εIso := Iso.refl _
  μIso A B := Iso.refl _
  μIso_hom_natural_left := by
    intro X Y g X'
    apply Hom.ext
    intro i j h
    have hf : f i ≤ f j := f.monotone h
    change (g.app (f i) (f j) hf ⊗ₘ 𝟙 (X'.obj (f i) (f j) hf)) ≫ 𝟙 _ =
      𝟙 _ ≫ (g.app (f i) (f j) hf ⊗ₘ 𝟙 (X'.obj (f i) (f j) hf))
    simp
  μIso_hom_natural_right := by
    intro X Y X' g
    apply Hom.ext
    intro i j h
    have hf : f i ≤ f j := f.monotone h
    change (𝟙 (X'.obj (f i) (f j) hf) ⊗ₘ g.app (f i) (f j) hf) ≫ 𝟙 _ =
      𝟙 _ ≫ (𝟙 (X'.obj (f i) (f j) hf) ⊗ₘ g.app (f i) (f j) hf)
    simp
  associativity := by
    intro X Y Z
    apply Hom.ext
    intro i j h
    have hf : f i ≤ f j := f.monotone h
    let x := X.obj (f i) (f j) hf
    let y := Y.obj (f i) (f j) hf
    let z := Z.obj (f i) (f j) hf
    change (𝟙 (x ⊗ y) ⊗ₘ 𝟙 z) ≫ 𝟙 _ ≫ (α_ x y z).hom =
      (α_ x y z).hom ≫ (𝟙 x ⊗ₘ 𝟙 (y ⊗ z)) ≫ 𝟙 _
    simp
  left_unitality := by
    intro X
    apply Hom.ext
    intro i j h
    have hf : f i ≤ f j := f.monotone h
    let x := X.obj (f i) (f j) hf
    change (λ_ x).hom = (𝟙 (𝟙_ C) ⊗ₘ 𝟙 x) ≫ 𝟙 _ ≫ (λ_ x).hom
    simp
  right_unitality := by
    intro X
    apply Hom.ext
    intro i j h
    have hf : f i ≤ f j := f.monotone h
    let x := X.obj (f i) (f j) hf
    change (ρ_ x).hom = (𝟙 x ⊗ₘ 𝟙 (𝟙_ C)) ≫ 𝟙 _ ≫ (ρ_ x).hom
    simp }


noncomputable def mapεHom (F : C ⥤ D) [F.Monoidal] :
    (𝟙_ (Diagram D I)) ⟶ (map F).obj (𝟙_ (Diagram C I)) where
  app _ _ _ := ε F
  unit i := by
    change ε F ≫ (F.map (𝟙 _) ≫ η F) = 𝟙 _
    simp
  cut i j k hij hjk := by
    change (ε F ⊗ₘ ε F) ≫ (μ F _ _ ≫ F.map (λ_ _).hom) = (λ_ _).hom ≫ ε F
    rw [←Category.assoc,ε_tensorHom_comp_μ]
    simp

noncomputable def mapμHom (F : C ⥤ D) [F.Braided]
    (A B : Diagram C I) : (map F).obj A ⊗ (map F).obj B ⟶ (map F).obj (A⊗B) where
  app i j h := μ F (A.obj i j h) (B.obj i j h)
  unit i := by
    change μ F _ _ ≫ (F.map (((A.unit i).hom ⊗ₘ (B.unit i).hom) ≫ (λ_ _).hom) ≫ η F) =
      ((F.map (A.unit i).hom ≫ η F) ⊗ₘ (F.map (B.unit i).hom ≫ η F)) ≫ (λ_ _).hom
    rw [F.map_comp]
    simp only [Category.assoc]
    rw [←μ_natural_assoc,Functor.Monoidal.map_leftUnitor]
    simp only [Category.assoc,Functor.Monoidal.μ_δ_assoc]
    rw [←leftUnitor_naturality,←tensorHom_comp_tensorHom]
    simp [MonoidalCategory.tensorHom_def]
  cut i j k hij hjk := by
    change (μ F _ _ ⊗ₘ μ F _ _) ≫ (μ F _ _ ≫ F.map
      (tensorμ _ _ _ _ ≫ ((A.cut i j k hij hjk).hom ⊗ₘ (B.cut i j k hij hjk).hom))) =
      (tensorμ _ _ _ _ ≫ ((μ F _ _ ≫ F.map (A.cut i j k hij hjk).hom) ⊗ₘ
        (μ F _ _ ≫ F.map (B.cut i j k hij hjk).hom))) ≫ μ F _ _
    simp only [F.map_comp,←tensorHom_comp_tensorHom,Category.assoc]
    rw [←tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc,←μ_natural]

noncomputable instance mapMonoidal (F : C ⥤ D) [F.Braided] :
    (map (I:=I) F).Monoidal := Functor.CoreMonoidal.toMonoidal {
  εIso := asIso (mapεHom F)
  μIso A B := asIso (mapμHom F A B)
  μIso_hom_natural_left := by
    intros; apply Hom.ext; intro i j h
    simp [map,mapObj,mapμHom]
  μIso_hom_natural_right := by
    intros; apply Hom.ext; intro i j h
    simp [map,mapObj,mapμHom]
  associativity := by
    intros; apply Hom.ext; intro i j h
    simp [map,mapObj,mapμHom]
  left_unitality := by
    intros; apply Hom.ext; intro i j h
    simp [map,mapObj,mapμHom,mapεHom]
  right_unitality := by
    intros; apply Hom.ext; intro i j h
    simp [map,mapObj,mapμHom,mapεHom] }

noncomputable instance reindexBraided {J : Type w} [Preorder J] (f : I →o J) :
    (reindex (C:=C) f).Braided where
  braided A B := by
    apply Hom.ext; intro i j h
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp

noncomputable instance mapBraided (F : C ⥤ D) [F.Braided] : (map (I:=I) F).Braided where
  braided A B := by
    apply Hom.ext; intro i j h
    change μ F _ _ ≫ F.map (β_ _ _).hom = (β_ _ _).hom ≫ μ F _ _
    exact Functor.LaxBraided.braided (F:=F) _ _

end IntervalBar.Diagram

end

open _root_.CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v u' v' u'' v'' w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D]
variable {E : Type u''} [Groupoid.{v''} E] [MonoidalCategory E]
variable {I : Type w} [Preorder I]

lemma ext_heq {A B : Diagram C I} (hobj : A.obj=B.obj)
    (hunit : HEq A.unit B.unit) (hcut : HEq A.cut B.cut) : A=B := by
  cases A; cases B; cases hobj; cases hunit; cases hcut; rfl

@[simp] lemma eqToHom_app {A B : Diagram C I} (h : A=B) (i j : I) (hij : i≤j) :
    (eqToHom h).app i j hij=eqToHom (congrArg (fun X : Diagram C I => X.obj i j hij) h) := by
  cases h; rfl

@[simp] lemma mapObj_id (A : Diagram C I) : mapObj (𝟭 C) A=A := by
  refine ext_heq ?_ ?_ ?_
  · rfl
  · apply heq_of_eq
    funext i
    apply Iso.ext
    simp [mapObj]
  · apply heq_of_eq
    funext i j k hij hjk
    apply Iso.ext
    simp [mapObj]
@[simp] lemma map_id : map (I:=I) (𝟭 C)=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A => mapObj_id A) ?_
  intro A B f
  apply Hom.ext; intro i j h
  erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
  simp [map]
  change f.app i j h = 𝟙 _ ≫ f.app i j h ≫ 𝟙 _
  simp

@[simp] lemma mapObj_comp (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal]
    (A : Diagram C I) : mapObj (F⋙G) A=mapObj G (mapObj F A) := by
  refine ext_heq ?_ ?_ ?_
  · rfl
  · apply heq_of_eq
    funext i
    apply Iso.ext
    simp [mapObj]
  · apply heq_of_eq
    funext i j k hij hjk
    apply Iso.ext
    simp [mapObj,Category.assoc]
@[simp] lemma map_comp (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal] :
    map (I:=I) (F⋙G)=map F ⋙ map G := by
  refine CategoryTheory.Functor.ext (fun A => mapObj_comp F G A) ?_
  intro A B f
  apply Hom.ext; intro i j h
  erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
  simp [map]
  change G.map (F.map (f.app i j h)) =
    𝟙 _ ≫ G.map (F.map (f.app i j h)) ≫ 𝟙 _
  simp

variable {J : Type w} [Preorder J]
@[simp] lemma reindex_map (F : C ⥤ D) [F.Monoidal] (f : I →o J) :
    reindex (C:=C) f ⋙ map F = map F ⋙ reindex f := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro A B g
  apply Hom.ext
  intro i j h
  change F.map (g.app (f i) (f j) (f.monotone h)) =
    𝟙 _ ≫ F.map (g.app (f i) (f j) (f.monotone h)) ≫ 𝟙 _
  simp

end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalPullback
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.NerveHomotopy.homologyMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IntervalBar.Diagram

section

open _root_.CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v w

section

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I J K L : Type w} [Preorder I] [Preorder J] [Preorder K] [Preorder L]
@[simp] lemma map_reindex_id :
    map (I:=I) (reindex (C:=C) (OrderHom.id (α:=J)))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · rfl
    · apply heq_of_eq; funext i
      apply Iso.ext; apply Hom.ext; intro j k h
      change (A.unit i).hom.app j k h ≫ 𝟙 _ = _
      exact Category.comp_id _
    · apply heq_of_eq; funext i j k hij hjk
      apply Iso.ext; apply Hom.ext; intro l m h
      change 𝟙 _ ≫ (A.cut i j k hij hjk).hom.app l m h = _
      exact Category.id_comp _
  · intro A B f
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro l m hlm
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp [map,reindex]
    change (f.app i j h).app l m hlm = 𝟙 _ ≫ (f.app i j h).app l m hlm ≫ 𝟙 _
    simp
@[simp] lemma map_reindex_comp (f : J →o K) (g : K →o L) :
    map (I:=I) (reindex (C:=C) (g.comp f)) = map (reindex g) ⋙ map (reindex f) := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · rfl
    · apply heq_of_eq; funext i
      apply Iso.ext; apply Hom.ext; intro j k h
      change (A.unit i).hom.app (g (f j)) (g (f k)) _ ≫ 𝟙 _ =
        ((A.unit i).hom.app (g (f j)) (g (f k)) _ ≫ 𝟙 _) ≫ 𝟙 _
      simp
    · apply heq_of_eq; funext i j k hij hjk
      apply Iso.ext; apply Hom.ext; intro l m h
      change 𝟙 _ ≫ (A.cut i j k hij hjk).hom.app (g (f l)) (g (f m)) _ =
        𝟙 _ ≫ (𝟙 _ ≫ (A.cut i j k hij hjk).hom.app (g (f l)) (g (f m)) _)
      simp
  · intro A B h
    apply Hom.ext; intro i j hij
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro l m hlm
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp [map,reindex]
    change (h.app i j hij).app (g (f l)) (g (f m)) _ =
      𝟙 _ ≫ (h.app i j hij).app (g (f l)) (g (f m)) _ ≫ 𝟙 _
    simp

end

open _root_.CategoryTheory

open scoped Simplicial
end

section

open _root_.CategoryTheory MonoidalCategory
universe u v w u₁ u₂
variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]
variable {I : Type w} [Preorder I]

omit [MonoidalCategory C] in
lemma iso_hext {X X' Y Y' : C} (hX : X=X') (hY : Y=Y')
    (f : X ≅ Y) (g : X' ≅ Y') (h : HEq f.hom g.hom) : HEq f g := by
  cases hX; cases hY
  exact heq_of_eq (Iso.ext (eq_of_heq h))

lemma hom_hext {A A' B B' : Diagram C I} (hA : A=A') (hB : B=B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : ∀ i j hij, HEq (f.app i j hij) (g.app i j hij)) :
    HEq f g := by
  cases hA; cases hB
  exact heq_of_eq (Hom.ext (fun i j hij => eq_of_heq (h i j hij)))

lemma hfunext {α : Sort u₁} {β β' : α → Sort u₂} {f : ∀ a, β a} {g : ∀ a, β' a}
    (h : ∀ a, HEq (f a) (g a)) : HEq f g :=
  Function.hfunext rfl (by intro a b hab; cases hab; exact h a)
end

open _root_.CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v w

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I J K : Type w} [Preorder I] [Preorder J] [Preorder K]

@[simp] lemma map_ε_app {D : Type*} [Groupoid D] [MonoidalCategory D] [SymmetricCategory D]
    (F : C ⥤ D) [F.Braided] (i j : I) (h : i≤j) :
    (ε (map (I:=I) F)).app i j h = ε F := rfl

@[simp] lemma map_η_app {D : Type*} [Groupoid D] [MonoidalCategory D] [SymmetricCategory D]
    (F : C ⥤ D) [F.Braided] (i j : I) (h : i≤j) :
    (η (map (I:=I) F)).app i j h = η F := by
  apply (cancel_mono (ε F)).mp
  have hh := congrArg (fun f : (map (I:=I) F).obj (𝟙_ (Diagram C I)) ⟶
    (map (I:=I) F).obj (𝟙_ (Diagram C I)) => f.app i j h)
    (Functor.Monoidal.η_ε (map (I:=I) F))
  simp only [comp_app,map_ε_app,id_app] at hh
  simpa only [Functor.Monoidal.η_ε, map, mapObj, tensorUnit_obj] using hh

@[simp] lemma map_μ_app {D : Type*} [Groupoid D] [MonoidalCategory D] [SymmetricCategory D]
    (F : C ⥤ D) [F.Braided] (A B : Diagram C I) (i j : I) (h : i≤j) :
    (μ (map (I:=I) F) A B).app i j h = μ F (A.obj i j h) (B.obj i j h) := rfl

@[simp] lemma reindex_η_app (f : I →o J) (i j : I) (h : i≤j) :
    (η (reindex (C:=C) f)).app i j h = 𝟙 _ := rfl

@[simp] lemma reindex_μ_app (f : I →o J) (A B : Diagram C J) (i j : I) (h : i≤j) :
    (μ (reindex (C:=C) f) A B).app i j h = 𝟙 _ := rfl

omit [SymmetricCategory C] in
@[simp] lemma reindex_map_app (f : I →o J) {A B : Diagram C J} (g : A ⟶ B)
    (i j : I) (h : i≤j) : ((reindex f).map g).app i j h = g.app (f i) (f j) (f.monotone h) := rfl

omit [SymmetricCategory C] in
@[simp] lemma map_map_app {D : Type*} [Groupoid D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {A B : Diagram C I} (g : A ⟶ B)
    (i j : I) (h : i≤j) : ((map F).map g).app i j h = F.map (g.app i j h) := rfl

omit [SymmetricCategory C] in
@[simp] lemma map_obj {D : Type*} [Groupoid D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (A : Diagram C I) : (map F).obj A = mapObj F A := rfl

open scoped Simplicial

end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalEquivalence
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IntervalBar.Diagram

section
open _root_.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
noncomputable def simplicialMap (F : C ⥤ D) [F.Monoidal] :
    simplicial (C:=C) ⟶ simplicial (C:=D) where
  app p := (map (I:=Fin (p.unop.len+1)) F).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    exact reindex_map F f.unop.toOrderHom
noncomputable def bar : SSet := SimplicialDiagonal.nerveDiagonal.obj (simplicial (C:=C))
noncomputable def barMap (F : C ⥤ D) [F.Monoidal] : bar (C:=C) ⟶ bar (C:=D) :=
  SimplicialDiagonal.nerveDiagonal.map (simplicialMap F)
end

end IntervalBar.Diagram

open _root_.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type} [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I J K : Type} [Preorder I] [Preorder J] [Preorder K]
lemma simplicialMap_reindex_id :
    simplicialMap (reindex (C:=C) (OrderHom.id (α:=I)))=𝟙 _ := by
  apply NatTrans.ext
  funext p
  apply Cat.ext
  exact map_reindex_id
@[simp] lemma barMap_reindex_id :
    barMap (reindex (C:=C) (OrderHom.id (α:=I)))=𝟙 _ := by
  simp [barMap,simplicialMap_reindex_id,bar]
end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IteratedBarMaps
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I J K L : Type} [Preorder I] [Preorder J] [Preorder K] [Preorder L]
@[simp] lemma map_map_reindex_id :
    map (I:=K) (map (I:=J) (reindex (C:=C) (OrderHom.id (α:=I))))=𝟭 _ := by
  have he (X : Diagram (Diagram C I) J) : mapObj (reindex (OrderHom.id (α:=I))) X=X :=
    congrArg (fun F => F.obj X) map_reindex_id
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · funext i j h
      exact congrArg (fun F => F.obj (A.obj i j h)) map_reindex_id
    · apply hfunext; intro i
      apply iso_hext (he _) rfl
      apply hom_hext (he _) rfl
      intro j k h
      apply hom_hext (by simp [mapObj]) (by rfl)
      intro l m hlm
      apply heq_of_eq
      change (((map (reindex (C:=C) (OrderHom.id (α:=I)))).map (A.unit i).hom ≫
        Functor.OplaxMonoidal.η (map (reindex (C:=C) (OrderHom.id (α:=I))))).app j k h).app l m hlm = _
      erw [comp_app, map_η_app (I:=J) (reindex (C:=C) (OrderHom.id (α:=I)))]
      change ((A.unit i).hom.app j k h).app l m hlm ≫ 𝟙 _ = _
      exact Category.comp_id _
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      intro l m hlm
      apply hom_hext (by simp [mapObj]) (by simp [mapObj])
      intro n p hnp
      apply heq_of_eq
      change 𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app l m hlm).app n p hnp = _
      exact Category.id_comp _
  · intro A B f
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro k l hkl
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro m n hmn
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp only [map,reindex]
    erw [Category.id_comp, Category.comp_id]
    rfl
end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_SimplicialH0
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialH0
open FreeChains

variable {X Y : SSet}
@[reassoc] lemma natural (f : X ⟶ Y) : SSet.homologyMap f Z 0 ≫ Y.homology₀ε Z=X.homology₀ε Z := by
  apply (cancel_epi ((X.chainComplex Z).homologyπ 0)).mp
  apply (cancel_epi (X.chainComplex Z).cycles₀Iso.inv).mp
  apply Sigma.hom_ext
  intro x
  have he : X.ιChainComplex x ≫ (X.chainComplex Z).cycles₀Iso.inv =
      (X.chainComplex Z).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
    apply (cancel_mono ((X.chainComplex Z).iCycles 0)).mp
    simp
  change X.ιChainComplex x ≫ (X.chainComplex Z).cycles₀Iso.inv ≫ _ =
    X.ιChainComplex x ≫ (X.chainComplex Z).cycles₀Iso.inv ≫ _
  simp only [←Category.assoc]
  rw [he]
  simp only [Category.assoc]
  change _ ≫ _ ≫ homologyMap (SSet.chainComplexMap f Z) 0 ≫ _ = _
  rw [homologyπ_naturality_assoc,liftCycles_comp_cyclesMap_assoc,SSet.ι_chainComplexMap_f]
  simp
end SimplicialH0

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FiberSum
attribute [-instance] _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.NerveHomotopy.homologyMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory Limits MonoidalCategory
namespace BarFiberProduct

section
variable {C D : Type} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D]
noncomputable instance prodBraided : BraidedCategory (C×D) where
  braiding X Y := (β_ X.1 Y.1).prod (β_ X.2 Y.2)
  braiding_naturality_left := by intro X Y f Z; ext <;> simp
  braiding_naturality_right := by intro X Y Z f; ext <;> simp
  hexagon_forward := by intro X Y Z; ext <;> simp
  hexagon_reverse := by intro X Y Z; ext <;> simp
end
variable {C D : Type} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
noncomputable instance prodSymmetric :
    SymmetricCategory (C×D) where
  symmetry X Y := by
    apply Prod.hom_ext
    · change (β_ X.1 Y.1).hom ≫ (β_ Y.1 X.1).hom=𝟙 _
      simp
    · change (β_ X.2 Y.2).hom ≫ (β_ Y.2 X.2).hom=𝟙 _
      simp
end BarFiberProduct
open BarFiberProduct

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FilteredHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ConnectedProduct.connected_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits Opposite
namespace StageProductColimit

variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
variable (κ : Type)
def powerMap (F : C ⥤ D) : (κ → C) ⥤ (κ → D) where
  obj U i := F.obj (U i)
  map f i := F.map (f i)
  map_id _ := by funext i; exact F.map_id _
  map_comp _ _ := by funext i; exact F.map_comp _ _
instance instFaithfulForallPowerMap (F : C ⥤ D) [F.Faithful] : (powerMap κ F).Faithful where
  map_injective h := by funext i; exact F.map_injective (congrFun h i)
end StageProductColimit

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PowerEquivalence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ConnectedProduct.connected_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory
namespace StageProductColimit

variable {C D : Type} [Category.{0} C] [Category.{0} D] (κ ι : Type)
noncomputable instance instFullForallPowerMap (F : C ⥤ D) [F.Full] : (powerMap κ F).Full where
  map_surjective f := ⟨fun i => F.preimage (f i),by funext i; exact F.map_preimage (f i)⟩
noncomputable instance instEssSurjForallPowerMap (F : C ⥤ D) [F.EssSurj] : (powerMap κ F).EssSurj where
  mem_essImage X := ⟨fun i => F.objPreimage (X i),⟨{
    hom i := (F.objObjPreimageIso (X i)).hom
    inv i := (F.objObjPreimageIso (X i)).inv
    hom_inv_id := by funext i; exact Iso.hom_inv_id _
    inv_hom_id := by funext i; exact Iso.inv_hom_id _ }⟩⟩
noncomputable instance instIsEquivalenceForallPowerMap (F : C ⥤ D) [F.IsEquivalence] : (powerMap κ F).IsEquivalence where

def uncurry : (κ → ι → C) ⥤ (κ × ι → C) where
  obj U i := U i.1 i.2
  map f i := f i.1 i.2
def curry : (κ × ι → C) ⥤ (κ → ι → C) where
  obj U i j := U (i,j)
  map f i j := f (i,j)
noncomputable def curryEquiv : (κ → ι → C) ≌ (κ × ι → C) where
  functor := uncurry κ ι
  inverse := curry κ ι
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp only [Iso.refl_hom]
    erw [Category.id_comp, Category.comp_id]
    rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp only [Iso.refl_hom]
    erw [Category.id_comp, Category.comp_id]
    rfl)
  functor_unitIso_comp := by
    intro X
    funext i
    change 𝟙 (X i.1 i.2) ≫ 𝟙 (X i.1 i.2) = 𝟙 (X i.1 i.2)
    exact Category.id_comp _
instance instIsEquivalenceForallForallForallProdUncurry : (uncurry (C:=C) κ ι).IsEquivalence := (curryEquiv κ ι).isEquivalence_functor
end StageProductColimit
namespace IntervalBar.Diagram
open StageProductColimit MonoidalCategory

variable {C D : Type} [Groupoid.{0} C] [Groupoid.{0} D]
    [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
noncomputable def eval₂ (m n:ℕ) : Diagram (Diagram C (Fin (n+1))) (Fin (m+1)) ⥤
    (Fin m × Fin n → C) := eval m ⋙ powerMap (Fin m) (eval n) ⋙ uncurry (Fin m) (Fin n)
noncomputable instance instIsEquivalenceFinHAddNatOfNatForallProdEval₂ (m n:ℕ) : (eval₂ (C:=C) m n).IsEquivalence := by
  dsimp [eval₂]; infer_instance
end IntervalBar.Diagram

end

open _root_.CategoryTheory Limits

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageTripleHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ConnectedProduct.connected_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory
namespace IntervalBar.Diagram
variable {C D : Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
noncomputable instance map₂Monoidal (F : C ⥤ D) [F.Braided] (m n : ℕ) :
    (map (I:=Fin (m+1)) (map (I:=Fin (n+1)) F)).Monoidal := by
  letI : (map (I:=Fin (n+1)) F).Braided := mapBraided F
  exact mapMonoidal _
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
@[simp] lemma map₂_η_app (F : C ⥤ D) [F.Braided] (m p:ℕ)
    (i j:Fin (m+1)) (hij:i≤j) (v w:Fin (p+1)) (hvw:v≤w) :
    ((Functor.OplaxMonoidal.η (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) F))).app i j hij).app v w hvw =
      Functor.OplaxMonoidal.η F := by
  exact (congrArg (fun f => f.app v w hvw) (map_η_app (map (I:=Fin (p+1)) F) i j hij)).trans
    (map_η_app F v w hvw)
@[simp] lemma map₂_μ_app (F : C ⥤ D) [F.Braided] (m p:ℕ)
    (A B : Diagram (Diagram C (Fin (p+1))) (Fin (m+1)))
    (i j:Fin (m+1)) (hij:i≤j) (v w:Fin (p+1)) (hvw:v≤w) :
    ((Functor.LaxMonoidal.μ (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) F)) A B).app i j hij).app v w hvw =
      Functor.LaxMonoidal.μ F ((A.obj i j hij).obj v w hvw) ((B.obj i j hij).obj v w hvw) := rfl
end IntervalBar.Diagram

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TripleComposition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory MonoidalCategory Simplicial Opposite
namespace BarFinitePower

section Swap
variable {C : Type} [Category.{0} C] (κ ι : Type)
def swap : (κ → ι → C) ⥤ (ι → κ → C) where
  obj X i k := X k i
  map f i k := f k i
noncomputable def swapEquiv : (κ → ι → C) ≌ (ι → κ → C) where
  functor := swap κ ι
  inverse := swap ι κ
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp only [Iso.refl_hom]; erw [Category.comp_id, Category.id_comp]; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp only [Iso.refl_hom]; erw [Category.comp_id, Category.id_comp]; rfl)
  functor_unitIso_comp := by
    intro X
    funext i k
    exact Category.id_comp (𝟙 (X k i))
instance instIsEquivalenceForallForallSwap : (swap (C:=C) κ ι).IsEquivalence := (swapEquiv κ ι).isEquivalence_functor
end Swap
variable {C : Type} (κ : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
open IntervalBar IntervalBar.Diagram StageProductColimit
noncomputable def project (k:κ) : (κ → C) ⥤ C := Pi.eval (fun _ : κ => C) k
noncomputable instance instBraidedForallProject (k:κ) : (project (C:=C) κ k).Braided := inferInstanceAs ((Pi.eval (fun _ : κ => C) k).Braided)
end BarFinitePower

end

open _root_.CategoryTheory Simplicial Opposite
namespace BarFinitePower

variable (κ : Type)
def power : SSet ⥤ SSet where
  obj X := {
    obj p := κ → X.obj p
    map f := ↾fun x k => X.map f (x k)
    map_id p := by ext x k; exact congrArg (fun f => f (x k)) (X.map_id p)
    map_comp f g := by ext x k; exact congrArg (fun f => f (x k)) (X.map_comp f g) }
  map f := {
    app p := ↾fun x k => f.app p (x k)
    naturality _ _ g := by ext x k; exact congrArg (fun f => f (x k)) (f.naturality g) }
  map_id _ := rfl
  map_comp _ _ := rfl
noncomputable def lift {X Y : SSet} (f : κ → (X ⟶ Y)) : X ⟶ (power κ).obj Y where
  app p := ↾fun x k => (f k).app p x
  naturality _ _ g := by
    apply ConcreteCategory.hom_ext; intro x; funext k
    exact congrArg (fun f => f x) ((f k).naturality g)
variable {C : Type} [Category.{0} C]
noncomputable def nervePiIso : nerve (κ → C) ≅ (power κ).obj (nerve C) where
  hom := lift κ (fun k => nerveMap (Pi.eval (fun _ : κ => C) k))
  inv := {
    app _ := ↾fun X => Functor.pi' X
    naturality _ _ _ := by ext X; rfl }
  hom_inv_id := by ext p X; rfl
  inv_hom_id := by ext p X; rfl
lemma lift_nerve {D : Type} [Category.{0} D] (F : κ → (D ⥤ C)) :
    lift κ (fun k => nerveMap (F k)) = nerveMap (Functor.pi' F) ≫ (nervePiIso κ).hom := rfl
lemma lift_nerve_homology_isIso {D : Type} [Category.{0} D] (F : κ → (D ⥤ C))
    [(Functor.pi' F).IsEquivalence] (n:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k => nerveMap (F k))) DiagonalResolution.Z n) := by
  rw [lift_nerve,SSet.homologyMap_comp]
  infer_instance
end BarFinitePower

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_FiberAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory Limits MonoidalCategory
namespace BarFiberProduct

universe homSource homTarget
variable {A C D:Type} [Category.{homSource} A] [Category.{homTarget} C]
  [Category.{homTarget} D]
  [MonoidalCategory A] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory A] [BraidedCategory C] [BraidedCategory D]
noncomputable instance prodFunctorBraided (F:A⥤C) (G:A⥤D) [F.Braided] [G.Braided] :
    (F.prod' G).Braided where
  braided X Y := by
    apply CategoryTheory.Prod.hom_ext
    · simp only [CategoryTheory.prod_comp_fst,Functor.prod'_μ_fst]
      change Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
        (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X
      exact Functor.Braided.braided (F:=F) X Y
    · simp only [CategoryTheory.prod_comp_snd,Functor.prod'_μ_snd]
      change Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
        (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X
      exact Functor.Braided.braided (F:=G) X Y
end BarFiberProduct

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ProductNatural
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂ SimplicialObject Simplicial Opposite AlgebraicTopology
namespace ProductChains
open FreeChains

variable {X Y X' Y':SSet}
def map (f:X⟶X') (g:Y⟶Y') : product X Y ⟶ product X' Y' where
  app d := ↾fun z => (f.app (op d.unop.1) z.1,g.app (op d.unop.2) z.2)
  naturality _ _ h := by ext z; exact Prod.ext (congrArg (fun k => k z.1) (f.naturality h.unop.1.op)) (congrArg (fun k => k z.2) (g.naturality h.unop.2.op))
noncomputable def chainMap (f:X⟶X') : complex X ⟶ complex X' :=
  (alternatingFaceMapComplex A).map (Functor.whiskerRight f (ModuleCat.free ℤ))
noncomputable def twoFreeMap (f:X⟶X') (g:Y⟶Y') : twoFree X Y ⟶ twoFree X' Y' :=
  (alternatingFaceMapComplex (ChainComplex A ℕ)).map
    (Functor.whiskerRight (Functor.curry.map
      (Functor.whiskerLeft (CategoryTheory.prodOpEquiv SimplexCategory (D:=SimplexCategory)).inverse
        (Functor.whiskerRight (map f g) (ModuleCat.free ℤ)))) (alternatingFaceMapComplex A))
@[reassoc] lemma free_natural (f:X⟶X') (g:Y⟶Y') :
    EilenbergZilber.twoMap (map f g) ≫ (freeIso X' Y').hom =
      (freeIso X Y).hom ≫ twoFreeMap f g := by
  apply HomologicalComplex.Hom.ext; funext p
  apply HomologicalComplex.Hom.ext; funext q
  exact (FreeChains.naturalIso.hom.naturality ((map f g).app (op (SimplexCategory.mk p,SimplexCategory.mk q))))
noncomputable def tensorBiMap (f:X⟶X') (g:Y⟶Y') :
    TensorProductHomology.bicomplex (complex X) (complex Y) ⟶
      TensorProductHomology.bicomplex (complex X') (complex Y') :=
  (((curriedTensor A).mapBifunctorHomologicalComplex c c).map (chainMap f)).app (complex Y) ≫
    (((curriedTensor A).mapBifunctorHomologicalComplex c c).obj (complex X')).map (chainMap g)
@[reassoc] lemma tensor_natural (f:X⟶X') (g:Y⟶Y') :
    tensorBiMap f g ≫ (tensorIso X' Y').hom = (tensorIso X Y).hom ≫ twoFreeMap f g := by
  apply HomologicalComplex.Hom.ext; funext p
  apply HomologicalComplex.Hom.ext; funext q
  simp only [tensorBiMap,tensorIso,rowIso,twoFreeMap,HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  change (((ModuleCat.free ℤ).map (f.app (op ⦋p⦌))) ▷ ((ModuleCat.free ℤ).obj (Y.obj (op ⦋q⦌))) ≫
    ((ModuleCat.free ℤ).obj (X'.obj (op ⦋p⦌))) ◁ ((ModuleCat.free ℤ).map (g.app (op ⦋q⦌)))) ≫
      Functor.LaxMonoidal.μ (ModuleCat.free ℤ) _ _ =
    Functor.LaxMonoidal.μ (ModuleCat.free ℤ) _ _ ≫
      (ModuleCat.free ℤ).map (f.app (op ⦋p⦌) ⊗ₘ g.app (op ⦋q⦌))
  rw [←MonoidalCategory.tensorHom_def]
  exact Functor.LaxMonoidal.μ_natural (ModuleCat.free ℤ) _ _
noncomputable def homologyIsoN (X Y:SSet) (n:ℕ) :
    (X⊗Y).homology Z n ≅ ((complex X⊗complex Y).homology n) :=
  EilenbergZilber.homologyIsoN (product X Y) n ≪≫
      (homologyFunctor A c n).mapIso (total.mapIso (freeIso X Y ≪≫ (tensorIso X Y).symm) c)
@[reassoc] lemma homology_natural (f:X⟶X') (g:Y⟶Y') (n:ℕ) :
    SSet.homologyMap (f⊗ₘg) Z n ≫ (homologyIsoN X' Y' n).hom =
      (homologyIsoN X Y n).hom ≫ homologyMap (chainMap f⊗ₘchainMap g) n := by
  have ht : EilenbergZilber.twoMap (map f g) ≫
      (freeIso X' Y' ≪≫ (tensorIso X' Y').symm).hom =
    (freeIso X Y ≪≫ (tensorIso X Y).symm).hom ≫ tensorBiMap f g := by
    simp only [Iso.trans_hom,Iso.symm_hom]
    rw [←Category.assoc,free_natural,Category.assoc]
    apply (cancel_mono (tensorIso X' Y').hom).mp
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rw [tensor_natural]
    simp
  have hh := EilenbergZilber.homology_natural (map f g) n
  have ht' := congrArg (fun φ => homologyMap (total.map φ c) n) ht
  simp only [total.map_comp,homologyMap_comp] at ht'
  simp only [homologyIsoN]

  change homologyMap (EilenbergZilber.diagonalMap (map f g)) n ≫
      (EilenbergZilber.homologyIsoN (product X' Y') n).hom ≫
        homologyMap (total.map (freeIso X' Y' ≪≫ (tensorIso X' Y').symm).hom c) n =
    (EilenbergZilber.homologyIsoN (product X Y) n).hom ≫
      homologyMap (total.map (freeIso X Y ≪≫ (tensorIso X Y).symm).hom c) n ≫
        homologyMap (total.map (tensorBiMap f g) c) n
  rw [reassoc_of% hh,ht']
end ProductChains

end

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace TensorCoefficient

variable {R:Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

lemma flatPresentation (A:ModuleCat.{0} R) :
    ∃S:ShortComplex (ModuleCat.{0} R),S.X₃=A ∧ S.ShortExact ∧
      Module.Flat R S.X₁ ∧ Module.Flat R S.X₂ := by
  let φ : (A→₀R) →ₗ[R] A := Finsupp.linearCombination R (fun x:A => x)
  have hφ : Function.Surjective φ := by
    intro x; exact ⟨Finsupp.single x 1,by simp [φ]⟩
  let B : ModuleCat R := ModuleCat.of R (A→₀R)
  let C : ModuleCat R := ModuleCat.of R φ.ker
  let i : C ⟶ B := ModuleCat.ofHom φ.ker.subtype
  let p : B ⟶ A := ModuleCat.ofHom φ
  have hi : Mono i := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have hp : Epi p := (ModuleCat.epi_iff_surjective _).mpr hφ
  have hz : i≫p=0 := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; exact x.property
  let S : ShortComplex (ModuleCat R) := ShortComplex.mk i p hz
  have he : S.ShortExact := {
    mono_f := hi
    epi_g := hp
    exact := (S.moduleCat_exact_iff).mpr (by intro x hx; exact ⟨⟨x,hx⟩,rfl⟩) }
  exact ⟨S,rfl,he,inferInstance,inferInstance⟩
variable (K:ChainComplex (ModuleCat.{0} R) ℕ)
omit [IsDomain R] [IsPrincipalIdealRing R] in
lemma flat_isZero (A:ModuleCat.{0} R) [Module.Flat R A] (n:ℕ)
    (h:IsZero (K.homology n)) : IsZero ((homologyFunctor K n).obj A) := by
  exact IsZero.of_iso (Functor.map_isZero (tensorRight A) h)
    ((K.sc n).mapHomologyIso (tensorRight A))
variable [∀n,Module.Flat R (K.X n)]
lemma arbitrary_zero_succ (A:ModuleCat.{0} R) (n:ℕ)
    (h0:IsZero (K.homology n)) (h1:IsZero (K.homology (n+1))) :
    IsZero ((homologyFunctor K (n+1)).obj A) := by
  obtain ⟨S,hA,hS,h1f,h2f⟩ := flatPresentation A
  have := h1f; have := h2f
  rw [←hA]
  exact ((shortExact K hS).homology_exact₃ (n+1) n rfl).isZero_X₂
    ((flat_isZero K S.X₂ (n+1) h1).eq_of_src _ _)
    ((flat_isZero K S.X₁ n h0).eq_of_tgt _ _)
lemma arbitrary_zero_zero (A:ModuleCat.{0} R) (h:IsZero (K.homology 0)) :
    IsZero ((homologyFunctor K 0).obj A) := by
  obtain ⟨S,hA,hS,h1f,h2f⟩ := flatPresentation A
  have := h1f; have := h2f
  rw [←hA]
  have hs := shortExact K hS
  have := hs.epi_g
  have homology_epi : Epi (homologyMap (S.map (functor K)).g 0) :=
    epi_homologyMap_of_epi_of_not_rel _ 0 (by intro _; simp [ComplexShape.down_Rel])
  exact @IsZero.of_epi _ _ _ _ _ (homologyMap (S.map (functor K)).g 0)
    homology_epi (flat_isZero K S.X₂ 0 h)
end TensorCoefficient

end

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace TensorProductHomology

variable {R:Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
lemma arbitrary_isZero (K L:ChainComplex (ModuleCat.{0} R) ℕ)
    [∀n,Module.Flat R (K.X n)] (a b n:ℕ) (hn:n<a+b)
    (hK:∀i,i<a→IsZero (K.homology i)) (hL:∀i,i<b→IsZero (L.homology i)) :
    IsZero (((bicomplex K L).total c).homology n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply TotalFiniteness.subsingleton
  intro p q hpq
  apply ModuleCat.isZero_iff_subsingleton.mp
  apply IsZero.of_iso _ ((homologyFunctor _ c p).mapIso (rowIso K L q))
  by_cases hq:q<b
  · exact Functor.map_isZero (TensorCoefficient.homologyFunctor K p) (hL q hq)
  · cases p with
    | zero => exact TensorCoefficient.arbitrary_zero_zero K _ (hK 0 (by omega))
    | succ p => exact TensorCoefficient.arbitrary_zero_succ K _ p (hK p (by omega)) (hK (p+1) (by omega))
end TensorProductHomology

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TensorJoint
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace ChainTensor
open FreeChains

variable (S T:ShortComplex (ChainComplex A ℕ)) (s:S.Splitting) (t:T.Splitting)
lemma splitting_tensor_identity :
    (s.r⊗ₘt.r) ≫ (S.f⊗ₘT.f) +
      (𝟙 S.X₂⊗ₘT.g) ≫ ((s.r≫S.f)⊗ₘt.s) +
      (S.g⊗ₘ𝟙 T.X₂) ≫ (s.s⊗ₘ𝟙 T.X₂) = 𝟙 (S.X₂⊗T.X₂) := by
  have tensor_add {sourceLeft targetLeft sourceRight targetRight : ChainComplex A ℕ}
      (left : sourceLeft ⟶ targetLeft) (right₁ right₂ : sourceRight ⟶ targetRight) :
      left ⊗ₘ (right₁ + right₂) = left ⊗ₘ right₁ + left ⊗ₘ right₂ := by
    apply HomologicalComplex.Hom.ext
    funext degree
    apply mapBifunctor.hom_ext
    intro leftDegree rightDegree totalDegree
    change ιMapBifunctor sourceLeft sourceRight (curriedTensor A) c leftDegree rightDegree degree totalDegree ≫
        (mapBifunctorMap left (right₁ + right₂) (curriedTensor A) c).f degree =
      ιMapBifunctor sourceLeft sourceRight (curriedTensor A) c leftDegree rightDegree degree totalDegree ≫
        ((mapBifunctorMap left right₁ (curriedTensor A) c).f degree +
          (mapBifunctorMap left right₂ (curriedTensor A) c).f degree)
    simp [Preadditive.comp_add]
  have add_tensor {sourceLeft targetLeft sourceRight targetRight : ChainComplex A ℕ}
      (left₁ left₂ : sourceLeft ⟶ targetLeft) (right : sourceRight ⟶ targetRight) :
      (left₁ + left₂) ⊗ₘ right = left₁ ⊗ₘ right + left₂ ⊗ₘ right := by
    apply HomologicalComplex.Hom.ext
    funext degree
    apply mapBifunctor.hom_ext
    intro leftDegree rightDegree totalDegree
    change ιMapBifunctor sourceLeft sourceRight (curriedTensor A) c leftDegree rightDegree degree totalDegree ≫
        (mapBifunctorMap (left₁ + left₂) right (curriedTensor A) c).f degree =
      ιMapBifunctor sourceLeft sourceRight (curriedTensor A) c leftDegree rightDegree degree totalDegree ≫
        ((mapBifunctorMap left₁ right (curriedTensor A) c).f degree +
          (mapBifunctorMap left₂ right (curriedTensor A) c).f degree)
    simp [Preadditive.comp_add]
  simp only [tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
  rw [←tensor_add,t.id,←add_tensor,s.id,id_tensorHom_id]
include s t in
lemma homology_joint_kernel (n:ℕ) (hz:IsZero ((S.X₁⊗T.X₁).homology n))
    (x:(S.X₂⊗T.X₂).homology n)
    (h1:homologyMap (𝟙 S.X₂⊗ₘT.g) n x=0)
    (h2:homologyMap (S.g⊗ₘ𝟙 T.X₂) n x=0) : x=0 := by
  have hm : homologyMap ((s.r⊗ₘt.r) ≫ (S.f⊗ₘT.f)) n=0 := by
    rw [homologyMap_comp,hz.eq_of_src (homologyMap (S.f⊗ₘT.f) n) 0,comp_zero]
  have hid := congrArg (fun f => homologyMap f n) (splitting_tensor_identity S T s t)
  simp only [homologyMap_add] at hid
  rw [hm,homologyMap_comp,homologyMap_comp,homologyMap_id] at hid
  have hh := congrArg (fun f => f x) hid
  change 0 + homologyMap ((s.r≫S.f)⊗ₘt.s) n (homologyMap (𝟙 S.X₂⊗ₘT.g) n x) +
    homologyMap (s.s⊗ₘ𝟙 T.X₂) n (homologyMap (S.g⊗ₘ𝟙 T.X₂) n x) = x at hh
  simpa only [h1,h2,map_zero,add_zero] using hh.symm
end ChainTensor

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ConstantSplit
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.NerveHomotopy.homologyMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ProductChains
open FreeChains

variable {X Y W:SSet}
@[simp] lemma chainMap_id (X:SSet) : chainMap (𝟙 X)=𝟙 (complex X) := by
  unfold chainMap; simp [complex]; rfl
@[simp] lemma chainMap_comp (f:X⟶Y) (g:Y⟶W) : chainMap (f≫g)=chainMap f≫chainMap g := by
  unfold chainMap; simp; rfl
lemma chainMap_aug (f:X⟶Y) : chainMap f ≫ SimplicialAugment.aug Y = SimplicialAugment.aug X := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f,SimplicialAugment.aug_f_zero]
  apply ModuleCat.free_hom_ext; intro x
  change SimplicialAugment.aug0 Y ((ModuleCat.free ℤ).map (f.app (op ⦋0⦌)) (ModuleCat.freeMk x)) = SimplicialAugment.aug0 X (ModuleCat.freeMk x)
  simp only [ModuleCat.free_map_apply]
  rw [SimplicialAugment.aug0_mk,SimplicialAugment.aug0_mk]
end ProductChains
namespace ConstantSplit
open FreeChains ProductChains

abbrev one := ConnectedProduct.one
noncomputable def aug (X:SSet) : complex X ⟶ complex one := chainMap (SSet.const (Y:=one) PUnit.unit)
noncomputable def sec (X:SSet) (x:X.obj (op ⦋0⦌)) : complex one ⟶ complex X := chainMap (SSet.const x)
lemma section_aug (X:SSet) (x:X.obj (op ⦋0⦌)) : sec X x ≫ aug X = 𝟙 (complex one) := by
  rw [sec,aug,←chainMap_comp]
  have he : (SSet.const (X:=one) x) ≫ SSet.const (Y:=one) PUnit.unit = 𝟙 one := by ext n z; rfl
  rw [he,chainMap_id]
noncomputable def sc (X:SSet) : ShortComplex (ChainComplex A ℕ) :=
  ShortComplex.mk (kernel.ι (aug X)) (aug X) (kernel.condition _)
noncomputable def splitting (X:SSet) (x:X.obj (op ⦋0⦌)) : (sc X).Splitting :=
  ShortComplex.Splitting.ofExactOfSection (sc X)
    ((sc X).exact_of_f_is_kernel (kernelIsKernel (aug X))) (sec X x) (section_aug X x)
      (by dsimp [sc]; infer_instance)
instance aug_iso (X:SSet) [X.IsConnected] : IsIso (homologyMap (aug X) 0) := by
  have oneConnected : one.IsConnected := {
    allEq := by
      intro first second
      obtain ⟨first,rfl⟩ := SSet.π₀.mk_surjective first
      obtain ⟨second,rfl⟩ := SSet.π₀.mk_surjective second
      exact congrArg SSet.π₀.mk (show first=second from PUnit.ext first second)
    nonempty := ⟨PUnit.unit⟩ }
  have he : homologyMap (aug X) 0 ≫ homologyMap (SimplicialAugment.aug one) 0 =
      homologyMap (SimplicialAugment.aug X) 0 := by
    rw [←homologyMap_comp]; exact congrArg (fun f => homologyMap f 0) (chainMap_aug _)
  have compositeIso : IsIso (homologyMap (aug X) 0 ≫ homologyMap (SimplicialAugment.aug one) 0) := by
    rw [he]; infer_instance
  exact (isIso_comp_right_iff _ (homologyMap (SimplicialAugment.aug one) 0)).mp inferInstance
lemma red_zero (X:SSet) [X.IsConnected] (a:ℕ)
    (hv : ∀ i, 0 < i → i < a → IsZero ((complex X).homology i)) :
    ∀ i, i < a → IsZero (((sc X).X₁).homology i) := by
  intro i hi
  let s := splitting X (ConnectedProduct.point X)
  have hz : homologyMap (sc X).f i=0 := by
    by_cases h:i=0
    · subst i
      change homologyMap (kernel.ι (aug X)) 0 = 0
      apply (cancel_mono (homologyMap (aug X) 0)).mp
      rw [←homologyMap_comp,kernel.condition,homologyMap_zero,zero_comp]
    · exact (hv i (by omega) hi).eq_of_tgt _ _
  apply (IsZero.iff_id_eq_zero _).mpr
  have hh := congrArg (fun f => homologyMap f i) s.f_r
  rw [homologyMap_comp,homologyMap_id,hz,zero_comp] at hh
  exact hh.symm
instance red_flat (X:SSet) (i:ℕ) : Module.Flat ℤ (((sc X).X₁).X i) := by
  have hi : Function.Injective ((kernel.ι (aug X)).f i) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have reducedTorsionFree : Module.IsTorsionFree ℤ (((sc X).X₁).X i) :=
    hi.moduleIsTorsionFree _ (fun r x => ((kernel.ι (aug X)).f i).hom.map_smul r x)
  infer_instance
end ConstantSplit

end

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConnectedProduct
open FreeChains ProductChains

variable (X Y:SSet) [X.IsConnected] [Y.IsConnected]
lemma projection_kernel_aux (a b n:ℕ) (hab:n<a+b)
    (hX:∀ i, 0 < i → i < a → IsZero ((complex X).homology i))
    (hY:∀ i, 0 < i → i < b → IsZero ((complex Y).homology i))
    (x:((X⊗Y).homology Z n : A)) (hx:projection X Y n x=0) : x=0 := by
  have hf : SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n x=0 := by
    have h := congrArg (fun z => (biprod.fst : X.homology Z n ⊞ Y.homology Z n ⟶ X.homology Z n) z) hx
    simp only [map_zero] at h
    change (projection X Y n ≫ biprod.fst) x=0 at h
    simpa only [projection,biprod.lift_fst] using h
  have hg : SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n x=0 := by
    have h := congrArg (fun z => (biprod.snd : X.homology Z n ⊞ Y.homology Z n ⟶ Y.homology Z n) z) hx
    simp only [map_zero] at h
    change (projection X Y n ≫ biprod.snd) x=0 at h
    simpa only [projection,biprod.lift_snd] using h
  let e := homologyIsoN X Y n
  have h1 : homologyMap (𝟙 (complex X)⊗ₘConstantSplit.aug Y) n (e.hom x)=0 := by
    have hn := homology_natural (𝟙 X) (SSet.const (X:=Y) (Y:=one) PUnit.unit) n
    rw [chainMap_id] at hn
    have he : (𝟙 X)⊗ₘ(SSet.const (X:=Y) (Y:=one) PUnit.unit) =
        CartesianMonoidalCategory.fst X Y ≫ pairLeft X one PUnit.unit := by ext d z <;> rfl
    rw [he,SSet.homologyMap_comp] at hn
    have hh := congrArg (fun f => f x) hn
    change (homologyIsoN X one n).hom
      (SSet.homologyMap (pairLeft X one PUnit.unit) Z n
        (SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n x)) = _ at hh
    simpa only [hf,map_zero,ConstantSplit.aug,ConstantSplit.one,e,ModuleCat.comp_apply] using hh.symm
  have h2 : homologyMap (ConstantSplit.aug X⊗ₘ𝟙 (complex Y)) n (e.hom x)=0 := by
    have hn := homology_natural (SSet.const (X:=X) (Y:=one) PUnit.unit) (𝟙 Y) n
    rw [chainMap_id] at hn
    have he : (SSet.const (X:=X) (Y:=one) PUnit.unit)⊗ₘ(𝟙 Y) =
        CartesianMonoidalCategory.snd X Y ≫ pairRight one Y PUnit.unit := by ext d z <;> rfl
    rw [he,SSet.homologyMap_comp] at hn
    have hh := congrArg (fun f => f x) hn
    change (homologyIsoN one Y n).hom
      (SSet.homologyMap (pairRight one Y PUnit.unit) Z n
        (SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n x)) = _ at hh
    simpa only [hg,map_zero,ConstantSplit.aug,ConstantSplit.one,e,ModuleCat.comp_apply] using hh.symm
  have hz : IsZero ((((ConstantSplit.sc X).X₁)⊗((ConstantSplit.sc Y).X₁)).homology n) :=
    TensorProductHomology.arbitrary_isZero _ _ a b n hab
      (ConstantSplit.red_zero X a hX) (ConstantSplit.red_zero Y b hY)
  have hh := ChainTensor.homology_joint_kernel (ConstantSplit.sc X) (ConstantSplit.sc Y)
    (ConstantSplit.splitting X (point X)) (ConstantSplit.splitting Y (point Y)) n hz (e.hom x) h1 h2
  exact e.toLinearEquiv.injective (hh.trans (map_zero e.toLinearEquiv).symm)

lemma projection_isIso_arbitrary (a b n:ℕ) (hn:0<n) (hab:n<a+b)
    (hX:∀ i, 0 < i → i < a → IsZero ((complex X).homology i))
    (hY:∀ i, 0 < i → i < b → IsZero ((complex Y).homology i)) :
    IsIso (projection X Y n) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    apply sub_eq_zero.mp
    apply projection_kernel_aux X Y a b n hab hX hY (x-y)
    rw [map_sub,h,sub_self]
  · intro z
    refine ⟨inclusion X Y (point X) (point Y) n z,?_⟩
    exact congrArg (fun f => f z) (inclusion_projection X Y (point X) (point Y) n (by omega))
end ConnectedProduct

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_PowerDiagonal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Simplicial Opposite
namespace BarFinitePower
open SimplicialDiagonal

variable (κ : Type) {X Y : SimplexCategoryᵒᵖ ⥤ SSet}
noncomputable def liftRows (f : κ → (X ⟶ Y)) : X ⟶ Y ⋙ power κ where
  app p := lift κ (fun k => (f k).app p)
  naturality p q g := by
    apply NatTrans.ext; funext r
    apply ConcreteCategory.hom_ext; intro x; funext k
    exact congrArg (fun f => (f.app r) x) ((f k).naturality g)
lemma liftDiagonal (f : κ → (X ⟶ Y)) :
    lift κ (fun k => diagonal.map (f k)) = diagonal.map (liftRows κ f) := rfl
end BarFinitePower

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageCoordinateMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory MonoidalCategory
namespace BarFinitePower
variable (κ:Type) (X:SSet)
def evaluate (k:κ) : (power κ).obj X ⟶ X where
  app _ := ↾fun x => x k
  naturality _ _ _ := rfl
end BarFinitePower

end

section
open _root_.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace BarFinitePower

variable (X:SSet)
noncomputable def reindexIso {κ ι:Type} (e:κ≃ι) : (power κ).obj X ≅ (power ι).obj X where
  hom := { app _ := ↾fun x i => x (e.symm i)
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun x k => x (e k)
           naturality _ _ _ := rfl }
  hom_inv_id := by apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext k; exact congrArg x (e.symm_apply_apply k)
  inv_hom_id := by apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext i; exact congrArg x (e.apply_symm_apply i)
noncomputable def finSuccIso (s:ℕ) : (power (Fin (s+1))).obj X ≅ X ⊗ (power (Fin s)).obj X where
  hom := { app _ := ↾fun x => (x 0,fun i => x i.succ)
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun x => Fin.cases x.1 x.2
           naturality _ _ _ := by
             apply ConcreteCategory.hom_ext; intro x; funext i
             cases i using Fin.cases <;> rfl }
  hom_inv_id := by
    apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext i
    cases i using Fin.cases <;> rfl
  inv_hom_id := by ext p x <;> rfl
noncomputable def finZeroIso : (power (Fin 0)).obj X ≅ ConnectedProduct.one where
  hom := { app _ := ↾fun _ => PUnit.unit
           naturality _ _ _ := rfl }
  inv :=
    { app _ := ↾fun _ => Fin.elim0
      naturality _ _ _ := by apply ConcreteCategory.hom_ext; intro x; funext i; exact i.elim0 }
  hom_inv_id := by apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext i; exact i.elim0
  inv_hom_id := by ext p x; rfl
lemma connected_of_iso {Y:SSet} (e:X≅Y) [Y.IsConnected] : X.IsConnected where
  allEq x y := by
    have he := congrArg (SSet.mapπ₀ e.inv) (Subsingleton.elim (SSet.mapπ₀ e.hom x) (SSet.mapπ₀ e.hom y))
    simpa only [←SSet.mapπ₀_comp_apply,Iso.hom_inv_id,SSet.mapπ₀_id_apply] using he
  nonempty := ⟨e.inv.app _ (Classical.arbitrary _)⟩
instance connected_one : ConnectedProduct.one.IsConnected where
  allEq x y := by
    obtain ⟨x,rfl⟩ := SSet.π₀.mk_surjective x
    obtain ⟨y,rfl⟩ := SSet.π₀.mk_surjective y
    exact congrArg SSet.π₀.mk (show x=y from PUnit.ext x y)
  nonempty := ⟨PUnit.unit⟩
lemma fin_connected [X.IsConnected] (s:ℕ) : ((power (Fin s)).obj X).IsConnected := by
  induction s with
  | zero => exact connected_of_iso _ (finZeroIso X)
  | succ s ih =>
    have connectedPower := ih
    exact connected_of_iso _ (finSuccIso X s)
noncomputable instance connected (κ:Type) [Finite κ] [X.IsConnected] : ((power κ).obj X).IsConnected := by
  let finiteCoordinates := Fintype.ofFinite κ
  have connectedPower := fin_connected X (Fintype.card κ)
  exact connected_of_iso _ (reindexIso X (Fintype.equivFin κ))
lemma homology_isZero_complex (q:ℕ) (h:IsZero (X.homology DiagonalResolution.Z q)) :
    IsZero ((FreeChains.complex X).homology q) :=
  IsZero.of_iso h ((HomologicalComplex.homologyFunctor FreeChains.A FreeChains.c q).mapIso (FreeChains.complexIso X)).symm
end BarFinitePower

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FinitePowerLow
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace BarFinitePower

section
open FreeChains

attribute [local instance 1200] Pi.module Prod.instModule
variable (κ:Type) (X:SSet) (j:ℕ)
noncomputable def coordinates : ((power κ).obj X).homology Z j ⟶ ModuleCat.of ℤ (κ → (X.homology Z j : A)) :=
  ModuleCat.ofHom (LinearMap.pi (fun k => (SSet.homologyMap (evaluate κ X k) Z j).hom))
@[reassoc (attr := simp)] lemma coordinates_evaluate (k:κ) :
    coordinates κ X j ≫ ModuleCat.ofHom (LinearMap.proj k) = SSet.homologyMap (evaluate κ X k) Z j := rfl
lemma modulePi_hom_ext {κ:Type} {M B:A} {f g:B ⟶ ModuleCat.of ℤ (κ → M)}
    (h:∀i,f ≫ ModuleCat.ofHom (LinearMap.proj i)=g ≫ ModuleCat.ofHom (LinearMap.proj i)) : f=g := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext i
  exact congrArg (fun f => f x) (h i)
variable (M:A)
noncomputable def vectorSplit (s:ℕ) : (Fin (s+1) → M) ≃ₗ[ℤ] M × (Fin s → M) where
  toFun x := (x 0,fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by funext i; cases i using Fin.cases <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def coordinateSplit (s:ℕ) : ModuleCat.of ℤ (Fin (s+1) → M) ≅ M ⊞ ModuleCat.of ℤ (Fin s → M) :=
  (vectorSplit M s).toModuleIso ≪≫ (ModuleCat.biprodIsoProd M (ModuleCat.of ℤ (Fin s → M))).symm
@[reassoc (attr := simp)] lemma coordinateSplit_fst (s:ℕ) :
    (coordinateSplit M s).hom ≫ biprod.fst = ModuleCat.ofHom (LinearMap.proj (0:Fin (s+1))) := by
  simp only [coordinateSplit,Iso.trans_hom,Iso.symm_hom,Category.assoc,ModuleCat.biprodIsoProd_inv_comp_fst]
  rfl
@[reassoc (attr := simp)] lemma coordinateSplit_snd_proj (s:ℕ) (i:Fin s) :
    (coordinateSplit M s).hom ≫ biprod.snd ≫ ModuleCat.ofHom (LinearMap.proj i) =
      ModuleCat.ofHom (LinearMap.proj i.succ) := by
  simp only [coordinateSplit,Iso.trans_hom,Iso.symm_hom,Category.assoc]
  have h := congrArg (fun f => f ≫ (ModuleCat.ofHom (LinearMap.proj i) : ModuleCat.of ℤ (Fin s→M) ⟶ M))
    (ModuleCat.biprodIsoProd_inv_comp_snd M (ModuleCat.of ℤ (Fin s→M)))
  simp only [Category.assoc] at h
  rw [h]
  rfl
lemma coordinates_fin_succ (s:ℕ) :
    coordinates (Fin (s+1)) X j ≫ (coordinateSplit (X.homology Z j) s).hom =
      SSet.homologyMap (finSuccIso X s).hom Z j ≫
        ConnectedProduct.projection X ((power (Fin s)).obj X) j ≫
          biprod.map (𝟙 _) (coordinates (Fin s) X j) := by
  apply biprod.hom_ext
  · simp only [Category.assoc,coordinateSplit_fst,coordinates_evaluate,biprod.map_fst,
      Category.comp_id,ConnectedProduct.projection,biprod.lift_fst,←SSet.homologyMap_comp]
    rfl
  · apply modulePi_hom_ext
    intro i
    simp only [Category.assoc,coordinateSplit_snd_proj,coordinates_evaluate,
      biprod.map_snd_assoc,ConnectedProduct.projection,biprod.lift_snd_assoc,←SSet.homologyMap_comp]
    rfl
end
open FreeChains

attribute [local instance 1200] Pi.module Prod.instModule
variable (X:SSet)
  [X.IsConnected]
noncomputable def coefficientReindex {κ ι:Type} (e:κ≃ι) (M:A) :
    ModuleCat.of ℤ (κ→M) ≅ ModuleCat.of ℤ (ι→M) :=
  (show (κ→M) ≃ₗ[ℤ] (ι→M) from {
    toFun f i := f (e.symm i)
    invFun f k := f (e k)
    left_inv f := by funext k; exact congrArg f (e.symm_apply_apply k)
    right_inv f := by funext i; exact congrArg f (e.apply_symm_apply i)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }).toModuleIso
omit [X.IsConnected] in
lemma coordinates_reindex {κ ι:Type} (e:κ≃ι) (j:ℕ) :
    coordinates κ X j ≫ (coefficientReindex e (X.homology Z j)).hom =
      SSet.homologyMap (reindexIso X e).hom Z j ≫ coordinates ι X j := by
  apply modulePi_hom_ext; intro i
  have he : (coefficientReindex e (X.homology Z j)).hom ≫ ModuleCat.ofHom (LinearMap.proj i)=
      ModuleCat.ofHom (LinearMap.proj (e.symm i)) := rfl
  rw [Category.assoc,he,coordinates_evaluate,Category.assoc,coordinates_evaluate,←SSet.homologyMap_comp]
  rfl
end BarFinitePower

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FinitePowerConnected
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace BarFinitePower
open FreeChains

attribute [local instance 1200] Pi.module Prod.instModule

def LowConnected (X:SSet) : Prop := ∀ j:ℕ, 0 < j → j < 3 → IsZero (X.homology Z j)
namespace LowConnected
variable {X Y:SSet}
lemma of_iso (e:X≅Y) (h:LowConnected Y) : LowConnected X :=
  fun j hj h3 => IsZero.of_iso (h j hj h3) ((SSet.homologyFunctor Z j).mapIso e)
lemma one : LowConnected ConnectedProduct.one := fun j hj _ =>
  ConnectedProduct.one_homology_zero j (by omega)
lemma projection_isIso [X.IsConnected] [Y.IsConnected] (hX:LowConnected X) (hY:LowConnected Y)
    (j:ℕ) (hj:0<j) (hj5:j≤5) : IsIso (ConnectedProduct.projection X Y j) := by
  apply ConnectedProduct.projection_isIso_arbitrary X Y 3 3 j hj (by omega)
  · intro i hi h3; exact homology_isZero_complex X i (hX i hi h3)
  · intro i hi h3; exact homology_isZero_complex Y i (hY i hi h3)
lemma tensor [X.IsConnected] [Y.IsConnected] (hX:LowConnected X) (hY:LowConnected Y) :
    LowConnected (X⊗Y) := by
  intro j hj h3
  have := projection_isIso hX hY j hj (by omega)
  exact IsZero.of_iso ((biprod_isZero_iff _ _).mpr ⟨hX j hj h3,hY j hj h3⟩)
    (asIso (ConnectedProduct.projection X Y j))
lemma fin [X.IsConnected] (hX:LowConnected X) (s:ℕ) : LowConnected ((power (Fin s)).obj X) := by
  induction s with
  | zero => exact of_iso (finZeroIso X) one
  | succ s ih => exact of_iso (finSuccIso X s) (tensor hX ih)
end LowConnected
variable (X:SSet) [X.IsConnected] (hX:LowConnected X)
include hX in
lemma coordinates_fin_isIso_connected (s j:ℕ) (hj:0<j) (hj5:j≤5) :
    IsIso (coordinates (Fin s) X j) := by
  induction s with
  | zero =>
    have hz : IsZero (((power (Fin 0)).obj X).homology Z j) :=
      IsZero.of_iso (ConnectedProduct.one_homology_zero j (by omega))
        ((SSet.homologyFunctor Z j).mapIso (finZeroIso X))
    exact hz.isIso (ModuleCat.isZero_iff_subsingleton.mpr inferInstance) _
  | succ s ih =>
    have := ih
    have := LowConnected.projection_isIso hX (hX.fin s) j hj hj5
    have : IsIso (biprod.map (𝟙 (X.homology Z j)) (coordinates (Fin s) X j)) := by
      change IsIso (biprod.mapIso (Iso.refl _) (asIso (coordinates (Fin s) X j))).hom
      infer_instance
    have : IsIso (coordinates (Fin (s+1)) X j ≫ (coordinateSplit (X.homology Z j) s).hom) := by
      rw [coordinates_fin_succ]; infer_instance
    exact (isIso_comp_right_iff _ (coordinateSplit (X.homology Z j) s).hom).mp inferInstance
include hX in
lemma coordinates_isIso_connected (κ:Type) [Finite κ] (j:ℕ) (hj:0<j) (hj5:j≤5) :
    IsIso (coordinates κ X j) := by
  let := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  have := coordinates_fin_isIso_connected X hX (Fintype.card κ) j hj hj5
  have : IsIso (coordinates κ X j ≫ (coefficientReindex e (X.homology Z j)).hom) := by
    rw [coordinates_reindex]; infer_instance
  exact (isIso_comp_right_iff _ (coefficientReindex e (X.homology Z j)).hom).mp inferInstance
end BarFinitePower

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FinitePowerGeneral
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory MonoidalCategory Simplicial Opposite
namespace BarFinitePower
open IntervalBar IntervalBar.Diagram StageProductColimit SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C] (κ:Type)
noncomputable def doubleProject (m n:ℕ) :
    Diagram (Diagram (κ→C) (Fin (n+1))) (Fin (m+1)) ⥤
    (κ→Diagram (Diagram C (Fin (n+1))) (Fin (m+1))) :=
  Functor.pi' (fun k => map (I:=Fin (m+1)) (map (I:=Fin (n+1)) (project κ k)))
lemma doubleProject_eval (m n:ℕ) :
    doubleProject (C:=C) κ m n ⋙ powerMap κ (eval₂ m n) = eval₂ m n ⋙ swap (Fin m × Fin n) κ := rfl
noncomputable instance instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject (m n:ℕ) : (doubleProject (C:=C) κ m n).IsEquivalence := by
  have : (doubleProject (C:=C) κ m n ⋙ powerMap κ (eval₂ m n)).IsEquivalence := by
    rw [doubleProject_eval]
    infer_instance
  exact Functor.isEquivalence_of_comp_right _ (powerMap κ (eval₂ m n))
lemma doubleDegree_homology_isIso (l p r:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k=>nerveMap (map (I:=Fin (l+1))
      (map (I:=Fin (p+1)) (project (C:=C) κ k))))) DiagonalResolution.Z r) := by
  have : (Functor.pi' (fun k=>map (I:=Fin (l+1))
      (map (I:=Fin (p+1)) (project (C:=C) κ k)))).IsEquivalence :=
    inferInstanceAs (doubleProject (C:=C) κ l p).IsEquivalence
  exact lift_nerve_homology_isIso κ (fun k=>map (I:=Fin (l+1))
    (map (I:=Fin (p+1)) (project (C:=C) κ k))) r
end BarFinitePower

end

open _root_.CategoryTheory MonoidalCategory Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ConnectedProduct.connected_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory MonoidalCategory
namespace RestrictedNerve

section

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
noncomputable abbrev inclusion := wideSubcategoryInclusion W
end

open IntervalBar IntervalBar.Diagram

end RestrictedNerve

end OAI
end


