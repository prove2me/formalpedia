-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:28:25.856635+00:00
-- url     : https://prove2.me/theorems/26bec32f-ebf7-444d-9e61-4a70a963900d
-- title:
--   Deg Unif
-- statement:
--   Definitions and structural lemmas for Deg Unif, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/DegUnif.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
section Unif
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)
namespace DegPre
variable (D : DegPre R)
def Oφ {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) :
    Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A p (toUnit T ≫ D.c χ)).left, (toUnit T ≫ D.c χ).left, p.left,
    (toUnit T ≫ η[D.P.A]).left]
def prBe (e : ℕ) : (Over.map (thick R I e)).obj (thickObj R I e D.P.A) ⟶ D.P.A :=
  Over.homMk (pullback.fst D.P.A.hom (thick R I e)) pullback.condition
end DegPre
def Oε : Fin 4 → ℤ := ![1, -1, -1, 1]
def Oinvε : Fin 4 → ℤ := ![-1, 1, 1, -1]
def fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ G :=
  Over.homMk (pullback.fst G.hom (thick R I e)) pullback.condition
def charGen {S : Scheme.{0}} (X : Type) [AddCommGroup X] (G : Over S) {Z : Scheme.{0}} (L : LB Z)
    (χ : X) : LB.Gen (LB.LinComb L (Y := (splitTorus S X ⊗ G).left) (K := PEmpty) PEmpty.elim
      PEmpty.elim) where
  s := fun _ => res (fun x _ => show (fst (splitTorus S X) G).left.base x ∈ (⊤ : TopologicalSpace.Opens _)
      from trivial) (pullU (fst (splitTorus S X) G).left ⊤ (charUnit S X χ))
structure GtCoord (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] where
  q : thickObj R I e G ⟶ thickObj R I e D.P.A
  q_hom : IsMonHom q
  q_flat : Flat q.left
  q_surj : Surjective q.left
  q_affine : IsAffineHom q.left
  i : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ thickObj R I e G
  i_hom : IsMonHom i
  isKernel : IsPullback i (toUnit _) q (η[thickObj R I e D.P.A])
  t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L
    (D.Oφ ((Over.map (thick R I e)).map q ≫ D.prBe I e) χ) Oinvε)
  t_gen : ∀ χ, (t χ).IsGen
  t_mul : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
        (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ')
          ((Over.map (thick R I e)).map q ≫ D.prBe I e))).left))
    (LB.mulGen D.P.L _ _ _ _ (t χ) (t χ'))
  t_unit : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.pullGen D.P.L _ _ (t χ) (eSec (thickObj R I e G))) (LB.oneGen D.P.L)
  t_weight : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.pullGen D.P.L _ _ (t χ)
      (lift (fst (splitTorus _ D.X) (thickObj R I e G) ≫ i) (snd _ _) ≫ μ[thickObj R I e G]).left)
    (LB.mulGen D.P.L _ _ _ _ (charGen D.X (thickObj R I e G) D.P.L χ)
      (LB.pullGen D.P.L _ _ (t χ) (snd (splitTorus _ D.X) (thickObj R I e G)).left))
namespace GtCoord
variable {I} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
abbrev pG (g : GtCoord I D e G) : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ D.P.A :=
  (Over.map (thick R I e)).map g.q ≫ D.prBe I e
end GtCoord
def GtCoordIsGt (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] : Prop :=
  Nonempty (GtCoord I D e G) ↔
    ∃ (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : E.B ≅ thickObj R I e D.P.A) (xe : D.X ≃+ E.X), IsMonHom β.hom ∧
      (∀ χ : D.X, ∃ w : LB.Iso (E.O (xe χ)).L (LB.LinComb D.P.L
          (fun k => ((Over.map (thick R I e)).map β.hom ≫ D.prBe I e).left ≫
            D.Oφ (𝟙 _) χ k) Oε), w.IsGen) ∧
      E.IsGt (thickObj R I e G)
end Unif
section UnifPre
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)
structure UnifPre (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] where
  smooth : Smooth G.hom
  separated : IsSeparated G.hom
  gen : (Over.pullback (jK R)).obj G ≅ A.A
  gen_hom : IsMonHom gen.hom
  LG : RigLB G
  cubG : CubicalStr G LG
  symG : LB.Gen (LB.LinComb LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])
  symG_gen : symG.IsGen
  symG_rig : LB.Gen.Corr LG.L _ _ _ _ (LB.pullGen LG.L _ _ symG (eSec G)) (LB.oneGen LG.L)
  ext : ∃ w : LB.Iso (A.L.pull gen.hom.left) (LG.L.pull (pullback.fst G.hom (jK R))), w.IsGen
  gt : ∀ e : ℕ, GtCoord I D.toPre e G
  gt_q : ∀ e : ℕ, thickMap R I e G ≫ (gt (e + 1)).pG.left = (gt e).pG.left
  gt_t : ∀ (e : ℕ) (χ : D.toPre.X), LB.Gen.Corr D.toPre.P.L _ _ _ _
    (LB.pullGen D.toPre.P.L _ _ ((gt (e + 1)).t χ) (thickMap R I e G)) ((gt e).t χ)
  w : ∀ e : ℕ, LB.Iso (LG.L.pull (fstG I e G).left) (D.toPre.P.L.pull (gt e).pG.left)
  w_gen : ∀ e, (w e).IsGen
  w_rig : ∀ (e : ℕ) (p : (PUnit → D.toPre.P.L.ι) × (PUnit → LG.L.ι))
    (V : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))).Opens)
    (h₁ : V ≤ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.toPre.P.L.pull (gt e).pG.left).U p.1 ⊓ (LG.L.pull (fstG I e G).left).U p.2))
    (h₂ : V ≤ thick R I e ⁻¹ᵁ (LG.L.pull (eSec G)).U p.2)
    (h₃ : V ≤ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U p.1),
    res h₁ (pullU (eSec (thickObj R I e G)) _ ((w e).s p)) *
      res h₂ (pullU (thick R I e) _ (LG.rig.s p.2)) =
      res h₃ (pullU (thick R I e) _ (D.toPre.rig.s p.1))
  w_even : ∀ (e : ℕ) (jS : Fin 2 → LG.L.ι) (jT : Fin 2 → D.toPre.P.L.ι),
    LB.Coh LG.L (fun k => (fstG I e G).left ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k) jS →
    LB.Coh D.toPre.P.L
      (fun k => (gt e).pG.left ≫ (![(ι[D.toPre.P.A]).left, 𝟙 D.toPre.P.A.left] : Fin 2 → _) k) jT →
    ∀ (V : (thickObj R I e G).left.Opens)
      (h₁ : V ≤ (gt e).pG.left ⁻¹ᵁ (LB.LinComb D.toPre.P.L (K := Fin 2)
        ![(ι[D.toPre.P.A]).left, 𝟙 D.toPre.P.A.left] ![1, -1]).U jT)
      (h₂ : V ≤ (D.toPre.P.L.pull (gt e).pG.left).U (fun _ => jT 1) ⊓
        (LG.L.pull (fstG I e G).left).U (fun _ => jS 1))
      (h₃ : V ≤ (ι[thickObj R I e G]).left ⁻¹ᵁ ((D.toPre.P.L.pull (gt e).pG.left).U (fun _ => jT 0) ⊓
        (LG.L.pull (fstG I e G).left).U (fun _ => jS 0)))
      (h₄ : V ≤ (fstG I e G).left ⁻¹ᵁ (LB.LinComb LG.L (K := Fin 2)
        ![(ι[G]).left, 𝟙 G.left] ![1, -1]).U jS),
      res h₁ (pullU (gt e).pG.left _ (D.toPre.sym.s jT)) *
        res h₂ ((w e).s (fun _ => jT 1, fun _ => jS 1)) =
      res h₃ (pullU (ι[thickObj R I e G]).left _ ((w e).s (fun _ => jT 0, fun _ => jS 0))) *
        res h₄ (pullU (fstG I e G).left _ (symG.s jS))
  w_cub : ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (jL : thK → LG.L.ι) (jM : thK → D.toPre.P.L.ι),
    LB.Coh LG.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
        ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ≫ thφ G (x3 G) k) jL →
    LB.Coh D.toPre.P.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ (gt e).pG)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ (gt e).pG)
        ((Over.map (thick R I e)).map (x 2) ≫ (gt e).pG))).left ≫
          thφ D.toPre.P.A (x3 D.toPre.P.A) k) jM →
    ∀ (V : T.left.Opens)
      (hB : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ (gt e).pG)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ (gt e).pG)
          ((Over.map (thick R I e)).map (x 2) ≫ (gt e).pG))).left ⁻¹ᵁ
            (Theta D.toPre.P.A D.toPre.P.L).U jM)
      (hG : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
          ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ⁻¹ᵁ (Theta G LG.L).U jL)
      (hw : ∀ k : thK, V ≤ (psum (thickObj R I e G) x k.down).left ⁻¹ᵁ
        ((D.toPre.P.L.pull (gt e).pG.left).U (fun _ => jM k) ⊓
          (LG.L.pull (fstG I e G).left).U (fun _ => jL k))),
      res hB (pullU _ _ (D.toPre.cub.t.s jM)) =
        (∏ k : thK, res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
          ((w e).s (fun _ => jM k, fun _ => jL k))) ^ thε k) *
        res hG (pullU _ _ (cubG.t.s jL))
  w_compat : ∀ (e : ℕ) (p : (PUnit → D.toPre.P.L.ι) × (PUnit → LG.L.ι))
    (V : (thickObj R I e G).left.Opens)
    (h₁ : V ≤ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (gt (e + 1)).pG.left).U p.1 ⊓
      (LG.L.pull (fstG I (e + 1) G).left).U p.2))
    (h₂ : V ≤ (D.toPre.P.L.pull (gt e).pG.left).U p.1 ⊓ (LG.L.pull (fstG I e G).left).U p.2),
    res h₁ (pullU (thickMap R I e G) _ ((w (e + 1)).s p)) = res h₂ ((w e).s p)
end UnifPre
end ReciprocityTheory.ChartRestriction.G.Out


