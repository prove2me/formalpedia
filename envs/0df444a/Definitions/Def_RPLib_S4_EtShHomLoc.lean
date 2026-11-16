-- Prove2me | Definitions.Def_RPLib_S4_EtShHomLoc
-- name    : RPLib_S4_EtShHomLoc
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:27:50.433436+00:00
-- url     : https://prove2.me/theorems/e569071d-e40e-4545-9168-c6b99e379f03
-- title:
--   The internal Hom of etale sheaves is local
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For an etale $g : U \to X$, slices over $V$ in the etale sites of $U$ and of $X$ are equivalent, so restricting $\mathcal{H}om(F, G)$ to $U$ gives $\mathcal{H}om(F|_U, G|_U)$; in particular $g^*(F^\vee) \cong (g^*F)^\vee$. $\mathcal{H}om(-, -)$ is transported along isomorphisms in both variables.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IV, Section 12; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShHom

/-!
# S4-EtSheaves, part 10: the internal Hom is local

For an etale `g : U ⟶ X`, `Over.post (etComp g) : Over V ⥤ Over (etComp g V)` is an equivalence, so
restricting `Hom(F, G)` to `U` gives `Hom(F|_U, G|_U)` (`resHomIso`, `pullHomIso`); in particular
`g^*(F^∨) ≅ (g^*F)^∨` (`pullDualIso`). `homShCongr` transports `Hom(-, -)` along isomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

section Post

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g]

instance etComp_faithful : (etComp g).Faithful where
  map_injective {_ _} _ _ h := MorphismProperty.Over.Hom.ext (congrArg (fun f => f.left) h)

instance (V : U.Etale) : (Over.post (X := V) (etComp g)).Full where
  map_surjective {A B} ψ := by
    have h2 : ψ.left.left ≫ B.hom.left = A.hom.left := congrArg (fun f => f.left) (Over.w ψ)
    have h1 : ψ.left.left ≫ B.left.hom = A.left.hom :=
      calc ψ.left.left ≫ B.left.hom = ψ.left.left ≫ (B.hom.left ≫ V.hom) :=
            congrArg (ψ.left.left ≫ ·) (MorphismProperty.Over.w B.hom).symm
        _ = (ψ.left.left ≫ B.hom.left) ≫ V.hom := (Category.assoc _ _ _).symm
        _ = A.hom.left ≫ V.hom := congrArg (· ≫ V.hom) h2
        _ = A.left.hom := MorphismProperty.Over.w A.hom
    exact ⟨Over.homMk (MorphismProperty.Over.homMk ψ.left.left h1 trivial)
      (MorphismProperty.Over.Hom.ext h2), Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext rfl)⟩

instance (V : U.Etale) : (Over.post (X := V) (etComp g)).EssSurj where
  mem_essImage T := by
    have ha : T.hom.left ≫ V.hom ≫ g = T.left.hom := MorphismProperty.Over.w T.hom
    refine ⟨Over.mk (MorphismProperty.Over.homMk T.hom.left rfl trivial :
      etLift g (W := V) T.left T.hom.left ha ⟶ V), ⟨Over.isoMk
        (MorphismProperty.Over.isoMk (Iso.refl _) ?_) ?_⟩⟩
    · exact (Category.id_comp _).trans ((Category.assoc _ _ _).trans ha).symm
    · exact MorphismProperty.Over.Hom.ext (Category.id_comp _)

instance (V : U.Etale) : (Over.post (X := V) (etComp g)).IsEquivalence where

variable {Λ : Type u} [CommRing Λ] (F G : EtSh Λ X)

/-- `Hom(F, G)(g V) ≃ Hom(F|_U, G|_U)(V)`: whiskering along `Over.post (etComp g)`. -/
def resHomEquiv (V : U.Etale) :
    HomOver F G ((etComp g).obj V) ≃ₗ[Λ] HomOver ((res g Λ).obj F) ((res g Λ).obj G) V :=
  { presheafHomEquiv F.obj G.obj (Over.post (X := V) (etComp g)) with
    map_add' := fun _ _ => NatTrans.ext (funext fun _ => rfl)
    map_smul' := fun _ _ => NatTrans.ext (funext fun _ => rfl) }

theorem resHomEquiv_natural {V V' : U.Etale} (f : V' ⟶ V) (α : HomOver F G ((etComp g).obj V)) :
    resHomEquiv g F G V' (homOverMap F G ((etComp g).map f) α) =
      homOverMap _ _ f (resHomEquiv g F G V α) :=
  NatTrans.ext (funext fun _ => rfl)

/-- **`Hom(F, G)|_U ≅ Hom(F|_U, G|_U)`** for an etale `g : U ⟶ X`. -/
def resHomIso : (res g Λ).obj (homSh F G) ≅ homSh ((res g Λ).obj F) ((res g Λ).obj G) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
    (fun V => ((Shrink.linearEquiv Λ _).trans ((resHomEquiv g F G V.unop).trans
      (Shrink.linearEquiv Λ _).symm)).toModuleIso) (by
      intro V V' f
      ext x
      change (Shrink.linearEquiv Λ _).symm (resHomEquiv g F G V'.unop (Shrink.linearEquiv Λ _
          (shrinkMap (homOverMap F G ((etComp g).map f.unop)) x))) =
        shrinkMap (homOverMap ((res g Λ).obj F) ((res g Λ).obj G) f.unop)
          ((Shrink.linearEquiv Λ _).symm (resHomEquiv g F G V.unop (Shrink.linearEquiv Λ _ x)))
      rw [shrinkMap_apply, shrinkMap_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, resHomEquiv_natural]))

end Post

section Congr

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ] {F F' G G' : EtSh Λ X} (e : F ≅ F') (e' : G ≅ G')

/-- Transport of sections of `Hom(F, G)` along isomorphisms `F ≅ F'`, `G ≅ G'`. -/
def homOverCongr (V : X.Etale) : HomOver F G V ≃ₗ[Λ] HomOver F' G' V :=
  Linear.homCongr Λ (Functor.isoWhiskerLeft (Over.forget V).op
    ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).mapIso e))
    (Functor.isoWhiskerLeft (Over.forget V).op
      ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).mapIso e'))

theorem homOverCongr_natural {V V' : X.Etale} (f : V' ⟶ V) (α : HomOver F G V) :
    homOverCongr e e' V' (homOverMap F G f α) = homOverMap F' G' f (homOverCongr e e' V α) :=
  NatTrans.ext (funext fun _ => rfl)

/-- **`Hom(F, G) ≅ Hom(F', G')`** for `F ≅ F'`, `G ≅ G'`. -/
def homShCongr : homSh F G ≅ homSh F' G' :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
    (fun V => ((Shrink.linearEquiv Λ _).trans ((homOverCongr e e' V.unop).trans
      (Shrink.linearEquiv Λ _).symm)).toModuleIso) (by
      intro V V' f
      ext x
      change (Shrink.linearEquiv Λ _).symm (homOverCongr e e' V'.unop (Shrink.linearEquiv Λ _
          (shrinkMap (homOverMap F G f.unop) x))) =
        shrinkMap (homOverMap F' G' f.unop)
          ((Shrink.linearEquiv Λ _).symm (homOverCongr e e' V.unop (Shrink.linearEquiv Λ _ x)))
      rw [shrinkMap_apply, shrinkMap_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, homOverCongr_natural]))

end Congr

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {Λ : Type u} [CommRing Λ] (F G : EtSh Λ X)

/-- **`g^* Hom(F, G) ≅ Hom(g^*F, g^*G)`** for an etale `g`. -/
def pullHomIso : (pull g Λ).obj (homSh F G) ≅ homSh ((pull g Λ).obj F) ((pull g Λ).obj G) :=
  (pullIsoRes g Λ).app (homSh F G) ≪≫ resHomIso g F G ≪≫
    homShCongr ((pullIsoRes g Λ).app F).symm ((pullIsoRes g Λ).app G).symm

/-- **`g^*(F^∨) ≅ (g^*F)^∨`** for an etale `g`. -/
def pullDualIso : (pull g Λ).obj (dualSh F) ≅ dualSh ((pull g Λ).obj F) :=
  pullHomIso g F (unitSh Λ X) ≪≫ homShCongr (Iso.refl _) (pullConst Λ g (ModuleCat.of Λ Λ))

end RamanujanPetersson.EtSheaves


