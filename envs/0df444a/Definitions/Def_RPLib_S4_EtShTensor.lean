-- Prove2me | Definitions.Def_RPLib_S4_EtShTensor
-- name    : RPLib_S4_EtShTensor
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:23:32.959065+00:00
-- url     : https://prove2.me/theorems/3ce83414-b8c3-43f8-acaf-3d6e8683ccfd
-- title:
--   Tensor products of etale sheaves
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ carries the monoidal structure obtained by sheafifying the pointwise tensor product of presheaves. The file proves $(F \otimes G)_{\bar s} \cong F_{\bar s} \otimes_\Lambda G_{\bar s}$, $M_X \otimes N_X \cong (M \otimes_\Lambda N)_X$, that for an etale $g : U \to X$ the pullback $g^*$ is restriction along composition with $g$ (so $g^*(F \otimes G) \cong g^*F \otimes g^*G$), and that tensor products of lisse (locally constant) sheaves are lisse (locally constant).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IX; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShPullComp

/-!
# S4-EtSheaves, part 5: tensor products of etale sheaves

`EtSh Λ X` carries Mathlib's monoidal structure on sheaves (localisation of the pointwise tensor
product of presheaves; the small etale site has enough points, so sheafification is monoidal).
* stalks: `(F ⊗ G)_s ≅ F_s ⊗ G_s` (`stalkTensIso`);
* constant sheaves: `M_X ⊗ N_X ≅ (M ⊗ N)_X` (`constTensIso`);
* for an etale `g : U ⟶ X`, `g^*` is restriction along `etComp g : U.Etale ⥤ X.Etale`
  (`sheafifyPullIso`: `g^* ∘ sheafify ≅ sheafify ∘ restriction`, from uniqueness of left adjoints),
  hence `g^*(F ⊗ G) ≅ g^*F ⊗ g^*G` (`pullTensIso`);
* `IsLisse.tens`: lisse ⊗ lisse is lisse; `IsLocConst.tens` likewise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

/-- Sheafification on the small etale site is monoidal (the site has enough points). -/
instance etW_isMonoidal (X : Scheme.{u}) :
    (X.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal :=
  (Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X).isMonoidal_W (ModuleCat.{u} Λ)

/-- The tensor product of etale sheaves of `Λ`-modules. -/
instance (X : Scheme.{u}) : MonoidalCategory (EtSh Λ X) :=
  Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u} Λ)

/-- **Stalks of a tensor product**: `(F ⊗ G)_s ≅ F_s ⊗ G_s`. -/
def stalkTensIso {X : Scheme.{u}} (s : GeomPt X) (F G : EtSh Λ X) :
    (s.stalkF Λ).obj (F ⊗ G) ≅ (s.stalkF Λ).obj F ⊗ (s.stalkF Λ).obj G :=
  (Functor.Monoidal.μIso s.point.sheafFiber F G).symm

/-- The tensor product of sheaves is the sheafification of the tensor product of presheaves. -/
def tensIso {X : Scheme.{u}} (F G : EtSh Λ X) :
    F ⊗ G ≅ (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj (F.obj ⊗ G.obj) :=
  tensorIso (sheafificationIso F) (sheafificationIso G) ≪≫
    Functor.Monoidal.μIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) F.obj G.obj

/-- **Constant sheaves**: `M_X ⊗ N_X ≅ (M ⊗ N)_X`. -/
def constTensIso (X : Scheme.{u}) (M N : ModuleCat.{u} Λ) :
    constSh Λ X M ⊗ constSh Λ X N ≅ constSh Λ X (M ⊗ N) :=
  Functor.Monoidal.μIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) _ _ ≪≫
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).mapIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (by
        intro V W φ
        simp))

/-- Precomposition commutes with the pointwise tensor product of presheaves. -/
def compTensIso {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D) (P Q : D ⥤ ModuleCat.{u} Λ) :
    H ⋙ (P ⊗ Q) ≅ (H ⋙ P) ⊗ (H ⋙ Q) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro V W φ
    simp)

section Etale

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g]

/-- Composition with an etale `g : U ⟶ X`: etale `U`-schemes are etale `X`-schemes. -/
def etComp : U.Etale ⥤ X.Etale := MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale g)

/-- `etComp g ⊣ etPull g`. -/
def etCompAdj : etComp g ⊣ etPull g :=
  MorphismProperty.Over.mapPullbackAdj (P := @Etale) (Q := ⊤) g (inferInstance : Etale g) trivial

/-- Restriction of presheaves along `etComp g` is left adjoint to restriction along `etPull g`. -/
def presheafResAdj :
    (Functor.whiskeringLeft _ _ (ModuleCat.{u} Λ)).obj (etComp g).op ⊣
      (Functor.whiskeringLeft _ _ (ModuleCat.{u} Λ)).obj (etPull g).op :=
  Adjunction.whiskerLeft (ModuleCat.{u} Λ) (Adjunction.op (etCompAdj g))

/-- **For etale `g`, `g^*` is restriction**: `g^* ∘ sheafify ≅ sheafify ∘ (· ∘ etComp g)`. -/
def sheafifyPullIso :
    presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⋙ pull g Λ ≅
      (Functor.whiskeringLeft _ _ (ModuleCat.{u} Λ)).obj (etComp g).op ⋙
        presheafToSheaf U.smallEtaleTopology (ModuleCat.{u} Λ) :=
  ((sheafificationAdjunction _ _).comp (pullAdj g Λ)).leftAdjointUniq
    (((presheafResAdj Λ g).comp (sheafificationAdjunction _ _)).ofNatIsoRight
      ((etPull g).sheafPushforwardContinuousCompSheafToPresheafIso (ModuleCat.{u} Λ)
        X.smallEtaleTopology U.smallEtaleTopology).symm)

/-- `g^* F ≅ sheafify (F ∘ etComp g)` for a sheaf `F`. -/
def pullResIso (F : EtSh Λ X) :
    (pull g Λ).obj F ≅
      (presheafToSheaf U.smallEtaleTopology (ModuleCat.{u} Λ)).obj ((etComp g).op ⋙ F.obj) :=
  (pull g Λ).mapIso (sheafificationIso F) ≪≫ (sheafifyPullIso Λ g).app F.obj

/-- **`g^*` is monoidal for etale `g`**: `g^*(F ⊗ G) ≅ g^*F ⊗ g^*G`. -/
def pullTensIso (F G : EtSh Λ X) :
    (pull g Λ).obj (F ⊗ G) ≅ (pull g Λ).obj F ⊗ (pull g Λ).obj G :=
  (pull g Λ).mapIso (tensIso Λ F G) ≪≫ (sheafifyPullIso Λ g).app (F.obj ⊗ G.obj) ≪≫
    (presheafToSheaf U.smallEtaleTopology (ModuleCat.{u} Λ)).mapIso
      (compTensIso Λ (etComp g).op F.obj G.obj) ≪≫
    (Functor.Monoidal.μIso (presheafToSheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) _ _).symm ≪≫
    tensorIso (pullResIso Λ g F).symm (pullResIso Λ g G).symm

end Etale

variable {X : Scheme.{u}} {Λ}

/-- If `F|_U ≅ M` then `F|_T ≅ M` for every `T ⟶ U`. -/
def restrictLocalIso {F : EtSh Λ X} (U : X.Etale) (M : ModuleCat.{u} Λ)
    (e : (pull U.hom Λ).obj F ≅ constSh Λ U.left M) {T : Scheme.{u}} (h : T ⟶ U.left) :
    (pull (h ≫ U.hom) Λ).obj F ≅ constSh Λ T M :=
  (pullCompIso Λ h U.hom).app F ≪≫ (pull h Λ).mapIso e ≪≫ pullConst Λ h M

/-- A common etale refinement of two etale neighbourhoods `U`, `V` of `x`. -/
theorem exists_common_refinement (U V : X.Etale) (u : U.left) (v : V.left)
    (h : V.hom v = U.hom u) :
    ∃ (W : X.Etale) (w : W.left), W.hom w = U.hom u ∧
      ∃ (a : W.left ⟶ U.left) (b : W.left ⟶ V.left), W.hom = a ≫ U.hom ∧ W.hom = b ≫ V.hom := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback v u h
  refine ⟨(etComp U.hom).obj ((etPull U.hom).obj V), z, ?_, pullback.snd V.hom U.hom,
    pullback.fst V.hom U.hom, rfl, (pullback.condition (f := V.hom) (g := U.hom)).symm⟩
  change U.hom (pullback.snd V.hom U.hom z) = _
  rw [hz2]

/-- **Lisse ⊗ lisse is lisse.** -/
theorem IsLisse.tens {F G : EtSh Λ X} (hF : IsLisse Λ F) (hG : IsLisse Λ G) :
    IsLisse Λ (F ⊗ G) := by
  intro x
  obtain ⟨U, u, hu, M, hM, ⟨e⟩⟩ := hF x
  obtain ⟨V, v, hv, N, hN, ⟨e'⟩⟩ := hG x
  obtain ⟨W, w, hw, a, b, ha, hb⟩ := exists_common_refinement U V u v (hv.trans hu.symm)
  have : Etale W.hom := W.prop
  refine ⟨W, w, hw.trans hu, M ⊗ N, ?_, ⟨pullTensIso Λ W.hom F G ≪≫ tensorIso
    ((pullCongr Λ ha).app F ≪≫ restrictLocalIso U M e a)
    ((pullCongr Λ hb).app G ≪≫ restrictLocalIso V N e' b) ≪≫ constTensIso Λ W.left M N⟩⟩
  change Module.Finite Λ (TensorProduct Λ M N)
  infer_instance

/-- **Locally constant ⊗ locally constant is locally constant.** -/
theorem IsLocConst.tens {F G : EtSh Λ X} (hF : IsLocConst Λ F) (hG : IsLocConst Λ G) :
    IsLocConst Λ (F ⊗ G) := by
  intro x
  obtain ⟨U, u, hu, M, ⟨e⟩⟩ := hF x
  obtain ⟨V, v, hv, N, ⟨e'⟩⟩ := hG x
  obtain ⟨W, w, hw, a, b, ha, hb⟩ := exists_common_refinement U V u v (hv.trans hu.symm)
  have : Etale W.hom := W.prop
  exact ⟨W, w, hw.trans hu, M ⊗ N, ⟨pullTensIso Λ W.hom F G ≪≫ tensorIso
    ((pullCongr Λ ha).app F ≪≫ restrictLocalIso U M e a)
    ((pullCongr Λ hb).app G ≪≫ restrictLocalIso V N e' b) ≪≫ constTensIso Λ W.left M N⟩⟩

end RamanujanPetersson.EtSheaves


