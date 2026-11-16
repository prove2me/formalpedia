-- Prove2me | Definitions.Def_RPLib_S4_EtShRes
-- name    : RPLib_S4_EtShRes
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:25:36.107641+00:00
-- url     : https://prove2.me/theorems/1def6633-54e5-4421-99fd-91a97b7a88e9
-- title:
--   Restriction of etale sheaves along an etale morphism
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For an etale $g : U \to X$, composition with $g$ is a continuous functor from the small etale site of $U$ to that of $X$, so restriction (precomposition with it) maps sheaves to sheaves. Restriction is left adjoint to $g_*$, hence $g^* \cong$ restriction: the sections of $g^*F$ over $W \to U$ are $F(W \to U \to X)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose III; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShTensor

/-!
# S4-EtSheaves, part 6: restriction along an etale map

For an etale `g : U ⟶ X`, `etComp g : U.Etale ⥤ X.Etale` (composition with `g`) is continuous, so
restriction `res g` (precomposition with `etComp g`) maps sheaves to sheaves. It is left adjoint to
`g_*`, hence `g^* ≅ res g` (`pullIsoRes`): the sections of `g^*F` over `W` are `F(W → U → X)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g]

@[simp] theorem etComp_obj_left (W : U.Etale) : ((etComp g).obj W).left = W.left := rfl

@[simp] theorem etComp_obj_hom (W : U.Etale) : ((etComp g).obj W).hom = W.hom ≫ g := rfl

@[simp] theorem etComp_map_left {W W' : U.Etale} (φ : W ⟶ W') : ((etComp g).map φ).left = φ.left :=
  rfl

/-- An etale `X`-scheme `T` with a map `a : T ⟶ W` (over `X`) to `etComp g W` is etale over `U`. -/
def etLift {W : U.Etale} (T : X.Etale) (a : T.left ⟶ W.left) (ha : a ≫ W.hom ≫ g = T.hom) : U.Etale :=
  MorphismProperty.Over.mk ⊤ (a ≫ W.hom) (by
    have h1 : Etale ((a ≫ W.hom) ≫ g) := by
      rw [Category.assoc, ha]
      exact T.prop
    exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) (a ≫ W.hom) g
      (inferInstance : Etale g) h1)

/-- `etComp g` preserves covers. -/
theorem etComp_coverPreserving :
    CoverPreserving U.smallEtaleTopology X.smallEtaleTopology (etComp g) where
  cover_preserve {V} {R} hR := by
    rw [mem_smallEtale_iff] at hR ⊢
    intro z
    obtain ⟨W, φ, w, hφ, hw⟩ := hR z
    exact ⟨_, (etComp g).map φ, w, R.image_mem_functorPushforward (etComp g) hφ, hw⟩

set_option backward.isDefEq.respectTransparency false in
/-- `etComp g` preserves compatible families (as `Over.map` does in Mathlib's `Sites/Over`). -/
theorem etComp_compatiblePreserving :
    CompatiblePreserving X.smallEtaleTopology (etComp g) where
  compatible {F Z _ x hx Y₁ Y₂ T f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    have h1 : f₁.left ≫ Y₁.hom ≫ g = T.hom := MorphismProperty.Over.w f₁
    have hl : f₁.left ≫ g₁.left = f₂.left ≫ g₂.left := by
      have := congrArg (fun φ : T ⟶ (etComp g).obj Z => φ.left) h
      exact this
    have h2 : f₂.left ≫ Y₂.hom = f₁.left ≫ Y₁.hom := by
      rw [← MorphismProperty.Over.w g₂, ← Category.assoc, ← hl, Category.assoc,
        MorphismProperty.Over.w g₁]
    let W' : U.Etale := etLift g (W := Y₁) T f₁.left h1
    let g₁' : W' ⟶ Y₁ := MorphismProperty.Over.homMk f₁.left rfl trivial
    let g₂' : W' ⟶ Y₂ := MorphismProperty.Over.homMk f₂.left h2 trivial
    let e : (etComp g).obj W' ≅ T := MorphismProperty.Over.isoMk (Iso.refl _)
      (by simpa [W', etLift] using h1.symm)
    have e1 : f₁ = e.inv ≫ (etComp g).map g₁' :=
      MorphismProperty.Over.Hom.ext (Category.id_comp f₁.left).symm
    have e2 : f₂ = e.inv ≫ (etComp g).map g₂' :=
      MorphismProperty.Over.Hom.ext (Category.id_comp f₂.left).symm
    have hc := hx g₁' g₂' hg₁ hg₂ (MorphismProperty.Over.Hom.ext hl)
    rw [e1, e2, op_comp, op_comp, F.obj.map_comp, F.obj.map_comp, types_comp_apply,
      types_comp_apply]
    exact congrArg (F.obj.map e.inv.op) hc

instance : (etComp g).IsContinuous U.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving (etComp_compatiblePreserving g) (etComp_coverPreserving g)

variable (Λ : Type u) [CommRing Λ]

/-- Restriction of etale sheaves along an etale `g`: `(res g F)(W) = F(W → U → X)`. -/
abbrev res : EtSh Λ X ⥤ EtSh Λ U :=
  (etComp g).sheafPushforwardContinuous (ModuleCat.{u} Λ) U.smallEtaleTopology X.smallEtaleTopology

/-- `res g ⊣ g_*`. -/
def resAdj : res g Λ ⊣ push g Λ :=
  (etCompAdj g).sheafPushforwardContinuous (E := ModuleCat.{u} Λ) U.smallEtaleTopology
    X.smallEtaleTopology

/-- **For etale `g`, `g^*` is restriction**: `g^* ≅ res g`. -/
def pullIsoRes : pull g Λ ≅ res g Λ := (pullAdj g Λ).leftAdjointUniq (resAdj g Λ)

end RamanujanPetersson.EtSheaves


