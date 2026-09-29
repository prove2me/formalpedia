-- Prove2me | Definitions.Def_AlgebraicGeometry_RelPicardPullback
-- name    : AlgebraicGeometry_RelPicardPullback
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/8eebf392-78e1-510b-b961-78e01e51494b
-- title:
--   Picard functoriality: pullback of rigidified bundles along curve maps
-- statement:
--   Throughout, $R$ is a commutative ring, $c : C \to \operatorname{Spec} R$ and $c' : C' \to \operatorname{Spec} R$ are schemes over $R$ equipped with sections $\varepsilon, \varepsilon'$ of $c, c'$, and $f : C' \to C$ is a morphism with $f$ followed by $c$ equal to $c'$ and with $\varepsilon'$ followed by $f$ equal to $\varepsilon$. For an $R$-scheme $t : T \to \operatorname{Spec} R$, `curveChange` is the induced map $C' \times_R T \to C \times_R T$, namely $f \times \mathrm{id}_T$; the helper lemmas record that it carries the rigidifying section $\varepsilon'_T$ of `rigSection` to $\varepsilon_T$, commutes with second-factor base change `baseChangeSnd` along a morphism of $R$-schemes $T' \to T$, and commutes with projection to $T$. `RigidifiedLineBundle.pullbackCurve` then sends a rigidified invertible module $M$ on $C \times_R T$ (a module $M.L$, a local-triviality predicate, and a witness that its restriction along $\varepsilon_T$ is the unit module) to its pullback along `curveChange`, with the induced trivialisation along $\varepsilon'_T$. Further declarations supply: compatibility of this operation with isomorphism of underlying modules (as a `Nonempty` statement about the modules, not an equality of rigidified bundles); an isomorphism comparing pullback along $\psi : T' \to T$ with pullback along the curve map in either order; an isomorphism identifying iterated base change with base change along the composite; an isomorphism from the curve-pullback of the unit bundle to the unit bundle; and the stability of `FibrewiseAlgEquivZero`, the condition that over every algebraically closed field $k$ and every $k$-point $s$ of $T$ the fibre of $M.L$ is algebraically equivalent to zero in the sense of `IsAlgEquivZero`.
--
--   In the `RepresentsRelSubPic` namespace, given designations $D, D'$ representing the `algEquivZeroCut` sub-Picard conditions for $(c,\varepsilon)$ and $(c',\varepsilon')$, `pullbackHom` is the $R$-morphism $D \to D'$ obtained by classifying the curve-pullback of the Poincaré bundle of $D$. The accompanying theorems state that composing a classifying map of $M$ with `pullbackHom` gives the classifying map of the curve-pullback of $M$, that this property characterises the morphism uniquely (`pullbackHom_unique`, `existsUnique_pullbackHom`), and that `pullbackHom` carries the zero section of $D$ to that of $D'$.
--
--   **Relation to Mathlib.** Mathlib has no relative Picard functor or Pic⁰ representability framework; the rigidified-line-bundle structures, sub-Picard conditions and designations used here are the project's own, built on Mathlib's schemes, pullbacks and sheaves of modules.
--
--   **Where it is used.** This is the pullback half of the functoriality of relative Pic⁰ in the curve, the formal input for the maps between Jacobians induced by morphisms of modular curves, and hence for Hecke correspondences on those Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)

def curveChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : pullback c' t ⟶ pullback c t :=
  pullback.map c' t c t f (𝟙 T) (𝟙 _) (by rw [Category.comp_id, hf]) (by simp)

include hε in
theorem rigSection_curveChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    rigSection c' t ε' ≫ curveChange f hf t = rigSection c t ε := by
  apply pullback.hom_ext
  · simp only [rigSection, curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hε]
  · simp only [rigSection, curveChange, Category.assoc, pullback.lift_snd, Category.comp_id]

theorem curveChange_baseChangeSnd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    curveChange f hf t' ≫ baseChangeSnd c ψ = baseChangeSnd c' ψ ≫ curveChange f hf t := by
  apply pullback.hom_ext <;>
    simp only [curveChange, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

theorem curveChange_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange f hf t ≫ pullback.snd c t = pullback.snd c' t := by
  simp only [curveChange, pullback.lift_snd, Category.comp_id]

def RigidifiedLineBundle.pullbackCurve {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) : RigidifiedLineBundle c' ε' t where
  L := (Scheme.Modules.pullback (curveChange f hf t)).obj M.L
  isInvertible := M.isInvertible.pullback _
  rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_curveChange f hf hε t)).app M.L ≪≫ M.rigidified.some⟩

theorem RigidifiedLineBundle.pullbackCurve_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M M' : RigidifiedLineBundle c ε t} (h : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((M.pullbackCurve f hf hε).L ≅ (M'.pullbackCurve f hf hε).L) :=
  ⟨(Scheme.Modules.pullback _).mapIso h.some⟩

def RigidifiedLineBundle.pullbackCurvePullbackAlongIso {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) (ψ : SchemeHomOver t' t) :
    ((M.pullbackCurve f hf hε).pullbackAlong ψ).L ≅ ((M.pullbackAlong ψ).pullbackCurve f hf hε).L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd f hf ψ).symm).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

def RigidifiedLineBundle.pullbackAlongPullbackAlongIso' {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (ψ : SchemeHomOver t' t) (φ : SchemeHomOver t'' t') :
    ((M.pullbackAlong ψ).pullbackAlong φ).L ≅ (M.pullbackAlong (postComp ψ φ)).L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c ψ φ)).app M.L

def RigidifiedLineBundle.unitPullbackCurveIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ((RigidifiedLineBundle.unit (c := c) (ε := ε) t).pullbackCurve f hf hε).L ≅
      (RigidifiedLineBundle.unit (c := c') (ε := ε') t).L :=
  Scheme.Modules.pullbackUnitIso _

include hf in
theorem FibrewiseAlgEquivZero.pullbackCurve {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M : RigidifiedLineBundle c ε t} (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero (M.pullbackCurve f hf hε) := by
  intro k _ _ s

  let e : Limits.pullback (pullback.snd c' t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (curveChange f hf t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, curveChange_snd]) (by simp)
  have he : e ≫ fibreAt c t s = fibreAt c' t s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c' t) s ≫ curveChange f hf t := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

namespace RepresentsRelSubPic

variable {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')

def pullbackHom : SchemeHomOver D.toBase D'.toBase :=
  h'.classify D.toBase (h.poincare.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε h.poincare_mem)

theorem postComp_pullbackHom_classify {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : (algEquivZeroCut c ε).P t M) :
    postComp (pullbackHom f hf hε h h') (h.classify t M hM) =
      h'.classify t (M.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε hM) := by
  refine h'.classify_unique t _ _ _ ⟨?_⟩
  exact (h'.poincare.pullbackAlongPullbackAlongIso' _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (h'.classify_spec D.toBase _ _).some ≪≫
    (h.poincare.pullbackCurvePullbackAlongIso f hf hε _) ≪≫
    (Scheme.Modules.pullback _).mapIso (h.classify_spec t M hM).some

theorem pullbackHom_unique (g : SchemeHomOver D.toBase D'.toBase)
    (hg : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
      (hM : (algEquivZeroCut c ε).P t M),
      postComp g (h.classify t M hM) =
        h'.classify t (M.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε hM)) :
    g = pullbackHom f hf hε h h' := by
  have hid : h.classify D.toBase h.poincare h.poincare_mem = ⟨𝟙 _, Category.id_comp _⟩ :=
    (h.classify_unique D.toBase _ _ _ ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c D.toBase)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _⟩).symm
  have := hg D.toBase h.poincare h.poincare_mem
  rw [hid] at this
  refine Eq.trans ?_ this
  apply Subtype.ext
  simp [postComp]

theorem zeroSection_pullbackHom :
    D.zeroSection ≫ (pullbackHom f hf hε h h').1 = D'.zeroSection := by
  have key := h'.ext_of_iso (𝟙 _)
    (postComp (pullbackHom f hf hε h h') ⟨D.zeroSection, D.zeroSection_toBase⟩)
    ⟨D'.zeroSection, D'.zeroSection_toBase⟩ ⟨?_⟩
  · exact congrArg Subtype.val key
  · exact (h'.poincare.pullbackAlongPullbackAlongIso' _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (h'.classify_spec D.toBase _ _).some ≪≫
      (h.poincare.pullbackCurvePullbackAlongIso f hf hε _) ≪≫
      (Scheme.Modules.pullback _).mapIso h.zero.some ≪≫
      RigidifiedLineBundle.unitPullbackCurveIso f hf hε _ ≪≫ h'.zero.some.symm

theorem existsUnique_pullbackHom :
    ∃! fstar : SchemeHomOver D.toBase D'.toBase,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
        (hM : (algEquivZeroCut c ε).P t M),
        postComp fstar (h.classify t M hM) =
          h'.classify t (M.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε hM) :=
  ⟨pullbackHom f hf hε h h', fun t M hM => postComp_pullbackHom_classify f hf hε h h' t M hM,
    fun g hg => pullbackHom_unique f hf hε h h' g hg⟩

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard

end


