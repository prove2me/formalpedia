-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleStrictHenselianSectionGerms
-- name    : AlgebraicGeometry_EtaleStrictHenselianSectionGerms
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T00:39:59.906812+00:00
-- url     : https://prove2.me/theorems/df0a1456-7ab6-4ec1-aa00-3ab3ef8f7056
-- title:
--   Sections and germs over a strictly henselian ring
-- statement:
--   Étale sheaf sections on a strictly henselian local scheme agree with the stalk at its closed point.

import Definitions.Def_AlgebraicGeometry_EtaleModeledCech
import Definitions.Def_AlgebraicGeometry_HenselianEtaleSections
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.FieldTheory.PurelyInseparable.Basic

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponHenselianEtaleFieldDescent

universe u

/-- An extended-field point of an étale chart descends to the original
separably closed field if its image in the base scheme does. -/
theorem exists_descent_of_etale_point {X U : Scheme.{u}} (g : U ⟶ X) [Etale g]
    {K L : Type u} [Field K] [IsSepClosed K] [Field L]
    (s : Spec (.of K) ⟶ X) (a : Spec (.of L) ⟶ Spec (.of K))
    (t : Spec (.of L) ⟶ U) (ht : t ≫ g = a ≫ s) :
    ∃ r : Spec (.of K) ⟶ U, r ≫ g = s ∧ a ≫ r = t := by
  let q := pullback.snd g s
  let z := pullback.lift t a ht
  have : Etale q := inferInstanceAs (Etale (pullback.snd g s))
  obtain ⟨v, hv, hs⟩ := Scheme.exists_fac_of_etale_of_isSepClosed q (𝟙 _) (z default)
    (Subsingleton.elim _ _)
  have : Etale (v ≫ q) := hv ▸ inferInstance
  have : Etale v := Etale.of_comp v q
  have : Mono v := mono_of_mono_fac hv
  have : IsOpenImmersion v := IsOpenImmersion.of_flat_of_mono v
  have hZ : Set.range z ⊆ Set.range v := by
    rintro _ ⟨x, rfl⟩
    exact ⟨default, hs.trans (congrArg z (Subsingleton.elim _ _))⟩
  let b := IsOpenImmersion.lift v z hZ
  have hb : b ≫ v = z := IsOpenImmersion.lift_fac _ _ _
  have he : b = a := by
    have hz : z ≫ q = a := pullback.lift_snd _ _ _
    rw [← hb, Category.assoc, hv, Category.comp_id] at hz
    exact hz
  refine ⟨v ≫ pullback.fst g s, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ s) hv).trans (Category.id_comp s)
  · rw [← he, ← Category.assoc, hb]
    exact pullback.lift_fst _ _ _

end PhilipponHenselianEtaleFieldDescent

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponHenselianEtaleSection (exists_scheme_section)


namespace PhilipponStrictHenselianEtaleCohomology

universe u

/-- A finite local algebra over a local ring with separably closed
residue field again has separably closed residue field. -/
theorem residueField_isSepClosed_of_moduleFinite {R B : Type*} [CommRing R] [IsLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B] :
    IsSepClosed (ResidueField B) := by
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (maximalIdeal B)
  have : IsLocalHom (algebraMap R B) :=
    ((local_hom_TFAE (algebraMap R B)).out 4 0).mp (eq_maximalIdeal h)
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField R)

section TerminalGerms

variable {Y : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (a : Spec (.of K) ⟶ Y)

private abbrev terminal (Y : Scheme.{u}) := Scheme.Etale.mk (𝟙 Y)

private abbrev terminalPoint : (Scheme.pointSmallEtale a).fiber.obj (terminal Y) :=
  Over.homMk a (Category.comp_id _)

/-- The germ of a global section at a geometric point. -/
abbrev terminalGerm : globalSections Y ⟶ (Scheme.pointSmallEtale a).sheafFiber (A := AddCommGrpCat.{u}) :=
  Functor.whiskerLeft (sheafToPresheaf _ _)
    ((Scheme.pointSmallEtale a).toPresheafFiberNatTrans (terminal Y) (terminalPoint a))

/-- A pointed chart with trivial endomorphisms computes the stalk when
it maps to every pointed étale neighborhood. -/
theorem chartGerm_bijective_of_pointedSections (T : Y.Etale)
    (t : (Scheme.pointSmallEtale a).fiber.obj T) (hEnd : ∀ g : T ⟶ T, g = 𝟙 T)
    (h : ∀ (W : Y.Etale) (w : (Scheme.pointSmallEtale a).fiber.obj W),
      ∃ g : T ⟶ W, (Scheme.pointSmallEtale a).fiber.map g t = w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective ((Scheme.pointSmallEtale a).toPresheafFiber T t F.obj) := by
  let Φ := Scheme.pointSmallEtale a
  constructor
  · intro a b hab
    obtain ⟨W, g, w, _, he⟩ := (Φ.toPresheafFiber_eq_iff' T t a b).mp hab
    obtain ⟨j, _⟩ := h W w
    have hjg := hEnd (j ≫ g)
    have hr : F.obj.map g.op ≫ F.obj.map j.op = 𝟙 _ := by
      rw [← F.obj.map_comp, ← op_comp, hjg]
      exact F.obj.map_id _
    change F.obj.map g.op a = F.obj.map g.op b at he
    calc
      a = F.obj.map j.op (F.obj.map g.op a) := (ConcreteCategory.congr_hom hr a).symm
      _ = F.obj.map j.op (F.obj.map g.op b) := congrArg (fun z => F.obj.map j.op z) he
      _ = b := ConcreteCategory.congr_hom hr b
  · intro a
    obtain ⟨W, w, b, rfl⟩ := Φ.toPresheafFiber_jointly_surjective a
    obtain ⟨g, hg⟩ := h W w
    refine ⟨F.obj.map g.op b, ?_⟩
    change Φ.toPresheafFiber T t F.obj (F.obj.map g.op b) = Φ.toPresheafFiber W w F.obj b
    rw [Φ.toPresheafFiber_w_apply, hg]

private theorem terminalGerm_bijective_of_pointedSections
    (h : ∀ (W : Y.Etale) (w : (Scheme.pointSmallEtale a).fiber.obj W),
      ∃ g : terminal Y ⟶ W, (Scheme.pointSmallEtale a).fiber.map g (terminalPoint a) = w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective ((terminalGerm a).app F) := by
  have hT : IsTerminal (terminal Y) :=
    IsTerminal.isTerminalOfObj (Scheme.Etale.forget Y) _ Over.mkIdTerminal
  exact chartGerm_bijective_of_pointedSections a _ _ (fun g => hT.hom_ext g _) h F

end TerminalGerms

variable (R : Type u) [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]

private abbrev X := Spec (CommRingCat.of R)
private abbrev s := Spec.map (CommRingCat.ofHom (residue R))
private abbrev Φ := Scheme.pointSmallEtale (s R)
private abbrev Ab := Sheaf (X R).smallEtaleTopology AddCommGrpCat.{u}

private theorem pointed_section (W : (X R).Etale) (w : (Φ R).fiber.obj W) :
    ∃ g : terminal (X R) ⟶ W, (Φ R).fiber.map g (terminalPoint (s R)) = w := by
  obtain ⟨a, ha, hw⟩ := exists_scheme_section W.hom w.left (Over.w w)
  refine ⟨MorphismProperty.Over.homMk a ha trivial, Over.OverMorphism.ext hw⟩

/-- For a strictly Henselian local scheme, global sections of an étale
abelian sheaf are its stalk at the residue point. -/
def globalSectionsIsoClosedStalk : globalSections (X R) ≅ (Φ R).sheafFiber (A := AddCommGrpCat.{u}) :=
  NatIso.ofComponents
    (fun F => (AddEquiv.ofBijective ((terminalGerm (s R)).app F).hom
      (terminalGerm_bijective_of_pointedSections (s R) (pointed_section R) F)).toAddCommGrpIso)
    (fun a => (terminalGerm (s R)).naturality a)

/-- Every pointed étale neighborhood of a geometric point over the closed
point of a strictly henselian local scheme admits a compatible section. -/
theorem exists_pointed_section_at_closedPoint {K : Type u} [Field K] [IsSepClosed K]
    (a : Spec (.of K) ⟶ X R) (ha : a default = IsLocalRing.closedPoint R)
    (W : (X R).Etale) (w : (Scheme.pointSmallEtale a).fiber.obj W) :
    ∃ g : terminal (X R) ⟶ W, (Scheme.pointSmallEtale a).fiber.map g (terminalPoint a) = w := by
  let f := Spec.preimage a
  have hf : Spec.map f = a := Spec.map_preimage _
  have : IsLocalHom f.hom := (IsLocalRing.isLocalHom_iff_comap_closedPoint f.hom).2 (by
    change (Spec.map f) (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint R
    rw [hf, ← Subsingleton.elim (default : Spec (.of K)) (IsLocalRing.closedPoint K)]
    exact ha)
  let b := Spec.map (CommRingCat.ofHom (ResidueField.lift f.hom))
  have hb : b ≫ s R = a := by
    change Spec.map (CommRingCat.ofHom (ResidueField.lift f.hom)) ≫
      Spec.map (CommRingCat.ofHom (residue R)) = a
    rw [← Spec.map_comp, ← hf]
    rfl
  obtain ⟨r, hr, hwr⟩ := PhilipponHenselianEtaleFieldDescent.exists_descent_of_etale_point
    W.hom (s R) b w.left ((Over.w w).trans hb.symm)
  obtain ⟨e, he, hre⟩ := exists_scheme_section W.hom r hr
  refine ⟨MorphismProperty.Over.homMk e he trivial, Over.OverMorphism.ext ?_⟩
  change a ≫ e = w.left
  calc
    a ≫ e = (b ≫ s R) ≫ e := congrArg (· ≫ e) hb.symm
    _ = b ≫ r := (Category.assoc _ _ _).trans (congrArg (b ≫ ·) hre)
    _ = w.left := hwr

/-- The global-section germ is bijective at a geometric point lying
over the residue point of a strictly henselian local scheme. -/
theorem terminalGerm_bijective_at_closedPoint {K : Type u} [Field K] [IsSepClosed K]
    (a : Spec (.of K) ⟶ X R) (ha : a default = IsLocalRing.closedPoint R) (F : Ab R) :
    Function.Bijective ((terminalGerm a).app F) :=
  terminalGerm_bijective_of_pointedSections a (exists_pointed_section_at_closedPoint R a ha) F

end PhilipponStrictHenselianEtaleCohomology

end

end


