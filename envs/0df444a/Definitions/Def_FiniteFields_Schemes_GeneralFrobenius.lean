-- Prove2me | Definitions.Def_FiniteFields_Schemes_GeneralFrobenius
-- name    : FiniteFields_Schemes_GeneralFrobenius
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-25T12:10:45.19902+00:00
-- url     : https://prove2.me/theorems/852384fe-a3a2-5c37-8e25-9e54c177f767
-- title:
--   The $q^m$-power Frobenius endomorphism of a scheme over $\mathbb F_q$
-- statement:
--   Let $k$ be a finite field with $q=p^e$ elements and $X$ a scheme over $\operatorname{Spec}k$. For $m\ge 0$, the **$q^m$-power Frobenius** $F^m_X\colon X\to X$ is the endomorphism which is the identity on the underlying topological space and acts on the structure sheaf by $s\mapsto s^{q^m}$ on every open set. Since $a^{q}=a$ for $a\in k$, it is a morphism over $\operatorname{Spec}k$; the file provides it both as an endomorphism of $X$ and as an endomorphism in the category of schemes over $\operatorname{Spec}k$.
-- source:
--   The Stacks Project, Chapter 64 (Trace Formula), section on Frobenii (the absolute and relative Frobenius); P. Deligne, La conjecture de Weil. I, Publ. Math. IHÉS 43 (1974), §1.

import Mathlib
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_FiniteFields_Dwork_Foundations

noncomputable section

namespace FiniteFields.Schemes

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable {k : Type u} [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The positive exponent `e` such that `Nat.card k = p ^ e`. -/
private noncomputable def finiteFieldExponent : ℕ :=
  letI := Fintype.ofFinite k
  ((FiniteField.card k p).choose : ℕ)

omit [Fact p.Prime] in
private theorem natCard_eq_char_pow :
    Nat.card k = p ^ finiteFieldExponent (k := k) p := by
  letI := Fintype.ofFinite k
  simpa [finiteFieldExponent, Nat.card_eq_fintype_card] using
    (FiniteField.card k p).choose_spec.2

/-- The ground-field map into sections on an open of a scheme over `k`. -/
private noncomputable def toSections (X : Over (Spec (.of k))) (U : X.left.Opens) :
    k →+* Γ(X.left, U) :=
  ((X.hom.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)

omit [Finite k] in
private theorem toSections_injective (X : Over (Spec (.of k))) (U : X.left.Opens)
    [Nonempty U] : Function.Injective (toSections X U) :=
  (toSections X U).injective

/-- Pullback by the `m`th q-power Frobenius on one open set. -/
private noncomputable def qPowerSectionHom (X : Over (Spec (.of k))) (m : ℕ)
    (U : X.left.Opens) : Γ(X.left, U) →+* Γ(X.left, U) := by
  classical
  by_cases hU : Nonempty U
  · letI : Nonempty U := hU
    letI : CharP Γ(X.left, U) p :=
      charP_of_injective_ringHom (toSections_injective X U) p
    exact iterateFrobenius Γ(X.left, U) p (finiteFieldExponent (k := k) p * m)
  · exact RingHom.id _

@[simp]
private theorem qPowerSectionHom_apply (X : Over (Spec (.of k))) (m : ℕ)
    (U : X.left.Opens) (a : Γ(X.left, U)) :
    qPowerSectionHom (p := p) X m U a = a ^ (Nat.card k) ^ m := by
  classical
  by_cases hU : Nonempty U
  · letI : Nonempty U := hU
    letI : CharP Γ(X.left, U) p :=
      charP_of_injective_ringHom (toSections_injective X U) p
    rw [qPowerSectionHom, dif_pos hU, iterateFrobenius_def, natCard_eq_char_pow]
    congr 1
    rw [← pow_mul]
  · have hsub : Subsingleton Γ(X.left, U) := by
      have hbot : U = ⊥ := by
        apply SetLike.ext
        intro x
        constructor
        · intro hx
          exact False.elim (hU ⟨⟨x, hx⟩⟩)
        · simp
      subst hbot
      infer_instance
    exact Subsingleton.elim _ _

/-- The natural q-power endomorphism of the structure presheaf. -/
private noncomputable def qPowerNatTrans (X : Over (Spec (.of k))) (m : ℕ) :
    X.left.presheaf ⟶ X.left.presheaf where
  app U := CommRingCat.ofHom (qPowerSectionHom (p := p) X m U.unop)
  naturality U V f := by
    apply CommRingCat.hom_ext
    ext a
    simp only [CommRingCat.comp_apply]
    change qPowerSectionHom (p := p) X m V.unop (X.left.presheaf.map f a) =
      X.left.presheaf.map f (qPowerSectionHom (p := p) X m U.unop a)
    rw [qPowerSectionHom_apply, qPowerSectionHom_apply, map_pow]

/-- The presheafed-space morphism underlying q-power Frobenius. -/
private noncomputable def qPowerPresheafedSpaceHom (X : Over (Spec (.of k))) (m : ℕ) :
    X.left.toPresheafedSpace.Hom X.left.toPresheafedSpace where
  base := 𝟙 _
  c := qPowerNatTrans (p := p) X m

private theorem qPowerStalkMap_apply (X : Over (Spec (.of k))) (m : ℕ) (x : X.left)
    (a : X.left.presheaf.stalk x) :
    (qPowerPresheafedSpaceHom (p := p) X m).stalkMap x a =
      a ^ (Nat.card k) ^ m := by
  obtain ⟨U, hxU, s, rfl⟩ := X.left.presheaf.exists_germ_eq a
  change (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (qPowerNatTrans (p := p) X m) ≫
    X.left.presheaf.stalkPushforward CommRingCat (𝟙 _) x)
      (X.left.presheaf.germ U x hxU s)) = _
  rw [TopCat.Presheaf.stalkPushforward.id]
  erw [← Functor.map_comp]
  have hc : qPowerNatTrans (p := p) X m ≫
      (TopCat.Presheaf.Pushforward.id X.left.presheaf).hom =
        qPowerNatTrans (p := p) X m := by
    ext V
    rfl
  rw [hc]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change X.left.presheaf.germ U x hxU (qPowerSectionHom (p := p) X m U s) =
    X.left.presheaf.germ U x hxU s ^ (Nat.card k) ^ m
  rw [qPowerSectionHom_apply, map_pow]

/-- The locally-ringed-space morphism underlying q-power Frobenius. -/
private noncomputable def qPowerLocallyRingedSpaceHom (X : Over (Spec (.of k))) (m : ℕ) :
    X.left.toLocallyRingedSpace ⟶ X.left.toLocallyRingedSpace where
  toHom := qPowerPresheafedSpaceHom (p := p) X m
  prop x := by
    constructor
    intro a ha
    -- Portage v4.33 : `CommRingCat.Hom.hom` au lieu de `ConcreteCategory.hom`.
    erw [qPowerStalkMap_apply (p := p)] at ha
    exact (isUnit_pow_iff (pow_ne_zero m (Nat.card_pos.ne'))).mp ha

/-- The literal `q^m`-power Frobenius of a native scheme over the finite field `k`.

It is the identity on the topological carrier and sends every local section `a` to
`a ^ (Nat.card k) ^ m`. -/
noncomputable def qPowerFrobenius (X : Over (Spec (.of k))) (m : ℕ) : X.left ⟶ X.left :=
  Scheme.Hom.mk (qPowerLocallyRingedSpaceHom (p := p) X m)

@[simp]
private theorem qPowerFrobenius_apply (X : Over (Spec (.of k))) (m : ℕ) (x : X.left) :
    qPowerFrobenius p X m x = x :=
  rfl

@[simp]
private theorem qPowerFrobenius_app (X : Over (Spec (.of k))) (m : ℕ) (U : X.left.Opens)
    (a : Γ(X.left, U)) :
    (qPowerFrobenius p X m).app U a = a ^ (Nat.card k) ^ m :=
  qPowerSectionHom_apply (p := p) X m U a

private theorem baseSection_pow_natCard (m : ℕ) (U : (Spec (.of k)).Opens)
    (a : Γ(Spec (.of k), U)) : a ^ (Nat.card k) ^ m = a := by
  classical
  by_cases hU : Nonempty U
  · have htop : U = ⊤ := by
      apply le_antisymm le_top
      rintro x -
      obtain ⟨y, hy⟩ := hU
      simpa only [Subsingleton.elim x y] using hy
    subst U
    letI := Fintype.ofFinite k
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).hom).injective
    rw [map_pow]
    simpa only [Nat.card_eq_fintype_card] using
      FiniteField.pow_card_pow m ((Scheme.ΓSpecIso (.of k)).hom a)
  · have hbot : U = ⊥ := by
      apply SetLike.ext
      intro x
      constructor
      · intro hx
        exact False.elim (hU ⟨⟨x, hx⟩⟩)
      · simp
    subst U
    exact Subsingleton.elim _ _

private theorem qPowerFrobenius_over_base (X : Over (Spec (.of k))) (m : ℕ) :
    qPowerFrobenius p X m ≫ X.hom = X.hom := by
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  ext a
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  erw [qPowerFrobenius_app]
  rw [← map_pow, baseSection_pow_natCard]

/-- The q-power Frobenius as an actual endomorphism in schemes over `Spec k`. -/
noncomputable def qPowerFrobenius_over (X : Over (Spec (.of k))) (m : ℕ) : X ⟶ X :=
  Over.homMk (qPowerFrobenius p X m) (qPowerFrobenius_over_base p X m)









end FiniteFields.Schemes


