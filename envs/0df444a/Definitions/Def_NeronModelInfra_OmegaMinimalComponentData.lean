-- Prove2me | Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
-- name    : NeronModelInfra_OmegaMinimalComponentData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/2bd87016-0ac4-51e3-aaf0-24c54649bf97
-- title:
--   Readings of a top differential form; ω-minimal component data
-- statement:
--   Throughout, $R$ is a discrete valuation ring, $K$ an $R$-algebra which is a field, $g_K\colon X_K\to\operatorname{Spec}K$ a scheme over $K$, $d$ a natural number and $\omega$ a global section of the $d$-th determinant module $\omega$-sheaf `gK.topDifferentials d` built from the relative Kähler module of $g_K$.
--
--   Two auxiliary results record that the canonical $R$-algebra structure on a stalk $\mathcal O_{Y,y}$ of an $R$-scheme $f\colon Y\to\operatorname{Spec}R$ is compatible with $f$: the composite $\operatorname{Spec}\mathcal O_{Y,y}\to Y\xrightarrow{f}\operatorname{Spec}R$ is $\operatorname{Spec}$ of the structure map $R\to\mathcal O_{Y,y}$.
--
--   A `ComponentReading` is a bundle of data: a smooth morphism $f\colon Y\to\operatorname{Spec}R$ locally of finite type; a $K$-morphism $e$ from the generic fibre $Y\times_{\operatorname{Spec}R}\operatorname{Spec}K$ to $X_K$ which is an open immersion; a point $y\in Y$ above the closed point of $R$ that is maximal for specialisation among such points; the assertions that $\mathcal O=\mathcal O_{Y,y}$ is a domain and a discrete valuation ring; an $R$-algebra structure on $\mathcal O$ satisfying the above compatibility (carried as a field), a $K$-algebra structure on $F=\operatorname{Frac}\mathcal O$ in a tower over $R$; a basis $b$ of $\Omega_{\mathcal O/R}$ indexed by $\mathrm{Fin}\,d$; an affine open $U\subseteq X_K$, an algebra map $\Gamma(X_K,U)\to F$ in a tower over $K$ whose spectrum composed with $U$'s inclusion is the $F$-point of $X_K$ obtained from $y$ through $e$; an element $\omega_U\in\bigwedge^d_{\Gamma(X_K,U)}$ of the Kähler presheaf on $U$ whose image in sections is $\omega|_U$; and a nonzero $a\in F$ with $\omega_U = a\,(db_1\wedge\cdots\wedge db_d)$ after base change to $\bigwedge^d_F\Omega_{F/K}$. Its invariant `n` is the normalised additive order $\operatorname{ord}_{\mathcal O}(a)\in\mathbb Z$.
--
--   `MinimalComponentData` is a finite non-empty family of readings whose structure morphisms are separated and quasi-compact, whose charts $e$ are isomorphisms, whose marked points are generic in the closed fibre (every point above the closed point is a specialisation of $y$), and which are pairwise inequivalent: for $c\neq c'$ no $R$-morphism from a neighbourhood of $y_c$ to $Y_{c'}$ agrees with the charts on generic fibres. Such data is `IsOmegaMinimal` when each $n(C_c)$ is least among the orders of all readings, and every reading whose order equals one of them admits, on a neighbourhood $W$ of its marked point, an open immersion over $R$ into some $Y_c$ carrying the marked point to $y_c$ and compatible with the two charts into $X_K$. Supplementary lemmas compute $n=1$ and $n=2$ when $a$ is the image of a uniformiser or of its square, and show that the orders of all members of $\omega$-minimal data coincide.
--
--   **Relation to Mathlib.** Mathlib has no notion of weak Néron model or of $\omega$-minimality; these structures are the project's own, expressed in terms of Mathlib's discrete valuation rings, height-one-spectrum valuations, Kähler differentials, exterior powers and scheme stalks, together with the project's presheaf-level exterior powers and determinant modules.
--
--   **Where it is used.** These notions set up the component-by-component bookkeeping used to produce weak Néron models of smooth $K$-group schemes over a discrete valuation ring, the minimality of the order of an invariant top form along a component being the criterion by which candidate models are compared and glued. This is part of the Néron-model infrastructure underlying the elliptic-curve input to the Frey–Serre–Ribet part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NeronModelInfra_OmegaMinimalComponentData.lean

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_SmoothnessDefect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace NeronModelInfra

section StalkAlgebra

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (y : Y)

theorem ofHom_stalkAlgebraMap_eq :
    CommRingCat.ofHom (stalkAlgebraMap f y) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial) ≫ f.stalkMap y := by
  ext r
  change stalkAlgebraMap f y r = _
  rw [stalkAlgebraMap_apply]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [Scheme.Hom.germ_stalkMap_apply]
  rfl

theorem fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra :
    letI := stalkAlgebra f y
    Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))) := by
  letI := stalkAlgebra f y
  change Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (stalkAlgebraMap f y))
  rw [ofHom_stalkAlgebraMap_eq, Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk f,
    Spec.fromSpecStalk_eq]

end StalkAlgebra

section Reading

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) (ω : Γ(gK.topDifferentials d, ⊤))

structure ComponentReading where

  Y : Scheme.{u}

  f : Y ⟶ Spec (CommRingCat.of R)

  smooth : Smooth f

  locallyOfFiniteType : LocallyOfFiniteType f

  e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK

  isOpenImmersion : IsOpenImmersion e.1

  y : Y

  hy : f.base y = IsLocalRing.closedPoint R

  hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y

  isDomain : IsDomain (Y.presheaf.stalk y)

  isDiscreteValuationRing : IsDiscreteValuationRing (Y.presheaf.stalk y)

  algebra : Algebra R (Y.presheaf.stalk y)

  halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))

  algebraK : Algebra K (FractionRing (Y.presheaf.stalk y))

  isScalarTower : IsScalarTower R K (FractionRing (Y.presheaf.stalk y))

  b : Module.Basis (Fin d) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R])

  U : XK.Opens

  hU : IsAffineOpen U

  algebraU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y))

  isScalarTowerU : letI := gK.sectionsAlgebra U
    IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y))

  hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫ hU.fromSpec =
    (schemeHomOverComp
      (pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
        (⟨Y.fromSpecStalk y, halg⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
      e).1

  ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U))

  hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω

  a : FractionRing (Y.presheaf.stalk y)

  ha : letI := gK.sectionsAlgebra U
    TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU =
      a • TopFormOrder.topFormMap R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) d
        (exteriorPower.ιMulti (Y.presheaf.stalk y) d b)

  ha0 : a ≠ 0

attribute [instance] ComponentReading.smooth ComponentReading.locallyOfFiniteType
  ComponentReading.isOpenImmersion ComponentReading.isDomain ComponentReading.isDiscreteValuationRing

variable {R K gK d ω}

def ComponentReading.n (T : ComponentReading R K gK d ω) : ℤ :=
  TopFormOrder.addOrd (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) T.a

end Reading

section Minimal

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) (ω : Γ(gK.topDifferentials d, ⊤))

structure MinimalComponentData where

  ι : Type u

  finite : Finite ι

  nonempty : Nonempty ι

  C : ι → ComponentReading R K gK d ω

  isSeparated : ∀ c, IsSeparated (C c).f

  quasiCompact : ∀ c, QuasiCompact (C c).f

  isIso : ∀ c, IsIso (C c).e.1

  hgen : ∀ c (y' : ↥(C c).Y), (C c).f.base y' = IsLocalRing.closedPoint R → (C c).y ⤳ y'

  inequiv : ∀ c c', c ≠ c' → ∀ (U : ((C c).Y).Opens), (C c).y ∈ U →
    ∀ u : SchemeHomOver (U.ι ≫ (C c).f) (C c').f,
      (genericFibreRestrict R K (C c').f (U.ι ≫ (C c).f) u).1 ≫ (C c').e.1 ≠
        (genericFibreRestrict R K (C c).f (U.ι ≫ (C c).f) ⟨U.ι, rfl⟩).1 ≫ (C c).e.1

attribute [instance] MinimalComponentData.finite MinimalComponentData.nonempty

variable {R K gK d ω}

def MinimalComponentData.IsOmegaMinimal (D : MinimalComponentData R K gK d ω) : Prop :=
  (∀ (c : D.ι) (T : ComponentReading R K gK d ω), (D.C c).n ≤ T.n) ∧
  (∀ T : ComponentReading R K gK d ω, (∃ c : D.ι, T.n = (D.C c).n) →
    ∃ (c : D.ι) (W : T.Y.Opens) (hyW : T.y ∈ W) (ε : SchemeHomOver (W.ι ≫ T.f) (D.C c).f),
      IsOpenImmersion ε.1 ∧ ε.1.base ⟨T.y, hyW⟩ = (D.C c).y ∧
      (genericFibreRestrict R K (D.C c).f (W.ι ≫ T.f) ε).1 ≫ (D.C c).e.1 =
        (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1)

end Minimal

section Gates

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ} {ω : Γ(gK.topDifferentials d, ⊤)}

theorem ComponentReading.n_eq_one_of_a_eq_uniformizer (T : ComponentReading R K gK d ω)
    (ϖ : T.Y.presheaf.stalk T.y) (hϖ : IsLocalRing.maximalIdeal (T.Y.presheaf.stalk T.y) = Ideal.span {ϖ})
    (h : T.a = algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) ϖ) :
    T.n = 1 := by
  unfold ComponentReading.n
  rw [h]
  exact TopFormOrder.addOrd_uniformizer _ _ ϖ hϖ

theorem ComponentReading.n_eq_two_of_a_eq_uniformizer_sq (T : ComponentReading R K gK d ω)
    (ϖ : T.Y.presheaf.stalk T.y) (hϖ : IsLocalRing.maximalIdeal (T.Y.presheaf.stalk T.y) = Ideal.span {ϖ})
    (h : T.a = algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) ϖ ^ 2) :
    T.n = 2 := by
  unfold ComponentReading.n
  rw [h]
  exact TopFormOrder.addOrd_uniformizer_sq _ _ ϖ hϖ

theorem MinimalComponentData.IsOmegaMinimal.n_eq (D : MinimalComponentData R K gK d ω)
    (hD : D.IsOmegaMinimal) (c c' : D.ι) : (D.C c).n = (D.C c').n :=
  le_antisymm (hD.1 c (D.C c')) (hD.1 c' (D.C c))

end Gates

end NeronModelInfra

end

/--
info: 'NeronModelInfra.fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra

/--
info: 'NeronModelInfra.ComponentReading.n_eq_one_of_a_eq_uniformizer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.ComponentReading.n_eq_one_of_a_eq_uniformizer

/--
info: 'NeronModelInfra.MinimalComponentData.IsOmegaMinimal.n_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.MinimalComponentData.IsOmegaMinimal.n_eq


