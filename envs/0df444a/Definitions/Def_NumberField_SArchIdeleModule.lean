-- Prove2me | Definitions.Def_NumberField_SArchIdeleModule
-- name    : NumberField_SArchIdeleModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/af2f3d3d-138c-54ef-a458-195439746260
-- title:
--   Restricted S∪∞ idèle module as a Galois representation
-- statement:
--   Throughout, $E\subseteq K$ are number fields with $K/E$ given by an algebra structure, $G=K\simeq_{\mathrm{alg}[E]}K$ is the group of $E$-algebra automorphisms of $K$, and $S$ is a finite set of height-one primes of $\mathcal O_E$. The index type `Index` is $\{v\in S\}\sqcup\{\text{infinite places of }E\}$, i.e. the places of $S$ together with the archimedean ones, with no factor at the finite places outside $S$. The family `fibre` assigns to $v\in S$ the coinduced representation $\mathrm{Coind}$ from the decomposition subgroup $D$ of the chosen prime $w(v)$ of $\mathcal O_K$ above $v$ (the stabiliser of the valuation ring) to $G$, of the $\mathbb Z$-linearised multiplicative group $(K_{w(v)})^\times$ of the adic completion; to an infinite place $v$ it assigns the corresponding coinduction from the stabiliser in $G$ of the chosen infinite place above $v$ of the units of its completion. Two lemmas record these values in their `Rep.coind` form. The object `obj` is the product of this family in $\mathrm{Rep}\,\mathbb Z\,G$, with $G$ acting coordinatewise, and `proj` its projections.
--
--   Two morphisms out of and into it are defined. `toSIdele` maps `obj` to the full $S$-idèle module of the companion module, componentwise by the identity (the relevant projection) at the places of $S$ and at the infinite places, and by $0$ at the finite places outside $S$; `toSIdele_injective` states that the underlying map is injective, and three lemmas give its coordinates. `diagS` maps the $S$-unit representation $\mathrm{sUnitsRep}$ (the subrepresentation of $\mathrm{Additive}\,K^\times$ of units all of whose $G$-conjugates have valuation $1$ at every prime of $\mathcal O_K$ lying under a prime not in $S$) into `obj`, using at $v\in S$ the local diagonal $\mathrm{diagIn}$, $x\mapsto (g\mapsto g\cdot x$ viewed in $K_{w(v)}^\times)$, and at the infinite places the archimedean analogue $\mathrm{diagInf}$. Further lemmas give the coordinates of `diagS` and compare `toSIdele` composed after `diagS` with the full diagonal of the $S$-idèle module: the two agree at the places of $S$ and at the infinite places, while outside $S$ the composite has coordinate $0$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here — adic and archimedean completions of number fields, coinduced representations `Rep.coind` — but not the idèle modules themselves; the product of a family of representations (`GroupCohomology.RepPi`) and these $S$-restricted idèle modules with their diagonal and comparison maps are the project's own.
--
--   **Where it is used.** This restricted product, indexed only by $S$ and the archimedean places, is the module against which global duality with ramification restricted to $S$ is computed, so that the relevant $\mathrm{Ext}$-groups decompose as a finite sum of local terms over $S\cup\infty$; the maps `toSIdele` and `diagS` relate it to the full $S$-idèle module and its idèle class quotient, which carry the Galois-cohomological input to the deformation theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_SArchIdeleModule.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

namespace NumberField.SArchIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
variable (S : Finset (HeightOneSpectrum (𝓞 E)))

abbrev Index : Type := {v // v ∈ S} ⊕ InfinitePlace E

noncomputable def fibre : Index E S → Rep ℤ (K ≃ₐ[E] K) :=
  Sum.elim (fun v => NumberField.FiniteSIdele.fibre E K S (Sum.inl v)) (NumberField.ArchIdele.fibre E K)

@[simp] theorem fibre_inl (v : {v // v ∈ S}) : fibre E K S (Sum.inl v) = NumberField.FiniteSIdele.fibre E K S (Sum.inl v) := rfl

@[simp] theorem fibre_inr (v : InfinitePlace E) : fibre E K S (Sum.inr v) = NumberField.ArchIdele.fibre E K v := rfl

theorem fibre_inl_eq_coind (v : {v // v ∈ S}) :
    fibre E K S (Sum.inl v) =
      Rep.coind (NumberField.FiniteSIdele.D E K v.1).subtype (NumberField.FiniteSIdele.localUnits E K v.1) := rfl

theorem fibre_inr_eq_coind (v : InfinitePlace E) :
    fibre E K S (Sum.inr v) =
      Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
        (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)) := rfl

noncomputable abbrev obj : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepPi.obj (fibre E K S)

noncomputable abbrev proj (i : Index E S) : obj E K S ⟶ fibre E K S i := GroupCohomology.RepPi.proj (fibre E K S) i

noncomputable def toSIdeleComponent : (i : NumberField.SIdele.Index E S) → (obj E K S ⟶ NumberField.SIdele.fibre E K S i)
  | Sum.inl (Sum.inl v) => proj E K S (Sum.inl v)
  | Sum.inl (Sum.inr _) => 0
  | Sum.inr v => proj E K S (Sum.inr v)

noncomputable def toSIdele : obj E K S ⟶ NumberField.SIdele.obj E K S :=
  GroupCohomology.RepPi.lift (NumberField.SIdele.fibre E K S) (toSIdeleComponent E K S)

@[simp] theorem toSIdele_hom_apply_inl_inl (x : obj E K S) (v : {v // v ∈ S}) :
    (toSIdele E K S).hom x (Sum.inl (Sum.inl v)) = x (Sum.inl v) := rfl

@[simp] theorem toSIdele_hom_apply_inl_inr (x : obj E K S) (v : {v // v ∉ S}) :
    (toSIdele E K S).hom x (Sum.inl (Sum.inr v)) = 0 := rfl

@[simp] theorem toSIdele_hom_apply_inr (x : obj E K S) (v : InfinitePlace E) :
    (toSIdele E K S).hom x (Sum.inr v) = x (Sum.inr v) := rfl

theorem toSIdele_injective : Function.Injective (toSIdele E K S).hom := by
  intro x y h
  funext i
  cases i with
  | inl v => exact congrFun h (Sum.inl (Sum.inl v))
  | inr v => exact congrFun h (Sum.inr v)

noncomputable def diagSComponent : (i : Index E S) → (NumberField.SUnits.sUnitsRep E K S ⟶ fibre E K S i)
  | Sum.inl v => NumberField.SUnits.diagIn E K S v
  | Sum.inr v => NumberField.SIdele.diagInf E K S v

noncomputable def diagS : NumberField.SUnits.sUnitsRep E K S ⟶ obj E K S :=
  GroupCohomology.RepPi.lift (fibre E K S) (diagSComponent E K S)

theorem diagS_hom_apply_inl (x : NumberField.SUnits.sUnitsRep E K S) (v : {v // v ∈ S}) :
    (diagS E K S).hom x (Sum.inl v) = (NumberField.SUnits.diagIn E K S v).hom x := rfl

theorem diagS_hom_apply_inr (x : NumberField.SUnits.sUnitsRep E K S) (v : InfinitePlace E) :
    (diagS E K S).hom x (Sum.inr v) = (NumberField.SIdele.diagInf E K S v).hom x := rfl

theorem toSIdele_diagS_apply_inl_inl (x : NumberField.SUnits.sUnitsRep E K S) (v : {v // v ∈ S}) :
    (toSIdele E K S).hom ((diagS E K S).hom x) (Sum.inl (Sum.inl v)) = (NumberField.SIdele.diag E K S).hom x (Sum.inl (Sum.inl v)) := rfl

theorem toSIdele_diagS_apply_inr (x : NumberField.SUnits.sUnitsRep E K S) (v : InfinitePlace E) :
    (toSIdele E K S).hom ((diagS E K S).hom x) (Sum.inr v) = (NumberField.SIdele.diag E K S).hom x (Sum.inr v) := rfl

theorem toSIdele_diagS_apply_inl_inr (x : NumberField.SUnits.sUnitsRep E K S) (v : {v // v ∉ S}) :
    (toSIdele E K S).hom ((diagS E K S).hom x) (Sum.inl (Sum.inr v)) = 0 := rfl

end NumberField.SArchIdele


