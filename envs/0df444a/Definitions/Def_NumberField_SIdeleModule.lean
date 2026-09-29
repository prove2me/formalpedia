-- Prove2me | Definitions.Def_NumberField_SIdeleModule
-- name    : NumberField_SIdeleModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/aad02bbf-4c90-50a4-ad24-f8a988cb11f0
-- title:
--   The full S-idèle module and its class quotient
-- statement:
--   Throughout, $E$ and $K$ are number fields with $K$ an $E$-algebra, $G = K \simeq_{\mathrm{alg}[E]} K$ is the group of $E$-algebra automorphisms of $K$, and $S$ is a finite set of height-one primes of $\mathcal{O}_E$. The archimedean ingredients come first: for an infinite place $v$ of $E$, `locInf` is the structure map $K \to$ (completion of $K$ at the chosen place $w(v) =$ `ArchIdele.above E K v` above $v$), `locInf_apply` identifies it with the canonical coercion, and `smul_locInf` says that for $\sigma$ in the decomposition subgroup (the stabiliser of $w(v)$ in $G$) one has $\sigma \cdot \mathrm{loc}(x) = \mathrm{loc}(\sigma x)$. On the $S$-unit module `SUnits.sUnitsRep E K S` — the $\mathbb{Z}$-module $\mathrm{Additive}$ of the subgroup of $x \in K^\times$ with $w(\sigma x) = 1$ for all $\sigma \in G$ and all finite $w$ of $K$ lying under a prime outside $S$, with $G$ acting by translation — `diagFunInf` is the $\mathbb{Z}$-linear map $x \mapsto (g \mapsto \mathrm{loc}_{w(v)}(g \cdot x))$ into functions $G \to \mathrm{Additive}\,(K_{w(v)})^\times$; `diagFunInf_mem_coindV` checks the equivariance condition cutting out the coinduced submodule, and `diagInf` packages the result as a morphism in $\mathrm{Rep}\,\mathbb{Z}\,G$ into `ArchIdele.fibre E K v`, the coinduction from the decomposition subgroup of $(K_{w(v)})^\times$.
--
--   The index set `Index` is `FiniteSIdele.Index E S ⊕ InfinitePlace E`, i.e. $\{v \in S\} \sqcup \{v \notin S\} \sqcup \{v \mid \infty\}$, and `fibre` assigns to these, respectively, the coinduced modules of $(K_{w(v)})^\times$, of $\mathcal{O}_{w(v)}^\times$ and of $(K_{w(v)})^\times$ at the archimedean place. The $S$-idèle module `obj` is the single product representation over `Index` of these fibres; `toFinite` and `toArch` are the morphisms onto the finite and archimedean partial products obtained from the coordinate projections. The diagonal `diag` assembles the finite components of `SUnits.diagComponent` with the archimedean `diagInf`, and `diag_toFinite` records that $\mathrm{diag}$ followed by `toFinite` is the finite diagonal `SUnits.diag`. Finally `classObj` is the quotient of `obj` by the image of `diag`, with the induced $G$-representation, `toClass` the quotient morphism, `toClass_hom_apply_eq_zero_iff` the criterion that a class vanishes exactly when the element lies in the image of the diagonal, and `classSeq` the short complex $K_S \to J_{K,S} \to C_{K,S}$.
--
--   **Relation to Mathlib.** The local factors use Mathlib's $v$-adic completions and `InfinitePlace.Completion`, but the $S$-idèle module is not Mathlib's adèle or idèle ring: it is built here as an explicit product, indexed by places of the base field $E$, of modules coinduced from decomposition subgroups, so that it is a product of $G$-representations place by place. Products and cokernels in $\mathrm{Rep}\,\mathbb{Z}\,G$ are taken in the project's explicit presentations `GroupCohomology.RepPi` and `GroupCohomology.RepCokernel`.
--
--   **Where it is used.** These modules are the carriers for the cohomological computations of class field theory used in the argument: the explicit product form makes Shapiro's lemma and the product formulae for Tate cohomology applicable factor by factor, leading to the Herbrand quotient of $J_{K,S}$ and, for cyclic $K/E$ and $S$ large enough, of the $S$-idèle class module $C_{K,S}$, which is what the first inequality needs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_SIdeleModule.lean

import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_NumberField_SIdeleClassModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

namespace NumberField.SIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

noncomputable abbrev locInf (v : InfinitePlace E) : K →+* (NumberField.ArchIdele.above E K v).Completion := algebraMap K _

theorem locInf_apply (v : InfinitePlace E) (x : K) :
    locInf E K v x = ((WithAbs.equiv (NumberField.ArchIdele.above E K v).1).symm x : (NumberField.ArchIdele.above E K v).Completion) := rfl

theorem smul_locInf (v : InfinitePlace E) (σ : NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)) (x : K) :
    σ • locInf E K v x = locInf E K v ((σ : K ≃ₐ[E] K) x) := by
  rw [NumberField.InfPlaceDecomp.smul_def, locInf_apply, locInf_apply, NumberField.InfPlaceDecomp.actRingEquiv_coe, WithAbs.congr_apply]
  rfl

variable (S : Finset (HeightOneSpectrum (𝓞 E)))

noncomputable def diagFunInf (v : InfinitePlace E) :
    NumberField.SUnits.sUnitsRep E K S →ₗ[ℤ] ((K ≃ₐ[E] K) → Additive ((NumberField.ArchIdele.above E K v).Completion)ˣ) where
  toFun x g := Additive.ofMul (Units.map (locInf E K v).toMonoidHom (g • NumberField.SUnits.val E K S x))
  map_add' x y := by
    funext g
    change Additive.ofMul (Units.map (locInf E K v).toMonoidHom (g • (NumberField.SUnits.val E K S x * NumberField.SUnits.val E K S y))) = _
    rw [smul_mul', map_mul, ofMul_mul]
    rfl
  map_smul' n x := by
    funext g
    change Additive.ofMul (Units.map (locInf E K v).toMonoidHom (g • (NumberField.SUnits.val E K S x ^ n))) = _
    rw [smul_zpow', map_zpow, ofMul_zpow]
    rfl

theorem diagFunInf_apply (v : InfinitePlace E) (x : NumberField.SUnits.sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    diagFunInf E K S v x g = Additive.ofMul (Units.map (locInf E K v).toMonoidHom (g • NumberField.SUnits.val E K S x)) := rfl

theorem diagFunInf_mem_coindV (v : InfinitePlace E) (x : NumberField.SUnits.sUnitsRep E K S) :
    diagFunInf E K S v x ∈ Representation.coindV (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
      (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)).ρ := by
  intro d h
  change Additive.ofMul (Units.map (locInf E K v).toMonoidHom (((d : K ≃ₐ[E] K) * h) • NumberField.SUnits.val E K S x)) =
    Additive.ofMul (d • Units.map (locInf E K v).toMonoidHom (h • NumberField.SUnits.val E K S x))
  rw [mul_smul]
  congr 1
  ext : 1
  exact (smul_locInf E K v d _).symm

noncomputable def diagInf (v : InfinitePlace E) :
    NumberField.SUnits.sUnitsRep E K S ⟶ NumberField.ArchIdele.fibre E K v :=
  Rep.ofHom ⟨(diagFunInf E K S v).codRestrict _ (diagFunInf_mem_coindV E K S v), fun g => LinearMap.ext fun x =>
    Subtype.ext (funext fun h => by
      change diagFunInf E K S v ((NumberField.SUnits.sUnitsRep E K S).ρ g x) h = diagFunInf E K S v x (h * g)
      rw [diagFunInf_apply, diagFunInf_apply, NumberField.SUnits.val_rho, mul_smul])⟩

theorem diagInf_hom_apply_apply (v : InfinitePlace E) (x : NumberField.SUnits.sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    ((diagInf E K S v).hom x).1 g = Additive.ofMul (Units.map (locInf E K v).toMonoidHom (g • NumberField.SUnits.val E K S x)) := rfl

abbrev Index : Type := NumberField.FiniteSIdele.Index E S ⊕ InfinitePlace E

noncomputable def fibre : Index E S → Rep ℤ (K ≃ₐ[E] K) :=
  Sum.elim (NumberField.FiniteSIdele.fibre E K S) (NumberField.ArchIdele.fibre E K)

@[simp] theorem fibre_inl (i : NumberField.FiniteSIdele.Index E S) : fibre E K S (Sum.inl i) = NumberField.FiniteSIdele.fibre E K S i := rfl

@[simp] theorem fibre_inr (v : InfinitePlace E) : fibre E K S (Sum.inr v) = NumberField.ArchIdele.fibre E K v := rfl

noncomputable abbrev obj : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepPi.obj (fibre E K S)

noncomputable def toFinite : obj E K S ⟶ NumberField.FiniteSIdele.obj E K S :=
  GroupCohomology.RepPi.lift _ fun i => GroupCohomology.RepPi.proj (fibre E K S) (Sum.inl i)

noncomputable def toArch : obj E K S ⟶ NumberField.ArchIdele.obj E K :=
  GroupCohomology.RepPi.lift _ fun v => GroupCohomology.RepPi.proj (fibre E K S) (Sum.inr v)

@[simp] theorem toFinite_hom_apply (x : obj E K S) (i : NumberField.FiniteSIdele.Index E S) : (toFinite E K S).hom x i = x (Sum.inl i) := rfl

@[simp] theorem toArch_hom_apply (x : obj E K S) (v : InfinitePlace E) : (toArch E K S).hom x v = x (Sum.inr v) := rfl

noncomputable def diagComponent : (i : Index E S) → (NumberField.SUnits.sUnitsRep E K S ⟶ fibre E K S i)
  | Sum.inl i => NumberField.SUnits.diagComponent E K S i
  | Sum.inr v => diagInf E K S v

noncomputable def diag : NumberField.SUnits.sUnitsRep E K S ⟶ obj E K S :=
  GroupCohomology.RepPi.lift (fibre E K S) (diagComponent E K S)

theorem diag_hom_apply_inl (x : NumberField.SUnits.sUnitsRep E K S) (i : NumberField.FiniteSIdele.Index E S) :
    (diag E K S).hom x (Sum.inl i) = (NumberField.SUnits.diagComponent E K S i).hom x := rfl

theorem diag_hom_apply_inr (x : NumberField.SUnits.sUnitsRep E K S) (v : InfinitePlace E) :
    (diag E K S).hom x (Sum.inr v) = (diagInf E K S v).hom x := rfl

theorem diag_toFinite : diag E K S ≫ toFinite E K S = NumberField.SUnits.diag E K S :=
  GroupCohomology.RepPi.hom_ext _ fun i => by
    cases i <;> rfl

noncomputable abbrev classObj : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepCokernel.obj (diag E K S)

noncomputable abbrev toClass : obj E K S ⟶ classObj E K S := GroupCohomology.RepCokernel.π (diag E K S)

theorem toClass_hom_apply_eq_zero_iff (y : obj E K S) :
    (toClass E K S).hom y = 0 ↔ y ∈ Set.range (diag E K S).hom :=
  GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff (diag E K S) y

noncomputable abbrev classSeq : ShortComplex (Rep ℤ (K ≃ₐ[E] K)) := GroupCohomology.RepCokernel.seq (diag E K S)

end NumberField.SIdele


