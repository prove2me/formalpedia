-- Prove2me | Definitions.Def_NumberField_FiniteSIdeleModule
-- name    : NumberField_FiniteSIdeleModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/c700d40b-7d8d-5473-95c0-c300223ad5bb
-- title:
--   Finite S-idèle Galois module from coinduced local unit groups
-- statement:
--   Throughout, $E$ and $K$ are number fields with $K$ an $E$-algebra, and $G = K \simeq_{\mathrm{alg}[E]} K$ is the group of $E$-algebra automorphisms of $K$. For a finite place $v$ of $E$, i.e. a point $v$ of the height-one spectrum of $\mathcal{O}_E$, the abbreviation `D` is the decomposition subgroup of $G$ attached to the chosen place $w(v)$ of $K$ above $v$ (the place produced by [`NumberField.PlaceAbove.above`](../def/NumberField_PlaceAbove.html#L27), characterised by the fact that the contraction of its prime along $\mathcal{O}_E \to \mathcal{O}_K$ is $v$), namely the stabiliser in $G$ of the valuation subring of the $w(v)$-adic valuation on $K$. Two local modules over this subgroup are then formed out of the multiplicative-distributive actions of $D$ on the unit groups of the $w(v)$-adic completion and of its valuation ring: `localUnits` is $K_{w(v)}^{\times}$ and `localIntegerUnits` is $\mathcal{O}_{w(v)}^{\times}$, each regarded as an object of `Rep ℤ (D E K v)` through its additive copy, and `integerUnitsToUnits` is the morphism of such representations induced by the inclusion $\mathcal{O}_{w(v)}^{\times} \hookrightarrow K_{w(v)}^{\times}$ (with a lemma identifying it on elements with `Units.map` of the subring inclusion).
--
--   Given a finite set $S$ of finite places of $E$, `Index` is the index type $\{v \in S\} \sqcup \{v \notin S\}$ and `fibre` assigns to an index the $G$-representation coinduced along $D \le G$ from $K_{w(v)}^{\times}$ in the first case and from $\mathcal{O}_{w(v)}^{\times}$ in the second (two computation lemmas record these two values). Finally `obj` is the single product of this family taken in $\mathbb{Z}$-linear representations of $G$: the module of all functions on the index type with the componentwise $G$-action. So the finite $S$-idèle module is realised as one product over places of the base field, with coinduced local factors, rather than as a product over places of $K$.
--
--   **Relation to Mathlib.** The local factors and the coinduction use Mathlib's `Rep.ofMulDistribMulAction` and `Rep.coind`; the $D$-action on the adic completion and on its unit groups comes from the project's place-decomposition module, and the product over the index type is taken with the project's explicit construction [`GroupCohomology.RepPi.obj`](../def/GroupCohomology_RepPi.html#L21), whose underlying representation is the pointwise action on a dependent function type.
--
--   **Where it is used.** This module supplies the finite part of the $S$-idèle group as a Galois module, in the shape needed for cohomological computations: because the product is indexed by places of the base field with coinduced factors, Shapiro's lemma applies factor by factor. It is used in the parts of the tree developing the Galois cohomology of idèle and idèle class groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_FiniteSIdeleModule.lean

import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

namespace NumberField.FiniteSIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

noncomputable abbrev D (v : HeightOneSpectrum (𝓞 E)) : Subgroup (K ≃ₐ[E] K) :=
  NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)

section local_modules

noncomputable abbrev localUnits (v : HeightOneSpectrum (𝓞 E)) : Rep ℤ (D E K v) :=
  Rep.ofMulDistribMulAction (D E K v) ((NumberField.PlaceAbove.above E K v).adicCompletion K)ˣ

noncomputable abbrev localIntegerUnits (v : HeightOneSpectrum (𝓞 E)) : Rep ℤ (D E K v) :=
  Rep.ofMulDistribMulAction (D E K v) ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K)ˣ

set_option synthInstance.maxHeartbeats 200000 in

noncomputable def integerUnitsToUnits (v : HeightOneSpectrum (𝓞 E)) : localIntegerUnits E K v ⟶ localUnits E K v :=
  Rep.ofHom ⟨(Units.map ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K).subtype.toMonoidHom).toAdditive.toIntLinearMap,
    fun _ => rfl⟩

set_option synthInstance.maxHeartbeats 200000 in
theorem integerUnitsToUnits_hom_apply (v : HeightOneSpectrum (𝓞 E)) (u : ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K)ˣ) :
    Additive.toMul ((integerUnitsToUnits E K v).hom (Additive.ofMul u))
      = Units.map ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K).subtype.toMonoidHom u := rfl

end local_modules

abbrev Index (S : Finset (HeightOneSpectrum (𝓞 E))) : Type := {v // v ∈ S} ⊕ {v // v ∉ S}

noncomputable def fibre (S : Finset (HeightOneSpectrum (𝓞 E))) : Index E S → Rep ℤ (K ≃ₐ[E] K) :=
  Sum.elim (fun v => Rep.coind (D E K v.1).subtype (localUnits E K v.1))
    (fun v => Rep.coind (D E K v.1).subtype (localIntegerUnits E K v.1))

@[simp] theorem fibre_inl (S : Finset (HeightOneSpectrum (𝓞 E))) (v : {v // v ∈ S}) :
    fibre E K S (Sum.inl v) = Rep.coind (D E K v.1).subtype (localUnits E K v.1) := rfl

@[simp] theorem fibre_inr (S : Finset (HeightOneSpectrum (𝓞 E))) (v : {v // v ∉ S}) :
    fibre E K S (Sum.inr v) = Rep.coind (D E K v.1).subtype (localIntegerUnits E K v.1) := rfl

noncomputable abbrev obj (S : Finset (HeightOneSpectrum (𝓞 E))) : Rep ℤ (K ≃ₐ[E] K) :=
  GroupCohomology.RepPi.obj (fibre E K S)

end NumberField.FiniteSIdele


