-- Prove2me | Definitions.Def_ModularCurve_ShimuraCovering
-- name    : ModularCurve_ShimuraCovering
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/d657d2e3-bb65-5022-8307-1260ab07183b
-- title:
--   Shimura covering data for X0​(p) and its kernel
-- statement:
--   Throughout, function fields are realised as intermediate fields of $\mathbb{Q} \subseteq \mathbb{Q}((q))$, and `laurentBaseChange L F` denotes the base change of such an $F$ to Laurent series with coefficients in $L$. The helper `inclusionBar` turns an inclusion $F_0 \le F_1$ into the induced $L$-algebra map of base changes (it is the inclusion of intermediate fields, compatible with the underlying Laurent series, as `coe_inclusionBar` records), and `ramificationIndexAlong_inclusionBar_refl` states that the ramification index of the map induced by $F_0 \le F_0$ is $1$ at every place.
--
--   For a prime $p$, `ShimuraCoveringData p` is a structure bundling: an intermediate field `field` of $\mathbb{Q}((q))$ containing `modularFunctionFieldFull p` (the field generated over $\mathbb{Q}$ by the $q$-expansions $q \mapsto q^d$ applied to the $j$-series, for $d \mid p$); a monoid homomorphism `deck` from $(\mathbb{Z}/p)^{\times}$ to the $\mathbb{Q}$-algebra automorphisms of `field`; two clauses saying that every `deck d` fixes each element whose Laurent series lies in the base field, and conversely that an element fixed by all `deck d` lies in the base field (so the base is exactly the fixed field of the image); the requirement that the image of `deck` have cardinality `eisensteinNumerator p` $= (p-1)/\gcd(p-1,12)$; and an unramifiedness clause asserting that the ramification index along the base-changed inclusion is $1$ at every place of the base change of `field` to $\overline{\mathbb{Q}}$. Existence of such data at a given prime is not asserted here.
--
--   Given such a $D$ and a prime $\ell$, `LiftData ℓ` records a compatible lift of the deck action to the compositum of `D.field` with `modularFunctionFieldFull (p\ell)`: the compositum is unchanged when `D.field` is replaced by its image under the $\ell$-th $q$-expansion operator `qExpandₐ ℓ`; a homomorphism `deckUp` from $(\mathbb{Z}/p)^{\times}$ to the $\mathbb{Q}$-algebra automorphisms of that compositum; and the compatibilities that `deckUp d` restricts to `D.deck d` on `D.field`, fixes `modularFunctionFieldFull (p\ell)` pointwise, and commutes with `qExpand ℚ ℓ` on elements of `D.field`.
--
--   Finally, `fieldBar` is the base change of `D.field` to $\overline{\mathbb{Q}}$, `coverHom` the induced map from `modularFunctionFieldBar p` to it, `KernelInputs` the conjunction (as an existential over the relevant witnesses) of integrality of `coverHom`, the predicate `HasPrincipalDivisors` for `fieldBar`, and `FundamentalIdentityAlong` for `coverHom`; and `kernel` is the additive subgroup of `JZero p` given by the kernel of the pullback map `Pic0.pullbackHom` along `coverHom` when `KernelInputs` holds, and $\bot$ otherwise, the latter case being `kernel_of_not`.
--
--   **Relation to Mathlib.** Mathlib has no modular curves, no Shimura covering and no degree-zero divisor class group of a function field; the notions used here (`laurentBaseChange`, places and ramification indices along an algebra map, `Pic0` and its pullback, `JZero`) are the project's own, built on Mathlib's `IntermediateField`, `LaurentSeries` and `HahnSeries`.
--
--   **Where it is used.** The kernel attached to such a covering is the object that the project's predicate `IsShimuraSubgroup` is to be verified for: a $\mu$-type subgroup of $J_0(p)$ of order $(p-1)/\gcd(p-1,12)$ on which the Hecke operators act through the Eisenstein system. That input is used in the level-lowering step, where the Shimura subgroup controls the comparison of $p$-torsion in Jacobians of different levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ShimuraCovering.lean

import Definitions.Def_ModularCurve_ShimuraSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve

namespace ModularCurve

section Supply

variable (L : Type*) [Field L] [Algebra ℚ L]

private theorem laurentBaseChange_mono_of_le {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

def inclusionBar {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) :
    laurentBaseChange L F₀ →ₐ[L] laurentBaseChange L F₁ :=
  IntermediateField.inclusion (laurentBaseChange_mono_of_le L h)

@[simp]
theorem coe_inclusionBar {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁)
    (x : laurentBaseChange L F₀) :
    (inclusionBar L h x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

theorem ramificationIndexAlong_inclusionBar_refl (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (w : Place L (laurentBaseChange L F₀)) :
    Place.ramificationIndexAlong (inclusionBar L (le_refl F₀)) w = 1 := by
  classical
  unfold Place.ramificationIndexAlong Place.ramificationIndex
  have hid : ∀ f : laurentBaseChange L F₀, inclusionBar L (le_refl F₀) f = f :=
    fun f => Subtype.ext (coe_inclusionBar L (le_refl F₀) f)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have h1 : (1 : ℕ) ∈ {n : ℕ | 0 < n ∧ ∃ f : laurentBaseChange L F₀, f ≠ 0 ∧
      w.ord (algebraMap (laurentBaseChange L F₀) (laurentBaseChange L F₀) f) = n} := by
    refine ⟨Nat.one_pos, (π : laurentBaseChange L F₀), ?_, ?_⟩
    · simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    · show w.ord (inclusionBar L (le_refl F₀) π) = 1
      rw [hid, w.ord_coe_irreducible hπ]
  refine le_antisymm (Nat.sInf_le h1) ?_
  exact le_csInf ⟨1, h1⟩ fun n hn => hn.1

end Supply

section Carrier

variable (p : ℕ) [Fact p.Prime]

structure ShimuraCoveringData where

  field : IntermediateField ℚ (LaurentSeries ℚ)

  base_le : modularFunctionFieldFull p ≤ field

  deck : (ZMod p)ˣ →* (field ≃ₐ[ℚ] field)

  deck_apply_eq_self : ∀ (d : (ZMod p)ˣ) (x : field),
    (x : LaurentSeries ℚ) ∈ modularFunctionFieldFull p → deck d x = x

  mem_base_of_forall_deck_apply_eq : ∀ x : field,
    (∀ d : (ZMod p)ˣ, deck d x = x) → (x : LaurentSeries ℚ) ∈ modularFunctionFieldFull p

  card_range_deck : Nat.card deck.range = eisensteinNumerator p

  unramified : ∀ w : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) field),
    Place.ramificationIndexAlong (inclusionBar (AlgebraicClosure ℚ) base_le) w = 1

end Carrier

namespace ShimuraCoveringData

variable {p : ℕ} [Fact p.Prime] (D : ShimuraCoveringData p)

structure LiftData (ℓ : ℕ) [Fact ℓ.Prime] where

  sup_eq_map_sup : D.field ⊔ modularFunctionFieldFull (p * ℓ)
      = D.field.map (qExpandₐ ℓ) ⊔ modularFunctionFieldFull (p * ℓ)

  deckUp : (ZMod p)ˣ →* (↥(D.field ⊔ modularFunctionFieldFull (p * ℓ))
      ≃ₐ[ℚ] ↥(D.field ⊔ modularFunctionFieldFull (p * ℓ)))

  coe_deckUp_inclusion : ∀ (d : (ZMod p)ˣ) (x : D.field),
    (deckUp d (IntermediateField.inclusion le_sup_left x) : LaurentSeries ℚ)
      = (D.deck d x : LaurentSeries ℚ)

  deckUp_apply_eq_self : ∀ (d : (ZMod p)ˣ) (y : ↥(D.field ⊔ modularFunctionFieldFull (p * ℓ))),
    (y : LaurentSeries ℚ) ∈ modularFunctionFieldFull (p * ℓ) → deckUp d y = y

  coe_deckUp_qExpand : ∀ (d : (ZMod p)ˣ) (x : D.field)
    (hx : qExpand ℚ ℓ (x : LaurentSeries ℚ) ∈ D.field ⊔ modularFunctionFieldFull (p * ℓ)),
    (deckUp d ⟨qExpand ℚ ℓ (x : LaurentSeries ℚ), hx⟩ : LaurentSeries ℚ)
      = qExpand ℚ ℓ (D.deck d x : LaurentSeries ℚ)

abbrev fieldBar : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) D.field

def coverHom : modularFunctionFieldBar p →ₐ[AlgebraicClosure ℚ] D.fieldBar :=
  inclusionBar (AlgebraicClosure ℚ) D.base_le

@[simp]
theorem coe_coverHom (x : modularFunctionFieldBar p) :
    (D.coverHom x : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) :=
  coe_inclusionBar _ _ x

def KernelInputs : Prop :=
  ∃ (hint : D.coverHom.toRingHom.IsIntegral)
    (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) D.fieldBar),
    FundamentalIdentityAlong (AlgebraicClosure ℚ) D.coverHom hint

open Classical in

def kernel : AddSubgroup (JZero p) :=
  if h : D.KernelInputs then
    letI := algebraAlong D.coverHom
    haveI := isScalarTower_along D.coverHom
    haveI := isIntegral_along D.coverHom h.1
    haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) D.fieldBar := h.2.1
    haveI : FundamentalIdentity (AlgebraicClosure ℚ) (modularFunctionFieldBar p) D.fieldBar :=
      h.2.2
    (Pic0.pullbackHom (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p) D.fieldBar).ker
  else ⊥

theorem kernel_of_not (h : ¬ D.KernelInputs) : D.kernel = ⊥ := by
  rw [kernel, dif_neg h]

end ShimuraCoveringData

end ModularCurve

end


