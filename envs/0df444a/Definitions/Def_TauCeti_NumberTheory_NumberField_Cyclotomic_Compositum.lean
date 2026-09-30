-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Compositum
-- name    : TauCeti_NumberTheory_NumberField_Cyclotomic_Compositum
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:55:31.171619+00:00
-- url     : https://prove2.me/theorems/53fa8c4e-a198-4f70-82f2-9c1b877fc5f4
-- title:
--   The cyclotomic compositum M = L(μ_m) and its joint restriction isomorphism
-- statement:
--   For a Galois extension $L/K$ and a cyclotomic compositum $M=L(\mu_m)$, restriction to $L$ and the action on roots of unity give the joint homomorphism
--
--   $$
--   \operatorname{Gal}(M/K)\longrightarrow\operatorname{Gal}(L/K)\times(\mathbb Z/m\mathbb Z)^\times.
--   $$
--
--   The bundle supplies the Galois structure, injectivity, and the product equivalence under the degree and coprimality hypotheses. This is the group decomposition used to attach cyclotomic tags.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Cyclotomic/Compositum.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Cyclotomic/Compositum.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_FieldTheory_IntermediateField_Adjoin_EqTop
import Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Finrank
import Definitions.Def_TauCeti_RingTheory_RootsOfUnity_PrimitiveRoots
import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

section
set_option autoImplicit true
/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
/-!
# The cyclotomic compositum `M = L(μ_m)` and its joint restriction isomorphism

Let `L / K` be a Galois extension of number fields and let `M = L(μ_m)` be obtained from `L`
by adjoining the `m`-th roots of unity. When `m` is coprime to the discriminant of `L`, the
two restriction maps out of `Gal(M/K)` — to `Gal(L/K)`, and to `(ZMod m)ˣ` via the cyclotomic
character — are *jointly* bijective:

`Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ`.

## Main results

* `IsCyclotomicExtension.isGalois_of_isGalois_of_isCyclotomicExtension`: `M / K` is itself
  Galois, so `Gal(M/K)` below is not an extra assumption.
* `IsPrimitiveRoot.autToPow_bijective`: the cyclotomic character
  `Gal(M/L) → (ZMod m)ˣ` is bijective.
* `IsCyclotomicExtension.restrictNormalHom_prod_autToPow_injective`: the joint restriction
  is faithful (no arithmetic hypothesis needed).
* `IsCyclotomicExtension.galEquivProd`: that map packaged as a `MulEquiv`, with
  `IsCyclotomicExtension.galEquivProd_apply` computing both of its components, and
  `IsCyclotomicExtension.restrictNormal_galEquivProd_symm` together with
  `IsCyclotomicExtension.autToPow_galEquivProd_symm` eliminating its inverse. Those three
  `simp` lemmas are the whole interface: no consumer needs the `MulEquiv.ofBijective` that
  packages the equivalence, in either direction.
* `IsCyclotomicExtension.ker_autToPow_eq_comap_galEquivProd` and
  `IsCyclotomicExtension.ker_restrictNormalHom_eq_comap_galEquivProd`: the same interface one
  level up, on subgroups rather than elements — each component's kernel is what `galEquivProd`
  reads off as the opposite factor.

The two general prerequisites this rests on are stated where they belong rather than here:
the degree identity `[M : K] = φ m` is `IsCyclotomicExtension.finrank_eq_totient` in
`TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank`, and the compositum step
`K(ζ) ⊔ L = ⊤` is `TauCeti.IntermediateField.adjoin_sup_fieldRange_eq_top` in
`TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop`.

## Implementation notes

The file is split by hypothesis strength, in three steps.
`restrictNormalHom_prod_autToPow_injective` comes first and assumes only `[Normal K L]`:
normality is exactly what defines
`AlgEquiv.restrictNormalHom L`, and the faithfulness argument never separates anything, so
requiring `IsGalois K L` there would be an avoidable hypothesis. Next
`isGalois_of_isGalois_of_isCyclotomicExtension` turns on `[IsGalois K L]`, needing no hypothesis
beyond the tower itself (algebraicity and separability of `M / K` are both derived inside the
proof from `IsGalois K L` and the cyclotomic tower). Both are pure field theory and carry no
`NumberField` instances. Only the results downstream of the degree count, which mention
`discr L`, take number fields.

`isGalois_of_isGalois_of_isCyclotomicExtension` is a theorem and not an `instance` because
neither `L` nor `m` can be recovered from the goal `IsGalois K M`, so there is no synthesization
order for it; call sites introduce it with `have`.

That `M / K` is Galois is *derived*, not assumed: `M` is the compositum of `L` with `K(ζ)`,
both of which are normal over `K`, and the engine for a compositum of two normal extensions is
Mathlib's `IntermediateField.normal_sup`. So `Gal(M/K)` below rests on no hypothesis beyond
`IsGalois K L` and the cyclotomic tower. Separability comes from transitivity along the same
tower: `L / K` is separable because it is Galois, and `M / L` because a cyclotomic extension is
(`IsCyclotomicExtension.isSeparable`). No characteristic assumption is needed, since a primitive
`m`-th root of unity exists in `M` only if the characteristic does not divide `m`.

Faithfulness of the joint restriction is *not* re-derived here: it is Mathlib's compositum
engine `IntermediateField.fixingSubgroup_sup` (with `fixingSubgroup_top`), applied to `K(ζ)`
and the image of `L` inside `M`. We invoke that shared lemma rather than
`IntermediateField.restrictRestrictAlgEquivMapHom_injective`, which is built from it, because
the latter concerns `Gal(M/L) →* Gal(K(ζ)/K)` whereas the map here is defined on `Gal(M/K)`;
using it would first require transporting an element of `Gal(M/K)` that fixes `L` into
`Gal(M/L)`, which is strictly more work than calling the underlying lemma directly.

Surjectivity does go through a degree count. That is not an oversight: surjectivity onto the
`(ZMod m)ˣ` factor *is* the assertion that the `m`-th cyclotomic polynomial stays irreducible
over `L`, which is exactly what the coprimality hypothesis `hcop` buys. Mathlib's companion
`restrictRestrictAlgEquivMapHom_surjective` needs `K(ζ) ⊓ L = ⊥`, and the proof of that
intersection statement is the same discriminant input, so it would not avoid the arithmetic.

Adapted from the Birkbeck–Brasca Chebotarev density project.
-/

 section

section AutToPow

variable (L : Type*) [Field L] [NumberField L] {M : Type*} [Field M] [Algebra L M]
  {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} L M]



end AutToPow

namespace IsCyclotomicExtension

section Compositum

variable (K L M : Type*) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]

section Faithful

/-! Faithfulness of the joint restriction needs only that `L / K` is *normal* — enough to
define `AlgEquiv.restrictNormalHom L` — not that it is Galois. Separability of `L / K` enters
only with the compositum-Galois and degree-count results below. -/

variable [Normal K L]

/-- **The joint restriction is faithful.** An automorphism of `M = L(μ_m)` over `K` that is
trivial on `L` and trivial on the `m`-th roots of unity is the identity. No arithmetic
hypothesis is needed, only normality of `L / K`. -/
theorem restrictNormalHom_prod_autToPow_injective {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    Function.Injective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K)) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  rw [MonoidHom.prod_apply, Prod.mk_eq_one] at hσ
  obtain ⟨hσL, hσζ⟩ := hσ
  have hζfix : σ ζ = ζ := (hζ.autToPow_eq_one_iff σ).mp hσζ
  have hLfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
    intro x
    have hcomm := σ.restrictNormal_commutes L x
    have hrn : σ.restrictNormal L = (1 : Gal(L/K)) := hσL
    rw [hrn] at hcomm
    simpa using hcomm.symm
  -- `σ` fixes the compositum of `K(ζ)` and (the image of) `L`, which is all of `M`.
  have hmem : σ ∈ IntermediateField.fixingSubgroup
      (IntermediateField.adjoin K {ζ} ⊔ (IsScalarTower.toAlgHom K L M).fieldRange) := by
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem y hy => rw [Set.mem_singleton_iff] at hy; subst hy; exact hζfix
      | algebraMap r => exact σ.commutes r
      | add a b _ _ ha hb => rw [map_add, ha, hb]
      | inv a _ ha => rw [map_inv₀, ha]
      | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      rintro _ ⟨x, rfl⟩
      exact hLfix x
  have htop : IntermediateField.adjoin K {ζ} ⊔ (IsScalarTower.toAlgHom K L M).fieldRange
      = (⊤ : IntermediateField K M) :=
    TauCeti.IntermediateField.adjoin_sup_fieldRange_eq_top K L M
      (IntermediateField.adjoin_eq_top_of_algebra _ _
        (IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ))
  rw [htop, IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hmem
  exact hmem

end Faithful

variable [IsGalois K L]

include L m in
/-- **The cyclotomic compositum of a Galois extension is Galois.** If `L / K` is Galois and
`M = L(μ_m)`, then `M / K` is Galois, so `Gal(M/K)` is available without a further hypothesis.

Both tower hypotheses are needed, which is what the name records: the cyclotomic extension is
`M / L`, and `L / K` is Galois. Mathlib's `IsCyclotomicExtension.isGalois` is the one-step
statement, for a cyclotomic extension of the base itself. Call sites introduce this with
`have`; see the module Implementation notes. -/
theorem isGalois_of_isGalois_of_isCyclotomicExtension : IsGalois K M := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M
    (Set.mem_singleton m) (NeZero.ne m)
  -- `M / K` is algebraic: `L / K` is Galois hence algebraic, and `M / L` is a cyclotomic
  -- extension for the single modulus `m`, hence finite. This is what the dropped `NumberField`
  -- instances used to supply.
  have : FiniteDimensional L M := IsCyclotomicExtension.finiteDimensional (S := {m}) (K := L) M
  have : Algebra.IsIntegral K M := Algebra.IsIntegral.trans L
  have hcyc : IsCyclotomicExtension {m} K (IntermediateField.adjoin K {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := K)
  have : IsGalois K (IntermediateField.adjoin K {ζ}) :=
    IsCyclotomicExtension.isGalois (S := {m}) (K := K) (L := IntermediateField.adjoin K {ζ})
  have : Normal K ((IsScalarTower.toAlgHom K L M).fieldRange) :=
    Normal.of_algEquiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L M))
  have hsup : Normal K
      (IntermediateField.adjoin K {ζ} ⊔ (IsScalarTower.toAlgHom K L M).fieldRange :
        IntermediateField K M) := IntermediateField.normal_sup K M _ _
  rw [TauCeti.IntermediateField.adjoin_sup_fieldRange_eq_top K L M
    (IntermediateField.adjoin_eq_top_of_algebra _ _
        (IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ))] at hsup
  have : Normal K M := Normal.of_algEquiv (h := hsup) IntermediateField.topEquiv
  have : Algebra.IsSeparable L M := IsCyclotomicExtension.isSeparable (S := {m}) (K := L) (L := M)
  have : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  exact ⟨⟩

/-! The remaining results are arithmetic: they need the discriminant of `L`, hence number
fields rather than bare characteristic-zero fields. Only the *base* fields `K` and `L` carry
`NumberField`; `M` does not, because a cyclotomic extension of a number field is finite over it
and so is a number field already — the instances it needs are installed locally where used. -/

variable [NumberField K] [NumberField L]

/-- **The joint restriction is bijective.** The two restrictions out of `Gal(M/K)` — to
`Gal(L/K)`, and to `(ZMod m)ˣ` via the cyclotomic character — are jointly bijective.
Faithfulness is `restrictNormalHom_prod_autToPow_injective`; surjectivity is then forced by
the degree identity `IsCyclotomicExtension.finrank_eq_totient`, since `[M : K] = [L : K] · φ m`.

`private`: it exists only to build `galEquivProd`, after which it is recoverable as
`(galEquivProd K L M m hcop hζ).bijective`, so exporting it would duplicate that canonical API. -/
 theorem restrictNormalHom_prod_autToPow_bijective
    (hcop : ((NumberField.discr L).natAbs).Coprime m) {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    Function.Bijective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K)) := by
  have : FiniteDimensional L M := IsCyclotomicExtension.finiteDimensional (S := {m}) (K := L) M
  have : FiniteDimensional K M := FiniteDimensional.trans K L M
  have : IsGalois L M := IsCyclotomicExtension.isGalois (S := {m}) (K := L) (L := M)
  have : IsGalois K M := isGalois_of_isGalois_of_isCyclotomicExtension K L M m
  have hcard : Nat.card Gal(M/K) = Nat.card (Gal(L/K) × (ZMod m)ˣ) := by
    rw [Nat.card_prod, IsGalois.card_aut_eq_finrank K M, IsGalois.card_aut_eq_finrank K L,
      ← Module.finrank_mul_finrank K L M, IsCyclotomicExtension.finrank_eq_totient L M m hcop,
      Nat.card_eq_fintype_card (α := (ZMod m)ˣ), ZMod.card_units_eq_totient]
  exact (Nat.bijective_iff_injective_and_card _).mpr
    ⟨restrictNormalHom_prod_autToPow_injective K L M m hζ, hcard⟩

/-- The joint restriction `Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ`, packaged as a `MulEquiv`. -/
noncomputable def galEquivProd (hcop : ((NumberField.discr L).natAbs).Coprime m)
    {ζ : M} (hζ : IsPrimitiveRoot ζ m) : Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ :=
  MulEquiv.ofBijective _ (restrictNormalHom_prod_autToPow_bijective K L M m hcop hζ)











end Compositum

end IsCyclotomicExtension

end
end


