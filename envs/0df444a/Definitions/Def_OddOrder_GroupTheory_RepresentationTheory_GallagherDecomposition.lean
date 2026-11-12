-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_GallagherDecomposition
-- name    : OddOrder_GroupTheory_RepresentationTheory_GallagherDecomposition
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:44:35.017592+00:00
-- url     : https://prove2.me/theorems/2d2f663e-67ff-4390-8e04-8ec71ea2df51
-- title:
--   Gallagher's decomposition for a coprime abelian quotient (toward Isaacs 6.17)
-- statement:
--   Isaacs, *Character Theory of Finite Groups*, Corollary 6.17 (Gallagher), specialized to an abelian quotient with coprime degree: for $H\trianglelefteq K$ with $K/H$ abelian, $\theta\in\mathrm{Irr}(H)$ $K$-invariant and extending to $\chi\in\mathrm{Irr}(K)$, and $\gcd([K:H],\theta(1))=1$, the induced character $\mathrm{Ind}_H^K\theta$ decomposes as a sum of $\chi\beta$ over the linear characters $\beta$ of $K/H$.
--
--   Main results: `induce_eq_sum_mul_linearClassFunction` (Gallagher's decomposition, coprime abelian case), `induce_trivial_eq_sum_linearClassFunction` (the induced trivial character as a sum of quotient linear characters) and `induce_restrict_eq_mul_sum_linearClassFunction` (the restriction-induction identity), plus a finiteness instance for homomorphisms from a finite group into the units of a domain.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/GallagherDecomposition.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/GallagherDecomposition.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CanonicalCharacterExtension
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterProduct
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCount
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace OddOrder.RepresentationTheory

/-- **Homomorphisms from a finite group into the units of a domain form a finite type**:
every value is a `|G|`-th root of unity (`pow_card_eq_one'`), and `rootsOfUnity` of a domain
is finite.  Gives `Finite ((K ⧸ H) →* ℂˣ)`, the index type of the Gallagher decomposition. -/
instance {G M : Type*} [Group G] [Finite G] [CommRing M] [IsDomain M] :
    Finite (G →* Mˣ) := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  have hmem : ∀ (f : G →* Mˣ) (g : G), f g ∈ rootsOfUnity (Nat.card G) M := fun f g => by
    rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]
  refine Finite.of_injective
    (fun f g => (⟨f g, hmem f g⟩ : rootsOfUnity (Nat.card G) M)) fun f₁ f₂ h => ?_
  refine MonoidHom.ext fun g => ?_
  exact Subtype.ext_iff.mp (congrFun h g)

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]

/-- **Distinct linear twists of an extension stay distinct** (coprime degree).  For `χ ∈ Irr(K)`
of degree `d` coprime to `[K:H]`, the twisting map `β ↦ χ · Inf(β)` on `Hom(K/H, ℂˣ)` is
injective.

The determinantal characters separate the twists: `det(χ·Inf β) = β^d · det χ`
(`determinant_mul_linearClassFunction`), so `χ·Inf β₁ = χ·Inf β₂` forces `(β₁/β₂)^d = 1`; and
`β₁/β₂` is trivial on `H`, hence killed by `[K:H]` as well.  Coprimality of `d` and `[K:H]` then
makes `β₁/β₂` trivial.

Extracted from `induce_eq_sum_mul_linearClassFunction`, which cites it for the distinctness of
its constituents.  It is stated separately because the multiplicity-one *packaging* of that
decomposition (a `Finset (IrreducibleCharacter K)` of cardinality `[K:H]`) needs exactly this
injectivity, and re-deriving it inside every such repackaging would duplicate the determinantal
argument. -/
theorem injective_mul_linearClassFunction_of_coprime [Finite K]
    {χ : ClassFunction K ℂ} (hχ : IsIrreducibleCharacter χ)
    {d : ℕ} (hd_χ : χ 1 = (d : ℂ)) (hcop : Nat.Coprime H.index d) :
    Function.Injective fun β : (K ⧸ H) →* ℂˣ =>
      χ * linearClassFunction (β.comp (QuotientGroup.mk' H)) := by
  let : Fintype K := Fintype.ofFinite K
  intro β₁ β₂ hcoe
  simp only at hcoe
  set f₁ := β₁.comp (QuotientGroup.mk' H) with hf₁
  set f₂ := β₂.comp (QuotientGroup.mk' H) with hf₂
  have hIrr₁ : IsIrreducibleCharacter (χ * linearClassFunction f₁) :=
    isIrreducibleCharacter_mul_linearClassFunction hχ f₁
  have hIrr₂ : IsIrreducibleCharacter (χ * linearClassFunction f₂) :=
    isIrreducibleCharacter_mul_linearClassFunction hχ f₂
  -- equal characters have equal determinantal characters
  have hdeq : hIrr₁.determinant = hIrr₂.determinant := by
    revert hIrr₁ hIrr₂
    rw [hcoe]
    intro h₁ h₂
    rfl
  have hdet₁ : hIrr₁.determinant = f₁ ^ d * hχ.determinant :=
    hχ.determinant_mul_linearClassFunction f₁ hIrr₁ hd_χ
  have hdet₂ : hIrr₂.determinant = f₂ ^ d * hχ.determinant :=
    hχ.determinant_mul_linearClassFunction f₂ hIrr₂ hd_χ
  have hpow : f₁ ^ d = f₂ ^ d :=
    mul_right_cancel ((hdet₁.symm.trans hdeq).trans hdet₂)
  -- `f₁/f₂` is trivial on `H`, hence index-torsion; and `d`-torsion by `hpow`
  have htriv : ∀ h : ↥H, (f₁ * f₂⁻¹) ((h : K)) = 1 := fun h => by
    have e1 : QuotientGroup.mk' H ((h : K)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h.2
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hf₁, hf₂, MonoidHom.comp_apply,
      MonoidHom.comp_apply, e1, map_one, map_one, inv_one, mul_one]
  have hq : (f₁ * f₂⁻¹) ^ H.index = 1 :=
    pow_index_eq_one_of_forall_coe_eq_one htriv
  have hd' : (f₁ * f₂⁻¹) ^ d = 1 := by
    calc
      (f₁ * f₂⁻¹) ^ d = f₁ ^ d * (f₂⁻¹) ^ d := mul_pow f₁ f₂⁻¹ d
      _ = f₁ ^ d * (f₂ ^ d)⁻¹ := congrArg (f₁ ^ d * ·) (inv_pow f₂ d)
      _ = f₂ ^ d * (f₂ ^ d)⁻¹ := congrArg (· * (f₂ ^ d)⁻¹) hpow
      _ = 1 := mul_inv_cancel (f₂ ^ d)
  have hf : f₁ * f₂⁻¹ = 1 := by
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸
      Nat.dvd_gcd
        (orderOf_dvd_of_pow_eq_one (x := f₁ * f₂⁻¹) (n := H.index) hq)
        (orderOf_dvd_of_pow_eq_one (x := f₁ * f₂⁻¹) (n := d) hd')))
  have hf12 : f₁ = f₂ := mul_inv_eq_one.mp hf
  rw [hf₁, hf₂] at hf12
  exact (MonoidHom.cancel_right (QuotientGroup.mk'_surjective H)).mp hf12

open scoped commutatorElement in
/-- **Gallagher's decomposition, coprime abelian case** (Isaacs, *Character Theory*,
Corollary 6.17 specialized; issue 9002 (G2)).  Let `H ⊴ K` finite with `K/H` abelian, let
`θ ∈ Irr(H)` be `K`-invariant of degree `d` coprime to `[K:H]`, and let `χ ∈ Irr(K)` extend
`θ`.  Then

  `Ind_H^K θ = ∑_{β ∈ Hom(K/H, ℂˣ)} χ · Inf(β)`

— a multiplicity-one decomposition into `[K:H]` distinct irreducible constituents.

The extension `χ` exists whenever `gcd([K:H], o(θ)·d) = 1`
(`IsIrreducibleCharacter.exists_extension_of_forall_conjBy_eq`, Isaacs 8.16). -/
theorem induce_eq_sum_mul_linearClassFunction [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] [Invertible (Nat.card ↥H : ℂ)]
    [Fintype ((K ⧸ H) →* ℂˣ)]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hinv : ∀ y : K, ClassFunction.conjBy y θ = θ)
    (hab : ∀ x y : K, ⁅x, y⁆ ∈ H)
    {χ : ClassFunction K ℂ} (hχ : IsIrreducibleCharacter χ)
    (hres : ClassFunction.restrict H χ = θ)
    {d : ℕ} (hd : θ 1 = (d : ℂ)) (hcop : Nat.Coprime H.index d) :
    ClassFunction.induce H θ
      = ∑ β : (K ⧸ H) →* ℂˣ, χ * linearClassFunction (β.comp (QuotientGroup.mk' H)) := by
  classical
  let : Fintype ↥H := Fintype.ofFinite _
  have : Finite (IrreducibleCharacter K) := finite_irreducibleCharacter (G := K)
  let : Fintype (IrreducibleCharacter K) := Fintype.ofFinite _
  -- the quotient is a finite abelian group
  let : CommGroup (K ⧸ H) :=
    { (inferInstance : Group (K ⧸ H)) with
      mul_comm := fun a b => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        refine (QuotientGroup.eq).mpr ?_
        have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
          rw [commutatorElement_def]
          group
        rw [h1]
        exact hab y⁻¹ x⁻¹ }
  have : NeZero (Monoid.exponent (K ⧸ H)) := ⟨by exact Monoid.exponent_ne_zero_of_finite⟩
  -- self-duality of the finite abelian quotient: `[K:H]` linear characters
  have hcard_hom : Nat.card ((K ⧸ H) →* ℂˣ) = H.index :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (K ⧸ H) ℂ
  -- the degree of `χ` is `d`
  have hd_χ : χ 1 = (d : ℂ) := by
    rw [← hd, ← hres]
    change χ (((1 : ↥H) : K)) = χ 1
    rw [OneMemClass.coe_one]
  -- the family of twists, as bundled irreducible characters
  set Φ : ((K ⧸ H) →* ℂˣ) → IrreducibleCharacter K := fun β =>
    ⟨χ * linearClassFunction (β.comp (QuotientGroup.mk' H)),
      isIrreducibleCharacter_mul_linearClassFunction hχ _⟩ with hΦ
  have hcoeΦ : ∀ β : (K ⧸ H) →* ℂˣ, ((Φ β : IrreducibleCharacter K) : ClassFunction K ℂ)
      = χ * linearClassFunction (β.comp (QuotientGroup.mk' H)) := fun β => rfl
  -- distinctness: the determinantal characters separate the twists (coprime degree)
  have hΦinj : Function.Injective Φ := fun β₁ β₂ hβeq =>
    injective_mul_linearClassFunction_of_coprime hχ hd_χ hcop
      (show χ * linearClassFunction (β₁.comp (QuotientGroup.mk' H))
          = χ * linearClassFunction (β₂.comp (QuotientGroup.mk' H)) by
        rw [← hcoeΦ β₁, ← hcoeΦ β₂, hβeq])
  -- the twists as a finset, of cardinality `[K:H]`
  set S : Finset (IrreducibleCharacter K) := Finset.univ.image Φ with hS
  have hcard_S : S.card = H.index := by
    rw [hS, Finset.card_image_of_injective _ hΦinj, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcard_hom]
  -- multiplicity one: `⟨Ind θ, χ·Inf(β)⟩ = ⟨θ, θ⟩ = 1` by Frobenius reciprocity
  have h1 : ∀ c ∈ S,
      ClassFunction.inner (ClassFunction.induce H θ) (c : ClassFunction K ℂ) = 1 := by
    intro c hc
    obtain ⟨β, _, rfl⟩ := Finset.mem_image.mp hc
    rw [hcoeΦ β, ClassFunction.inner_induce_eq_inner_restrict,
      ClassFunction.restrict_mul_of_apply_eq_one χ _
        (fun x => linearClassFunction_comp_mk'_apply_eq_one β x.2), hres]
    exact hθ.inner_self_eq_one
  -- the norm exhausts: `⟨Ind θ, Ind θ⟩ = [K:H]` since the inertia group is all of `K`
  have hnorm : ClassFunction.inner (ClassFunction.induce H θ) (ClassFunction.induce H θ)
      = (S.card : ℂ) := by
    rw [hcard_S]
    have hkey := card_mul_inner_self_induce_eq_card_inertia (G := K)
      (⟨θ, hθ⟩ : IrreducibleCharacter ↥H)
    have hcoeθ : ((⟨θ, hθ⟩ : IrreducibleCharacter ↥H) : ClassFunction ↥H ℂ) = θ := rfl
    rw [hcoeθ] at hkey
    have hinertia : ClassFunction.inertia (G := K) θ = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro y
      rw [ClassFunction.mem_inertia]
      exact hinv y
    rw [hinertia] at hkey
    have hne : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    apply mul_left_cancel₀ hne
    rw [hkey]
    have htop : (Nat.card ↥(⊤ : Subgroup K) : ℂ) = (Nat.card K : ℂ) := by
      norm_cast
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [htop]
    norm_cast
    rw [mul_comm]
    exact (Subgroup.index_mul_card H).symm
  -- collapse the Fourier expansion onto the twists
  have hfinal := eq_sum_of_inner_eq_one_of_inner_self_eq_card h1 hnorm
  rw [hfinal, hS, Finset.sum_image fun β₁ _ β₂ _ h => hΦinj h]

open scoped commutatorElement in
/-- **Induced trivial character of a normal subgroup with abelian quotient = sum of the quotient's
linear characters** (the regular character of `K/H`, inflated).  For `H ⊴ K` finite with `K/H`
abelian, `Ind_H^K 1_H = ∑_{β ∈ Hom(K/H, ℂˣ)} Inf(β)`.

The `θ = 1_H` case of `induce_eq_sum_mul_linearClassFunction` (coprimality `gcd([K:H], 1) = 1` is
vacuous, extension `1_K`), followed by `1_K · Inf(β) = Inf(β)`.  This is the `Ind_H^T 1_H` factor of
the projection-formula (`induce_restrict_mul`) route to the **general** Peterfalvi (1.7.b) — the
equal-degree induced-constituent decomposition for an abelian inertia quotient, no coprimality. -/
theorem induce_trivial_eq_sum_linearClassFunction [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] [Invertible (Nat.card ↥H : ℂ)]
    [Fintype ((K ⧸ H) →* ℂˣ)] (hab : ∀ x y : K, ⁅x, y⁆ ∈ H) :
    ClassFunction.induce H (trivialClassFunction ↥H)
      = ∑ β : (K ⧸ H) →* ℂˣ, linearClassFunction (β.comp (QuotientGroup.mk' H)) := by
  have hinv : ∀ y : K,
      ClassFunction.conjBy y (trivialClassFunction ↥H) = trivialClassFunction ↥H := by
    intro y; ext h; simp [ClassFunction.conjBy_apply, trivialClassFunction_apply]
  have hres : ClassFunction.restrict H (trivialClassFunction K) = trivialClassFunction ↥H := by
    ext h; simp [trivialClassFunction_apply]
  have hgal := induce_eq_sum_mul_linearClassFunction (K := K) (H := H)
    trivialClassFunction_isIrreducible hinv hab trivialClassFunction_isIrreducible hres
    (d := 1) (by rw [trivialClassFunction_apply]; norm_num) (Nat.coprime_one_right _)
  rw [hgal]
  refine Finset.sum_congr rfl fun β _ => ?_
  ext y
  rw [ClassFunction.mul_apply, trivialClassFunction_apply, one_mul]

open scoped commutatorElement in
/-- **The abelian-quotient restriction–induction identity** `Ind_H^K(Res_H ψ) = ∑_β ψ·Inf(β)`.
Combines the projection formula (`ClassFunction.induce_restrict_mul`, with `χ = 1_H`, using
`Res_H ψ · 1_H = Res_H ψ`) and `induce_trivial_eq_sum_linearClassFunction`.

For `ψ ∈ Irr K` lying over `θ ∈ Irr H` this exhibits `Ind_H^K(Res ψ)` as `ψ` times the sum of the
`[K:H]` linear characters of `K/H`; distributing (each `ψ·Inf(β)` has degree `ψ(1)`, `Inf(β)`
linear) gives the constituent list of the general Peterfalvi (1.7.b), all constituents of common
degree `ψ(1)`.  With `Res_H ψ = e·θ` (Clifford), `Ind_H^K(Res ψ) = e·Ind_H^K θ`, giving the
equal-degree decomposition of `Ind_H^K θ` for an abelian quotient `K/H` — the fact Peterfalvi (12.5)
needs at the `H'/H` level (`K/H` abelian automatic since `H' = [H,H]`), where the coprime Gallagher
case does not apply.  (`ClassFunction` carries only `Mul`, not a semiring, so the sum is kept
factored as `ψ · ∑`; downstream distribution is pointwise.) -/
theorem induce_restrict_eq_mul_sum_linearClassFunction [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] [Invertible (Nat.card ↥H : ℂ)]
    [Fintype ((K ⧸ H) →* ℂˣ)] (hab : ∀ x y : K, ⁅x, y⁆ ∈ H) (ψ : ClassFunction K ℂ) :
    ClassFunction.induce H (ClassFunction.restrict H ψ)
      = ψ * ∑ β : (K ⧸ H) →* ℂˣ, linearClassFunction (β.comp (QuotientGroup.mk' H)) := by
  have key := ClassFunction.induce_restrict_mul (H := H) ψ (trivialClassFunction ↥H)
  have e1 : ClassFunction.induce H (ClassFunction.restrict H ψ)
      = ψ * ClassFunction.induce H (trivialClassFunction ↥H) := by
    rw [← key]
    congr 1
    ext h
    simp [ClassFunction.mul_apply, trivialClassFunction_apply]
  rw [e1, induce_trivial_eq_sum_linearClassFunction hab]

end OddOrder.RepresentationTheory


