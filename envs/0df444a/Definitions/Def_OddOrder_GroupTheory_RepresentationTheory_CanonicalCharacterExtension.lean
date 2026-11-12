-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CanonicalCharacterExtension
-- name    : OddOrder_GroupTheory_RepresentationTheory_CanonicalCharacterExtension
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:42:49.632821+00:00
-- url     : https://prove2.me/theorems/ddaf6944-6be0-475f-9d19-368fad9f3f6f
-- title:
--   The canonical extension along a prime-cyclic quotient (toward Isaacs 6.28)
-- statement:
--   Isaacs, *Character Theory of Finite Groups*, Theorem 6.25 / Corollary 6.28 (prime-cyclic step): let $N\trianglelefteq N'$ with $[N':N]=p$ prime and let $\varphi\in\mathrm{Irr}(N)$ be $N'$-invariant with $\gcd(p,o(\varphi)\varphi(1))=1$. Then $\varphi$ has a unique extension $\chi\in\mathrm{Irr}(N')$ with $p\nmid o(\chi)$, the canonical extension.
--
--   Contains `IsIrreducibleCharacter.exists_extension_of_forall_conjBy_eq` (extension along an abelian coprime quotient, Isaacs Theorem 8.16) and its strong-induction engine.
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CanonicalCharacterExtension.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CanonicalCharacterExtension.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_RepresentationDeterminant
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclicCharacterExtension
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtensionLinearTwist
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Mathlib.GroupTheory.Commutator.Basic

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **The determinant of a linear twist**: `det (χ · lcf β) = β^d · det χ`, where `d = χ(1)`
is the degree.  Character-level form of `representationDeterminant_twistRep`. -/
theorem IsIrreducibleCharacter.determinant_mul_linearClassFunction [Finite G]
    {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ) (β : G →* ℂˣ)
    (hχβ : IsIrreducibleCharacter (χ * linearClassFunction β))
    {d : ℕ} (hd : χ 1 = (d : ℂ)) :
    hχβ.determinant = β ^ d * hχ.determinant := by
  obtain ⟨V', _, _, _, ρ, hρ, hc⟩ := id hχ
  -- the twisted representation affords `χ · lcf β`
  have h1 : ((χ * linearClassFunction β : ClassFunction G ℂ) : G → ℂ)
      = (twistRep ρ β).character := by
    funext y
    rw [show ((χ * linearClassFunction β : ClassFunction G ℂ) : G → ℂ) y
          = χ y * (β y : ℂ) from by
        rw [show ((χ * linearClassFunction β : ClassFunction G ℂ) : G → ℂ) y
            = (χ * linearClassFunction β) y from rfl, ClassFunction.mul_apply,
          linearClassFunction_apply],
      twistRep_character, congrFun hc y]
    ring
  rw [IsIrreducibleCharacter.determinant_spec hχβ (twistRep ρ β) h1]
  refine MonoidHom.ext fun y => ?_
  -- the degree is the dimension of the affording space
  have hfr : Module.finrank ℂ V' = d := by
    have h2 := congrFun hc 1
    rw [show (χ : G → ℂ) 1 = χ 1 from rfl, hd, Representation.char_one] at h2
    exact_mod_cast h2.symm
  rw [representationDeterminant_twistRep, hfr,
    IsIrreducibleCharacter.determinant_spec hχ ρ hc]
  rfl

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]

/-- **Conjugation-equivariance of the determinantal character**:
`det (θ^g) = (det θ) ∘ conj_g`.  The witnessing representation of `θ^g` can be taken to be
the conjugate representation `conjRep ρ g = ρ ∘ conj_g`, whose determinant is
`det ρ ∘ conj_g` by `representationDeterminant_comp`.

This is the equivariance that lets uniqueness of the canonical extension propagate
invariance in the abelian iterate (issue 9002 (v-d)): if `θ` is `K`-invariant, the conjugate
of the canonical extension is again an extension with the same determinantal order, hence
equals the canonical extension. -/
theorem IsIrreducibleCharacter.determinant_conjBy [Finite K]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ) (g : K)
    (hconj : IsIrreducibleCharacter (ClassFunction.conjBy g θ)) :
    hconj.determinant
      = hθ.determinant.comp
          (ClassFunction.conjByMulEquiv (G := K) (H := H) g).toMonoidHom := by
  obtain ⟨V', _, _, _, ρ, hρ, hc⟩ := id hθ
  -- `conjRep ρ g` affords `θ^g`
  have h1 : ((ClassFunction.conjBy g θ : ClassFunction ↥H ℂ) : ↥H → ℂ)
      = (conjRep ρ g).character := by
    funext h
    rw [conjRep_character]
    exact congrFun hc (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)
  rw [IsIrreducibleCharacter.determinant_spec hconj (conjRep ρ g) h1, conjRep,
    representationDeterminant_comp, IsIrreducibleCharacter.determinant_spec hθ ρ hc]

/-- **A linear character trivial on `H ⊴ K` is `[K:H]`-torsion**: it factors through `K/H`,
so its `[K:H]`-th power evaluates as `μ(y^{[K:H]})` with `y^{[K:H]} ∈ H`
(`Subgroup.pow_index_mem`).  Bounds the determinantal drift of an extension: the twist
between any two extensions is `[K:H]`-torsion, so a `[K:H]`-coprime determinantal order pins
the extension down (issue 9002 (v-c3)/(v-c4)). -/
theorem pow_index_eq_one_of_forall_coe_eq_one {μ : K →* ℂˣ}
    (hμ : ∀ h : ↥H, μ ((h : K)) = 1) :
    μ ^ H.index = 1 := by
  refine MonoidHom.ext fun y => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow]
  exact hμ ⟨y ^ H.index, H.pow_index_mem y⟩

/-- **Bézout adjustment** (the arithmetic core of Isaacs *CT* 6.25).  In a commutative group,
if `(x^o)^p = 1` and both `o` and `d` are coprime to `p`, then some `β` in the cyclic
subgroup generated by `x^o` satisfies `(β^d · x)^o = 1`.

Concretely `β = (x^o)^{-A·C}` where `A·o ≡ 1` and `C·d ≡ 1 (mod p)`: then
`(β^d · x)^o = (x^o)^{-ACdo + 1}` with `p ∣ -ACdo + 1`, so the `p`-torsion of `x^o` kills it.

In the application `x = det χ'` for an extension `χ'` of `θ` and `o = o(θ)`, so that `x^o` is
trivial on `H` and hence `p = [K:H]`-torsion; `β` is then a linear character trivial on `H`
twisting `χ'` into the extension with determinant `β^d · det χ'` of order dividing `o(θ)`. -/
theorem exists_mem_zpowers_pow_mul_pow_eq_one {W : Type*} [CommGroup W] (x : W) {o p d : ℕ}
    (hop : (x ^ o) ^ p = 1) (hgo : Nat.gcd o p = 1) (hgd : Nat.gcd d p = 1) :
    ∃ β ∈ Subgroup.zpowers (x ^ o), (β ^ d * x) ^ o = 1 := by
  set A : ℤ := Nat.gcdA o p
  set B : ℤ := Nat.gcdB o p
  set C : ℤ := Nat.gcdA d p
  set D : ℤ := Nat.gcdB d p
  have h1 : (1 : ℤ) = ↑o * A + ↑p * B := by
    have h := Nat.gcd_eq_gcd_ab o p
    rw [hgo, Nat.cast_one] at h
    exact h
  have h2 : (1 : ℤ) = ↑d * C + ↑p * D := by
    have h := Nat.gcd_eq_gcd_ab d p
    rw [hgd, Nat.cast_one] at h
    exact h
  refine ⟨(x ^ o) ^ (-(A * C)), Subgroup.zpow_mem_zpowers _ _, ?_⟩
  -- the total exponent `-ACdo + 1` is a multiple of `p`, by Bézout
  have key : -(A * C) * ↑d * ↑o + 1
      = ↑p * (↑o * A * D + B * ↑d * C + ↑p * B * D) := by
    have e1 : (1 : ℤ) = (↑o * A + ↑p * B) * (↑d * C + ↑p * D) := by
      rw [← h1, ← h2, one_mul]
    rw [e1]
    ring
  have e2 : (((x ^ o) ^ (-(A * C))) ^ d * x) ^ o
      = x ^ ((-(A * C) * ↑d * ↑o + 1) * ↑o) := by
    group
  have e3 : x ^ ((↑p * (↑o * A * D + B * ↑d * C + ↑p * B * D)) * ↑o)
      = ((x ^ o) ^ p) ^ (↑o * A * D + B * ↑d * C + ↑p * B * D) := by
    group
  rw [e2, key, e3, hop, one_zpow]

/-- **Existence of the canonical extension** (Isaacs *CT* 6.25/6.28, existence half; issue
9002 (v-c3)).  Let `H ⊴ K` with `[K:H] = p` prime and the image of `g : K` generating `K/H`,
and let `θ ∈ Irr(H)` be `g`-invariant of degree `d` with `p ∤ d` and `p ∤ o(θ)`.  Then `θ`
has an extension `χ ∈ Irr(K)` whose determinantal order is again coprime to `p` — the
**canonical extension** (unique by `extension_unique_of_not_dvd_orderOf_determinant`).

Starting from any extension `χ'` (`CyclicCharacterExtension`, Isaacs 11.22), the
determinantal character `λ' = det χ'` restricts to `det θ`, so `λ'^{o(θ)}` is trivial on `H`
and hence `p`-torsion; the Bézout adjustment `exists_mem_zpowers_pow_mul_pow_eq_one`
produces a linear character `β` trivial on `H` with `(β^d · λ')^{o(θ)} = 1`, and
`χ = χ' · β` has determinant `β^d · λ'` of order dividing `o(θ)`, coprime to `p`. -/
theorem IsIrreducibleCharacter.exists_extension_not_dvd_orderOf_determinant [Finite K]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ) {g : K}
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hinv : ClassFunction.conjBy g θ = θ)
    {p : ℕ} (hp : p.Prime) (hidx : H.index = p)
    {d : ℕ} (hd : θ 1 = (d : ℂ)) (hpd : ¬ p ∣ d)
    (ho : ¬ p ∣ orderOf hθ.determinant) :
    ∃ (χ : ClassFunction K ℂ) (hχ : IsIrreducibleCharacter χ),
      ClassFunction.restrict H χ = θ ∧ ¬ p ∣ orderOf hχ.determinant := by
  obtain ⟨χ', hχ', hr⟩ := hθ.exists_extension_of_conjBy_eq hgen hinv
  subst hr
  let : Fintype K := Fintype.ofFinite K
  have : Invertible (Nat.card K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hdet_res : hθ.determinant = hχ'.determinant.comp H.subtype :=
    hχ'.determinant_restrict hθ
  -- `(det χ')^{o(θ)}` is trivial on `H`, hence `p`-torsion
  have hμH : ∀ h : ↥H,
      (hχ'.determinant ^ orderOf hθ.determinant) ((h : K)) = 1 := by
    intro h
    have e : hχ'.determinant ((h : K)) = hθ.determinant h := by rw [hdet_res]; rfl
    rw [MonoidHom.pow_apply, e, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
      MonoidHom.one_apply]
  have hμp : (hχ'.determinant ^ orderOf hθ.determinant) ^ p = 1 := by
    rw [← hidx]
    exact pow_index_eq_one_of_forall_coe_eq_one hμH
  -- Bézout adjustment: `β` is a power of `(det χ')^{o(θ)}` — so trivial on `H` — and the
  -- adjusted determinant `β^d · det χ'` has order dividing `o(θ)`
  obtain ⟨β, hβmem, hβpow⟩ := exists_mem_zpowers_pow_mul_pow_eq_one hχ'.determinant hμp
    ((hp.coprime_iff_not_dvd.mpr ho).symm.gcd_eq_one : Nat.gcd (orderOf hθ.determinant) p = 1)
    ((hp.coprime_iff_not_dvd.mpr hpd).symm.gcd_eq_one : Nat.gcd d p = 1)
  have hβH : ∀ h : ↥H, β ((h : K)) = 1 := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hβmem
    intro h
    rw [← hn, MonoidHom.zpow_apply, hμH, one_zpow]
  -- the twist `χ' · β` is the canonical extension
  have hχnew : IsIrreducibleCharacter (χ' * linearClassFunction β) :=
    isIrreducibleCharacter_mul_linearClassFunction hχ' β
  refine ⟨χ' * linearClassFunction β, hχnew, ?_, ?_⟩
  · exact ClassFunction.restrict_mul_of_apply_eq_one χ' (linearClassFunction β)
      fun x => by rw [linearClassFunction_apply, hβH x, Units.val_one]
  · -- the degree of `χ'` is `d`
    have hd₁ : χ' 1 = (d : ℂ) := by
      rw [← hd]
      change χ' (((1 : ↥H) : K)) = χ' 1
      rw [OneMemClass.coe_one]
    have hdet_new : hχnew.determinant = β ^ d * hχ'.determinant :=
      hχ'.determinant_mul_linearClassFunction β hχnew hd₁
    rw [hdet_new]
    intro hcon
    exact ho (hcon.trans (orderOf_dvd_of_pow_eq_one hβpow))

/-- **Uniqueness of the canonical extension** (Isaacs *CT* 6.25/6.28, uniqueness half; issue
9002 (v-c4)).  Let `[K:H] = p` be prime and let `θ = Res_H χ₁ = Res_H χ₂` be irreducible of
degree `d` with `p ∤ d`.  If both extensions have determinantal order coprime to `p`, they
are **equal**.

The twist `β` between them (`ExtensionLinearTwist`) satisfies: `β^p = 1` (trivial on `H`,
index-torsion) and `β^d = det χ₂ · (det χ₁)⁻¹` has order dividing both `p` and the coprime
number `o₁·o₂`, hence is trivial; then `p ∤ d` forces `β = 1`. -/
theorem extension_unique_of_not_dvd_orderOf_determinant [Finite K]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    {χ₁ χ₂ : ClassFunction K ℂ}
    (hχ₁ : IsIrreducibleCharacter χ₁) (hχ₂ : IsIrreducibleCharacter χ₂)
    (hr₁ : ClassFunction.restrict H χ₁ = θ) (hr₂ : ClassFunction.restrict H χ₂ = θ)
    {p : ℕ} (hp : p.Prime) (hidx : H.index = p)
    {d : ℕ} (hd : θ 1 = (d : ℂ)) (hpd : ¬ p ∣ d)
    (ho₁ : ¬ p ∣ orderOf hχ₁.determinant) (ho₂ : ¬ p ∣ orderOf hχ₂.determinant) :
    χ₂ = χ₁ := by
  -- the two extensions differ by a linear character `β` trivial on `H`
  obtain ⟨β, hβH, hβeq⟩ :=
    exists_linearClassFunction_mul_of_restrict_eq_restrict hχ₁ hχ₂
      (hr₁.trans hr₂.symm) (hr₁ ▸ hθ)
  -- the degree of `χ₁` is `d`
  have hd₁ : χ₁ 1 = (d : ℂ) := by
    rw [← hd, ← hr₁]
    change χ₁ (((1 : ↥H) : K)) = χ₁ 1
    rw [OneMemClass.coe_one]
  -- `β` is `p`-torsion
  have hβp : β ^ p = 1 := by
    rw [← hidx]
    exact pow_index_eq_one_of_forall_coe_eq_one hβH
  -- `β^d` is the determinantal drift, killed by both `p`-torsion and coprime order
  have hβd : β ^ d = hχ₂.determinant * hχ₁.determinant⁻¹ := by
    have h1 : hχ₂.determinant = β ^ d * hχ₁.determinant := by
      have h2 : ∀ (hχ₂' : IsIrreducibleCharacter (χ₁ * linearClassFunction β)),
          hχ₂'.determinant = β ^ d * hχ₁.determinant := fun hχ₂' =>
        IsIrreducibleCharacter.determinant_mul_linearClassFunction hχ₁ β hχ₂' hd₁
      calc hχ₂.determinant = (hβeq ▸ hχ₂ :
              IsIrreducibleCharacter (χ₁ * linearClassFunction β)).determinant := by
            congr 1
        _ = β ^ d * hχ₁.determinant := h2 _
    calc
      β ^ d = (β ^ d * hχ₁.determinant) * hχ₁.determinant⁻¹ :=
        (mul_inv_cancel_right (β ^ d) hχ₁.determinant).symm
      _ = hχ₂.determinant * hχ₁.determinant⁻¹ :=
        congrArg (· * hχ₁.determinant⁻¹) h1.symm
  have hβd1 : β ^ d = 1 := by
    have hdvd_p : orderOf (β ^ d) ∣ p := by
      refine orderOf_dvd_of_pow_eq_one ?_
      calc
        (β ^ d) ^ p = β ^ (d * p) := (pow_mul β d p).symm
        _ = β ^ (p * d) := by rw [Nat.mul_comm d p]
        _ = (β ^ p) ^ d := pow_mul β p d
        _ = (1 : K →* ℂˣ) ^ d := congrArg (· ^ d) hβp
        _ = 1 := @one_pow (K →* ℂˣ) _ d
    have hdvd_o : orderOf (β ^ d)
        ∣ orderOf hχ₂.determinant * orderOf hχ₁.determinant := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [hβd]
      have e1 : hχ₂.determinant
          ^ (orderOf hχ₂.determinant * orderOf hχ₁.determinant) = 1 := by
        calc
          hχ₂.determinant
              ^ (orderOf hχ₂.determinant * orderOf hχ₁.determinant) =
              (hχ₂.determinant ^ orderOf hχ₂.determinant)
                ^ orderOf hχ₁.determinant :=
            pow_mul hχ₂.determinant (orderOf hχ₂.determinant)
              (orderOf hχ₁.determinant)
          _ = (1 : K →* ℂˣ) ^ orderOf hχ₁.determinant :=
            congrArg (· ^ orderOf hχ₁.determinant)
              (pow_orderOf_eq_one hχ₂.determinant)
          _ = 1 := @one_pow (K →* ℂˣ) _ (orderOf hχ₁.determinant)
      have e2 : (hχ₁.determinant⁻¹)
          ^ (orderOf hχ₂.determinant * orderOf hχ₁.determinant) = 1 := by
        calc
          (hχ₁.determinant⁻¹)
              ^ (orderOf hχ₂.determinant * orderOf hχ₁.determinant) =
              (hχ₁.determinant⁻¹)
                ^ (orderOf hχ₁.determinant * orderOf hχ₂.determinant) := by
                  rw [Nat.mul_comm]
          _ = ((hχ₁.determinant⁻¹) ^ orderOf hχ₁.determinant)
                ^ orderOf hχ₂.determinant :=
            pow_mul hχ₁.determinant⁻¹ (orderOf hχ₁.determinant)
              (orderOf hχ₂.determinant)
          _ = ((hχ₁.determinant ^ orderOf hχ₁.determinant)⁻¹)
                ^ orderOf hχ₂.determinant :=
            congrArg (· ^ orderOf hχ₂.determinant)
              (inv_pow hχ₁.determinant (orderOf hχ₁.determinant))
          _ = ((1 : K →* ℂˣ)⁻¹) ^ orderOf hχ₂.determinant :=
            congrArg (fun z : K →* ℂˣ => z⁻¹ ^ orderOf hχ₂.determinant)
              (pow_orderOf_eq_one hχ₁.determinant)
          _ = (1 : K →* ℂˣ) ^ orderOf hχ₂.determinant :=
            congrArg (· ^ orderOf hχ₂.determinant) (@inv_one (K →* ℂˣ) _)
          _ = 1 := @one_pow (K →* ℂˣ) _ (orderOf hχ₂.determinant)
      calc
        (hχ₂.determinant * hχ₁.determinant⁻¹)
            ^ (orderOf hχ₂.determinant * orderOf hχ₁.determinant) =
            hχ₂.determinant ^ (orderOf hχ₂.determinant * orderOf hχ₁.determinant) *
              (hχ₁.determinant⁻¹)
                ^ (orderOf hχ₂.determinant * orderOf hχ₁.determinant) :=
          mul_pow hχ₂.determinant hχ₁.determinant⁻¹
            (orderOf hχ₂.determinant * orderOf hχ₁.determinant)
        _ = 1 * 1 := congrArg₂ (· * ·) e1 e2
        _ = 1 := @one_mul (K →* ℂˣ) _ (1 : K →* ℂˣ)
    have hcop : Nat.Coprime p (orderOf hχ₂.determinant * orderOf hχ₁.determinant) :=
      hp.coprime_iff_not_dvd.mpr (fun hcon => (hp.dvd_mul.mp hcon).elim ho₂ ho₁)
    exact orderOf_eq_one_iff.mp
      (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd_p hdvd_o))
  -- `p ∤ d` upgrades `β^d = 1`, `β^p = 1` to `β = 1`
  have hβ1 : β = 1 := by
    have hdvd_d : orderOf β ∣ d := orderOf_dvd_of_pow_eq_one hβd1
    have hdvd_p : orderOf β ∣ p := orderOf_dvd_of_pow_eq_one hβp
    have hcop : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hpd
    exact orderOf_eq_one_iff.mp
      (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd_p hdvd_d))
  rw [hβeq, hβ1, ClassFunction.mul_linearClassFunction_one]

/-- **The canonical extension preserves the determinantal order** (Isaacs *CT* 6.25(c); issue
9002 (v-c5)).  If `χ ∈ Irr(K)` extends `θ ∈ Irr(H)` along a prime index `[K:H] = p` and
`p ∤ o(χ)`, then `o(χ) = o(θ)`.

`o(θ) ∣ o(χ)` because `det χ` restricts to `det θ`; conversely `(det χ)^{o(θ)}` is trivial
on `H`, hence `p`-torsion, so `o(χ) ∣ o(θ)·p`, and `p ∤ o(χ)` strips the factor `p`.  This
is the invariant that threads through the composition-series iterate (issue 9002 (v-d)): the
coprimality hypothesis `gcd([K:H], o(θ)·θ(1)) = 1` survives each prime-cyclic step. -/
theorem orderOf_determinant_eq_of_restrict_eq_of_not_dvd [Finite K]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    {χ : ClassFunction K ℂ} (hχ : IsIrreducibleCharacter χ)
    (hr : ClassFunction.restrict H χ = θ)
    {p : ℕ} (hp : p.Prime) (hidx : H.index = p)
    (ho : ¬ p ∣ orderOf hχ.determinant) :
    orderOf hχ.determinant = orderOf hθ.determinant := by
  subst hr
  have hdet_res : hθ.determinant = hχ.determinant.comp H.subtype :=
    hχ.determinant_restrict hθ
  -- `o(θ) ∣ o(χ)`: the restriction of `(det χ)^{o(χ)} = 1` kills `det θ`
  have h1 : orderOf hθ.determinant ∣ orderOf hχ.determinant := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hdet_res]
    refine MonoidHom.ext fun h => ?_
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply,
      pow_orderOf_eq_one, MonoidHom.one_apply, MonoidHom.one_apply]
  -- `o(χ) ∣ o(θ)·p`: `(det χ)^{o(θ)}` is trivial on `H`, hence `p`-torsion
  have h2 : orderOf hχ.determinant ∣ orderOf hθ.determinant * p := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_mul, ← hidx]
    refine pow_index_eq_one_of_forall_coe_eq_one fun h => ?_
    have e : hχ.determinant ((h : K)) = hθ.determinant h := by rw [hdet_res]; rfl
    rw [MonoidHom.pow_apply, e, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
      MonoidHom.one_apply]
  exact Nat.dvd_antisymm
    ((Nat.Coprime.dvd_mul_right ((hp.coprime_iff_not_dvd.mpr ho).symm)).mp h2) h1

open scoped commutatorElement in
/-- Strong-induction engine for
`IsIrreducibleCharacter.exists_extension_of_forall_conjBy_eq` — see that theorem for the
mathematical statement.  The index `[K:H]` is generalized to `n` and all data are
`∀`-quantified so that the inductive step can recurse to the intermediate subgroup `N₁`
(with `[K:N₁] = [K:H]/p < [K:H]`) produced by Cauchy's theorem in `K ⧸ H`. -/
theorem exists_extension_of_forall_conjBy_eq_aux {K : Type*} [Group K] [Finite K] (n : ℕ) :
    ∀ (H : Subgroup K) [H.Normal] (θ : ClassFunction ↥H ℂ)
      (hθ : IsIrreducibleCharacter θ), H.index = n →
      (∀ y : K, ClassFunction.conjBy y θ = θ) →
      (∀ x y : K, ⁅x, y⁆ ∈ H) →
      ∀ d : ℕ, θ 1 = (d : ℂ) →
      Nat.Coprime H.index (orderOf hθ.determinant * d) →
      ∃ (χ : ClassFunction K ℂ) (hχ : IsIrreducibleCharacter χ),
        ClassFunction.restrict H χ = θ ∧
          orderOf hχ.determinant = orderOf hθ.determinant := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro H _ θ hθ hn hinv hab d hd hcop
  by_cases htop : H = ⊤
  · -- base case: `H = ⊤`, transport `θ` along `topEquiv`
    subst htop
    set e : K →* ↥(⊤ : Subgroup K) := (Subgroup.topEquiv (G := K)).symm.toMonoidHom with he
    have hsurj : Function.Surjective e := (Subgroup.topEquiv (G := K)).symm.surjective
    have hχ : IsIrreducibleCharacter (ClassFunction.compHom e θ) :=
      IsIrreducibleCharacter.compHom_of_surjective hsurj hθ
    refine ⟨ClassFunction.compHom e θ, hχ, ?_, ?_⟩
    · ext h
      exact congrArg θ (Subtype.ext rfl)
    · rw [hθ.determinant_compHom e hχ]
      exact orderOf_monoidHom_comp_of_surjective _ hsurj
  · -- inductive step: pick a prime-order element of `K ⧸ H` by Cauchy
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : K, x₀ ∉ H := by
      by_contra hcon
      push Not at hcon
      exact htop ((Subgroup.eq_top_iff' H).mpr hcon)
    have : Nontrivial (K ⧸ H) :=
      ⟨⟨QuotientGroup.mk x₀, 1, fun hcon => hx₀ ((QuotientGroup.eq_one_iff x₀).mp hcon)⟩⟩
    let : Fintype (K ⧸ H) := Fintype.ofFinite _
    set p := (Nat.card (K ⧸ H)).minFac with hp_def
    have hp : p.Prime := Nat.minFac_prime (Finite.one_lt_card (α := K ⧸ H)).ne'
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨xbar, hxbar⟩ := exists_prime_orderOf_dvd_card (G := K ⧸ H) p
      (by rw [← Nat.card_eq_fintype_card]; exact Nat.minFac_dvd _)
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective H xbar
    -- the intermediate subgroup `N₁`, the preimage of `⟨xbar⟩`
    set N₁ : Subgroup K := Subgroup.comap (QuotientGroup.mk' H) (Subgroup.zpowers xbar)
      with hN₁_def
    have hHN₁ : H ≤ N₁ := fun a ha => by
      have h1 : QuotientGroup.mk' H a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
      change QuotientGroup.mk' H a ∈ Subgroup.zpowers xbar
      rw [h1]
      exact one_mem _
    have hN₁normal : N₁.Normal := by
      constructor
      intro a ha y
      have h1 : y * a * y⁻¹ = ⁅y, a⁆ * a := by
        rw [commutatorElement_def]
        group
      rw [h1]
      exact N₁.mul_mem (hHN₁ (hab y a)) ha
    have : (H.subgroupOf N₁).Normal := ‹H.Normal›.subgroupOf N₁
    -- the relative index `[N₁ : H]` is `p`
    have hrel : (H.subgroupOf N₁).index = p := by
      have h1 : Subgroup.comap (QuotientGroup.mk' H) (⊥ : Subgroup (K ⧸ H)) = H := by
        rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
      calc (H.subgroupOf N₁).index
          = Subgroup.relIndex H N₁ := rfl
        _ = Subgroup.relIndex (Subgroup.comap (QuotientGroup.mk' H) ⊥) N₁ := by rw [h1]
        _ = Subgroup.relIndex ⊥ (Subgroup.map (QuotientGroup.mk' H) N₁) :=
            Subgroup.relIndex_comap ⊥ (QuotientGroup.mk' H) N₁
        _ = Nat.card (Subgroup.map (QuotientGroup.mk' H) N₁) :=
            Subgroup.relIndex_bot_left _
        _ = p := by
            rw [hN₁_def, Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective H), Nat.card_zpowers, hxbar]
    -- index bookkeeping for the recursion
    have hmul : p * N₁.index = H.index := by
      rw [← hrel]
      exact Subgroup.relIndex_mul_index hHN₁
    have hNindex_ne : N₁.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hlt : N₁.index < n := by
      rw [← hn, ← hmul]
      calc N₁.index < 2 * N₁.index := by omega
        _ ≤ p * N₁.index := Nat.mul_le_mul_right _ hp.two_le
    have hpdvd : p ∣ H.index := ⟨N₁.index, hmul.symm⟩
    have hNdvd : N₁.index ∣ H.index := ⟨p, by rw [← hmul]; ring⟩
    -- coprimality specialized at `p`
    have hcop_p : Nat.Coprime p (orderOf hθ.determinant * d) :=
      Nat.Coprime.coprime_dvd_left hpdvd hcop
    have hpo : ¬ p ∣ orderOf hθ.determinant :=
      hp.coprime_iff_not_dvd.mp (hcop_p.coprime_dvd_right (dvd_mul_right _ d))
    have hpd : ¬ p ∣ d :=
      hp.coprime_iff_not_dvd.mp (hcop_p.coprime_dvd_right (dvd_mul_left d _))
    -- transport `θ` to the subgroup-of-subgroup `H.subgroupOf N₁`
    set e : ↥(H.subgroupOf N₁) ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHN₁ with he
    set θ' : ClassFunction ↥(H.subgroupOf N₁) ℂ := ClassFunction.compHom e.toMonoidHom θ
      with hθ'_def
    have hθ' : IsIrreducibleCharacter θ' :=
      IsIrreducibleCharacter.compHom_of_surjective e.surjective hθ
    have hodet' : orderOf hθ'.determinant = orderOf hθ.determinant := by
      rw [hθ.determinant_compHom e.toMonoidHom hθ']
      exact orderOf_monoidHom_comp_of_surjective _ e.surjective
    have hd' : θ' 1 = (d : ℂ) := by
      rw [hθ'_def, ClassFunction.compHom_apply, map_one, hd]
    -- the generator of `N₁ ⧸ H` coming from `xbar`
    set g₁ : ↥N₁ := ⟨x, show QuotientGroup.mk' H x ∈ Subgroup.zpowers xbar from
      hx ▸ Subgroup.mem_zpowers xbar⟩ with hg₁
    have hgen₁ : ∀ kk : ↥N₁, ∃ i : ℤ, (g₁ ^ i)⁻¹ * kk ∈ H.subgroupOf N₁ := by
      intro kk
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
        (show QuotientGroup.mk' H (kk : K) ∈ Subgroup.zpowers xbar from kk.2)
      refine ⟨i, ?_⟩
      rw [Subgroup.mem_subgroupOf]
      show (((g₁ ^ i)⁻¹ * kk : ↥N₁) : K) ∈ H
      have hg₁x : (g₁ : K) = x := rfl
      rw [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow, hg₁x,
        ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply H, map_mul, map_inv,
        map_zpow, hx, hi, inv_mul_cancel]
    -- `θ'` is invariant under the generator, by `K`-invariance of `θ`
    have hinv₁ : ClassFunction.conjBy g₁ θ' = θ' := by
      ext h'
      have key := congrFun (congrArg (fun f : ClassFunction ↥H ℂ => (f : ↥H → ℂ)) (hinv x))
        (⟨((h' : ↥N₁) : K), h'.2⟩ : ↥H)
      calc (ClassFunction.conjBy g₁ θ') h'
          = θ ⟨x * ((h' : ↥N₁) : K) * x⁻¹,
              ‹H.Normal›.conj_mem _ h'.2 x⟩ := by exact congrArg θ (Subtype.ext rfl)
        _ = θ ⟨((h' : ↥N₁) : K), h'.2⟩ := by
            exact (congrArg θ (Subtype.ext rfl)).trans key
        _ = θ' h' := by exact congrArg θ (Subtype.ext rfl)
    -- canonical extension of `θ'` to `N₁` (the prime-cyclic step)
    obtain ⟨χ₁, hχ₁, hres₁, hpo₁⟩ :=
      hθ'.exists_extension_not_dvd_orderOf_determinant hgen₁ hinv₁ hp hrel hd' hpd
        (by rwa [hodet'])
    have ho₁ : orderOf hχ₁.determinant = orderOf hθ.determinant :=
      (orderOf_determinant_eq_of_restrict_eq_of_not_dvd hθ' hχ₁ hres₁ hp hrel hpo₁).trans
        hodet'
    have hd₁ : χ₁ 1 = (d : ℂ) := by
      rw [← hd']
      rw [← hres₁]
      change χ₁ (((1 : ↥(H.subgroupOf N₁)) : ↥N₁)) = χ₁ 1
      rw [OneMemClass.coe_one]
    -- `K`-invariance of `χ₁`, by uniqueness of the canonical extension
    have hinvχ₁ : ∀ y : K, ClassFunction.conjBy y χ₁ = χ₁ := by
      intro y
      have hχ₂ : IsIrreducibleCharacter (ClassFunction.conjBy y χ₁) :=
        ClassFunction.IsIrreducibleCharacter.conjBy (H := N₁) hχ₁ y
      -- the conjugate still restricts to `θ'`
      have hres₂ : ClassFunction.restrict (H.subgroupOf N₁) (ClassFunction.conjBy y χ₁)
          = θ' := by
        ext h'
        have hwH : y * ((h' : ↥N₁) : K) * y⁻¹ ∈ H := ‹H.Normal›.conj_mem _ h'.2 y
        have key := congrFun (congrArg (fun f : ClassFunction ↥H ℂ => (f : ↥H → ℂ)) (hinv y))
          (⟨((h' : ↥N₁) : K), h'.2⟩ : ↥H)
        have key₁ := congrFun (congrArg
            (fun f : ClassFunction ↥(H.subgroupOf N₁) ℂ => (f : ↥(H.subgroupOf N₁) → ℂ)) hres₁)
          ((⟨⟨y * ((h' : ↥N₁) : K) * y⁻¹, hHN₁ hwH⟩, hwH⟩ : ↥(H.subgroupOf N₁)))
        calc (ClassFunction.restrict (H.subgroupOf N₁) (ClassFunction.conjBy y χ₁)) h'
            = χ₁ ⟨y * ((h' : ↥N₁) : K) * y⁻¹, hHN₁ hwH⟩ := by
              exact congrArg χ₁ (Subtype.ext rfl)
          _ = θ' ⟨⟨y * ((h' : ↥N₁) : K) * y⁻¹, hHN₁ hwH⟩, hwH⟩ := by exact key₁
          _ = θ ⟨y * ((h' : ↥N₁) : K) * y⁻¹, hwH⟩ := by
              exact congrArg θ (Subtype.ext rfl)
          _ = θ ⟨((h' : ↥N₁) : K), h'.2⟩ := by
              exact (congrArg θ (Subtype.ext rfl)).trans key
          _ = θ' h' := by exact congrArg θ (Subtype.ext rfl)
      -- the conjugate has the same determinantal order
      have hpo₂ : ¬ p ∣ orderOf hχ₂.determinant := by
        rw [hχ₁.determinant_conjBy y hχ₂,
          orderOf_monoidHom_comp_of_surjective _
            (ClassFunction.conjByMulEquiv (G := K) (H := N₁) y).surjective]
        exact hpo₁
      exact extension_unique_of_not_dvd_orderOf_determinant hθ' hχ₁ hχ₂ hres₁ hres₂ hp
        hrel hd' hpd hpo₁ hpo₂
    -- recurse on `N₁` (the index dropped by the factor `p`)
    obtain ⟨χ, hχ, hresN₁, hordχ⟩ := IH N₁.index hlt N₁ χ₁ hχ₁ rfl hinvχ₁
      (fun a b => hHN₁ (hab a b)) d hd₁
      (by rw [ho₁]; exact Nat.Coprime.coprime_dvd_left hNdvd hcop)
    refine ⟨χ, hχ, ?_, hordχ.trans ho₁⟩
    -- `Res_H χ = θ` via `Res_{N₁}` and the transport
    ext h
    have hmemN₁ : (h : K) ∈ N₁ := hHN₁ h.2
    have key₁ := congrFun (congrArg (fun f : ClassFunction ↥N₁ ℂ => (f : ↥N₁ → ℂ)) hresN₁)
      (⟨(h : K), hmemN₁⟩ : ↥N₁)
    have key₂ := congrFun (congrArg
        (fun f : ClassFunction ↥(H.subgroupOf N₁) ℂ => (f : ↥(H.subgroupOf N₁) → ℂ)) hres₁)
      ((⟨⟨(h : K), hmemN₁⟩, h.2⟩ : ↥(H.subgroupOf N₁)))
    calc (ClassFunction.restrict H χ) h
        = (ClassFunction.restrict N₁ χ) ⟨(h : K), hmemN₁⟩ := rfl
      _ = χ₁ ⟨(h : K), hmemN₁⟩ := key₁
      _ = θ' ⟨⟨(h : K), hmemN₁⟩, h.2⟩ := by exact key₂
      _ = θ h := by exact congrArg θ (Subtype.ext rfl)

open scoped commutatorElement in
/-- **Extension along an abelian coprime quotient — Isaacs, _Character Theory_, Theorem 8.16
(abelian case) / Corollary 6.28** (issue 9002 (v-d)).  Let `H ⊴ K` with `K` finite and
`K ⧸ H` abelian (hypothesis `hab`: all commutators lie in `H`), and let `θ ∈ Irr(H)` be
`K`-invariant of degree `d` with `gcd([K:H], o(θ)·d) = 1`, where `o(θ)` is the order of the
determinantal character of `θ`.  Then `θ` **extends** to `χ ∈ Irr(K)`, with the same
determinantal order `o(χ) = o(θ)`.

Induction on `[K:H]`: Cauchy's theorem provides `N₁/H ≤ K/H` of prime order `p` (with
`N₁ ⊴ K` since `K/H` is abelian); the prime-cyclic step
(`exists_extension_not_dvd_orderOf_determinant`) canonically extends `θ` to `χ₁ ∈ Irr(N₁)`,
whose **uniqueness** (`extension_unique_of_not_dvd_orderOf_determinant`) forces `χ₁` to be
`K`-invariant — its conjugates are extensions of `θ` with the same determinantal order.
Since `o(χ₁)·χ₁(1) = o(θ)·d` and `[K:N₁] = [K:H]/p`, the coprimality descends and the
recursion closes.

This is the (G1) extension input to Gallagher's theorem for the constructive Clifford
decomposition (Peterfalvi (1.7)(c)): in the type-I application `H = L_F` is a normal Hall
subgroup and `I(θ)/H` is abelian, so `o(θ)·θ(1) ∣ |H|` is coprime to `[I(θ):H]`.  (The coprimality
is what makes this the book's (1.7)(c); the multiplicity-`e` (1.7)(b) drops it.) -/
theorem IsIrreducibleCharacter.exists_extension_of_forall_conjBy_eq [Finite K]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hinv : ∀ y : K, ClassFunction.conjBy y θ = θ)
    (hab : ∀ x y : K, ⁅x, y⁆ ∈ H)
    {d : ℕ} (hd : θ 1 = (d : ℂ))
    (hcop : Nat.Coprime H.index (orderOf hθ.determinant * d)) :
    ∃ (χ : ClassFunction K ℂ) (hχ : IsIrreducibleCharacter χ),
      ClassFunction.restrict H χ = θ ∧
        orderOf hχ.determinant = orderOf hθ.determinant :=
  exists_extension_of_forall_conjBy_eq_aux H.index H θ hθ rfl hinv hab d hd hcop

end OddOrder.RepresentationTheory


