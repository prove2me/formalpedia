-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclicExtension
-- name    : OddOrder_GroupTheory_RepresentationTheory_CyclicExtension
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:46:22.2962+00:00
-- url     : https://prove2.me/theorems/3e4707d8-bf69-450b-890c-0de481fcafc2
-- title:
--   Extension of an invariant irreducible representation along a cyclic quotient
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Proposition 2.2(b): let $H\trianglelefteq K$ with $K/H$ cyclic, $F$ an algebraically closed field and $M$ an irreducible $FH$-module with $M\cong M^x$ for all $x\in K$. Then the representation of $H$ on $M$ extends to $K$.
--
--   Main definitions: `conjRep` (the conjugate representation $\rho^g$ of a normal subgroup's representation), `cyclicExtensionUnit` (the unit-valued extension function $g^ih\mapsto P^i\rho(h)$) and `cyclicExtension` (the extension representation, following Isaacs 11.22), together with the lemmas on conjugation units that make it well defined.
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CyclicExtension.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CyclicExtension.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_Inertia
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible

namespace OddOrder.RepresentationTheory

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

section ConjRep

/-- The **conjugate representation** `ρ^g` of a representation `ρ` of a normal subgroup
`H ⊴ K` by an ambient element `g : K`: it acts by `(ρ^g)(h) = ρ(g h g⁻¹)`.  Its character
is Peterfalvi's conjugate character `θ^g` (`ClassFunction.conjBy`). -/
def conjRep (ρ : Representation F ↥H V) (g : K) : Representation F ↥H V :=
  ρ.comp (ClassFunction.conjByMulEquiv (G := K) (H := H) g).toMonoidHom

@[simp] theorem conjRep_apply (ρ : Representation F ↥H V) (g : K) (h : ↥H) :
    conjRep ρ g h = ρ (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) :=
  rfl

/-- The character of the conjugate representation is the conjugate of the character. -/
theorem conjRep_character (ρ : Representation F ↥H V) (g : K) (h : ↥H) :
    (conjRep ρ g).character h
      = ρ.character (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) :=
  rfl

/-- **Irreducibility ascends along any precomposition.**  If `σ ∘ f` is irreducible for
*some* homomorphism `f : H' →* G'`, then `σ` is irreducible: a `σ`-invariant submodule is in
particular `σ ∘ f`-invariant.  (No surjectivity of `f` is needed, in contrast to the
descent direction `isIrreducible_comp_of_surjective`.) -/
theorem Representation.isIrreducible_of_isIrreducible_comp
    {G' H' : Type*} [Group G'] [Group H'] {f : H' →* G'}
    (σ : Representation F G' V) (hσ : Representation.IsIrreducible (σ.comp f)) :
    Representation.IsIrreducible σ := by
  have h1 : IsSimpleOrder (Subrepresentation (σ.comp f)) := hσ
  have := h1.toNontrivial
  -- restrict the invariance condition of a `σ`-subrepresentation to the image of `f`
  let ι : Subrepresentation σ → Subrepresentation (σ.comp f) := fun R =>
    { toSubmodule := R.toSubmodule
      apply_mem_toSubmodule := fun h _v hv => R.apply_mem_toSubmodule (f h) hv }
  have hbotS : (⊥ : Subrepresentation σ).toSubmodule = ⊥ := rfl
  have htopS : (⊤ : Subrepresentation σ).toSubmodule = ⊤ := rfl
  have hbotC : (⊥ : Subrepresentation (σ.comp f)).toSubmodule = ⊥ := rfl
  have htopC : (⊤ : Subrepresentation (σ.comp f)).toSubmodule = ⊤ := rfl
  -- `⊥ ≠ ⊤` in `Submodule F V`, read off from the simple order on `Subrepresentation (σ.comp f)`.
  have hVne : (⊥ : Submodule F V) ≠ ⊤ := fun h2 =>
    bot_ne_top (α := Subrepresentation (σ.comp f))
      (Subrepresentation.toSubmodule_injective (by rw [hbotC, htopC]; exact h2))
  have hnt : Nontrivial (Subrepresentation σ) :=
    ⟨⟨⊥, ⊤, fun hbt => hVne (by rw [← hbotS, hbt, htopS])⟩⟩
  exact ⟨fun S => by
    rcases h1.eq_bot_or_eq_top (ι S) with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        ((congrArg Subrepresentation.toSubmodule h).trans hbotC))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        ((congrArg Subrepresentation.toSubmodule h).trans htopC))⟩

/-- The conjugate of an irreducible representation is irreducible: `ρ = (ρ^g) ∘ (conj g⁻¹)`,
so irreducibility of `ρ` ascends to `ρ^g` by `isIrreducible_of_isIrreducible_comp`. -/
theorem isIrreducible_conjRep (ρ : Representation F ↥H V) [Representation.IsIrreducible ρ]
    (g : K) : Representation.IsIrreducible (conjRep ρ g) := by
  have hcomp : (conjRep ρ g).comp
      (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹).toMonoidHom = ρ := by
    refine MonoidHom.ext fun h => ?_
    calc ((conjRep ρ g).comp
          (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹).toMonoidHom) h
        = ρ ((ClassFunction.conjByMulEquiv (G := K) (H := H) g)
            ((ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹) h)) := rfl
      _ = ρ h := by rw [ClassFunction.conjByMulEquiv_mul, mul_inv_cancel,
            ClassFunction.conjByMulEquiv_one]
  exact Representation.isIrreducible_of_isIrreducible_comp (conjRep ρ g)
    (hcomp ▸ ‹Representation.IsIrreducible ρ›)

end ConjRep

section Intertwiner

/-- **The conjugation unit** (step 1).  An equivalence `ρ ≅ ρ^g` — Bender-Glauberman's
hypothesis `M ≅ M^x` — packaged as a unit `P` of the endomorphism ring satisfying
`P · ρ(h) = ρ(g h g⁻¹) · P` for all `h ∈ H`, with `ρ(h)` written as `ρ.asGroupHom h`.

Over `ℂ` the equivalence is *derived* from equality of characters
(`nonempty_equiv_conjRep_of_character_eq`, which needs `char F ∤ |H|`); here it is taken as
given, so no characteristic hypothesis appears. -/
theorem exists_conjugation_unit_of_nonempty_equiv (ρ : Representation F ↥H V) (g : K)
    (hequiv : Nonempty (ρ.Equiv (conjRep ρ g))) :
    ∃ P : (Module.End F V)ˣ, ∀ h : ↥H,
      P * ρ.asGroupHom h
        = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P := by
  obtain ⟨φ⟩ := hequiv
  refine ⟨⟨φ.toLinearMap, φ.toLinearEquiv.symm.toLinearMap,
    LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩, fun h => ?_⟩
  · rw [Module.End.mul_apply]
    exact φ.toLinearEquiv.apply_symm_apply v
  · rw [Module.End.mul_apply]
    exact φ.toLinearEquiv.symm_apply_apply v
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    change φ.toLinearMap * (ρ.asGroupHom h : Module.End F V)
      = (ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)
          : Module.End F V) * φ.toLinearMap
    rw [Representation.asGroupHom_apply, Representation.asGroupHom_apply,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact φ.isIntertwining' h

end Intertwiner

section Normalization

variable [FiniteDimensional F V]

/-- **Schur's lemma, commutant form.**  An endomorphism commuting with every `ρ x` of a
finite-dimensional irreducible representation over an algebraically closed field is a scalar
multiple of the identity. -/
theorem exists_smul_id_of_forall_mul_comm {G' : Type*} [Group G'] [IsAlgClosed F]
    (ρ : Representation F G' V) [Representation.IsIrreducible ρ]
    (T : Module.End F V) (hT : ∀ x : G', ρ x * T = T * ρ x) :
    ∃ c : F, T = c • LinearMap.id := by
  have hT' : ∀ (x : G') (v : V), T (ρ x v) = ρ x (T v) := fun x v => by
    have h1 := LinearMap.congr_fun (hT x) v
    simpa only [Module.End.mul_apply] using h1.symm
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective (T.intertwiningMap_of_isIntertwiningMap ρ ρ hT')
  refine ⟨c, ?_⟩
  have hL : T = (algebraMap F (Representation.IntertwiningMap ρ ρ) c).toLinearMap := by
    rw [hc]
    rfl
  rw [hL, Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul]
  congr 1

variable {ρ : Representation F ↥H V} {g : K} {P : (Module.End F V)ˣ}

omit [FiniteDimensional F V] in
/-- The inverse of a conjugation unit conjugates in the opposite direction:
`P⁻¹ · ρ(h) = ρ(g⁻¹ h g) · P⁻¹`. -/
theorem conjugation_unit_inv_comm
    (hP : ∀ h : ↥H, P * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P) (h : ↥H) :
    P⁻¹ * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h) * P⁻¹ := by
  have key := hP (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h)
  rw [ClassFunction.conjByMulEquiv_mul, mul_inv_cancel,
    ClassFunction.conjByMulEquiv_one] at key
  calc P⁻¹ * ρ.asGroupHom h
      = P⁻¹ * (ρ.asGroupHom h * P) * P⁻¹ := by group
    _ = P⁻¹ * (P * ρ.asGroupHom
          (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h)) * P⁻¹ := by rw [← key]
    _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h) * P⁻¹ := by
        group

omit [FiniteDimensional F V] in
/-- **Iterated conjugation** (toward step 2).  A conjugation unit for `g` conjugates by `g^i`
after taking the `i`-th power: `P^i · ρ(h) = ρ(g^i h g^{-i}) · P^i` for every `i : ℤ`. -/
theorem conjugation_unit_zpow_comm
    (hP : ∀ h : ↥H, P * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P) :
    ∀ (i : ℤ) (h : ↥H), P ^ i * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ i) h) * P ^ i := by
  intro i
  induction i using Int.induction_on with
  | zero =>
    intro h
    rw [zpow_zero P, zpow_zero g, ClassFunction.conjByMulEquiv_one, one_mul, mul_one]
  | succ i ih =>
    intro h
    rw [zpow_add_one P (i : ℤ), zpow_add_one g (i : ℤ)]
    calc P ^ (i : ℤ) * P * ρ.asGroupHom h
        = P ^ (i : ℤ) * (P * ρ.asGroupHom h) := by group
      _ = P ^ (i : ℤ) * (ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P) := by rw [hP h]
      _ = P ^ (i : ℤ) * ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P := by group
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ (i : ℤ))
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)) * P ^ (i : ℤ) * P := by
          rw [ih (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)]
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ (i : ℤ) * g) h)
            * (P ^ (i : ℤ) * P) := by rw [ClassFunction.conjByMulEquiv_mul]; group
  | pred i ih =>
    intro h
    rw [zpow_sub_one P (-(i : ℤ)), zpow_sub_one g (-(i : ℤ))]
    calc P ^ (-(i : ℤ)) * P⁻¹ * ρ.asGroupHom h
        = P ^ (-(i : ℤ)) * (P⁻¹ * ρ.asGroupHom h) := by group
      _ = P ^ (-(i : ℤ)) * (ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h) * P⁻¹) := by
          rw [conjugation_unit_inv_comm hP h]
      _ = P ^ (-(i : ℤ)) * ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h) * P⁻¹ := by group
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ (-(i : ℤ)))
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h))
            * P ^ (-(i : ℤ)) * P⁻¹ := by
          rw [ih (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h)]
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H)
            (g ^ (-(i : ℤ)) * g⁻¹) h) * (P ^ (-(i : ℤ)) * P⁻¹) := by
          rw [ClassFunction.conjByMulEquiv_mul]; group

/-- **The normalized conjugation unit** (steps 2-3 of BG Prop 2.2(b)).  For an irreducible `ρ`
equivalent to its `g`-conjugate `ρ^g`, there is a unit `P` that

* conjugates `ρ(h)` to `ρ(g h g⁻¹)`: `P · ρ(h) = ρ(g h g⁻¹) · P`, and
* satisfies `P ^ t = ρ(g ^ t)` for **every** `t : ℤ` with `g ^ t ∈ H`.

The intertwiner of `exists_conjugation_unit_of_nonempty_equiv` satisfies the second condition
only up to a scalar (Schur's lemma applied to `ρ(g^m)⁻¹ P^m`, where `m` is the order of `gH`
in `K/H`); rescaling by an `m`-th root of that scalar — available over any algebraically
closed field, in any characteristic — repairs it, first at `t = m` and then for all multiples
of `m`, i.e. for all valid `t`. -/
theorem exists_normalized_conjugation_unit_of_nonempty_equiv [Finite K] [IsAlgClosed F]
    (ρ : Representation F ↥H V) [Representation.IsIrreducible ρ] (g : K)
    (hequiv : Nonempty (ρ.Equiv (conjRep ρ g))) :
    ∃ P : (Module.End F V)ˣ,
      (∀ h : ↥H, P * ρ.asGroupHom h
        = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P) ∧
      ∀ (t : ℤ) (ht : g ^ t ∈ H), P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩ := by
  obtain ⟨P₀, hP₀⟩ := exists_conjugation_unit_of_nonempty_equiv ρ g hequiv
  -- the order `m` of `gH` in `K/H`; `{t : ℤ | g^t ∈ H} = mℤ`
  set m : ℕ := orderOf (QuotientGroup.mk' H g) with hm
  have hm0 : 0 < m := orderOf_pos _
  have hgm : g ^ m ∈ H := by
    have h1 : (QuotientGroup.mk' H) (g ^ m) = 1 := by
      rw [map_pow]
      exact pow_orderOf_eq_one _
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hdvd : ∀ t : ℤ, g ^ t ∈ H → (m : ℤ) ∣ t := by
    intro t ht
    rw [hm, orderOf_dvd_iff_zpow_eq_one, ← map_zpow, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ht
  -- `T := ρ(g^m)⁻¹ · P₀^m` commutes with the image of `ρ` …
  set R : (Module.End F V)ˣ := ρ.asGroupHom ⟨g ^ m, hgm⟩ with hR
  have hTcomm : ∀ h : ↥H,
      ρ h * ((R⁻¹ * P₀ ^ (m : ℤ) : (Module.End F V)ˣ) : Module.End F V)
      = ((R⁻¹ * P₀ ^ (m : ℤ) : (Module.End F V)ˣ) : Module.End F V) * ρ h := by
    intro h
    have h2 : ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ (m : ℤ)) h
        = ⟨g ^ m, hgm⟩ * h * (⟨g ^ m, hgm⟩ : ↥H)⁻¹ := by
      apply Subtype.ext
      rw [ClassFunction.conjByMulEquiv_apply, zpow_natCast]
      rfl
    have h1 := conjugation_unit_zpow_comm hP₀ (m : ℤ) h
    rw [h2, map_mul, map_mul, map_inv, ← hR] at h1
    -- h1 : P₀^m * ρ(h) = (R · ρ(h) · R⁻¹) · P₀^m; rearrange to the commutant form
    have hu : ρ.asGroupHom h * (R⁻¹ * P₀ ^ (m : ℤ))
        = (R⁻¹ * P₀ ^ (m : ℤ)) * ρ.asGroupHom h := by
      calc ρ.asGroupHom h * (R⁻¹ * P₀ ^ (m : ℤ))
          = R⁻¹ * (R * ρ.asGroupHom h * R⁻¹ * P₀ ^ (m : ℤ)) := by group
        _ = R⁻¹ * (P₀ ^ (m : ℤ) * ρ.asGroupHom h) := by rw [← h1]
        _ = (R⁻¹ * P₀ ^ (m : ℤ)) * ρ.asGroupHom h := by group
    have := congrArg Units.val hu
    simpa only [Units.val_mul, Representation.asGroupHom_apply] using this
  -- … hence is a nonzero scalar `c` by Schur
  obtain ⟨c, hc⟩ := exists_smul_id_of_forall_mul_comm ρ _ hTcomm
  have : Nontrivial V := by
    have h1 : Nontrivial (Subrepresentation ρ) := IsSimpleOrder.toNontrivial
    have h2 : Nontrivial (Submodule F V) :=
      (Subrepresentation.toSubmodule_injective (ρ := ρ)).nontrivial
    exact (Submodule.nontrivial_iff F).mp h2
  have : Nontrivial (Module.End F V) := ⟨1, 0, fun h1 => by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (by simpa using LinearMap.congr_fun h1 v)⟩
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact Units.ne_zero (R⁻¹ * P₀ ^ (m : ℤ)) hc
  -- an `m`-th root `z` of `c⁻¹` rescales `P₀` into the normalized unit
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) hm0
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm0.ne'] at hz
    exact inv_ne_zero hc0 hz.symm
  -- scalar units are central in `(Module.End F V)ˣ`
  set U : Fˣ →* (Module.End F V)ˣ :=
    Units.map (algebraMap F (Module.End F V)).toMonoidHom with hUdef
  have hUval : ∀ w : Fˣ,
      ((U w : (Module.End F V)ˣ) : Module.End F V) = algebraMap F _ (w : F) := fun _ => rfl
  have hUcentral : ∀ (w : Fˣ) (x : (Module.End F V)ˣ), U w * x = x * U w := fun w x =>
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, hUval]
      exact Algebra.commutes (w : F) (x : Module.End F V))
  refine ⟨U (Units.mk0 z hz0) * P₀, fun h => ?_, ?_⟩
  · -- the intertwining property survives the scalar twist
    calc U (Units.mk0 z hz0) * P₀ * ρ.asGroupHom h
        = U (Units.mk0 z hz0) * (P₀ * ρ.asGroupHom h) := by group
      _ = U (Units.mk0 z hz0) * (ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P₀) := by rw [hP₀ h]
      _ = U (Units.mk0 z hz0) * ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P₀ := by group
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)
            * U (Units.mk0 z hz0) * P₀ := by rw [hUcentral]
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)
            * (U (Units.mk0 z hz0) * P₀) := by group
  · -- normalization: `P^t = ρ(g^t)` whenever `g^t ∈ H`
    intro t ht
    obtain ⟨s, rfl⟩ := hdvd t ht
    -- at `t = m`: `P₀^m = R · (c-scalar)`, and the `z`-twist cancels the scalar
    have hT : R⁻¹ * P₀ ^ (m : ℤ) = U (Units.mk0 c hc0) := Units.ext (by
      rw [hUval, hc]
      exact (Module.algebraMap_end_eq_smul_id F F V c).symm)
    have hP₀m : P₀ ^ (m : ℤ) = R * U (Units.mk0 c hc0) := by
      rw [← hT]
      group
    have hUm : U (Units.mk0 z hz0) ^ (m : ℤ) * U (Units.mk0 c hc0) = 1 := by
      rw [← map_zpow, ← map_mul]
      have h3 : Units.mk0 z hz0 ^ (m : ℤ) * Units.mk0 c hc0 = 1 := Units.ext (by
        rw [Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
        change z ^ m * c = 1
        rw [hz, inv_mul_cancel₀ hc0])
      rw [h3, map_one]
    have hmove : U (Units.mk0 z hz0) ^ (m : ℤ) * (R * U (Units.mk0 c hc0))
        = R * (U (Units.mk0 z hz0) ^ (m : ℤ) * U (Units.mk0 c hc0)) := by
      rw [← map_zpow, ← mul_assoc, hUcentral _ R, mul_assoc]
    calc (U (Units.mk0 z hz0) * P₀) ^ ((m : ℤ) * s)
        = ((U (Units.mk0 z hz0) * P₀) ^ (m : ℤ)) ^ s := by rw [zpow_mul]
      _ = (U (Units.mk0 z hz0) ^ (m : ℤ) * P₀ ^ (m : ℤ)) ^ s := by
          rw [Commute.mul_zpow (hUcentral (Units.mk0 z hz0) P₀)]
      _ = (U (Units.mk0 z hz0) ^ (m : ℤ) * (R * U (Units.mk0 c hc0))) ^ s := by rw [hP₀m]
      _ = (R * (U (Units.mk0 z hz0) ^ (m : ℤ) * U (Units.mk0 c hc0))) ^ s := by rw [hmove]
      _ = R ^ s := by rw [hUm, mul_one]
      _ = ρ.asGroupHom ((⟨g ^ m, hgm⟩ : ↥H) ^ s) := by rw [hR, ← map_zpow]
      _ = ρ.asGroupHom ⟨g ^ ((m : ℤ) * s), ht⟩ := by
          congr 1
          apply Subtype.ext
          rw [SubgroupClass.coe_zpow]
          change ((g ^ m : K)) ^ s = g ^ ((m : ℤ) * s)
          rw [← zpow_natCast g m, ← zpow_mul]

end Normalization

section Extension

variable {ρ : Representation F ↥H V} {g : K} {P : (Module.End F V)ˣ}

/-- Commuting `ρ(h)` past `P^j` from the left: `ρ(h) · P^j = P^j · ρ(g^{-j} h g^j)`.  The
mirrored form of `conjugation_unit_zpow_comm`, used to normalize products in the extension's
multiplicativity proof. -/
theorem conjugation_unit_comm_zpow
    (hP : ∀ h : ↥H, P * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P)
    (j : ℤ) (h : ↥H) :
    ρ.asGroupHom h * P ^ j
      = P ^ j * ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ j)⁻¹ h) := by
  have h1 := conjugation_unit_zpow_comm hP j
    (ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ j)⁻¹ h)
  rw [ClassFunction.conjByMulEquiv_mul, mul_inv_cancel,
    ClassFunction.conjByMulEquiv_one] at h1
  exact h1.symm

omit hH in
/-- **Well-definedness of the extension** (step 4, key computation).  The value
`P^i · ρ(g^{-i} k)` does not depend on the choice of exponent `i` with `g^{-i} k ∈ H`:
any two such exponents differ by an element of `{t : ℤ | g^t ∈ H}`, where the normalization
`P^t = ρ(g^t)` makes the discrepancy cancel. -/
theorem cyclicExtension_zpow_mul_eq
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H), P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    {k : K} {i j : ℤ} (hi : (g ^ i)⁻¹ * k ∈ H) (hj : (g ^ j)⁻¹ * k ∈ H) :
    P ^ i * ρ.asGroupHom ⟨(g ^ i)⁻¹ * k, hi⟩
      = P ^ j * ρ.asGroupHom ⟨(g ^ j)⁻¹ * k, hj⟩ := by
  have hij : g ^ (i - j) ∈ H := by
    have heq : ((g ^ j)⁻¹ * k) * ((g ^ i)⁻¹ * k)⁻¹ = g ^ (i - j) := by group
    exact heq ▸ mul_mem hj (inv_mem hi)
  have hsplit : (⟨g ^ (i - j), hij⟩ : ↥H) * ⟨(g ^ i)⁻¹ * k, hi⟩ = ⟨(g ^ j)⁻¹ * k, hj⟩ :=
    Subtype.ext (by
      change g ^ (i - j) * ((g ^ i)⁻¹ * k) = (g ^ j)⁻¹ * k
      group)
  have hzp : P ^ i = P ^ j * P ^ (i - j) := by
    rw [← zpow_add]
    congr 1
    omega
  calc P ^ i * ρ.asGroupHom ⟨(g ^ i)⁻¹ * k, hi⟩
      = P ^ j * (P ^ (i - j) * ρ.asGroupHom ⟨(g ^ i)⁻¹ * k, hi⟩) := by
        rw [hzp, mul_assoc]
    _ = P ^ j * (ρ.asGroupHom ⟨g ^ (i - j), hij⟩ * ρ.asGroupHom ⟨(g ^ i)⁻¹ * k, hi⟩) := by
        rw [hPt (i - j) hij]
    _ = P ^ j * ρ.asGroupHom ⟨(g ^ j)⁻¹ * k, hj⟩ := by
        rw [← map_mul, hsplit]

variable (ρ g P) in
/-- The unit-valued extension function: `k = g^i h ↦ P^i · ρ(h)`, for a choice of exponent
`i` with `g^{-i} k ∈ H` (available since the image of `g` generates `K/H`).  Well-defined by
`cyclicExtension_zpow_mul_eq`. -/
noncomputable def cyclicExtensionUnit (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H) (k : K) :
    (Module.End F V)ˣ :=
  P ^ (hgen k).choose * ρ.asGroupHom ⟨(g ^ (hgen k).choose)⁻¹ * k, (hgen k).choose_spec⟩

omit hH in
/-- Evaluation of `cyclicExtensionUnit` at **any** valid exponent. -/
theorem cyclicExtensionUnit_eq
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H), P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    {k : K} (i : ℤ) (hi : (g ^ i)⁻¹ * k ∈ H) :
    cyclicExtensionUnit ρ g P hgen k = P ^ i * ρ.asGroupHom ⟨(g ^ i)⁻¹ * k, hi⟩ :=
  cyclicExtension_zpow_mul_eq hPt (hgen k).choose_spec hi

/-- The extension function is multiplicative. -/
theorem cyclicExtensionUnit_mul
    (hP : ∀ h : ↥H, P * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P)
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H), P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H) (k₁ k₂ : K) :
    cyclicExtensionUnit ρ g P hgen (k₁ * k₂)
      = cyclicExtensionUnit ρ g P hgen k₁ * cyclicExtensionUnit ρ g P hgen k₂ := by
  obtain ⟨i₁, hi₁⟩ := hgen k₁
  obtain ⟨i₂, hi₂⟩ := hgen k₂
  -- the sum of valid exponents is a valid exponent for the product
  have hmem : (g ^ (i₁ + i₂))⁻¹ * (k₁ * k₂) ∈ H := by
    have h1 : (g ^ i₂)⁻¹ * ((g ^ i₁)⁻¹ * k₁) * ((g ^ i₂)⁻¹)⁻¹ ∈ H :=
      hH.conj_mem _ hi₁ (g ^ i₂)⁻¹
    have h2 := mul_mem h1 hi₂
    have heq : ((g ^ i₂)⁻¹ * ((g ^ i₁)⁻¹ * k₁) * ((g ^ i₂)⁻¹)⁻¹) * ((g ^ i₂)⁻¹ * k₂)
        = (g ^ (i₁ + i₂))⁻¹ * (k₁ * k₂) := by group
    exact heq ▸ h2
  rw [cyclicExtensionUnit_eq hPt hgen (i₁ + i₂) hmem,
    cyclicExtensionUnit_eq hPt hgen i₁ hi₁, cyclicExtensionUnit_eq hPt hgen i₂ hi₂]
  -- commute `ρ(h₁)` past `P^{i₂}` and reassemble
  have hcomm := conjugation_unit_comm_zpow hP i₂ (⟨(g ^ i₁)⁻¹ * k₁, hi₁⟩ : ↥H)
  have hfuse : ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ i₂)⁻¹
        (⟨(g ^ i₁)⁻¹ * k₁, hi₁⟩ : ↥H) * (⟨(g ^ i₂)⁻¹ * k₂, hi₂⟩ : ↥H)
      = ⟨(g ^ (i₁ + i₂))⁻¹ * (k₁ * k₂), hmem⟩ :=
    Subtype.ext (by
      simp only [Subgroup.coe_mul, ClassFunction.conjByMulEquiv_apply]
      group)
  calc P ^ (i₁ + i₂) * ρ.asGroupHom ⟨(g ^ (i₁ + i₂))⁻¹ * (k₁ * k₂), hmem⟩
      = P ^ i₁ * P ^ i₂ * ρ.asGroupHom
          (ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ i₂)⁻¹
              (⟨(g ^ i₁)⁻¹ * k₁, hi₁⟩ : ↥H)
            * (⟨(g ^ i₂)⁻¹ * k₂, hi₂⟩ : ↥H)) := by
        rw [hfuse, ← zpow_add]
    _ = P ^ i₁ * (ρ.asGroupHom (⟨(g ^ i₁)⁻¹ * k₁, hi₁⟩ : ↥H) * P ^ i₂)
          * ρ.asGroupHom (⟨(g ^ i₂)⁻¹ * k₂, hi₂⟩ : ↥H) := by
        rw [hcomm, map_mul]
        group
    _ = P ^ i₁ * ρ.asGroupHom ⟨(g ^ i₁)⁻¹ * k₁, hi₁⟩
          * (P ^ i₂ * ρ.asGroupHom ⟨(g ^ i₂)⁻¹ * k₂, hi₂⟩) := by group

variable (ρ g P) in
/-- **The extension representation** (step 4 of Isaacs 11.22).  Given a normalized
conjugation unit `P` for `ρ` and `g` (from `exists_normalized_conjugation_unit`), the map
`g^i h ↦ P^i · ρ(h)` is a representation of `K` on the same space `V`. -/
noncomputable def cyclicExtension
    (hP : ∀ h : ↥H, P * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P)
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H), P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H) :
    Representation F K V :=
  (Units.coeHom (Module.End F V)).comp
    { toFun := cyclicExtensionUnit ρ g P hgen
      map_one' := by
        have h0 : (g ^ (0 : ℤ))⁻¹ * (1 : K) ∈ H := by
          simp
        rw [cyclicExtensionUnit_eq hPt hgen 0 h0]
        have hone : (⟨(g ^ (0 : ℤ))⁻¹ * (1 : K), h0⟩ : ↥H) = 1 :=
          Subtype.ext (by simp)
        rw [hone, map_one, zpow_zero, one_mul]
      map_mul' := cyclicExtensionUnit_mul hP hPt hgen }

/-- **The extension restricts to `ρ` on the nose**: `cyclicExtension … ∘ H.subtype = ρ`. -/
theorem cyclicExtension_comp_subtype
    (hP : ∀ h : ↥H, P * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P)
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H), P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H) :
    (cyclicExtension ρ g P hP hPt hgen).comp H.subtype = ρ := by
  refine MonoidHom.ext fun h => ?_
  have h0 : (g ^ (0 : ℤ))⁻¹ * (h : K) ∈ H := by
    simp
  calc (cyclicExtension ρ g P hP hPt hgen).comp H.subtype h
      = ↑(cyclicExtensionUnit ρ g P hgen (h : K)) := rfl
    _ = ↑(P ^ (0 : ℤ) * ρ.asGroupHom ⟨(g ^ (0 : ℤ))⁻¹ * (h : K), h0⟩) := by
        rw [cyclicExtensionUnit_eq hPt hgen 0 h0]
    _ = ρ h := by
        have hcast : (⟨(g ^ (0 : ℤ))⁻¹ * (h : K), h0⟩ : ↥H) = h :=
          Subtype.ext (by simp)
        rw [hcast, zpow_zero, one_mul, Representation.asGroupHom_apply]

/-- **The extension is irreducible** whenever `ρ` is: a `K`-invariant submodule is in
particular `H`-invariant.  Immediate from `cyclicExtension_comp_subtype` and
`isIrreducible_of_isIrreducible_comp`. -/
theorem isIrreducible_cyclicExtension [Representation.IsIrreducible ρ]
    (hP : ∀ h : ↥H, P * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P)
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H), P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H) :
    Representation.IsIrreducible (cyclicExtension ρ g P hP hPt hgen) :=
  Representation.isIrreducible_of_isIrreducible_comp (f := H.subtype) _
    ((cyclicExtension_comp_subtype hP hPt hgen).symm ▸ ‹Representation.IsIrreducible ρ›)

end Extension

end OddOrder.RepresentationTheory


