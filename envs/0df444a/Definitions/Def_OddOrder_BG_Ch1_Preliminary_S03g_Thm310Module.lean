-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310Module
-- name    : OddOrder_BG_Ch1_Preliminary_S03g_Thm310Module
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:13:15.29883+00:00
-- url     : https://prove2.me/theorems/a5b3ddff-df42-44aa-a007-ff6936cfe916
-- title:
--   BG Theorem 3.10(a): module core terminal (abelian kernel)
-- statement:
--   Assembles the proven pieces into the abelian-kernel case of Theorem 3.10(a) of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*: the free block dimension keystone, the $|R|$-prime assembly and the weight-space spanning decomposition, ending with the elementary-abelian case `prime_card_of_elemAbelian_mulDistrib`.
--
--   The main declaration: `prime_card_of_elemAbelian_mulDistrib` (BG Theorem 3.10(a), elementary-abelian group case).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03g_Thm310Module.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03g_Thm310Module.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310Core
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_WeightSpan
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BaseChange
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ElementaryAbelianRepresentation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open Module

open OddOrder.BG.Ch1.S03e OddOrder.RepresentationTheory

namespace OddOrder.BG.Ch1.S03

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- **BG Theorem 3.10(a)+(b), abelian-kernel module case.**  Let `K ⊴ G` be abelian with
`char ∤ |K|`, acting via `ρ` on a nonzero finite-dimensional space `V` over an algebraically closed
field, with `C_V(K) = 0`.  Let `R ≤ G` (`R ≠ 1`) be such that every nonidentity element of `R` acts
fixed-point-freely by conjugation on `K` (the Frobenius condition), and the prime-action condition
`finrank V^⟨x⟩ = finrank V^R` holds for every `x ∈ R^#`.  Then `|R|` is prime **(a)** and
`finrank V = |R| · finrank V^R` **(b)** (the free block dimension formula — conclusion (b)
`|M| = |C_M(R)|^p` of BG Theorem 3.10 at the rank level).

The `K`-weight spaces decompose `V`; `R` permutes them freely (Frobenius ⟹ a nonidentity element
fixes only the trivial character, whose weight space is `C_V(K) = 0`), so the free block dimension
formula (`finrank_eq_card_mul_finrank_invariants_of_freeBlock`) gives (b), and with the prime-action
condition the free block keystone (`prime_card_of_freeBlock_cond3`) gives (a).

The thin projection `prime_card_of_abelian_frobenius_weight` recovers the (a)-only form used by the
existing elementary-abelian / conjugation ladder (and Prop 14.2(g) at `S14`). -/
theorem prime_card_and_finrank_of_abelian_frobenius_weight [Finite G] [IsAlgClosed F]
    (ρ : Representation F G V) [FiniteDimensional F V] [Nontrivial V]
    {K R : Subgroup G} [K.Normal] (hRne : R ≠ ⊥)
    (hKab : ∀ a b : ↥K, (a : G) * (b : G) = (b : G) * (a : G))
    (hKcard : (Nat.card ↥K : F) ≠ 0)
    (hCVK : Representation.invariants (ρ.comp K.subtype) = ⊥)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k)
    (hcond3 : ∀ x : G, x ∈ R → x ≠ 1 →
      finrank F (Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype))
        = finrank F (Representation.invariants (ρ.comp R.subtype))) :
    ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p ∧
      finrank F V = Nat.card ↥R * finrank F (Representation.invariants (ρ.comp R.subtype)) := by
  classical
  have : Finite ↥R := Subtype.finite
  -- The trivial character's weight space is `C_V(K) = 0`.
  have hTrivWS : weightSpace ρ K (fun _ => (1 : F)) = ⊥ := by
    have hset : weightSpace ρ K (fun _ => (1 : F))
        = Representation.invariants (ρ.comp K.subtype) := by
      ext v
      rw [mem_weightSpace, Representation.mem_invariants]
      constructor
      · intro h k; have := h k; rwa [one_smul] at this
      · intro h k; rw [one_smul]; exact h k
    rw [hset, hCVK]
  -- The block index set: characters with nonzero weight space.
  set ι : Type _ := {χ : ↥K → F // weightSpace ρ K χ ≠ ⊥} with hι
  -- (1) Instances on `ι`.
  have hindep : iSupIndep (weightSpace ρ K) := iSupIndep_weightSpace ρ hKab
  have : Fintype ι := hindep.fintypeNeBotOfFiniteDimensional
  -- (2) The `↥R`-action on `ι` via conjugation of characters.
  have hpres : ∀ (r : ↥R) (χ : ↥K → F), weightSpace ρ K χ ≠ ⊥ →
      weightSpace ρ K (conjChar K (r : G) χ) ≠ ⊥ := by
    intro r χ hχ
    rw [← map_weightSpace ρ (r : G) χ]
    intro hbot
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    have hmem : ρ (r : G) v ∈ (weightSpace ρ K χ).map (ρ (r : G)) := Submodule.mem_map_of_mem hv
    rw [hbot, Submodule.mem_bot] at hmem
    exact hv0 ((ρ.apply_bijective (r : G)).injective (hmem.trans (map_zero _).symm))
  let : MulAction ↥R ι :=
    { smul := fun r i => ⟨conjChar K (r : G) i.1, hpres r i.1 i.2⟩
      one_smul := fun i => by
        apply Subtype.ext
        change conjChar K ((1 : ↥R) : G) i.1 = i.1
        rw [Subgroup.coe_one, conjChar_one]
      mul_smul := fun r s i => by
        apply Subtype.ext
        change conjChar K ((r * s : ↥R) : G) i.1 = conjChar K (r : G) (conjChar K (s : G) i.1)
        rw [Subgroup.coe_mul, conjChar_mul] }
  have hsmul : ∀ (r : ↥R) (i : ι), (r • i).val = conjChar K (r : G) i.val := fun _ _ => rfl
  -- (3) The blocks.
  set W : ι → Submodule F V := fun i => weightSpace ρ K i.val with hW_def
  -- (4) The blocks form an internal direct sum.
  have hW : DirectSum.IsInternal W := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact hindep.comp Subtype.val_injective
    · have heq : (⨆ i : ι, weightSpace ρ K i.val) = (⨆ χ : ↥K → F, weightSpace ρ K χ) := by
        apply le_antisymm
        · exact iSup_le fun i => le_iSup (weightSpace ρ K) i.val
        · refine iSup_le fun χ => ?_
          by_cases hχ : weightSpace ρ K χ = ⊥
          · rw [hχ]; exact bot_le
          · exact le_iSup (fun i : ι => weightSpace ρ K i.val) (⟨χ, hχ⟩ : ι)
      change (⨆ i : ι, weightSpace ρ K i.val) = ⊤
      rw [heq]
      exact iSup_weightSpace_eq_top ρ K hKab hKcard
  -- (5) `R` permutes the blocks.
  have hperm : ∀ (h : ↥R) (i : ι), (W i).map (ρ (h : G)) = W (h • i) := by
    intro h i
    change (weightSpace ρ K i.val).map (ρ (h : G)) = weightSpace ρ K (h • i).val
    rw [hsmul h i]
    exact map_weightSpace ρ (h : G) i.val
  -- (6) The permutation is free (Frobenius ⟹ a nonidentity element fixes only the trivial char).
  have hfree : ∀ (h : ↥R) (i : ι), h • i = i → h = 1 := by
    intro h i hfix
    by_contra hne
    have hhne : (h : G) ≠ 1 := fun hc => hne (Subtype.ext hc)
    -- The fixed equation on characters.
    have hcharfix : conjChar K (h : G) i.val = i.val := by
      have := congrArg Subtype.val hfix
      rwa [hsmul h i] at this
    -- Fixed-point-freeness of conjugation by `(h:G)⁻¹` on `K`.
    have hFPF : MonoidHom.FixedPointFree (conjNormalMulAut K (h : G)⁻¹) := by
      intro k hk
      by_contra hk1
      have hkcoe : (h : G)⁻¹ * (k : G) * ((h : G)⁻¹)⁻¹ = (k : G) := by
        have := congrArg Subtype.val hk
        rwa [conjNormalMulAut_apply_coe] at this
      have hhinvne : (h : G)⁻¹ ≠ 1 := fun hc => hhne (inv_eq_one.mp hc)
      exact hFrob (h : G)⁻¹ (R.inv_mem h.2) hhinvne (k : G) k.2
        (fun hc => hk1 (Subtype.ext hc)) hkcoe
    -- Hence `i.val` is the trivial character, whose weight space is `⊥` — contradiction.
    have htriv : i.val = fun _ => (1 : F) :=
      weightChar_eq_one_of_conjChar_fixed ρ hFPF i.2 hcharfix
    exact i.2 (by rw [htriv]; exact hTrivWS)
  -- (7) Apply the free block keystone (a) and the free block dimension formula (b).
  obtain ⟨p, hp, hpcard⟩ := prime_card_of_freeBlock_cond3 ρ hRne hW hfree hperm hcond3
  exact ⟨p, hp, hpcard, ρ.finrank_eq_card_mul_finrank_invariants_of_freeBlock R hW hfree hperm⟩

section ElemAbelian

/-- **BG Theorem 3.10(a)+(b), elementary-abelian module case** (rank form).  With the
`ZMod p`-module
structure on `Additive M` supplied as a genuine instance binder (so tensor-product instance
synthesis
over `ZMod p` is not blocked by a `letI`-local module): `|R|` is prime **(a)** and
`finrank (Additive M) = |R| · finrank C_M(R)` **(b)** — conclusion (b) `|M| = |C_M(R)|^p` of BG
Theorem 3.10 at the rank level, the invariants being `C_M(R)` as the `R`-fixed submodule of
`Additive M`.  Base-changes to the algebraic closure where
`prime_card_and_finrank_of_abelian_frobenius_weight` applies; `Module.finrank_baseChange` and
`finrank_invariants_baseChangeRepresentation` transport (b) back to `ZMod p`.

The `(a)`-only projection `prime_card_of_elemAbelian_aux` feeds
`prime_card_of_elemAbelian_mulDistrib`
(conjugation ladder / Prop 14.2(g)); this `(a)+(b)` form feeds the conclusion-(b) ladder of the full
BG Theorem 3.10 (issue 8013). -/
theorem prime_card_and_finrank_of_elemAbelian {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H]
    {M : Type*} [CommGroup M] [Finite M] [Nontrivial M]
    [Module (ZMod p) (Additive M)]
    [MulDistribMulAction H M]
    {K R : Subgroup H} [K.Normal] (hRne : R ≠ ⊥)
    (hKab : ∀ a b : ↥K, (a : H) * (b : H) = (b : H) * (a : H))
    (hpK : ¬ p ∣ Nat.card ↥K)
    (hCK : ∀ m : M, (∀ k : ↥K, (k : H) • m = m) → m = 1)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k)
    (hcond3 : ∀ x : H, x ∈ R → x ≠ 1 →
      ∀ m : M, ((x : H) • m = m) ↔ (∀ s : ↥R, (s : H) • m = m)) :
    ∃ p' : ℕ, p'.Prime ∧ Nat.card ↥R = p' ∧
      finrank (ZMod p) (Additive M) = Nat.card ↥R *
        finrank (ZMod p) (Representation.invariants
          ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype)) := by
  classical
  -- The `ZMod p`-representation on `Additive M`.
  set ρ : Representation (ZMod p) H (Additive M) :=
    Representation.ofDistribMulAction (ZMod p) H (Additive M) with hρ
  -- Base change to the algebraic closure `F̄ = AlgebraicClosure (ZMod p)`.
  set ρ' := OddOrder.RepresentationTheory.baseChangeRepresentation
    (AlgebraicClosure (ZMod p)) ρ with hρ'
  -- Finite dimensionality of `Additive M` over `ZMod p` (a finite module over a field), and of the
  -- base change (synthesised now, with the module a genuine instance).
  have : FiniteDimensional (ZMod p) (Additive M) := Module.Finite.of_finite
  have : FiniteDimensional (AlgebraicClosure (ZMod p))
      (TensorProduct (ZMod p) (AlgebraicClosure (ZMod p)) (Additive M)) := inferInstance
  -- Characteristic of the algebraic closure is `p`.
  have hChar : CharP (AlgebraicClosure (ZMod p)) p :=
    (Algebra.charP_iff (ZMod p) (AlgebraicClosure (ZMod p)) p).mp inferInstance
  -- `Additive M` is nontrivial, hence so is the base change (faithfully flat field extension).
  have hntM : Nontrivial (Additive M) := inferInstanceAs (Nontrivial (Additive M))
  have : Nontrivial (TensorProduct (ZMod p) (AlgebraicClosure (ZMod p)) (Additive M)) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right (R := ZMod p)
      (M := AlgebraicClosure (ZMod p)) (N := Additive M)).mpr hntM
  -- **Bridge**: `ρ g v = v` over `Additive M` ⟺ `(g:H) • (toMul v) = toMul v` in `M`.
  have hbridge : ∀ (g : H) (v : Additive M),
      ρ g v = v ↔ (g : H) • Additive.toMul v = Additive.toMul v := by
    intro g v
    rw [hρ, Representation.ofDistribMulAction_apply_apply]
    constructor
    · intro h
      have := congrArg Additive.toMul h
      rwa [show Additive.toMul ((g : H) • v) = (g : H) • Additive.toMul v from rfl] at this
    · intro h
      apply Additive.toMul.injective
      rwa [show Additive.toMul ((g : H) • v) = (g : H) • Additive.toMul v from rfl]
  -- (hCK0) `C_V(K) = 0` over `ZMod p`.
  have hCK0 : Representation.invariants (ρ.comp K.subtype) = ⊥ := by
    ext v
    rw [Representation.mem_invariants, Submodule.mem_bot]
    constructor
    · intro h
      -- `v` is `K`-fixed, so `toMul v = 1` by `hCK`, hence `v = 0`.
      have hfix : ∀ k : ↥K, (k : H) • Additive.toMul v = Additive.toMul v := by
        intro k
        exact (hbridge (k : H) v).mp (h k)
      have := hCK (Additive.toMul v) hfix
      have hv : Additive.toMul v = (1 : M) := this
      simpa using hv
    · intro h k
      simp [h]
  -- (hKcard) `(Nat.card K : F̄) ≠ 0`.
  have hKcard : (Nat.card ↥K : AlgebraicClosure (ZMod p)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]
    exact hpK
  -- Apply the algebraically-closed terminal (a)+(b) to `ρ'`, then transport the rank formula (b)
  -- back to `ZMod p` (base change preserves `finrank` of `V` and of the invariants).
  obtain ⟨p', hp', hcard', hfr'⟩ := prime_card_and_finrank_of_abelian_frobenius_weight ρ' hRne hKab
    hKcard
    (by -- `C_{V'}(K) = 0`.
      rw [hρ', ← OddOrder.RepresentationTheory.baseChangeRepresentation_comp]
      exact OddOrder.RepresentationTheory.invariants_baseChangeRepresentation_eq_bot _ _ hCK0)
    hFrob
    (by -- The prime-action condition transfers (both `finrank`s come from the `ZMod p` ones).
      intro x hxR hx1
      rw [hρ', ← OddOrder.RepresentationTheory.baseChangeRepresentation_comp,
        ← OddOrder.RepresentationTheory.baseChangeRepresentation_comp,
        OddOrder.RepresentationTheory.finrank_invariants_baseChangeRepresentation,
        OddOrder.RepresentationTheory.finrank_invariants_baseChangeRepresentation]
      -- Reduce to equality of the two `ZMod p`-invariant submodules, then `finrank`s agree.
      have hsub : Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype)
          = Representation.invariants (ρ.comp R.subtype) := by
        ext v
        rw [Representation.mem_invariants, Representation.mem_invariants]
        have hgen : ∀ y : ↥(Subgroup.zpowers x), y ∈ Subgroup.zpowers
            (⟨x, Subgroup.mem_zpowers x⟩ : ↥(Subgroup.zpowers x)) := by
          intro y
          obtain ⟨n, hn⟩ := y.2
          exact ⟨n, Subtype.ext (by simpa using hn)⟩
        have hLHS : (∀ y : ↥(Subgroup.zpowers x), (ρ.comp (Subgroup.zpowers x).subtype) y v = v)
            ↔ ρ x v = v := by
          have h := Representation.mem_invariants_iff_of_forall_mem_zpowers
            (ρ.comp (Subgroup.zpowers x).subtype)
            (⟨x, Subgroup.mem_zpowers x⟩ : ↥(Subgroup.zpowers x)) hgen v
          rw [Representation.mem_invariants] at h
          simpa [MonoidHom.comp_apply] using h
        rw [hLHS, hbridge x v, hcond3 x hxR hx1 (Additive.toMul v)]
        refine forall_congr' (fun s => ?_)
        rw [← hbridge (s : H) v]
        rfl
      rw [hsub])
  refine ⟨p', hp', hcard', ?_⟩
  -- Transport `finrank_{F̄} V' = |R| · finrank_{F̄} C_{V'}(R)` (over the algebraic closure) back to
  -- `ZMod p`: base change preserves both `finrank V` (`Module.finrank_baseChange`) and `finrank` of
  -- the invariants (`finrank_invariants_baseChangeRepresentation`).
  rw [hρ', Module.finrank_baseChange (R := AlgebraicClosure (ZMod p)) (S := ZMod p)
      (M' := Additive M),
    ← OddOrder.RepresentationTheory.baseChangeRepresentation_comp,
    OddOrder.RepresentationTheory.finrank_invariants_baseChangeRepresentation] at hfr'
  exact hfr'

/-- (a)-only projection of `prime_card_and_finrank_of_elemAbelian`, dropping the rank conjunct
(b).  This is the form consumed by `prime_card_of_elemAbelian_mulDistrib` (and thus the conjugation
form / Prop 14.2(g)); the (a)+(b) form feeds the conclusion-(b) ladder of BG Theorem 3.10. -/
private theorem prime_card_of_elemAbelian_aux {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H]
    {M : Type*} [CommGroup M] [Finite M] [Nontrivial M]
    [Module (ZMod p) (Additive M)]
    [MulDistribMulAction H M]
    {K R : Subgroup H} [K.Normal] (hRne : R ≠ ⊥)
    (hKab : ∀ a b : ↥K, (a : H) * (b : H) = (b : H) * (a : H))
    (hpK : ¬ p ∣ Nat.card ↥K)
    (hCK : ∀ m : M, (∀ k : ↥K, (k : H) • m = m) → m = 1)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k)
    (hcond3 : ∀ x : H, x ∈ R → x ≠ 1 →
      ∀ m : M, ((x : H) • m = m) ↔ (∀ s : ↥R, (s : H) • m = m)) :
    ∃ p' : ℕ, p'.Prime ∧ Nat.card ↥R = p' := by
  obtain ⟨p', hp', hcard', _⟩ :=
    prime_card_and_finrank_of_elemAbelian hRne hKab hpK hCK hFrob hcond3
  exact ⟨p', hp', hcard'⟩

open scoped Classical in
/-- **BG Theorem 3.10(a), elementary-abelian group case.**  Let `H` act (`MulDistribMulAction`) on
a finite nontrivial elementary-abelian `p`-group `M`, with an abelian normal `K ⊴ H` (`p ∤ |K|`)
acting with `C_M(K) = 1`, a nonidentity `R ≤ H` acting fixed-point-freely (Frobenius: a nonidentity
element of `R` conjugates no nonidentity element of `K` to itself), and the prime-action condition
`C_M(x) = C_M(R)` for every `x ∈ R^#`.  Then `|R|` is prime.

The `ZMod p`-representation `Additive M` base-changes to the algebraic closure, where the abelian
Frobenius weight argument (`prime_card_of_abelian_frobenius_weight`) applies. -/
theorem prime_card_of_elemAbelian_mulDistrib {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H]
    {M : Type*} [CommGroup M] [Finite M] [Nontrivial M]
    (hM : OddOrder.GroupTheory.IsElementaryAbelian p M)
    [MulDistribMulAction H M]
    {K R : Subgroup H} [K.Normal] (hRne : R ≠ ⊥)
    (hKab : ∀ a b : ↥K, (a : H) * (b : H) = (b : H) * (a : H))
    (hpK : ¬ p ∣ Nat.card ↥K)
    (hCK : ∀ m : M, (∀ k : ↥K, (k : H) • m = m) → m = 1)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k)
    (hcond3 : ∀ x : H, x ∈ R → x ≠ 1 →
      ∀ m : M, ((x : H) • m = m) ↔ (∀ s : ↥R, (s : H) • m = m)) :
    ∃ p' : ℕ, p'.Prime ∧ Nat.card ↥R = p' := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let : Module (ZMod p) (Additive M) := hM.zmodModule
  exact prime_card_of_elemAbelian_aux hRne hKab hpK hCK hFrob hcond3

end ElemAbelian

end OddOrder.BG.Ch1.S03


