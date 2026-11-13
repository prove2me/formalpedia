-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310ElemAbelian
-- name    : OddOrder_BG_Ch1_Preliminary_S03g_Thm310ElemAbelian
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:20:00.150817+00:00
-- url     : https://prove2.me/theorems/bdace684-27d8-471a-a6f6-94bf5d181fa7
-- title:
--   BG Theorem 3.10 for elementary abelian $M$: the reducible-module induction
-- statement:
--   Extends the irreducible-module case of Theorem 3.10 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3 (general Frobenius kernel) to reducible modules over an elementary abelian group, as needed for the §15.2 application. It proves conclusions (a)+(b) and (c) in the elementary-abelian group case with a general kernel, using base change of invariants.
--
--   Main declarations: `invariants_baseChangeRepresentation_comp_eq`; `prime_card_and_finrank_of_elemAbelian_general`; `commutator_acts_trivially_of_elemAbelian_general`.
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03g_Thm310ElemAbelian.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03g_Thm310ElemAbelian.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310General
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_Thm35

namespace OddOrder.BG.Ch1.S03

open Module

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- **Bridging lemma: invariants of a subrepresentation, as an ambient `finrank`** (issue 8013
piece 5).  For a subrepresentation `W ≤ ρ` and a subgroup `H ≤ G`, the `H`-invariants of the
restricted representation `W.toRepresentation` (a submodule of `↥W.toSubmodule`) have the same
`finrank` as the ambient intersection `C_V(H) ⊓ W = invariants(ρ.comp H) ⊓ W.toSubmodule`
(a submodule of `V`).

This lets the reducible-module induction phrase every conclusion in ambient `finrank`s (so the
recursion stays over subrepresentations of the *fixed* `ρ`), while the irreducible leaves still
feed `prime_card_and_finrank_of_frobenius_general` through `W.toRepresentation`. -/
theorem invariants_toRepresentation_map_eq (ρ : Representation F G V) (W : Subrepresentation ρ)
    (H : Subgroup G) :
    (Representation.invariants (W.toRepresentation.comp H.subtype)).map W.toSubmodule.subtype
      = Representation.invariants (ρ.comp H.subtype) ⊓ W.toSubmodule := by
  ext v
  constructor
  · rintro ⟨⟨w, hw⟩, hinv, rfl⟩
    have hinv' :=
      (Representation.mem_invariants (W.toRepresentation.comp H.subtype) ⟨w, hw⟩).mp hinv
    refine Submodule.mem_inf.mpr
      ⟨(Representation.mem_invariants (ρ.comp H.subtype) w).mpr fun g => ?_, hw⟩
    have hg := congrArg Subtype.val (hinv' g)
    simpa [Subrepresentation.toRepresentation, LinearMap.coe_restrict_apply] using hg
  · intro hv
    obtain ⟨hfix, hw⟩ := Submodule.mem_inf.mp hv
    have hfix' := (Representation.mem_invariants (ρ.comp H.subtype) v).mp hfix
    refine ⟨⟨v, hw⟩, (Representation.mem_invariants (W.toRepresentation.comp H.subtype)
      ⟨v, hw⟩).mpr fun g => ?_, rfl⟩
    apply Subtype.ext
    simpa [Subrepresentation.toRepresentation, LinearMap.coe_restrict_apply] using hfix' g

theorem finrank_invariants_toRepresentation_inf (ρ : Representation F G V)
    (W : Subrepresentation ρ) (H : Subgroup G) :
    finrank F (Representation.invariants (W.toRepresentation.comp H.subtype))
      = finrank F ↥(Representation.invariants (ρ.comp H.subtype) ⊓ W.toSubmodule) := by
  rw [← Submodule.finrank_map_subtype_eq W.toSubmodule
    (Representation.invariants (W.toRepresentation.comp H.subtype)),
    invariants_toRepresentation_map_eq]

/-- **Hypothesis restriction: trivial invariants pass to a subrepresentation** (issue 8013 piece 5).
If `C_V(H) ⊓ W = ⊥` then the `H`-invariants of `W.toRepresentation` are `⊥`.  Used to transfer
`C_V(K) = ⊥` to the pieces `U, U'` of a Maschke split. -/
theorem invariants_toRepresentation_eq_bot (ρ : Representation F G V) (W : Subrepresentation ρ)
    (H : Subgroup G) (h : Representation.invariants (ρ.comp H.subtype) ⊓ W.toSubmodule = ⊥) :
    Representation.invariants (W.toRepresentation.comp H.subtype) = ⊥ := by
  have hmap := invariants_toRepresentation_map_eq ρ W H
  rw [h] at hmap
  apply Submodule.map_injective_of_injective (Submodule.injective_subtype W.toSubmodule)
  rw [Submodule.map_bot]
  exact hmap

/-- **Hypothesis restriction: the prime-manner equality passes to a subrepresentation** (issue 8013
piece 5).  If `C_V(H₁) ⊓ W = C_V(H₂) ⊓ W` then the `H₁`- and `H₂`-invariants of `W.toRepresentation`
agree.  Used to transfer the subspace-form prime-manner hypothesis `C_V(x) = C_V(R)` to `U, U'`. -/
theorem invariants_toRepresentation_eq_of_inf_eq (ρ : Representation F G V)
    (W : Subrepresentation ρ)
    (H₁ H₂ : Subgroup G)
    (h : Representation.invariants (ρ.comp H₁.subtype) ⊓ W.toSubmodule
      = Representation.invariants (ρ.comp H₂.subtype) ⊓ W.toSubmodule) :
    Representation.invariants (W.toRepresentation.comp H₁.subtype)
      = Representation.invariants (W.toRepresentation.comp H₂.subtype) := by
  apply Submodule.map_injective_of_injective (Submodule.injective_subtype W.toSubmodule)
  rw [invariants_toRepresentation_map_eq, invariants_toRepresentation_map_eq, h]

/-- **Invariants distribute over an internal direct sum of subrepresentations** (issue 8013 piece
5).
For two subrepresentations `W₀, W₁ ≤ ρ` that meet trivially (`W₀ ⊓ W₁ = ⊥`), the `H`-invariants of
their sum split: `C_V(H) ⊓ (W₀ ⊔ W₁) = (C_V(H) ⊓ W₀) ⊔ (C_V(H) ⊓ W₁)`.  This is NOT general lattice
distributivity (which fails for submodules); it uses that `W₀, W₁` are `H`-stable, so an `H`-fixed
vector's (unique, by disjointness) decomposition has `H`-fixed components.  Hence the `finrank`s
add,
which drives the additive step of the reducible-module induction. -/
theorem finrank_inf_invariants_sup_of_disjoint (ρ : Representation F G V) [FiniteDimensional F V]
    (W₀ W₁ : Subrepresentation ρ) (H : Subgroup G)
    (hdisj : W₀.toSubmodule ⊓ W₁.toSubmodule = ⊥) :
    finrank F ↥(Representation.invariants (ρ.comp H.subtype) ⊓ (W₀.toSubmodule ⊔ W₁.toSubmodule))
      = finrank F ↥(Representation.invariants (ρ.comp H.subtype) ⊓ W₀.toSubmodule)
        + finrank F ↥(Representation.invariants (ρ.comp H.subtype) ⊓ W₁.toSubmodule) := by
  set C := Representation.invariants (ρ.comp H.subtype) with hC
  -- The key `H`-equivariant distributivity.
  have hdistrib : C ⊓ (W₀.toSubmodule ⊔ W₁.toSubmodule)
      = (C ⊓ W₀.toSubmodule) ⊔ (C ⊓ W₁.toSubmodule) := by
    refine le_antisymm (fun v hv => ?_) (sup_le (inf_le_inf_left C le_sup_left)
      (inf_le_inf_left C le_sup_right))
    obtain ⟨hvC, hvW⟩ := Submodule.mem_inf.mp hv
    obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := Submodule.mem_sup.mp hvW
    have hfix := (Representation.mem_invariants (ρ.comp H.subtype) (v₀ + v₁)).mp hvC
    -- Each component is `H`-fixed: `ρ h v₀ - v₀ ∈ W₀ ⊓ W₁ = ⊥`.
    have hcomp : ∀ h : ↥H, ρ (H.subtype h) v₀ = v₀ ∧ ρ (H.subtype h) v₁ = v₁ := by
      intro h
      have hadd : ρ (H.subtype h) v₀ + ρ (H.subtype h) v₁ = v₀ + v₁ := by
        have := hfix h; rwa [MonoidHom.comp_apply, map_add] at this
      have hdiff : ρ (H.subtype h) v₀ - v₀ = v₁ - ρ (H.subtype h) v₁ := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm v₁ v₀]; exact hadd
      have hin0 : ρ (H.subtype h) v₀ - v₀ ∈ W₀.toSubmodule :=
        W₀.toSubmodule.sub_mem (W₀.apply_mem_toSubmodule _ hv₀) hv₀
      have hin1 : ρ (H.subtype h) v₀ - v₀ ∈ W₁.toSubmodule :=
        hdiff ▸ W₁.toSubmodule.sub_mem hv₁ (W₁.apply_mem_toSubmodule _ hv₁)
      have hz : ρ (H.subtype h) v₀ - v₀ = 0 := by
        have : ρ (H.subtype h) v₀ - v₀ ∈ W₀.toSubmodule ⊓ W₁.toSubmodule := ⟨hin0, hin1⟩
        rwa [hdisj, Submodule.mem_bot] at this
      refine ⟨sub_eq_zero.mp hz, ?_⟩
      have := hadd; rw [sub_eq_zero.mp hz] at this; exact (add_right_inj v₀).mp this
    refine Submodule.mem_sup.mpr ⟨v₀, ⟨?_, hv₀⟩, v₁, ⟨?_, hv₁⟩, rfl⟩
    · exact (Representation.mem_invariants (ρ.comp H.subtype) v₀).mpr fun h => by
        rw [MonoidHom.comp_apply]; exact (hcomp h).1
    · exact (Representation.mem_invariants (ρ.comp H.subtype) v₁).mpr fun h => by
        rw [MonoidHom.comp_apply]; exact (hcomp h).2
  have hdisj' : (C ⊓ W₀.toSubmodule) ⊓ (C ⊓ W₁.toSubmodule) = ⊥ := by
    refine le_antisymm (le_trans ?_ hdisj.le) bot_le
    exact le_inf (le_trans inf_le_left inf_le_right) (le_trans inf_le_right inf_le_right)
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq (C ⊓ W₀.toSubmodule) (C ⊓ W₁.toSubmodule)
  rw [hdisj', finrank_bot, add_zero] at hkey
  rw [hdistrib, hkey]

/-- **Maschke split of a reducible representation** (issue 8013 piece 5).  A semisimple (Maschke,
`NeZero (Nat.card G : F)`) representation that is not irreducible splits as a direct sum of two
nonzero subrepresentations `⊤ = U ⊕ U'`.  Shared by the `(a)+(b)` and `(c)` reducible-module
inductions. -/
theorem exists_maschke_split [Finite G] [NeZero (Nat.card G : F)] (ρ : Representation F G V)
    [Nontrivial V] (hirr : ¬ Representation.IsIrreducible ρ) :
    ∃ U U' : Subrepresentation ρ, U ≠ ⊥ ∧ U' ≠ ⊥ ∧
      U.toSubmodule ⊔ U'.toSubmodule = ⊤ ∧ U.toSubmodule ⊓ U'.toSubmodule = ⊥ := by
  have : Representation.IsSemisimpleRepresentation ρ := inferInstance
  have : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => absurd (congrArg Subrepresentation.toSubmodule h) bot_ne_top⟩
  obtain ⟨U, hUbot, hUtop⟩ : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
    by_contra hcon
    push Not at hcon
    exact hirr { eq_bot_or_eq_top := fun U => (em (U = ⊥)).imp id (hcon U) }
  obtain ⟨U', hUU'⟩ := exists_isCompl U
  have hsup : U.toSubmodule ⊔ U'.toSubmodule = ⊤ := by
    rw [← Subrepresentation.toSubmodule_sup]
    exact congrArg Subrepresentation.toSubmodule hUU'.sup_eq_top
  have hinf : U.toSubmodule ⊓ U'.toSubmodule = ⊥ := by
    rw [← Subrepresentation.toSubmodule_inf]
    exact congrArg Subrepresentation.toSubmodule hUU'.inf_eq_bot
  refine ⟨U, U', hUbot, ?_, hsup, hinf⟩
  rintro rfl
  rw [show ((⊥ : Subrepresentation ρ).toSubmodule) = ⊥ from rfl, sup_bot_eq] at hsup
  exact hUtop (Subrepresentation.toSubmodule_injective hsup)

/-- **BG Theorem 3.10 (a)+(b) for elementary abelian `M`, the reducible-module strong induction**
(issue 8013 piece 5, Case 1 of the proof, mmd L1287-1317).  The group `V` is universally quantified
inside the induction (the recursion passes to subrepresentations `U, U'`, different modules); the
measure is `finrank V`.

`ρ` is semisimple (Maschke, from `NeZero (Nat.card G : F)`).  If `ρ` is irreducible, the leaf is the
general-kernel piece 3 `prime_card_and_finrank_of_frobenius_general`.  Otherwise `ρ` splits as
`⊤ = U ⊕ U'` (a Maschke complement, `ComplementedLattice.exists_isCompl`); the induction hypothesis
applies to both pieces (`finrank` strictly smaller), the hypotheses restrict
(`invariants_toRepresentation_eq_bot`/`_eq_of_inf_eq`), and the conclusion recombines via additivity
of `finrank` and of the invariants over the direct sum (`finrank_inf_invariants_sup_of_disjoint`).
The prime-manner hypothesis is carried in **subspace-equality** form so it restricts to `U, U'`. -/
private theorem frobenius_elemAbelian_ab_aux
    [IsAlgClosed F] [Finite G] [Group.IsSolvable G] [NeZero (Nat.card G : F)]
    {K R : Subgroup G} [K.Normal]
    (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K)) (hRne : R ≠ ⊥) (hKne : K ≠ ⊥)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k) :
    ∀ (n : ℕ) {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
      (ρ : Representation F G V),
      Representation.invariants (ρ.comp K.subtype) = ⊥ →
      (∀ x : G, x ∈ R → x ≠ 1 →
        Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype)
          = Representation.invariants (ρ.comp R.subtype)) →
      finrank F V = n →
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p ∧
        finrank F V = Nat.card ↥R * finrank F (Representation.invariants (ρ.comp R.subtype)) := by
  have hKcard : (Nat.card ↥K : F) ≠ 0 := by
    obtain ⟨c, hc⟩ := Subgroup.card_subgroup_dvd_card K
    exact fun h0 => NeZero.ne (Nat.card G : F) (by rw [hc, Nat.cast_mul, h0, zero_mul])
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V _ _ _ _ ρ hCVK hcond3 hn
    classical
    by_cases hirr : Representation.IsIrreducible ρ
    · -- Irreducible leaf: the general-kernel form (piece 3).
      exact prime_card_and_finrank_of_frobenius_general ρ hRne hKne hKcard hcop hCVK hFrob
        (fun x hx hx1 => by rw [hcond3 x hx hx1])
    · -- Reducible: split `⊤ = U ⊕ U'` by Maschke and recurse on both pieces.
      obtain ⟨U, U', hUbot, hU'ne, hsup, hinf⟩ := exists_maschke_split ρ hirr
      have hsum : finrank F ↥U.toSubmodule + finrank F ↥U'.toSubmodule = finrank F V :=
        Submodule.finrank_add_eq_of_isCompl ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
      have : Nontrivial ↥U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
        (fun h => hUbot (Subrepresentation.toSubmodule_injective h))
      have : Nontrivial ↥U'.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
        (fun h => hU'ne (Subrepresentation.toSubmodule_injective h))
      have hUpos : 0 < finrank F ↥U.toSubmodule := finrank_pos
      have hU'pos : 0 < finrank F ↥U'.toSubmodule := finrank_pos
      have hUlt : finrank F ↥U.toSubmodule < n := by rw [hn] at hsum; omega
      have hU'lt : finrank F ↥U'.toSubmodule < n := by rw [hn] at hsum; omega
      obtain ⟨p, hp, hpcard, hfU⟩ := IH (finrank F ↥U.toSubmodule) hUlt U.toRepresentation
        (invariants_toRepresentation_eq_bot ρ _ K (by rw [hCVK]; exact bot_inf_eq _))
        (fun x hx hx1 => invariants_toRepresentation_eq_of_inf_eq ρ U (Subgroup.zpowers x) R
          (by rw [hcond3 x hx hx1])) rfl
      obtain ⟨_, _, _, hfU'⟩ := IH (finrank F ↥U'.toSubmodule) hU'lt U'.toRepresentation
        (invariants_toRepresentation_eq_bot ρ _ K (by rw [hCVK]; exact bot_inf_eq _))
        (fun x hx hx1 => invariants_toRepresentation_eq_of_inf_eq ρ U' (Subgroup.zpowers x) R
          (by rw [hcond3 x hx hx1])) rfl
      rw [finrank_invariants_toRepresentation_inf] at hfU hfU'
      refine ⟨p, hp, hpcard, ?_⟩
      rw [← hsum, hfU, hfU', ← mul_add,
        ← finrank_inf_invariants_sup_of_disjoint ρ U U' R hinf, hsup, inf_top_eq]

/-- **BG Theorem 3.10 (a)+(b), elementary abelian (reducible) module case** (issue 8013 piece 5).
For an irreducible-or-reducible representation `ρ` of a finite solvable `G` over an algebraically
closed `F` with `char F ∤ |G|` (so `ρ` is semisimple), a Frobenius kernel `K ⊴ G` with trivial
invariants `C_V(K) = ⊥`, complement `R` acting fixed-point-freely (`hFrob`) and in prime manner
(`hcond3`, subspace-equality form), coprimely:  `|R|` is prime and
`finrank V = |R| · finrank C_V(R)`.

This drops piece 3's `[ρ.IsIrreducible]` hypothesis (the reducible case is the Maschke induction
`frobenius_elemAbelian_ab_aux`).  The §15.2 application's `M = Q̄`, possibly reducible as a
`KD`-module over `F̄_q`, is exactly this case. -/
theorem prime_card_and_finrank_of_frobenius_elemAbelian
    [IsAlgClosed F] [Finite G] [Group.IsSolvable G] [NeZero (Nat.card G : F)]
    (ρ : Representation F G V) [FiniteDimensional F V] [Nontrivial V]
    {K R : Subgroup G} [K.Normal] (hRne : R ≠ ⊥) (hKne : K ≠ ⊥)
    (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hCVK : Representation.invariants (ρ.comp K.subtype) = ⊥)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k)
    (hcond3 : ∀ x : G, x ∈ R → x ≠ 1 →
      Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype)
        = Representation.invariants (ρ.comp R.subtype)) :
    ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p ∧
      finrank F V = Nat.card ↥R * finrank F (Representation.invariants (ρ.comp R.subtype)) :=
  frobenius_elemAbelian_ab_aux hcop hRne hKne hFrob (finrank F V) ρ hCVK hcond3 rfl

/-- **BG Theorem 3.10 (c) for elementary abelian `M`, the reducible-module induction** (issue 8013
piece 5, mmd L1313-1321/1321).  When `C_V(R)` is cyclic (here: `finrank C_V(R) ≤ 1`), the kernel's
derived subgroup centralizes `V`: `K' ⊆ C_K(V)`, i.e. `ρ g = 1` for every `g ∈ ⁅K, K⁆`.

Carries the genuine Frobenius-group structure `IsFrobeniusGroup G K R` (needed for Theorem 3.5 at
the
irreducible leaf).  The irreducible leaf is `thm35` (BG Theorem 3.5); `|R|` prime and the
one-dimensionality of `C_V(R)` come from the `(a)+(b)` result `…_frobenius_elemAbelian`.  The
reducible case splits `⊤ = U ⊕ U'`, the cyclicity restricts (`C_U(R) ≤ C_V(R)`), and the conclusions
`ρ g = 1` on `U` and on `U'` recombine to `ρ g = 1` on `V = U ⊕ U'`. -/
private theorem frobenius_elemAbelian_c_aux
    [IsAlgClosed F] [Finite G] [Group.IsSolvable G] [NeZero (Nat.card G : F)]
    {K R : Subgroup G} [K.Normal]
    (hIsFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G K R) (hRne : R ≠ ⊥) (hKne : K ≠ ⊥) :
    ∀ (n : ℕ) {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
      (ρ : Representation F G V),
      Representation.invariants (ρ.comp K.subtype) = ⊥ →
      (∀ x : G, x ∈ R → x ≠ 1 →
        Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype)
          = Representation.invariants (ρ.comp R.subtype)) →
      finrank F (Representation.invariants (ρ.comp R.subtype)) ≤ 1 →
      finrank F V = n →
      ∀ g ∈ ⁅K, K⁆, ρ g = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V _ _ _ _ ρ hCVK hcond3 hcyc hn
    classical
    by_cases hirr : Representation.IsIrreducible ρ
    · -- Irreducible leaf: BG Theorem 3.5.
      obtain ⟨p, hp, hpcard, hb⟩ := prime_card_and_finrank_of_frobenius_elemAbelian ρ hRne hKne
        hIsFrob.coprime_card_kernel_complement.symm hCVK hIsFrob.conj_frobenius hcond3
      have hCV1 : finrank F (Representation.invariants (ρ.comp R.subtype)) = 1 := by
        have hpos : 0 < finrank F V := finrank_pos
        rcases Nat.eq_zero_or_pos (finrank F (Representation.invariants (ρ.comp R.subtype)))
          with h0 | h1
        · rw [h0, mul_zero] at hb; omega
        · omega
      exact OddOrder.BG.Ch1.S03e.thm35 ρ K R hIsFrob inferInstance ⟨p, hp, hpcard⟩
        (NeZero.ne (Nat.card G : F)) hCV1
    · -- Reducible: split `⊤ = U ⊕ U'` and recurse on (c).
      obtain ⟨U, U', hUbot, hU'ne, hsup, hinf⟩ := exists_maschke_split ρ hirr
      have hsum : finrank F ↥U.toSubmodule + finrank F ↥U'.toSubmodule = finrank F V :=
        Submodule.finrank_add_eq_of_isCompl ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
      have : Nontrivial ↥U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
        (fun h => hUbot (Subrepresentation.toSubmodule_injective h))
      have : Nontrivial ↥U'.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
        (fun h => hU'ne (Subrepresentation.toSubmodule_injective h))
      have hUpos : 0 < finrank F ↥U.toSubmodule := finrank_pos
      have hU'pos : 0 < finrank F ↥U'.toSubmodule := finrank_pos
      have hUlt : finrank F ↥U.toSubmodule < n := by rw [hn] at hsum; omega
      have hU'lt : finrank F ↥U'.toSubmodule < n := by rw [hn] at hsum; omega
      have hcycU : finrank F (Representation.invariants (U.toRepresentation.comp R.subtype))
          ≤ 1 := by
        rw [finrank_invariants_toRepresentation_inf]
        exact le_trans (Submodule.finrank_mono inf_le_left) hcyc
      have hcycU' : finrank F (Representation.invariants (U'.toRepresentation.comp R.subtype))
          ≤ 1 := by
        rw [finrank_invariants_toRepresentation_inf]
        exact le_trans (Submodule.finrank_mono inf_le_left) hcyc
      have hIHU := IH (finrank F ↥U.toSubmodule) hUlt U.toRepresentation
        (invariants_toRepresentation_eq_bot ρ _ K (by rw [hCVK]; exact bot_inf_eq _))
        (fun x hx hx1 => invariants_toRepresentation_eq_of_inf_eq ρ U (Subgroup.zpowers x) R
          (by rw [hcond3 x hx hx1])) hcycU rfl
      have hIHU' := IH (finrank F ↥U'.toSubmodule) hU'lt U'.toRepresentation
        (invariants_toRepresentation_eq_bot ρ _ K (by rw [hCVK]; exact bot_inf_eq _))
        (fun x hx hx1 => invariants_toRepresentation_eq_of_inf_eq ρ U' (Subgroup.zpowers x) R
          (by rw [hcond3 x hx hx1])) hcycU' rfl
      intro g hg
      have hgU : ∀ u ∈ U.toSubmodule, ρ g u = u := by
        intro u hu
        have h := congrArg Subtype.val (DFunLike.congr_fun (hIHU g hg) ⟨u, hu⟩)
        simpa [Subrepresentation.toRepresentation, LinearMap.coe_restrict_apply,
          Module.End.one_apply] using h
      have hgU' : ∀ u ∈ U'.toSubmodule, ρ g u = u := by
        intro u hu
        have h := congrArg Subtype.val (DFunLike.congr_fun (hIHU' g hg) ⟨u, hu⟩)
        simpa [Subrepresentation.toRepresentation, LinearMap.coe_restrict_apply,
          Module.End.one_apply] using h
      refine LinearMap.ext fun v => ?_
      obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp
        (show v ∈ U.toSubmodule ⊔ U'.toSubmodule by rw [hsup]; exact Submodule.mem_top)
      change ρ g (u + u') = u + u'
      rw [map_add, hgU u hu, hgU' u' hu']

/-- **BG Theorem 3.10 (c), elementary abelian module case** (issue 8013 piece 5).  For a Frobenius
group `G = KR` acting on an elementary abelian `M = V` (over alg-closed `F`, `char F ∤ |G|`) with
`C_V(K) = ⊥` and prime-manner action, if `C_V(R)` is cyclic (`finrank ≤ 1`) then `K' ⊆ C_K(V)`. -/
theorem commutator_eq_one_of_frobenius_elemAbelian
    [IsAlgClosed F] [Finite G] [Group.IsSolvable G] [NeZero (Nat.card G : F)]
    (ρ : Representation F G V) [FiniteDimensional F V] [Nontrivial V]
    {K R : Subgroup G} [K.Normal]
    (hIsFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G K R) (hRne : R ≠ ⊥) (hKne : K ≠ ⊥)
    (hCVK : Representation.invariants (ρ.comp K.subtype) = ⊥)
    (hcond3 : ∀ x : G, x ∈ R → x ≠ 1 →
      Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype)
        = Representation.invariants (ρ.comp R.subtype))
    (hcyc : finrank F (Representation.invariants (ρ.comp R.subtype)) ≤ 1) :
    ∀ g ∈ ⁅K, K⁆, ρ g = 1 :=
  frobenius_elemAbelian_c_aux hIsFrob hRne hKne (finrank F V) ρ hCVK hcond3 hcyc rfl

open OddOrder.RepresentationTheory in
/-- **Base change preserves a subgroup-equality of invariants** (issue 8013 piece 5, the
prime-manner transfer for the group↔module bridge).  If `H₁ ≤ H₂` and the `H₁`- and `H₂`-invariants
of `ρ` over `F` coincide, then so do those of the scalar extension `baseChange L ρ` over `L`.

The `H₂`-invariants are always contained in the `H₁`-invariants (`H₁ ≤ H₂`), and base change
preserves the `finrank` of each (`finrank_invariants_baseChangeRepresentation`), which equal by
hypothesis; a containment of submodules with equal `finrank` is an equality.  This transfers the
subspace-form prime-manner hypothesis `C_M(x) = C_M(R)` to the algebraic closure, where the
elementary-abelian Theorem 3.10 applies. -/
theorem invariants_baseChangeRepresentation_comp_eq
    {F : Type*} [Field F] {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (L : Type*) [Field L] [Algebra F L]
    (ρ : Representation F H W) {H₁ H₂ : Subgroup H} (hle : H₁ ≤ H₂)
    (h : Representation.invariants (ρ.comp H₂.subtype)
      = Representation.invariants (ρ.comp H₁.subtype)) :
    Representation.invariants ((baseChangeRepresentation L ρ).comp H₂.subtype)
      = Representation.invariants ((baseChangeRepresentation L ρ).comp H₁.subtype) := by
  refine Submodule.eq_of_le_of_finrank_eq (fun v hv => ?_) ?_
  · rw [Representation.mem_invariants] at hv ⊢
    exact fun y => hv ⟨y.1, hle y.2⟩
  · rw [← baseChangeRepresentation_comp, ← baseChangeRepresentation_comp,
      finrank_invariants_baseChangeRepresentation, finrank_invariants_baseChangeRepresentation, h]

open OddOrder.RepresentationTheory in
/-- **BG Theorem 3.10 (a)+(b), elementary-abelian group case, GENERAL kernel** (issue 8013 piece 5).
Let `H` act (`MulDistribMulAction`) on a finite nontrivial elementary-abelian `p`-group `M`, with
`H` solvable, a normal `K ⊴ H` (not assumed abelian) acting with `C_M(K) = 1`, `R ≤ H` nonidentity
acting fixed-point-freely (`hFrob`) and in prime manner (`hcond3`), `p ∤ |H|` and `(|R|,|K|) = 1`.
Then `|R|` is prime and `finrank (Additive M) = |R| · finrank C_M(R)`.

This drops the **abelian-kernel** restriction of `prime_card_and_finrank_of_elemAbelian` by
base-changing to the algebraic closure and applying the general-kernel reducible-module Theorem 3.10
`prime_card_and_finrank_of_frobenius_elemAbelian`.  The subspace-form prime-manner hypothesis
transfers to the closure via `invariants_baseChangeRepresentation_comp_eq`. -/
theorem prime_card_and_finrank_of_elemAbelian_general {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] [Group.IsSolvable H]
    {M : Type*} [CommGroup M] [Finite M] [Nontrivial M]
    [Module (ZMod p) (Additive M)] [MulDistribMulAction H M]
    {K R : Subgroup H} [K.Normal] (hRne : R ≠ ⊥) (hKne : K ≠ ⊥)
    (hpH : ¬ p ∣ Nat.card H) (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hCK : ∀ m : M, (∀ k : ↥K, (k : H) • m = m) → m = 1)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k)
    (hcond3 : ∀ x : H, x ∈ R → x ≠ 1 →
      ∀ m : M, ((x : H) • m = m) ↔ (∀ s : ↥R, (s : H) • m = m)) :
    ∃ p' : ℕ, p'.Prime ∧ Nat.card ↥R = p' ∧
      finrank (ZMod p) (Additive M) = Nat.card ↥R *
        finrank (ZMod p) (Representation.invariants
          ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype)) := by
  classical
  set ρ : Representation (ZMod p) H (Additive M) :=
    Representation.ofDistribMulAction (ZMod p) H (Additive M) with hρ
  set ρ' := baseChangeRepresentation (AlgebraicClosure (ZMod p)) ρ with hρ'
  have : FiniteDimensional (ZMod p) (Additive M) := Module.Finite.of_finite
  have : FiniteDimensional (AlgebraicClosure (ZMod p))
      (TensorProduct (ZMod p) (AlgebraicClosure (ZMod p)) (Additive M)) := inferInstance
  have hChar : CharP (AlgebraicClosure (ZMod p)) p :=
    (Algebra.charP_iff (ZMod p) (AlgebraicClosure (ZMod p)) p).mp inferInstance
  have hntM : Nontrivial (Additive M) := inferInstanceAs (Nontrivial (Additive M))
  have : Nontrivial (TensorProduct (ZMod p) (AlgebraicClosure (ZMod p)) (Additive M)) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right (R := ZMod p)
      (M := AlgebraicClosure (ZMod p)) (N := Additive M)).mpr hntM
  -- `p ∤ |H|` gives `(|H| : F̄) ≠ 0`, hence the `NeZero` instance Maschke needs, and
  -- `(|K| : F̄) ≠ 0`.
  have hNeZeroH : NeZero (Nat.card H : AlgebraicClosure (ZMod p)) :=
    ⟨by rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]; exact hpH⟩
  have hpK : ¬ p ∣ Nat.card ↥K := fun hdvd => hpH (hdvd.trans (Subgroup.card_subgroup_dvd_card K))
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
  -- `C_V(K) = 0` over `ZMod p`.
  have hCK0 : Representation.invariants (ρ.comp K.subtype) = ⊥ := by
    ext v
    rw [Representation.mem_invariants, Submodule.mem_bot]
    constructor
    · intro h
      have hfix : ∀ k : ↥K, (k : H) • Additive.toMul v = Additive.toMul v :=
        fun k => (hbridge (k : H) v).mp (h k)
      have hv : Additive.toMul v = (1 : M) := hCK (Additive.toMul v) hfix
      simpa using hv
    · intro h k; simp [h]
  have hKcard : (Nat.card ↥K : AlgebraicClosure (ZMod p)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]; exact hpK
  -- Apply the general-kernel, alg-closed terminal to `ρ'`.
  obtain ⟨p', hp', hcard', hfr'⟩ := prime_card_and_finrank_of_frobenius_elemAbelian ρ' hRne
    hKne hcop
    (by rw [hρ', ← baseChangeRepresentation_comp]
        exact invariants_baseChangeRepresentation_eq_bot _ _ hCK0)
    hFrob
    (fun x hxR hx1 => by
      -- ZMod p subspace prime-manner, then transfer to the closure.
      have hsub : Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype)
          = Representation.invariants (ρ.comp R.subtype) := by
        ext v
        rw [Representation.mem_invariants, Representation.mem_invariants]
        have hgen : ∀ y : ↥(Subgroup.zpowers x), y ∈ Subgroup.zpowers
            (⟨x, Subgroup.mem_zpowers x⟩ : ↥(Subgroup.zpowers x)) := by
          intro y; obtain ⟨n, hn⟩ := y.2; exact ⟨n, Subtype.ext (by simpa using hn)⟩
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
      rw [hρ']
      exact (invariants_baseChangeRepresentation_comp_eq (AlgebraicClosure (ZMod p)) ρ
        (Subgroup.zpowers_le.mpr hxR) hsub.symm).symm)
  refine ⟨p', hp', hcard', ?_⟩
  rw [hρ', Module.finrank_baseChange (R := AlgebraicClosure (ZMod p)) (S := ZMod p)
      (M' := Additive M),
    ← baseChangeRepresentation_comp, finrank_invariants_baseChangeRepresentation] at hfr'
  exact hfr'

/-- **BG Theorem 3.10 (b) in cardinality form, elementary-abelian group case, general kernel**
(issue 8013 piece 5+2b — this is `(f)` `|Q̄| = q^p` of §15.2 step 4).  Under the same hypotheses as
`prime_card_and_finrank_of_elemAbelian_general`, `|M| = |C_M(R)|^{|R|}` where `C_M(R)` is the
`R`-invariant submodule (`= C_M(R)` as the `R`-fixed points of `M`).

Both `|M|` and `|C_M(R)|` are powers of `p` with exponents `finrank (Additive M)` and
`finrank C_M(R)` (`Module.card_eq_pow_finrank`); the rank formula `(b)`
`finrank (Additive M) = |R| · finrank C_M(R)` turns the first into the `|R|`-th power of the
second. -/
theorem card_eq_pow_card_invariants_of_elemAbelian_general {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] [Group.IsSolvable H]
    {M : Type*} [CommGroup M] [Finite M] [Nontrivial M]
    [Module (ZMod p) (Additive M)] [MulDistribMulAction H M]
    {K R : Subgroup H} [K.Normal] (hRne : R ≠ ⊥) (hKne : K ≠ ⊥)
    (hpH : ¬ p ∣ Nat.card H) (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hCK : ∀ m : M, (∀ k : ↥K, (k : H) • m = m) → m = 1)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k)
    (hcond3 : ∀ x : H, x ∈ R → x ≠ 1 →
      ∀ m : M, ((x : H) • m = m) ↔ (∀ s : ↥R, (s : H) • m = m)) :
    Nat.card M = (Nat.card ↥(Representation.invariants
      ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype)))
        ^ Nat.card ↥R := by
  classical
  obtain ⟨_, _, _, hfr⟩ := prime_card_and_finrank_of_elemAbelian_general hRne hKne hpH hcop hCK
    hFrob
    hcond3
  have : FiniteDimensional (ZMod p) (Additive M) := Module.Finite.of_finite
  have : Fintype (Additive M) := Fintype.ofFinite _
  have : Fintype ↥(Representation.invariants
    ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype)) :=
      Fintype.ofFinite _
  change Nat.card (Additive M) = (Nat.card ↥(Representation.invariants
    ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype))) ^ Nat.card ↥R
  have hM : Nat.card (Additive M) = p ^ finrank (ZMod p) (Additive M) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hInv : Nat.card ↥(Representation.invariants
      ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype))
      = p ^ finrank (ZMod p) (Representation.invariants
        ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype)) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  rw [hM, hfr, mul_comm, pow_mul, ← hInv]

open OddOrder.RepresentationTheory in
/-- **BG Theorem 3.10 (c), elementary-abelian group case, general kernel** (issue 8013 piece 5 —
this is `(g)` `D' ⊆ C_D(Q̄)` of §15.2 step 4).  Under the hypotheses of
`prime_card_and_finrank_of_elemAbelian_general` plus the genuine Frobenius-group structure
`IsFrobeniusGroup H K R` and cyclicity of `C_M(R)` (`finrank ≤ 1`), the kernel's derived subgroup
acts trivially: every `g ∈ ⁅K, K⁆` fixes every `m ∈ M` (i.e. `K' ⊆ C_K(M)`).

Base-changes to the algebraic closure where the reducible-module Theorem 3.10 (c)
`commutator_eq_one_of_frobenius_elemAbelian` gives `ρ̄ g = 1`; faithful flatness of the extension
descends this to `ρ g = 1` over `ZMod p`, and the action bridge turns it into `(g : H) • m = m`. -/
theorem commutator_acts_trivially_of_elemAbelian_general {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] [Group.IsSolvable H]
    {M : Type*} [CommGroup M] [Finite M] [Nontrivial M]
    [Module (ZMod p) (Additive M)] [MulDistribMulAction H M]
    {K R : Subgroup H} [K.Normal]
    (hIsFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup H K R) (hRne : R ≠ ⊥) (hKne : K ≠ ⊥)
    (hpH : ¬ p ∣ Nat.card H)
    (hCK : ∀ m : M, (∀ k : ↥K, (k : H) • m = m) → m = 1)
    (hcond3 : ∀ x : H, x ∈ R → x ≠ 1 →
      ∀ m : M, ((x : H) • m = m) ↔ (∀ s : ↥R, (s : H) • m = m))
    (hcyc : finrank (ZMod p) (Representation.invariants
      ((Representation.ofDistribMulAction (ZMod p) H (Additive M)).comp R.subtype)) ≤ 1) :
    ∀ g ∈ ⁅K, K⁆, ∀ m : M, (g : H) • m = m := by
  classical
  set ρ : Representation (ZMod p) H (Additive M) :=
    Representation.ofDistribMulAction (ZMod p) H (Additive M) with hρ
  set ρ' := baseChangeRepresentation (AlgebraicClosure (ZMod p)) ρ with hρ'
  have : FiniteDimensional (ZMod p) (Additive M) := Module.Finite.of_finite
  have : FiniteDimensional (AlgebraicClosure (ZMod p))
      (TensorProduct (ZMod p) (AlgebraicClosure (ZMod p)) (Additive M)) := inferInstance
  have hChar : CharP (AlgebraicClosure (ZMod p)) p :=
    (Algebra.charP_iff (ZMod p) (AlgebraicClosure (ZMod p)) p).mp inferInstance
  have hntM : Nontrivial (Additive M) := inferInstanceAs (Nontrivial (Additive M))
  have : Nontrivial (TensorProduct (ZMod p) (AlgebraicClosure (ZMod p)) (Additive M)) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right (R := ZMod p)
      (M := AlgebraicClosure (ZMod p)) (N := Additive M)).mpr hntM
  have hNeZeroH : NeZero (Nat.card H : AlgebraicClosure (ZMod p)) :=
    ⟨by rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]; exact hpH⟩
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
  have hCK0 : Representation.invariants (ρ.comp K.subtype) = ⊥ := by
    ext v
    rw [Representation.mem_invariants, Submodule.mem_bot]
    constructor
    · intro h
      have hfix : ∀ k : ↥K, (k : H) • Additive.toMul v = Additive.toMul v :=
        fun k => (hbridge (k : H) v).mp (h k)
      have hv : Additive.toMul v = (1 : M) := hCK (Additive.toMul v) hfix
      simpa using hv
    · intro h k; simp [h]
  have hCVK' : Representation.invariants (ρ'.comp K.subtype) = ⊥ := by
    rw [hρ', ← baseChangeRepresentation_comp]
    exact invariants_baseChangeRepresentation_eq_bot _ _ hCK0
  have hcond3' : ∀ x : H, x ∈ R → x ≠ 1 →
      Representation.invariants (ρ'.comp (Subgroup.zpowers x).subtype)
        = Representation.invariants (ρ'.comp R.subtype) := by
    intro x hxR hx1
    have hsub : Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype)
        = Representation.invariants (ρ.comp R.subtype) := by
      ext v
      rw [Representation.mem_invariants, Representation.mem_invariants]
      have hgen : ∀ y : ↥(Subgroup.zpowers x), y ∈ Subgroup.zpowers
          (⟨x, Subgroup.mem_zpowers x⟩ : ↥(Subgroup.zpowers x)) := by
        intro y; obtain ⟨n, hn⟩ := y.2; exact ⟨n, Subtype.ext (by simpa using hn)⟩
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
    rw [hρ']
    exact (invariants_baseChangeRepresentation_comp_eq (AlgebraicClosure (ZMod p)) ρ
      (Subgroup.zpowers_le.mpr hxR) hsub.symm).symm
  have hcyc' : finrank (AlgebraicClosure (ZMod p))
      (Representation.invariants (ρ'.comp R.subtype)) ≤ 1 := by
    rw [hρ', ← baseChangeRepresentation_comp, finrank_invariants_baseChangeRepresentation]
    exact hcyc
  -- Theorem 3.10 (c) over the closure gives `ρ' g = 1`; descend and use the action bridge.
  intro g hg m
  have hcomm := commutator_eq_one_of_frobenius_elemAbelian ρ' hIsFrob hRne hKne hCVK' hcond3' hcyc'
    g hg
  have hρg : ρ g = 1 := by
    apply LinearMap.ext
    intro v
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := ZMod p)
      (B := AlgebraicClosure (ZMod p)) (Additive M)
    have hmap := congrArg
      (fun f : TensorProduct (ZMod p) (AlgebraicClosure (ZMod p)) (Additive M)
        →ₗ[AlgebraicClosure (ZMod p)]
        TensorProduct (ZMod p) (AlgebraicClosure (ZMod p)) (Additive M) => f (1 ⊗ₜ[ZMod p] v)) hcomm
    simpa [hρ'] using hmap
  have hfix : ρ g (Additive.ofMul m) = Additive.ofMul m := by rw [hρg]; rfl
  simpa using (hbridge g (Additive.ofMul m)).mp hfix

end OddOrder.BG.Ch1.S03


