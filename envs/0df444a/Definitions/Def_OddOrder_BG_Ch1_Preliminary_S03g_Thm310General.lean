-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310General
-- name    : OddOrder_BG_Ch1_Preliminary_S03g_Thm310General
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:15:54.915208+00:00
-- url     : https://prove2.me/theorems/aabe7a86-c4d4-43db-a5f4-86ad9671628b
-- title:
--   BG Theorem 3.10 for a general (non-abelian) kernel: the $K_0$ reduction
-- statement:
--   Treats the general non-abelian Frobenius kernel in Theorem 3.10 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3. The abelian-kernel forms cover conclusions (a) $|R|$ prime and (b) $\dim V=|R|\cdot\dim C_V(R)$; here the Frobenius fixed-point-free action is lifted to the quotient kernel (Case B) in a reduction to $K_0$.
--
--   The main declaration: `fpf_lift_of_centralizer_bot`.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03g_Thm310General.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03g_Thm310General.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310Module
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03h_Thm38
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Subrepresentation

namespace OddOrder.BG.Ch1.S03

open Module

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- **Irreducible ⟹ the invariants of a normal subgroup are `⊥` or `⊤`** (the dichotomy driving the
`K₀` reduction of BG Theorem 3.10, Case 2; mmd L1342 "since `C_M(K₀)` is a `G`-invariant subgroup of
`M`, either `C_M(K₀)=1` or `C_M(K₀)=M`").  For an irreducible representation `ρ` and a normal
subgroup `K₀ ⊴ G`, the `K₀`-invariants `C_V(K₀) = invariants (ρ.comp K₀.subtype)` form a
`G`-invariant submodule (because `K₀` is normal: `ρ g` carries a `K₀`-fixed vector to a `K₀`-fixed
vector, conjugating the fixing element back into `K₀`), hence a subrepresentation, which an
irreducible `ρ` forces to be `⊥` or `⊤`. -/
theorem invariants_normal_eq_bot_or_top_of_isIrreducible
    (ρ : Representation F G V) [ρ.IsIrreducible]
    {K₀ : Subgroup G} [hK₀ : K₀.Normal] :
    Representation.invariants (ρ.comp K₀.subtype) = ⊥ ∨
      Representation.invariants (ρ.comp K₀.subtype) = ⊤ := by
  -- Package `C_V(K₀)` as a subrepresentation (it is `G`-invariant because `K₀ ⊴ G`).
  set S : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants (ρ.comp K₀.subtype)
      apply_mem_toSubmodule := by
        intro g v hv
        rw [Representation.mem_invariants] at hv ⊢
        intro k₀
        -- `ρ k₀ (ρ g v) = ρ (k₀ * g) v = ρ (g * (g⁻¹ k₀ g)) v = ρ g (ρ (g⁻¹ k₀ g) v) = ρ g v`.
        have hconj : g⁻¹ * (k₀ : G) * g ∈ K₀ := by
          have := hK₀.conj_mem (k₀ : G) k₀.2 g⁻¹
          simpa using this
        have hfix := hv ⟨g⁻¹ * (k₀ : G) * g, hconj⟩
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hfix ⊢
        rw [← Module.End.mul_apply, ← map_mul]
        have hgg : (k₀ : G) * g = g * (g⁻¹ * (k₀ : G) * g) := by group
        rw [hgg, map_mul, Module.End.mul_apply, hfix] } with hS
  -- An irreducible representation has only `⊥` and `⊤` as subrepresentations.
  rcases IsSimpleOrder.eq_bot_or_eq_top S with hb | ht
  · -- `S.toSubmodule` is defeq to the invariants and `(⊥ : Subrepresentation ρ).toSubmodule` to
    -- `⊥`, so the projected equation is exactly the goal.
    exact Or.inl (congrArg Subrepresentation.toSubmodule hb)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule ht)

/-- **BG Theorem 3.10(a)+(b), the induction base case** (mmd L1346 "we can assume that `K` is a
minimal normal subgroup of `KR`; since `KR` is solvable, this implies that `K` is an elementary
abelian `q`-group").  When the Frobenius kernel `K` is minimal normal in the (solvable) group `G`,
it is elementary abelian (`minimal_normal_isElementaryAbelian_of_isSolvable`),
in particular abelian, so
the abelian-kernel rank theorem `prime_card_and_finrank_of_abelian_frobenius_weight` applies and
yields (a) `|R|` prime and (b) `finrank V = |R| · finrank C_V(R)`.

This is the base of the `K₀`-reduction induction (issue 8013 piece 3): the recursive step reduces a
general kernel to this case via `invariants_normal_eq_bot_or_top_of_isIrreducible`. -/
theorem prime_card_and_finrank_of_minimalNormal_kernel [Finite G] [IsAlgClosed F]
    [Group.IsSolvable G]
    (ρ : Representation F G V) [FiniteDimensional F V] [Nontrivial V]
    {K R : Subgroup G} [K.Normal] (hRne : R ≠ ⊥)
    (hKmin : OddOrder.Isaacs.Ch02.IsMinimalNormal K)
    (hKcard : (Nat.card ↥K : F) ≠ 0)
    (hCVK : Representation.invariants (ρ.comp K.subtype) = ⊥)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k)
    (hcond3 : ∀ x : G, x ∈ R → x ≠ 1 →
      finrank F (Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype))
        = finrank F (Representation.invariants (ρ.comp R.subtype))) :
    ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p ∧
      finrank F V = Nat.card ↥R * finrank F (Representation.invariants (ρ.comp R.subtype)) := by
  obtain ⟨q, _hq, hKea⟩ :=
    OddOrder.Isaacs.Ch03.minimal_normal_isElementaryAbelian_of_isSolvable hKmin
  have hKab : ∀ a b : ↥K, (a : G) * (b : G) = (b : G) * (a : G) := by
    intro a b
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hKea.comm]
  exact prime_card_and_finrank_of_abelian_frobenius_weight ρ hRne hKab hKcard hCVK hFrob hcond3

/-- **Case B transfer brick — invariants are preserved under the lift to `G ⧸ K₀`** (issue 8013
piece 3).  When `K₀` acts trivially (`ρ x = 1` for `x ∈ K₀`), `ρ` factors as
`ρ̄ = QuotientGroup.lift K₀ ρ` through `G ⧸ K₀`, and the `ρ̄`-invariants of the image `S·K₀/K₀` of
any
`S ≤ G` coincide (as a submodule of `V`) with the `ρ`-invariants of `S`: the actions agree on
representatives (`ρ̄ ⟦g⟧ = ρ g`), so the same vectors are fixed.

In Case B of the `K₀` reduction this both transfers the hypothesis `C_V(K) = ⊥` to the quotient
(`S = K`) and transfers the conclusion's `C_V(R)` back from the quotient (`S = R`). -/
theorem invariants_lift_map_eq_of_trivial (ρ : Representation F G V) {K₀ : Subgroup G} [K₀.Normal]
    (hker : ∀ x ∈ K₀, ρ x = 1) (S : Subgroup G) :
    Representation.invariants
        ((QuotientGroup.lift K₀ ρ hker).comp (S.map (QuotientGroup.mk' K₀)).subtype)
      = Representation.invariants (ρ.comp S.subtype) := by
  ext v
  rw [Representation.mem_invariants, Representation.mem_invariants]
  constructor
  · intro h s
    have hmem : (QuotientGroup.mk' K₀) (s : G) ∈ S.map (QuotientGroup.mk' K₀) :=
      Subgroup.mem_map_of_mem _ s.2
    have hs := h ⟨(QuotientGroup.mk' K₀) (s : G), hmem⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hs ⊢
    exact hs
  · intro h s'
    obtain ⟨g, hgS, hgeq⟩ := s'.2
    have hg := h ⟨g, hgS⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hg
    have hX : (S.map (QuotientGroup.mk' K₀)).subtype s' = (QuotientGroup.mk' K₀) g := hgeq.symm
    rw [MonoidHom.comp_apply, hX]
    exact hg

/-- **Case B transfer brick — the complement's order is unchanged by the lift** (issue 8013 piece
3).
A Frobenius complement `R` meets the kernel trivially (`R ∩ K₀ = ⊥`, here `K₀ ⊆ K`), so the quotient
map `mk' K₀` is injective on `R` and `|R·K₀/K₀| = |R|`.  Used to transfer `|R'| = p` (the quotient
conclusion (a)) back to `|R| = p`. -/
theorem card_map_mk'_eq_of_disjoint {K₀ R : Subgroup G} [K₀.Normal] (hdisj : Disjoint R K₀) :
    Nat.card (R.map (QuotientGroup.mk' K₀)) = Nat.card ↥R := by
  have hinj : Function.Injective ((QuotientGroup.mk' K₀).comp R.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hr
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.disjoint_def.mp hdisj r.2 hr)
  have hrange : ((QuotientGroup.mk' K₀).comp R.subtype).range = R.map (QuotientGroup.mk' K₀) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

/-- **Case B transfer of BG Theorem 3.10 (a)+(b)** (issue 8013 piece 3): when `K₀` acts trivially,
the conclusion of the theorem for the lifted representation `ρ̄` on `G ⧸ K₀` (with kernel `K/K₀`,
complement `R·K₀/K₀`) transfers back to `ρ` on `G` (kernel `K`, complement `R`).  The complement's
order is unchanged (`card_map_mk'_eq_of_disjoint`) and so is the `finrank` of its invariants
(`invariants_lift_map_eq_of_trivial`), so `(a)` `|R| = p` and `(b)`
`finrank V = |R| · finrank C_V(R)`
carry over verbatim.  The induction (Case B) supplies the quotient conclusion `hquot` by applying
the
induction hypothesis to `ρ̄` (whose kernel `K/K₀` is strictly smaller). -/
theorem caseB_transfer (ρ : Representation F G V) {K₀ R : Subgroup G} [K₀.Normal]
    (hker : ∀ x ∈ K₀, ρ x = 1) (hdisj : Disjoint R K₀)
    (hquot : ∃ p : ℕ, p.Prime ∧ Nat.card (R.map (QuotientGroup.mk' K₀)) = p ∧
      finrank F V = Nat.card (R.map (QuotientGroup.mk' K₀)) *
        finrank F (Representation.invariants
          ((QuotientGroup.lift K₀ ρ hker).comp (R.map (QuotientGroup.mk' K₀)).subtype))) :
    ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p ∧
      finrank F V = Nat.card ↥R * finrank F (Representation.invariants (ρ.comp R.subtype)) := by
  obtain ⟨p, hp, hcardR', hfinrank'⟩ := hquot
  have hcard : Nat.card (R.map (QuotientGroup.mk' K₀)) = Nat.card ↥R :=
    card_map_mk'_eq_of_disjoint hdisj
  have hinv : Representation.invariants
      ((QuotientGroup.lift K₀ ρ hker).comp (R.map (QuotientGroup.mk' K₀)).subtype)
      = Representation.invariants (ρ.comp R.subtype) :=
    invariants_lift_map_eq_of_trivial ρ hker R
  exact ⟨p, hp, by rw [← hcard]; exact hcardR', by rw [hfinrank', hcard, hinv]⟩

/-- **Case B brick — irreducibility lifts to the quotient** (issue 8013 piece 3).  When `K₀` acts
trivially, the lifted representation `ρ̄ = QuotientGroup.lift K₀ ρ` on `G ⧸ K₀` is again
irreducible:
its subrepresentations are the same submodules as those of `ρ` (a submodule is `ρ̄`-invariant iff
`ρ`-invariant, since `ρ̄ ⟦g⟧ = ρ g` and `mk'` is surjective), so the simple-order structure carries
over.  Supplies the `[IsIrreducible ρ̄]` instance needed to apply the induction hypothesis to
`ρ̄`. -/
theorem isIrreducible_lift_of_trivial [Nontrivial V] (ρ : Representation F G V) [ρ.IsIrreducible]
    {K₀ : Subgroup G} [K₀.Normal] (hker : ∀ x ∈ K₀, ρ x = 1) :
    Representation.IsIrreducible (QuotientGroup.lift K₀ ρ hker) := by
  have hnt : Nontrivial (Subrepresentation (QuotientGroup.lift K₀ ρ hker)) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    exact absurd (congrArg Subrepresentation.toSubmodule h) bot_ne_top
  refine { eq_bot_or_eq_top := fun S => ?_ }
  let Sρ : Subrepresentation ρ :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g {v} hv => S.apply_mem_toSubmodule (QuotientGroup.mk' K₀ g) hv }
  rcases IsSimpleOrder.eq_bot_or_eq_top Sρ with h | h
  · refine Or.inl (Subrepresentation.toSubmodule_injective ?_)
    exact (congrArg Subrepresentation.toSubmodule h : Sρ.toSubmodule = (⊥ : Submodule F V))
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    exact (congrArg Subrepresentation.toSubmodule h : Sρ.toSubmodule = (⊤ : Submodule F V))

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Case B brick — the Frobenius FPF action lifts to the quotient kernel** (issue 8013 piece 3,
Proposition 1.5(d)).  If `r ∈ R` acts fixed-point-freely on `K` (`C_K(r) = 1`, the Frobenius
condition) and `r` acts coprimely on `K` (with `K₀ ⊴ G`, `K₀ ⊆ K`, `r`-invariant), then `r` acts
fixed-point-freely on the quotient `K / K₀`: a class `k̄` fixed by `r` (`⁅r, k⁆ ∈ K₀`) is trivial
(`k ∈ K₀`).

This transfers the Frobenius hypothesis of BG Theorem 3.10 to `KR/K₀` in Case B of the `K₀`
reduction.  Mirrors `OddOrder.BG.Ch4.S15.fpf_of_centralizer_inf_le`, but the fixed-point source is
`C_K(r) = 1` (the conjugation-action fixed points are `⊥` directly) and the target is the kernel
`K`. -/
theorem fpf_lift_of_centralizer_bot [Finite G] {K₀ K : Subgroup G} [K₀.Normal] {r : G}
    (hrK : r ∈ Subgroup.normalizer (K : Set G)) (hK₀K : K₀ ≤ K)
    (hKK₀ : K ≤ Subgroup.normalizer (K₀ : Set G)) (hrK₀ : r ∈ Subgroup.normalizer (K₀ : Set G))
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers r)) (Nat.card ↥K))
    (hsolv : Group.IsSolvable ↥(Subgroup.zpowers r) ∨ Group.IsSolvable ↥K)
    (hCbot : ∀ k ∈ K, r * k * r⁻¹ = k → k = 1)
    {k : G} (hkK : k ∈ K) (hfix : r * k * r⁻¹ * k⁻¹ ∈ K₀) :
    k ∈ K₀ := by
  classical
  have hzK : Subgroup.zpowers r ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr hrK
  have hzK₀ : Subgroup.zpowers r ≤ Subgroup.normalizer (K₀ : Set G) := Subgroup.zpowers_le.mpr hrK₀
  set φ : ↥(Subgroup.zpowers r) →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hzK) with hφ
  have hK₀_normal : (K₀.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀K).mpr hKK₀
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (K₀.subgroupOf K) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    change (a : G) * (y : G) * (a : G)⁻¹ ∈ K₀
    exact (Subgroup.mem_normalizer_iff.mp (hzK₀ a.2) (y : G)).mp hy
  -- The conjugation-action fixed points are `⊥` (the Frobenius FPF condition `C_K(r) = 1`).
  have hfpbot : Subgroup.fixedPointsOfMulAut φ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_fixedPointsOfMulAut] at hy
    have hr : ((φ ⟨r, Subgroup.mem_zpowers r⟩ y : ↥K) : G) = (y : G) :=
      congrArg Subtype.val (hy ⟨r, Subgroup.mem_zpowers r⟩)
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hCbot (y : G) y.2 hr)
  -- Proposition 1.5(d): the quotient fixed points push forward from `⊥`, hence are `⊥`.
  have heq := OddOrder.BG.Ch1.S03h.fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := φ) hcop hsolv hMinv
  rw [hfpbot, Subgroup.map_bot] at heq
  -- `k`'s class is fixed by every power of `r` (generator argument), hence is `1`, so `k ∈ K₀`.
  have hpow : ∀ (f : MulAut (↥K ⧸ K₀.subgroupOf K)) (y : ↥K ⧸ K₀.subgroupOf K),
      f y = y → ∀ i : ℤ, (f ^ i) y = y :=
    fun f y hf i => MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer (MulAut (↥K ⧸ K₀.subgroupOf K)) y).zpow_mem
        (MulAction.mem_stabilizer_iff.mpr hf) i)
  have hkbar : quotientMulAutHom hMinv ⟨r, Subgroup.mem_zpowers r⟩
      (QuotientGroup.mk' (K₀.subgroupOf K) ⟨k, hkK⟩) =
      QuotientGroup.mk' (K₀.subgroupOf K) ⟨k, hkK⟩ := by
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    change (r * k * r⁻¹)⁻¹ * k ∈ K₀
    have heqk : (r * k * r⁻¹)⁻¹ * k = k⁻¹ * (r * k * r⁻¹ * k⁻¹)⁻¹ * (k⁻¹)⁻¹ := by group
    have hkN : k ∈ Subgroup.normalizer (K₀ : Set G) := hKK₀ hkK
    rw [heqk]
    exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K₀ : Set G)).inv_mem hkN)
      ((r * k * r⁻¹ * k⁻¹)⁻¹)).mp (K₀.inv_mem hfix)
  have hxbar : QuotientGroup.mk' (K₀.subgroupOf K) ⟨k, hkK⟩ ∈
      Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) := by
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have ha : a = ⟨r, Subgroup.mem_zpowers r⟩ ^ i := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hi.symm
    rw [ha, map_zpow]
    exact hpow (quotientMulAutHom hMinv ⟨r, Subgroup.mem_zpowers r⟩)
      (QuotientGroup.mk' (K₀.subgroupOf K) ⟨k, hkK⟩) hkbar i
  rw [heq, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hxbar
  exact hxbar

/-- **BG Theorem 3.10(a)+(b), the type-polymorphic strong-induction core** (issue 8013 piece 3, the
`K₀` reduction of mmd L1340-1349).  The group `G` is universally quantified *inside* the induction,
because Case B passes to the quotient `G ⧸ K₀` (a different group); the recursion measure is
`Nat.card ↥K`.

Pick a minimal normal `K₀ ⊴ G` with `K₀ ≤ K` and run the `⊥`/`⊤` dichotomy
(`invariants_normal_eq_bot_or_top_of_isIrreducible`) on `C_V(K₀)`:
* `C_V(K₀) = ⊥` (Case A): `K₀` is minimal normal with trivial invariants, so the abelian-kernel base
  case `prime_card_and_finrank_of_minimalNormal_kernel` applies to `K₀` directly — no recursion;
* `C_V(K₀) = ⊤` (Case B): `K₀` acts trivially, so `ρ` factors through `G ⧸ K₀` with the strictly
  smaller kernel `K / K₀`; the induction hypothesis applies to the lift and `caseB_transfer` pulls
  the conclusion back.  The transfer bricks `invariants_lift_map_eq_of_trivial`,
  `card_map_mk'_eq_of_disjoint`, `isIrreducible_lift_of_trivial`, `fpf_lift_of_centralizer_bot`
  supply the lifted hypotheses (`Coprime |R| |K|` is needed for the last). -/
private theorem frobenius_general_aux [IsAlgClosed F] [FiniteDimensional F V] [Nontrivial V] :
    ∀ (n : ℕ) {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {K R : Subgroup G} [K.Normal]
      (ρ : Representation F G V) [ρ.IsIrreducible],
      R ≠ ⊥ → K ≠ ⊥ → (Nat.card ↥K : F) ≠ 0 → Nat.Coprime (Nat.card ↥R) (Nat.card ↥K) →
      Representation.invariants (ρ.comp K.subtype) = ⊥ →
      (∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k) →
      (∀ x : G, x ∈ R → x ≠ 1 →
        finrank F (Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype))
          = finrank F (Representation.invariants (ρ.comp R.subtype))) →
      Nat.card ↥K = n →
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p ∧
        finrank F V = Nat.card ↥R * finrank F (Representation.invariants (ρ.comp R.subtype)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro G _ _ _ K R _ ρ _ hRne hKne hKcard hcop hCVK hFrob hcond3 hn
    -- A minimal normal `K₀ ⊴ G` contained in `K`; it is `≠ ⊥`, normal, with `|K₀| ≠ 0` in `F`.
    obtain ⟨K₀, hK₀min, hK₀leK⟩ := OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal K hKne
    have hK₀norm : K₀.Normal := hK₀min.1
    have hK₀ne : K₀ ≠ ⊥ := hK₀min.2.1
    have hK₀card : (Nat.card ↥K₀ : F) ≠ 0 := by
      obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hK₀leK
      intro h0; exact hKcard (by rw [hc, Nat.cast_mul, h0, zero_mul])
    rcases invariants_normal_eq_bot_or_top_of_isIrreducible ρ (K₀ := K₀) with hbot | htop
    · -- Case A: `C_V(K₀) = ⊥`, so the minimal-normal base case applies to `K₀` directly.
      exact prime_card_and_finrank_of_minimalNormal_kernel ρ hRne hK₀min hK₀card hbot
        (fun r hr hr1 k hk hk1 => hFrob r hr hr1 k (hK₀leK hk) hk1) hcond3
    · -- Case B: `C_V(K₀) = ⊤`, so `K₀` acts trivially and `ρ` factors through `G ⧸ K₀`.
      have hker : ∀ x ∈ K₀, ρ x = 1 := by
        intro x hx
        ext v
        have hmem : v ∈ Representation.invariants (ρ.comp K₀.subtype) := by
          rw [htop]; exact Submodule.mem_top
        have hfix := (Representation.mem_invariants (ρ.comp K₀.subtype) v).mp hmem ⟨x, hx⟩
        simpa using hfix
      -- `R` meets `K` (hence `K₀`) trivially, by the Frobenius condition.
      have hdisjK : Disjoint R K := by
        rw [Subgroup.disjoint_def]
        intro g hgR hgK
        by_contra hg1
        exact hFrob g hgR hg1 g hgK hg1 (by group)
      have hdisj : Disjoint R K₀ := hdisjK.mono_right hK₀leK
      -- The lift `ρ̄` to `G ⧸ K₀` is irreducible; the quotient is finite and `K.map mk'` is normal.
      have : Representation.IsIrreducible (QuotientGroup.lift K₀ ρ hker) :=
        isIrreducible_lift_of_trivial ρ hker
      have : (K.map (QuotientGroup.mk' K₀)).Normal :=
        (‹K.Normal›).map (QuotientGroup.mk' K₀) (QuotientGroup.mk'_surjective K₀)
      have : Finite (G ⧸ K₀) := Finite.of_surjective _ (QuotientGroup.mk'_surjective K₀)
      -- `K.map mk' = K / K₀ ≠ ⊥` (else `K = K₀`, forcing `⊥ = C_V(K) = C_V(K₀) = ⊤`).
      have hKmapne : K.map (QuotientGroup.mk' K₀) ≠ ⊥ := by
        rw [Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        intro hle
        rw [le_antisymm hle hK₀leK] at hCVK
        rw [hCVK] at htop
        exact bot_ne_top htop
      -- `R.map mk' ≠ ⊥` (else `R ≤ K₀`, but `R ⊓ K₀ = ⊥` and `R ≠ ⊥`).
      have hRne' : R.map (QuotientGroup.mk' K₀) ≠ ⊥ := by
        rw [Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        intro hle
        exact hRne (by rw [← inf_eq_left.mpr hle]; exact disjoint_iff.mp hdisj)
      have hKcard' : (Nat.card (K.map (QuotientGroup.mk' K₀)) : F) ≠ 0 := by
        obtain ⟨c, hc⟩ := Subgroup.card_map_dvd (H := K) (QuotientGroup.mk' K₀)
        intro h0; exact hKcard (by rw [hc, Nat.cast_mul, h0, zero_mul])
      have hcop' : Nat.Coprime (Nat.card (R.map (QuotientGroup.mk' K₀)))
          (Nat.card (K.map (QuotientGroup.mk' K₀))) := by
        rw [card_map_mk'_eq_of_disjoint hdisj]
        exact hcop.coprime_dvd_right (Subgroup.card_map_dvd (H := K) (QuotientGroup.mk' K₀))
      have hCVK' : Representation.invariants
          ((QuotientGroup.lift K₀ ρ hker).comp (K.map (QuotientGroup.mk' K₀)).subtype) = ⊥ := by
        rw [invariants_lift_map_eq_of_trivial ρ hker K]; exact hCVK
      -- Prime-manner lifts: `zpowers (mk' x) = (zpowers x).map mk'`, then `invariants` agree (B1).
      have hcond3' : ∀ xb : G ⧸ K₀, xb ∈ R.map (QuotientGroup.mk' K₀) → xb ≠ 1 →
          finrank F (Representation.invariants
              ((QuotientGroup.lift K₀ ρ hker).comp (Subgroup.zpowers xb).subtype))
            = finrank F (Representation.invariants
              ((QuotientGroup.lift K₀ ρ hker).comp (R.map (QuotientGroup.mk' K₀)).subtype)) := by
        rintro _ ⟨x, hxR, rfl⟩ hxb1
        have hx1 : x ≠ 1 := fun h => hxb1 (by rw [h]; exact map_one _)
        rw [← MonoidHom.map_zpowers (QuotientGroup.mk' K₀) x,
          invariants_lift_map_eq_of_trivial ρ hker (Subgroup.zpowers x),
          invariants_lift_map_eq_of_trivial ρ hker R]
        exact hcond3 x hxR hx1
      -- Frobenius FPF lifts to `K / K₀` via `fpf_lift_of_centralizer_bot` (B4).
      have hFrob' : ∀ rb ∈ R.map (QuotientGroup.mk' K₀), rb ≠ 1 →
          ∀ kb ∈ K.map (QuotientGroup.mk' K₀), kb ≠ 1 → rb * kb * rb⁻¹ ≠ kb := by
        rintro _ ⟨r, hrR, rfl⟩ hrb1 _ ⟨k, hkK, rfl⟩ hkb1 hcontra
        have hr1 : r ≠ 1 := fun h => hrb1 (by rw [h]; exact map_one _)
        apply hkb1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        have hfix : r * k * r⁻¹ * k⁻¹ ∈ K₀ := by
          have hmk : (QuotientGroup.mk' K₀) (r * k * r⁻¹ * k⁻¹) = 1 := by
            simp only [map_mul, map_inv]
            rw [hcontra]; group
          rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmk
        have hrnK : r ∈ Subgroup.normalizer (K : Set G) := by
          rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top r
        have hrnK₀ : r ∈ Subgroup.normalizer (K₀ : Set G) := by
          rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top r
        have hKnK₀ : K ≤ Subgroup.normalizer (K₀ : Set G) := by
          rw [Subgroup.normalizer_eq_top]; exact le_top
        refine fpf_lift_of_centralizer_bot hrnK hK₀leK hKnK₀ hrnK₀ ?_ (Or.inr inferInstance) ?_ hkK
          hfix
        · exact hcop.coprime_dvd_left (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hrR))
        · intro y hyK hyfix
          by_contra hy1
          exact hFrob r hrR hr1 y hyK hy1 hyfix
      -- The kernel `K / K₀` is strictly smaller than `K` (its preimage map has kernel `K₀ ≠ ⊥`).
      have hcard_lt : Nat.card (K.map (QuotientGroup.mk' K₀)) < n := by
        rw [← hn]
        set φ : ↥K →* G ⧸ K₀ := (QuotientGroup.mk' K₀).comp K.subtype with hφ
        have hrange : φ.range = K.map (QuotientGroup.mk' K₀) := by
          rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
        have hcardK : Nat.card ↥K = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
          rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
          exact Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
        have hkerbot : φ.ker ≠ ⊥ := by
          have : Nontrivial ↥K₀ := (Subgroup.nontrivial_iff_ne_bot K₀).mpr hK₀ne
          obtain ⟨⟨k₀, hk₀K₀⟩, hk₀ne⟩ := exists_ne (1 : ↥K₀)
          have hk₀1 : k₀ ≠ 1 := fun h => hk₀ne (Subtype.ext h)
          intro hbot
          have hmem : (⟨k₀, hK₀leK hk₀K₀⟩ : ↥K) ∈ φ.ker := by
            rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply]
            change (QuotientGroup.mk' K₀) k₀ = 1
            rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hk₀K₀
          rw [hbot, Subgroup.mem_bot] at hmem
          exact hk₀1 (Subtype.ext_iff.mp hmem)
        have hkergt : 1 < Nat.card ↥φ.ker :=
          (Subgroup.one_lt_card_iff_ne_bot (H := φ.ker)).mpr hkerbot
        rw [hcardK, hrange]
        exact (lt_mul_iff_one_lt_right Nat.card_pos).mpr hkergt
      -- Apply the induction hypothesis to the lift and transfer the conclusion back.
      exact caseB_transfer ρ hker hdisj
        (IH (Nat.card (K.map (QuotientGroup.mk' K₀))) hcard_lt (QuotientGroup.lift K₀ ρ hker)
          hRne' hKmapne hKcard' hcop' hCVK' hFrob' hcond3' rfl)

/-- **BG Theorem 3.10(a)+(b), general (possibly non-abelian) kernel** (mmd L1267-1357, the
irreducible-module case = Case 2 of the proof).  Let `ρ` be an irreducible representation of a
finite
solvable group `G` over an algebraically closed field `F` (`char F ∤ |K|`, encoded by
`(|K| : F) ≠ 0`), with `K ⊴ G` a Frobenius kernel and `R ≤ G` a complement acting fixed-point-freely
(`hFrob`) and in prime manner (`hcond3`), coprimely (`Coprime |R| |K|`), with trivial invariants
`C_V(K) = ⊥`.  Then:
* **(a)** `|R|` is prime;
* **(b)** `finrank V = |R| · finrank C_V(R)`.

This is the general-kernel form needed by §15.2 (Theorem 15.2 step 4, issue 8012): there `K = D` may
be non-abelian.  The proof is the `K₀`-reduction strong induction `frobenius_general_aux`. -/
theorem prime_card_and_finrank_of_frobenius_general [Finite G] [IsAlgClosed F] [Group.IsSolvable G]
    (ρ : Representation F G V) [FiniteDimensional F V] [Nontrivial V] [ρ.IsIrreducible]
    {K R : Subgroup G} [K.Normal] (hRne : R ≠ ⊥) (hKne : K ≠ ⊥)
    (hKcard : (Nat.card ↥K : F) ≠ 0) (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hCVK : Representation.invariants (ρ.comp K.subtype) = ⊥)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k)
    (hcond3 : ∀ x : G, x ∈ R → x ≠ 1 →
      finrank F (Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype))
        = finrank F (Representation.invariants (ρ.comp R.subtype))) :
    ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p ∧
      finrank F V = Nat.card ↥R * finrank F (Representation.invariants (ρ.comp R.subtype)) :=
  frobenius_general_aux (Nat.card ↥K) (K := K) (R := R) ρ hRne hKne hKcard hcop hCVK hFrob hcond3
    rfl

end OddOrder.BG.Ch1.S03


