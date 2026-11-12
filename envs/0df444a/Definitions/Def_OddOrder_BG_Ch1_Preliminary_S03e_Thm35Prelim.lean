-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_Thm35Prelim
-- name    : OddOrder_BG_Ch1_Preliminary_S03e_Thm35Prelim
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:59:36.313309+00:00
-- url     : https://prove2.me/theorems/1f6318ee-4c4b-4f1d-84d0-329efbb1a885
-- title:
--   BG §3: Theorem 3.5, step infrastructure
-- statement:
--   The public machinery for Theorem 3.5 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3: the sub-Frobenius constructor, the step-(3.5) dichotomy ($U\subseteq C_V(N)$ or $W\subseteq C_V(N)$), the step-9 Clifford hard core over a general field, the weight-space and orbit-count layer for an abelian normal subgroup, and the step-9 assembly bridges.
--
--   Main declarations: `weightSpace`; `conjChar` (The conjugation action of `G` on characters of a normal subgroup `K'`: `(g · χ) k' = χ (g⁻¹ k' g)`); `kernel_trivial_on_submodule_of_centralizer_eq_bot` (Lemma 3.3 plumbing for (3.5)); `map_conjSemilinearEnd_eq_self_of_mem` (Inner conjugates are trivial (orbit-machinery entry point for step 9)); and 15 more.
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03e_Thm35Prelim.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03e_Thm35Prelim.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03b_Lemma33
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03c_Thm37
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03d_Thm34
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.Commutator.Basic

namespace OddOrder.BG.Ch1.S03e

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open scoped commutatorElement

/-- **Sub-Frobenius constructor.**  If `G = K R` is a Frobenius group and `N ≤ K` is a nontrivial
`R`-invariant subgroup (`R ≤ N_G(N)`), then `N R = N ⊔ R` is again a Frobenius group with kernel `N`
and complement `R` (viewed inside the subtype `↥(N ⊔ R)`).  The conjugation condition transfers from
`K`'s since `N ⊆ K`; complementation and normality transfer as in the `HR` setup of Theorem 3.4.

Used in Theorem 3.5 to feed the induction hypothesis to the proper `R`-invariant subgroups (step
(3.4)) and to apply Lemma 3.3 to `NR`-submodules (step (3.5)). -/
theorem isFrobeniusGroup_subgroupOf_sup
    {G : Type*} [Group G] {K R N : Subgroup G}
    (hFrob : IsFrobeniusGroup G K R) (hNK : N ≤ K) (hNinv : R ≤ Subgroup.normalizer N)
    (hNne : N ≠ ⊥) :
    IsFrobeniusGroup ↥(N ⊔ R) (N.subgroupOf (N ⊔ R)) (R.subgroupOf (N ⊔ R)) where
  isNormal := Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hNinv)
  isComplement := by
    have : (N.subgroupOf (N ⊔ R)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hNinv)
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
      rw [Subgroup.mem_inf] at hx
      simp only [Subgroup.mem_subgroupOf] at hx
      have hmem : (x : G) ∈ N ⊓ R := ⟨hx.1, hx.2⟩
      have hdisjNR : Disjoint N R := hFrob.isComplement.disjoint.mono_left hNK
      rw [hdisjNR.eq_bot, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]; exact Subtype.ext (by simpa using hmem)
    · have hsup : (N.subgroupOf (N ⊔ R)) ⊔ (R.subgroupOf (N ⊔ R)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (N.subgroupOf (N ⊔ R)) (R.subgroupOf (N ⊔ R))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  ne_bot_kernel := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    exact fun hd =>
      hNne ((inf_of_le_left (le_sup_left : N ≤ N ⊔ R)).symm.trans (disjoint_iff.mp hd))
  ne_bot_complement := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    exact fun hd =>
      hFrob.ne_bot_complement ((inf_of_le_left (le_sup_right : R ≤ N ⊔ R)).symm.trans
        (disjoint_iff.mp hd))
  conj_frobenius := by
    intro a haR ha n hnN hn hconj
    rw [Subgroup.mem_subgroupOf] at haR hnN
    have haG : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hnG : (n : G) ≠ 1 := fun h => hn (Subtype.ext h)
    have hconjG : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have := congrArg (Subtype.val) hconj
      simpa using this
    exact hFrob.conj_frobenius (a : G) haR haG (n : G) (hNK hnN) hnG hconjG

/-- **Frobenius normal dichotomy.**  In a Frobenius group `G = KR`, a normal subgroup `N` that does
not contain the kernel `K` is contained in `K`.  (With the trivial converse, every normal subgroup
of a Frobenius group is comparable to the kernel.)

Used in the non-faithful branch of Theorem 3.5 to show `C = C_G(V) ⊆ K` when `K ⊄ C`, so that the
Frobenius quotient `G/C` (with kernel `K/C`) is available for the induction (Lemma 3.2).

Proof: pick `c ∈ N \ K`.  By `centralizer_kernel_le`, `c` centralizes no nontrivial element of `K`
(else `c ∈ C_G(k) ≤ K`), so conjugation by `c` is a fixed-point-free automorphism of `K`.  Hence the
commutator map `k ↦ k · (c k c⁻¹)⁻¹` is surjective onto `K`
(`MonoidHom.FixedPointFree.commutatorMap_surjective`); each value `k c k⁻¹ c⁻¹` lies in `N`
(`c ∈ N ◁ G`), so `K ≤ N` — contradicting `¬ K ≤ N`. -/
theorem normal_le_kernel_of_not_kernel_le {G : Type*} [Group G] [Finite G]
    {K R N : Subgroup G} (hFrob : IsFrobeniusGroup G K R) [hNnorm : N.Normal]
    (hKN : ¬ K ≤ N) : N ≤ K := by
  have hKnorm : K.Normal := hFrob.isNormal
  intro c hcN
  by_contra hcK
  -- Conjugation by `c` is fixed-point-free on `K` (via `centralizer_kernel_le`).
  have hFPF : MonoidHom.FixedPointFree (OddOrder.RepresentationTheory.conjNormalMulAut K c) := by
    intro g hg
    by_contra hg1
    have hgcoe : c * (g : G) * c⁻¹ = (g : G) := by
      have := congrArg (Subtype.val) hg
      rwa [OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe] at this
    have hcent : c ∈ Subgroup.centralizer ({(g : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgcoe)
    exact hcK (hFrob.centralizer_kernel_le (g : G) g.2
      (fun h => hg1 (Subtype.ext (by simpa using h))) hcent)
  -- The commutator map is surjective onto `K`; every value lies in `N`, so `K ≤ N`.
  refine absurd (fun x hxK => ?_) hKN
  obtain ⟨k', hk'⟩ := hFPF.commutatorMap_surjective ⟨x, hxK⟩
  have h : ((MonoidHom.commutatorMap (OddOrder.RepresentationTheory.conjNormalMulAut K c) k'
      : ↥K) : G) = x := by rw [hk']
  rw [MonoidHom.commutatorMap_apply, Subgroup.coe_div,
    OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe] at h
  -- `h : (k' : G) / (c * (k' : G) * c⁻¹) = x`
  have hval : x = (k' : G) * c * (k' : G)⁻¹ * c⁻¹ := by rw [← h, div_eq_mul_inv]; group
  rw [hval]
  exact N.mul_mem (hNnorm.conj_mem c hcN (k' : G)) (N.inv_mem hcN)

section Dichotomy35

variable {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

omit [FiniteDimensional F V] in
/-- **Lemma 3.3 plumbing for (3.5).**  If `N ⊔ R` preserves a submodule `A`, `N ≤ K` is a
nontrivial `R`-invariant subgroup of the kernel of a Frobenius group `G = KR`, and `R` has no
nonzero fixed vector inside `A` (i.e. `C_A(R) = 0`), then `N` acts trivially on `A`.

This is the contrapositive of Wielandt's Lemma 3.3
(`OddOrder.BG.Ch1.S03b.kernel_acts_trivially_of_centralizer_eq_bot`) applied to the sub-Frobenius
group `NR = N ⊔ R` (constructed by `isFrobeniusGroup_subgroupOf_sup`) acting on the submodule
`A`. -/
theorem kernel_trivial_on_submodule_of_centralizer_eq_bot
    {K R N : Subgroup G} (hFrob : IsFrobeniusGroup G K R)
    (hNK : N ≤ K) (hNinv : R ≤ Subgroup.normalizer N) (hNne : N ≠ ⊥)
    (ρ : Representation F G V) (hchar : (Nat.card ↥N : F) ≠ 0)
    {A : Submodule F V} (hAinv : ∀ g ∈ N ⊔ R, ∀ a ∈ A, ρ g a ∈ A)
    (hCA : ∀ a ∈ A, (∀ r : ↥R, ρ (r : G) a = a) → a = 0) :
    ∀ n : ↥N, ∀ a ∈ A, ρ (n : G) a = a := by
  -- Restrict `ρ` to the subgroup `N ⊔ R` and to the invariant submodule `A`.
  set ρNR := ρ.comp (N ⊔ R).subtype with hρNR
  let σ : Subrepresentation ρNR :=
    { toSubmodule := A
      apply_mem_toSubmodule := fun g a ha => hAinv (g : G) g.2 a ha }
  -- The kernel `N.subgroupOf (N ⊔ R)` has the same order as `N`.
  have hcardN : Nat.card ↥(N.subgroupOf (N ⊔ R)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv
  have hchar' : (Nat.card ↥(N.subgroupOf (N ⊔ R)) : F) ≠ 0 := by rw [hcardN]; exact hchar
  -- `C_A(R') = 0` transported to the sub-Frobenius complement.
  have hCR' : ∀ v : ↥σ.toSubmodule,
      (∀ r : ↥(R.subgroupOf (N ⊔ R)), σ.toRepresentation (r : ↥(N ⊔ R)) v = v) → v = 0 := by
    intro v hv
    refine Submodule.coe_eq_zero.mp (hCA (v : V) v.2 (fun r => ?_))
    have hrmem : (r : G) ∈ N ⊔ R := Subgroup.mem_sup_right r.2
    have hr' : (⟨(r : G), hrmem⟩ : ↥(N ⊔ R)) ∈ R.subgroupOf (N ⊔ R) := by
      rw [Subgroup.mem_subgroupOf]; exact r.2
    have key := hv ⟨⟨(r : G), hrmem⟩, hr'⟩
    have := congrArg (Subtype.val) key
    simpa [σ, Subrepresentation.toRepresentation, ρNR] using this
  -- Lemma 3.3 (contrapositive) on the sub-Frobenius group.
  have hKtriv := OddOrder.BG.Ch1.S03b.kernel_acts_trivially_of_centralizer_eq_bot
    (isFrobeniusGroup_subgroupOf_sup hFrob hNK hNinv hNne) σ.toRepresentation hchar' hCR'
  intro n a ha
  have hnmem : (n : G) ∈ N ⊔ R := Subgroup.mem_sup_left n.2
  have hk : (⟨(n : G), hnmem⟩ : ↥(N ⊔ R)) ∈ N.subgroupOf (N ⊔ R) := by
    rw [Subgroup.mem_subgroupOf]; exact n.2
  set kk : ↥(N.subgroupOf (N ⊔ R)) := ⟨⟨(n : G), hnmem⟩, hk⟩ with hkk
  have h2 : σ.toRepresentation (kk : ↥(N ⊔ R)) ⟨a, ha⟩ = ⟨a, ha⟩ := by
    rw [hKtriv kk]; rfl
  have h3 := congrArg Subtype.val h2
  simpa [σ, Subrepresentation.toRepresentation, ρNR, kk] using h3

/-- **BG (3.5)** (mmd L931-939).  Let `G = KR` be a Frobenius group (`R` the complement), `ρ` a
representation on `V` with `dim C_V(R) = 1`.  If `N ≤ K` is a nontrivial `R`-invariant subgroup and
`A ⊕ B` is an `NR`-decomposition (`A`, `B` disjoint `NR`-invariant submodules), then `N` acts
trivially on `A` or on `B`.

Proof: `C_A(R)` and `C_B(R)` are disjoint subspaces of the one-dimensional `C_V(R)`, so one of them
is zero; the contrapositive of Lemma 3.3 (`kernel_trivial_on_submodule_of_centralizer_eq_bot`) then
makes `N` act trivially on the corresponding summand. -/
theorem dichotomy_3_5
    {K R N : Subgroup G} (hFrob : IsFrobeniusGroup G K R)
    (hNK : N ≤ K) (hNinv : R ≤ Subgroup.normalizer N) (hNne : N ≠ ⊥)
    (ρ : Representation F G V) (hchar : (Nat.card G : F) ≠ 0)
    (hCV1 : Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1)
    {A B : Submodule F V}
    (hAinv : ∀ g ∈ N ⊔ R, ∀ a ∈ A, ρ g a ∈ A)
    (hBinv : ∀ g ∈ N ⊔ R, ∀ b ∈ B, ρ g b ∈ B)
    (hAB : Disjoint A B) :
    (∀ n : ↥N, ∀ a ∈ A, ρ (n : G) a = a) ∨ (∀ n : ↥N, ∀ b ∈ B, ρ (n : G) b = b) := by
  -- `|N| ≠ 0` in `F` (it divides `|G|`).
  have hcharN : (Nat.card ↥N : F) ≠ 0 := by
    obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card N
    intro h0; exact hchar (by rw [hm, Nat.cast_mul, h0, zero_mul])
  -- Membership in `C_X(R)` as fixed vectors; abbreviate the predicate.
  set inv := Representation.invariants (ρ.comp R.subtype) with hinv
  have hmem_inv : ∀ w : V, w ∈ inv ↔ ∀ r : ↥R, ρ (r : G) w = w := by
    intro w; rw [hinv, Representation.mem_invariants]; rfl
  -- Either `C_A(R) = 0` or `C_B(R) = 0`.
  by_cases hA0 : ∀ a ∈ A, (∀ r : ↥R, ρ (r : G) a = a) → a = 0
  · exact Or.inl (kernel_trivial_on_submodule_of_centralizer_eq_bot hFrob hNK hNinv hNne ρ
      hcharN hAinv hA0)
  · refine Or.inr (kernel_trivial_on_submodule_of_centralizer_eq_bot hFrob hNK hNinv hNne ρ
      hcharN hBinv (fun b hb hbfix => ?_))
    -- From `¬ (C_A(R) = 0)` get a nonzero `a ∈ A` fixed by `R`; show `C_B(R) = 0`.
    push Not at hA0
    obtain ⟨a, haA, hafix, ha0⟩ := hA0
    -- `a ∈ inv`, `a ≠ 0`, and `inv` is one-dimensional, so `inv = span {a}`.
    have hainv : a ∈ inv := (hmem_inv a).mpr hafix
    have hspan : Submodule.span F {a} = inv := by
      refine Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hainv)) ?_
      rw [hCV1, finrank_span_singleton ha0]
    -- `b ∈ inv = span {a}`, so `b = c • a ∈ A`; with `b ∈ B` and `A ⊓ B = ⊥`, `b = 0`.
    have hbinv : b ∈ inv := (hmem_inv b).mpr hbfix
    rw [← hspan, Submodule.mem_span_singleton] at hbinv
    obtain ⟨c, hc⟩ := hbinv
    have hbA : b ∈ A := hc ▸ A.smul_mem c haA
    exact (Submodule.disjoint_def.mp hAB) b hbA hb

end Dichotomy35

section Step9

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable {W : Type*} [AddCommGroup W] [Module F W]

/-- On a one-dimensional module every linear endomorphism is a scalar (a homothety), so the
endomorphisms `ρ g` pairwise commute and the representation kills commutators: `⁅K, K⁆ ⊆ C_W(K)`
for any subgroup `K`.

This is the punchline of step 9 of Theorem 3.5: once the reductions force `dim_F U = 1`, the
abelian group `K' = ⁅K, K⁆` acts trivially on `U`, so `C_U(K') = U ≠ 0`. -/
theorem trivial_on_commutator_of_finrank_eq_one
    (ρ : Representation F G W) (hdim : Module.finrank F W = 1) (K : Subgroup G) :
    ∀ g ∈ (⁅K, K⁆ : Subgroup G), ρ g = 1 := by
  -- Every `ρ a` is a scalar `algebraMap F (End) c`.
  have hsc : ∀ a : G, ∃ c : F, ρ a = algebraMap F (Module.End F W) c := fun a => by
    obtain ⟨c, hc⟩ := (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ a)).exists
    exact ⟨c, by rw [hc]; exact (Algebra.algebraMap_eq_smul_one c).symm⟩
  -- Scalars commute, so all `ρ x` commute.
  have hcomm : ∀ x y : G, ρ x * ρ y = ρ y * ρ x := fun x y => by
    obtain ⟨cx, hx⟩ := hsc x; obtain ⟨cy, hy⟩ := hsc y
    rw [hx, hy, ← map_mul, ← map_mul, mul_comm cx cy]
  -- `⁅K, K⁆ ≤ ker ρ`, checking single commutators.
  suffices hle : (⁅K, K⁆ : Subgroup G) ≤ MonoidHom.ker ρ from fun g hg => hle hg
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul]
  calc ρ a * ρ b * ρ a⁻¹ * ρ b⁻¹
      = ρ a * (ρ b * ρ a⁻¹) * ρ b⁻¹ := by rw [mul_assoc (ρ a)]
    _ = ρ a * (ρ a⁻¹ * ρ b) * ρ b⁻¹ := by rw [hcomm b a⁻¹]
    _ = (ρ a * ρ a⁻¹) * (ρ b * ρ b⁻¹) := by simp only [mul_assoc]
    _ = ρ (a * a⁻¹) * ρ (b * b⁻¹) := by rw [← map_mul, ← map_mul]
    _ = 1 := by rw [mul_inv_cancel, mul_inv_cancel, map_one, mul_one]

/-- **The fixed space of a normal subgroup is `G`-invariant**, so for an irreducible `ρ` it is `⊥`
or `⊤`.  Hence if a normal subgroup `N ◁ G` has a nonzero fixed vector (`C_W(N) ≠ 0`), it acts
trivially on the whole irreducible module: `∀ g ∈ N, ρ g = 1`.

This is the step-8/9 reduction `C_U(K') ≠ 0 ⟹ K' ⊆ C_K(V)` (BG mmd L943): once `C_U(K')` is
shown nonzero, irreducibility upgrades it to all of `U`. -/
theorem trivial_of_invariants_comp_ne_bot
    (ρ : Representation F G W) [ρ.IsIrreducible] (N : Subgroup G) [hNnorm : N.Normal]
    (hne : Representation.invariants (ρ.comp N.subtype) ≠ ⊥) :
    ∀ g ∈ N, ρ g = 1 := by
  -- The fixed space `C_W(N)` carries a subrepresentation (it is `G`-invariant by normality of `N`).
  let Wρ : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants (ρ.comp N.subtype)
      apply_mem_toSubmodule := fun g v hv => by
        rw [Representation.mem_invariants] at hv ⊢
        intro n
        have hn' : g⁻¹ * (n : G) * g ∈ N := by
          have := hNnorm.conj_mem (n : G) n.2 g⁻¹; simpa using this
        have hfix := hv ⟨g⁻¹ * (n : G) * g, hn'⟩
        change ρ (n : G) (ρ g v) = ρ g v
        have hfix' : ρ (g⁻¹ * (n : G) * g) v = v := hfix
        rw [← Module.End.mul_apply, ← map_mul,
          show (n : G) * g = g * (g⁻¹ * (n : G) * g) by group, map_mul, Module.End.mul_apply,
          hfix'] }
  -- Irreducibility: `Wρ` is `⊥` or `⊤`; nonzero rules out `⊥`, so `N` fixes everything.
  rcases IsSimpleOrder.eq_bot_or_eq_top Wρ with hbot | htop
  · exact absurd (congrArg Subrepresentation.toSubmodule hbot) hne
  · have htop' : Representation.invariants (ρ.comp N.subtype) = ⊤ :=
      congrArg Subrepresentation.toSubmodule htop
    intro g hg
    ext v
    have hv : v ∈ Representation.invariants (ρ.comp N.subtype) := htop' ▸ Submodule.mem_top
    rw [Representation.mem_invariants] at hv
    exact hv ⟨g, hg⟩

open OddOrder.RepresentationTheory in
set_option backward.isDefEq.respectTransparency false in
/-- **Inner conjugates are trivial** (orbit-machinery entry point for step 9).  For `g ∈ H`, the
conjugate `M^g = M.map (conjSemilinearEnd ρ g)` of an `F[H]`-submodule `M` equals `M` itself: `ρ g`
preserves the `H`-submodule `M` (it is the action of the group element `single ⟨g,·⟩ 1`).

This supplies the `hconj` hypothesis of `restriction_isIrreducible` (BG Prop 2.2(a)) on the subgroup
elements; combined with `map_map_conjSemilinearEnd`, an isomorphism `M ≅ M^x` for a generator `x`
propagates to all of `G = ⟨H, x⟩`. -/
theorem map_conjSemilinearEnd_eq_self_of_mem (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] {g : G} (hg : g ∈ H)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule) :
    M.map (conjSemilinearEnd (H := H) ρ g) = M := by
  -- For `h ∈ H`, `conjSemilinearEnd ρ h v = single ⟨h,·⟩ 1 • v`, which stays in the
  -- `F[H]`-submodule `M`.
  have hact : ∀ {h : G} (hh : h ∈ H) (v : (resRep ρ H).asModule),
      (conjSemilinearEnd (H := H) ρ h v)
        = MonoidAlgebra.single (⟨h, hh⟩ : ↥H) (1 : F) • v := by
    intro h hh v
    rw [conjSemilinearEnd_apply, Representation.single_smul, one_smul, resRep_apply]; rfl
  refine le_antisymm ?_ ?_
  · rintro w ⟨v, hv, rfl⟩
    rw [hact hg v]; exact M.smul_mem _ hv
  · intro w hw
    rw [mem_map_conjSemilinearEnd]
    refine ⟨conjSemilinearEnd (H := H) ρ g⁻¹ w, ?_, ?_⟩
    · rw [hact (H.inv_mem hg) w]; exact M.smul_mem _ hw
    · rw [conjSemilinearEnd_apply]
      change ρ g (ρ g⁻¹ w) = w
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

open OddOrder.RepresentationTheory in
/-- **`hconj` propagation (character route).**  Let `ρ` be irreducible on `W` over an algebraically
closed `F` with `char F ∤ |H|`, `H ◁ G`, `G = ⟨H, x⟩`, and `M` a simple `F[H]`-submodule of the
restriction.  If the conjugate `M^x` has the same character as `M`, then `M ≅ M^g` for **every**
`g ∈ G` — exactly the `hconj` input of `restriction_isIrreducible` (BG Prop 2.2(a)).

The set of `g` with `char(M^g) = char(M)` is the conjugation-stabilizer of `char(M)` (a subgroup of
`G`, via the `conjNormalMulAut` composition law).  It contains `H` (inner conjugates are trivial,
`map_conjSemilinearEnd_eq_self_of_mem`) and `x` (hypothesis), hence all of `G = ⟨H, x⟩`; then
`submodule_iso_of_character_eq` (Schur orthogonality) turns equal characters into isomorphisms. -/
theorem nonempty_linearEquiv_map_conjSemilinearEnd_forall
    [IsAlgClosed F] [FiniteDimensional F W] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] [Finite ↥H] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hx : ((Subrepresentation.ofSubmodule'
              (M.map (conjSemilinearEnd (H := H) ρ x))).toRepresentation).character
        = ((Subrepresentation.ofSubmodule' M).toRepresentation).character) :
    ∀ g : G, Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ g))) := by
  have : Invertible (Nat.card ↥H : F) := invertibleOfNonzero hHchar
  set χ := ((Subrepresentation.ofSubmodule' M).toRepresentation).character with hχ
  -- Conjugation composition law for `conjNormalMulAut`.
  have hcomp : ∀ (a b : G) (h : ↥H),
      conjNormalMulAut H (a * b) h = conjNormalMulAut H a (conjNormalMulAut H b h) := by
    intro a b h; apply Subtype.ext
    rw [conjNormalMulAut_apply_coe, conjNormalMulAut_apply_coe, conjNormalMulAut_apply_coe]; group
  have hone : ∀ h : ↥H, conjNormalMulAut H 1 h = h := by
    intro h; apply Subtype.ext; rw [conjNormalMulAut_apply_coe]; group
  -- The conjugation-stabilizer subgroup of `χ`.
  let S : Subgroup G :=
    { carrier := {g | ∀ h : ↥H, χ (conjNormalMulAut H g⁻¹ h) = χ h}
      one_mem' := by intro h; rw [inv_one, hone]
      mul_mem' := fun {a b} ha hb h => by
        rw [mul_inv_rev, hcomp, hb (conjNormalMulAut H a⁻¹ h)]; exact ha h
      inv_mem' := fun {a} ha h => by
        have hkey := ha (conjNormalMulAut H a h)
        rw [← hcomp, inv_mul_cancel, hone] at hkey
        rw [inv_inv]; exact hkey.symm }
  -- `H ≤ S`: inner conjugates are trivial (`M^h = M`), so `char(M^h) = χ`.
  have hHS : (H : Set G) ⊆ (S : Set G) := by
    intro h₀ hh₀ h
    have hMM : M.map (conjSemilinearEnd (H := H) ρ h₀) = M :=
      map_conjSemilinearEnd_eq_self_of_mem ρ hh₀ M
    have hc := character_subRep_conj ρ M h₀ h
    rw [hMM] at hc
    exact hc.symm
  -- `x ∈ S`: hypothesis.
  have hxS : x ∈ S := by
    intro h
    have hc := character_subRep_conj ρ M x h
    rw [hx] at hc
    exact hc.symm
  -- `S = ⊤`, so every `g` stabilises `χ`, giving `char(M^g) = χ` and hence `M ≅ M^g`.
  have htop : (⊤ : Subgroup G) ≤ S := by
    rw [← hgen]; exact Subgroup.closure_le S |>.mpr (Set.union_subset hHS (by simpa using hxS))
  intro g
  have hgS : ∀ h : ↥H, χ (conjNormalMulAut H g⁻¹ h) = χ h := htop (Subgroup.mem_top g)
  have hcharg : ((Subrepresentation.ofSubmodule'
      (M.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation).character = χ := by
    funext h; rw [character_subRep_conj]; exact hgS h
  exact submodule_iso_of_character_eq ρ M g hcharg

open OddOrder.RepresentationTheory in
/-- **ISO case: the restriction `Res^G_H ρ` is irreducible** (BG Prop 2.2(a) applied).  If `M` is a
simple `F[H]`-submodule of an irreducible `ρ` (alg-closed, `char F ∤ |H|`, `H ◁ G`, `G = ⟨H, x⟩`)
and the conjugate `M^x` has the same character as `M`, then `ρ` restricted to `H` is irreducible.

Composes the character-route `hconj` propagation
(`nonempty_linearEquiv_map_conjSemilinearEnd_forall`) with `restriction_isIrreducible`.  Used in
step 9 with `H = K` (over `G`) and `H = K'` (over `K'R`). -/
theorem resRep_isIrreducible_of_char_eq_generator
    [IsAlgClosed F] [FiniteDimensional F W] [Nontrivial W] (ρ : Representation F G W)
    [ρ.IsIrreducible] {H : Subgroup G} [H.Normal] [Finite ↥H] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule) (hM : M ≠ ⊥)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hx : ((Subrepresentation.ofSubmodule'
              (M.map (conjSemilinearEnd (H := H) ρ x))).toRepresentation).character
        = ((Subrepresentation.ofSubmodule' M).toRepresentation).character) :
    (resRep ρ H).IsIrreducible := by
  have : NeZero (Nat.card ↥H : F) := ⟨hHchar⟩
  exact restriction_isIrreducible ρ x hgen M hM
    (nonempty_linearEquiv_map_conjSemilinearEnd_forall ρ hHchar M x hgen hx)

open OddOrder.RepresentationTheory in
/-- **Isomorphic constituents have equal characters** (reverse of `submodule_iso_of_character_eq`).
An `F[H]`-linear isomorphism `A ≃ₗ B` of constituents gives equal characters: compose with
`subRepAsModuleEquiv` to get an `F[H]`-linear iso of the subrepresentation `asModule`s, turn it into
a `Representation.Equiv` (`equivOfAsModuleEquiv`), and apply `Representation.char_iso`.

Used in the NONISO branch of step 9 to rule out `M ≅ M^{x^j}` from the character distinctness
`char(M^x) ≠ char(M)`. -/
theorem character_eq_of_nonempty_linearEquiv [FiniteDimensional F W] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal]
    {A B : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule}
    (e : ↥A ≃ₗ[MonoidAlgebra F ↥H] ↥B) :
    ((Subrepresentation.ofSubmodule' A).toRepresentation).character
      = ((Subrepresentation.ofSubmodule' B).toRepresentation).character :=
  Representation.char_iso (equivOfAsModuleEquiv
    ((subRepAsModuleEquiv (resRep ρ H) A).symm.trans
      (e.trans (subRepAsModuleEquiv (resRep ρ H) B))))

open OddOrder.RepresentationTheory in
/-- **ISO case, iso-phrased** (perf-safe variant of `resRep_isIrreducible_of_char_eq_generator`).
If a simple `F[H]`-constituent `M` of an irreducible `ρ` (alg-closed, `char F ∤ |H|`, `H ◁ G`,
`G = ⟨H, x⟩`) is isomorphic to its conjugate `M^x`, then `Res^G_H ρ` is irreducible.  Converts the
iso to the equal-character hypothesis once (`character_eq_of_nonempty_linearEquiv`). -/
theorem resRep_isIrreducible_of_iso_generator
    [IsAlgClosed F] [FiniteDimensional F W] [Nontrivial W] (ρ : Representation F G W)
    [ρ.IsIrreducible] {H : Subgroup G} [H.Normal] [Finite ↥H] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule) (hM : M ≠ ⊥)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hx : Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ x)))) :
    (resRep ρ H).IsIrreducible := by
  obtain ⟨e⟩ := hx
  exact resRep_isIrreducible_of_char_eq_generator ρ hHchar M hM x hgen
    (character_eq_of_nonempty_linearEquiv ρ e).symm

open OddOrder.RepresentationTheory in
/-- **`hconj` propagation, iso-phrased** (perf-safe variant of
`nonempty_linearEquiv_map_conjSemilinearEnd_forall`).  If the conjugate `M^x` for a generator `x`
(with `G = ⟨H, x⟩`) is `F[H]`-linearly isomorphic to `M`, then `M ≅ M^g` for **every** `g ∈ G`.

Converts the iso `M ≅ M^x` to the equal-character hypothesis once
(`character_eq_of_nonempty_linearEquiv`) and feeds it to the character-route propagation.  Phrasing
the hypothesis as a *module isomorphism* (rather than a character identity) keeps the downstream
NONISO arguments off the pathological nested-character `isDefEq` path. -/
theorem nonempty_linearEquiv_forall_of_iso_generator
    [IsAlgClosed F] [FiniteDimensional F W] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] [Finite ↥H] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hx : Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ x)))) :
    ∀ g : G, Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ g))) := by
  obtain ⟨e⟩ := hx
  exact nonempty_linearEquiv_map_conjSemilinearEnd_forall ρ hHchar M x hgen
    (character_eq_of_nonempty_linearEquiv ρ e).symm

open OddOrder.RepresentationTheory in
/-- **Distinctness of conjugates** (NONISO branch of step 9, iso-phrased).  Let `R = ⟨x⟩` be of
prime order with `G = ⟨H, x⟩`.  If `M` is *not* isomorphic to its conjugate `M^x`, then `M` is not
isomorphic to `M^{x^j}` for any `j` with `x^j ≠ 1` (i.e. for `1 ≤ j < |R|`).

Proof: a non-identity power `x^j` again generates the prime-order `R`
(`zpowers_eq_of_prime_card`), so `G = ⟨H, x^j⟩`; an iso `M ≅ M^{x^j}` would propagate
(`nonempty_linearEquiv_forall_of_iso_generator`) to `M ≅ M^x`, contradicting the hypothesis. -/
theorem not_nonempty_linearEquiv_pow_of_not_generator
    [IsAlgClosed F] [FiniteDimensional F W] [Finite G] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    {R : Subgroup G} {x : G} (hxR : Subgroup.zpowers x = R) (hRp : (Nat.card ↥R).Prime)
    (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hniso : ¬ Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ x))))
    {j : ℕ} (hxj : x ^ j ≠ 1) :
    ¬ Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ (x ^ j)))) := by
  intro hiso
  have hxR' : x ∈ R := hxR ▸ Subgroup.mem_zpowers x
  have hxjR : x ^ j ∈ R := R.pow_mem hxR' j
  have hgenj : Subgroup.zpowers (x ^ j) = R :=
    OddOrder.BG.Ch1.S03d.zpowers_eq_of_prime_card hRp hxjR hxj
  have hgenj' : Subgroup.closure ((H : Set G) ∪ {x ^ j}) = ⊤ := by
    have hle : Subgroup.zpowers (x ^ j) ≤ Subgroup.closure ((H : Set G) ∪ {x ^ j}) :=
      (Subgroup.zpowers_le).mpr (Subgroup.subset_closure (Or.inr rfl))
    have hxmem : x ∈ Subgroup.closure ((H : Set G) ∪ {x ^ j}) :=
      hle (by rw [hgenj, ← hxR]; exact Subgroup.mem_zpowers x)
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro s (hsH | hsx)
    · exact Subgroup.subset_closure (Or.inl hsH)
    · rw [Set.mem_singleton_iff] at hsx; rw [hsx]; exact hxmem
  exact hniso
    (nonempty_linearEquiv_forall_of_iso_generator ρ hHchar M (x ^ j) hgenj' hiso x)

open OddOrder.RepresentationTheory in
set_option backward.isDefEq.respectTransparency false in
/-- **(P) disjointness** (NONISO branch of step 9).  Let `R = ⟨x⟩` be of prime order `p` with
`G = ⟨H, x⟩`.  If `M` is a simple `F[H]`-constituent not isomorphic to its conjugate `M^x`, then `M`
meets the sum of the *other* conjugates `M^{x^i}` (`1 ≤ i < p`) trivially.

Proof: `M` is an atom, so `M ⊓ (⨆ …)` is `⊥` or `M`; if it were `M` then `M ≤ ⨆ M^{x^i}`, and a
simple submodule of a sum of simple modules is isomorphic to one of them
(`Submodule.linearEquiv_of_le_sSup`), i.e. `M ≅ M^{x^i}` for some `1 ≤ i < p` — contradicting the
distinctness `not_nonempty_linearEquiv_pow_of_not_generator`. -/
theorem inf_iSup_map_conjSemilinearEnd_eq_bot
    [IsAlgClosed F] [FiniteDimensional F W] [Finite G] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    {R : Subgroup G} {x : G} (hxR : Subgroup.zpowers x = R) (hRp : (Nat.card ↥R).Prime)
    (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hniso : ¬ Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ x)))) :
    M ⊓ (⨆ i ∈ Set.Ioo 0 (Nat.card ↥R),
        M.map (conjSemilinearEnd (H := H) ρ (x ^ i))) = ⊥ := by
  set p := Nat.card ↥R with hp
  have hordx : orderOf x = p := by rw [hp, ← hxR, Nat.card_zpowers]
  set Sup := ⨆ i ∈ Set.Ioo 0 p, M.map (conjSemilinearEnd (H := H) ρ (x ^ i)) with hSup
  have hatom : IsAtom M := IsSimpleModule.isAtom
  rcases eq_or_lt_of_le (inf_le_left : M ⊓ Sup ≤ M) with heq | hlt
  · exfalso
    have hMle : M ≤ Sup := by rw [← heq]; exact inf_le_right
    set s : Set (Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule) :=
      (fun i => M.map (conjSemilinearEnd (H := H) ρ (x ^ i))) '' Set.Ioo 0 p with hs
    have hssup : sSup s = Sup := by rw [hs, sSup_image]
    have hsimple : ∀ m : s, IsSimpleModule (MonoidAlgebra F ↥H)
        ↥(m : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule) := by
      rintro ⟨_, i, _, rfl⟩
      exact isSimpleModule_map_conjSemilinearEnd ρ (x ^ i) M
    obtain ⟨S, hSs, ⟨e⟩⟩ := M.linearEquiv_of_le_sSup s (by rw [hssup]; exact hMle)
    obtain ⟨i, hiIoo, rfl⟩ := hSs
    have hxi1 : x ^ i ≠ 1 := by
      intro h
      have hdvd := orderOf_dvd_of_pow_eq_one h
      rw [hordx] at hdvd
      exact Nat.not_dvd_of_pos_of_lt hiIoo.1 hiIoo.2 hdvd
    exact not_nonempty_linearEquiv_pow_of_not_generator ρ hHchar M hxR hRp hgen hniso hxi1 ⟨e⟩
  · exact hatom.2 (M ⊓ Sup) hlt

open OddOrder.RepresentationTheory in
set_option backward.isDefEq.respectTransparency false in
/-- **(P) projection / dimension bound** (NONISO branch of step 9).  With the hypotheses of
`inf_iSup_map_conjSemilinearEnd_eq_bot` and `dim C_W(R) = 1`, a simple `F[H]`-constituent `M` not
isomorphic to `M^x` is **one-dimensional** over `F`.

Proof (the BG projection argument): the `F`-linear map `T : M → W`, `m ↦ ∑_{i<p} ρ(xⁱ) m`, lands in
`C_W(R)` (it is `x`-invariant since `xᵖ = 1`: `a · Φ = Φ` for `a = ρ x`, `Φ = ∑ aⁱ`, by the
geometric-sum identity `Φ·(a-1) = aᵖ-1 = 0`) and is injective (if `T m = 0` then
`m = -∑_{1≤i<p} ρ(xⁱ) m ∈ M ⊓ ⨆ M^{xⁱ} = ⊥`, the disjointness above).  Hence
`dim_F M ≤ dim_F C_W(R) = 1`, and `M ≠ 0`, so `dim_F M = 1`. -/
theorem finrank_eq_one_of_not_iso_generator
    [IsAlgClosed F] [FiniteDimensional F W] [Finite G] (ρ : Representation F G W)
    {H : Subgroup G} [H.Normal] (hHchar : (Nat.card ↥H : F) ≠ 0)
    (M : Submodule (MonoidAlgebra F ↥H) (resRep ρ H).asModule)
    [IsSimpleModule (MonoidAlgebra F ↥H) M]
    {R : Subgroup G} {x : G} (hxR : Subgroup.zpowers x = R) (hRp : (Nat.card ↥R).Prime)
    (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hCV1 : Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1)
    (hniso : ¬ Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥H]
      ↥(M.map (conjSemilinearEnd (H := H) ρ x)))) :
    Module.finrank F ↥M = 1 := by
  set p := Nat.card ↥R with hp
  have hordx : orderOf x = p := by rw [hp, ← hxR, Nat.card_zpowers]
  have hxp : x ^ p = 1 := by rw [← hordx]; exact pow_orderOf_eq_one x
  set a : Module.End F W := ρ x with ha
  have hap : a ^ p = 1 := by rw [ha, ← map_pow, hxp, map_one]
  set Φ : Module.End F W := ∑ i ∈ Finset.range p, a ^ i with hΦ
  -- `a · Φ = Φ` (geometric sum, `aᵖ = 1`).
  have hΦfix : a * Φ = Φ := by
    have hcomm : a * Φ = Φ * a :=
      Commute.sum_right (Finset.range p) (fun i => a ^ i) a
        (fun i _ => (Commute.refl a).pow_right i)
    have hgs := geom_sum_mul a p
    rw [hap, sub_self, ← hΦ, mul_sub, mul_one, sub_eq_zero] at hgs
    rw [hcomm]; exact hgs
  -- disjointness from (P-disjoint).
  have hdisj := inf_iSup_map_conjSemilinearEnd_eq_bot ρ hHchar M hxR hRp hgen hniso
  set Sup := ⨆ i ∈ Set.Ioo 0 p, M.map (conjSemilinearEnd (H := H) ρ (x ^ i)) with hSup
  -- the projection `T`.
  let T : ↥M →ₗ[F] W := Φ ∘ₗ (M.subtype.restrictScalars F)
  have hTm : ∀ m : ↥M, T m = Φ (m : (resRep ρ H).asModule) := fun _ => rfl
  have hTsum : ∀ m : ↥M,
      T m = ∑ i ∈ Finset.range p, ρ (x ^ i) (m : (resRep ρ H).asModule) := by
    intro m
    rw [hTm, hΦ, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => by rw [ha, ← map_pow])
  -- `T` injective.
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    rw [LinearMap.mem_ker, hTsum] at hm
    have hp0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hRp.pos
    rw [← Finset.add_sum_erase _ _ hp0, pow_zero, map_one, Module.End.one_apply] at hm
    -- hm : (m : W) + ∑_{i ∈ erase 0} ρ(xⁱ) m = 0.
    have hmem : (m : (resRep ρ H).asModule) ∈ Sup := by
      have heq : (m : (resRep ρ H).asModule)
          = -(∑ i ∈ (Finset.range p).erase 0, ρ (x ^ i) (m : (resRep ρ H).asModule)) :=
        eq_neg_of_add_eq_zero_left hm
      rw [heq]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ (fun i hi => ?_))
      rw [Finset.mem_erase, Finset.mem_range] at hi
      have hiIoo : i ∈ Set.Ioo 0 p := ⟨Nat.pos_of_ne_zero hi.1, hi.2⟩
      have hsub : M.map (conjSemilinearEnd (H := H) ρ (x ^ i)) ≤ Sup :=
        le_iSup₂ (f := fun i (_ : i ∈ Set.Ioo 0 p) =>
          M.map (conjSemilinearEnd (H := H) ρ (x ^ i))) i hiIoo
      refine hsub ?_
      rw [mem_map_conjSemilinearEnd]
      exact ⟨(m : (resRep ρ H).asModule), m.2, rfl⟩
    have hbot : (m : (resRep ρ H).asModule) ∈ M ⊓ Sup := ⟨m.2, hmem⟩
    rw [hdisj, Submodule.mem_bot] at hbot
    rw [Submodule.mem_bot]
    exact Submodule.coe_eq_zero.mp hbot
  -- range `T` lands in `C_W(R)`.
  have hTinv : LinearMap.range T ≤ Representation.invariants (ρ.comp R.subtype) := by
    rw [SetLike.le_def]
    rintro v ⟨m, rfl⟩
    rw [Representation.mem_invariants]
    have hxfix : ρ x (T m) = T m := by
      have h := LinearMap.congr_fun hΦfix (m : (resRep ρ H).asModule)
      rwa [Module.End.mul_apply, ← hTm, ha] at h
    let Stab : Subgroup G :=
      { carrier := {g | ρ g (T m) = T m}
        one_mem' := by simp only [Set.mem_ofPred_eq, map_one, Module.End.one_apply]
        mul_mem' := fun {b c} hb hc => by
          simp only [Set.mem_ofPred_eq, map_mul] at *
          rw [Module.End.mul_apply, hc, hb]
        inv_mem' := fun {b} hb => by
          simp only [Set.mem_ofPred_eq] at *
          have h1 : ρ b⁻¹ (ρ b (T m)) = T m := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
          rwa [hb] at h1 }
    have hRStab : R ≤ Stab := by rw [← hxR, Subgroup.zpowers_le]; exact hxfix
    intro r
    exact hRStab r.2
  -- dimension count.
  have : Nontrivial ↥M := IsSimpleModule.nontrivial (MonoidAlgebra F ↥H) ↥M
  have : Module.Finite F ↥M :=
    Module.Finite.of_injective (M.subtype.restrictScalars F) Subtype.val_injective
  have hle : Module.finrank F ↥M ≤ 1 := by
    rw [← hCV1]
    calc Module.finrank F ↥M
        = Module.finrank F ↥(LinearMap.range T) := (LinearEquiv.ofInjective T hTinj).finrank_eq
      _ ≤ Module.finrank F ↥(Representation.invariants (ρ.comp R.subtype)) :=
          Submodule.finrank_mono hTinv
  have hpos : 0 < Module.finrank F ↥M := Module.finrank_pos
  omega

end Step9

section WeightSpace

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable {W : Type*} [AddCommGroup W] [Module F W]

/-- The `χ`-**weight space** of `K'` acting via `ρ`: the simultaneous `χ k'`-eigenspace of every
`ρ k'` (`k' ∈ K'`).  For abelian `K'` over an algebraically closed field these are the
one-dimensional `F[K']`-isotypic pieces of `U`. -/
def weightSpace (ρ : Representation F G W) (K' : Subgroup G) (χ : ↥K' → F) : Submodule F W :=
  ⨅ k' : ↥K', Module.End.eigenspace (ρ (k' : G)) (χ k')

theorem mem_weightSpace {ρ : Representation F G W} {K' : Subgroup G} {χ : ↥K' → F} {v : W} :
    v ∈ weightSpace ρ K' χ ↔ ∀ k' : ↥K', ρ (k' : G) v = χ k' • v := by
  simp only [weightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- The conjugation action of `G` on characters of a normal subgroup `K'`:
`(g · χ) k' = χ (g⁻¹ k' g)`. -/
noncomputable def conjChar (K' : Subgroup G) [K'.Normal] (g : G) (χ : ↥K' → F) : ↥K' → F :=
  fun k' => χ (OddOrder.RepresentationTheory.conjNormalMulAut K' g⁻¹ k')

omit [Field F] in
theorem conjChar_one (K' : Subgroup G) [K'.Normal] (χ : ↥K' → F) : conjChar K' 1 χ = χ := by
  funext k'
  simp only [conjChar, inv_one]
  congr 1
  apply Subtype.ext
  rw [OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe]; group

omit [Field F] in
theorem conjChar_mul (K' : Subgroup G) [K'.Normal] (g₁ g₂ : G) (χ : ↥K' → F) :
    conjChar K' (g₁ * g₂) χ = conjChar K' g₁ (conjChar K' g₂ χ) := by
  funext k'
  simp only [conjChar]
  congr 1
  apply Subtype.ext
  rw [OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe,
    OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe,
    OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe]
  group

/-- **`G` permutes the weight spaces**: `ρ g` carries the `χ`-weight space onto the
`(g · χ)`-weight space.  This is the key conjugation identity — purely an eigenspace computation
(`ρ g` is `F`-linear), with no semilinearity, because `ρ k' (ρ g v) = ρ g (ρ (g⁻¹ k' g) v)`. -/
theorem map_weightSpace (ρ : Representation F G W) {K' : Subgroup G} [K'.Normal] (g : G)
    (χ : ↥K' → F) :
    (weightSpace ρ K' χ).map (ρ g) = weightSpace ρ K' (conjChar K' g χ) := by
  have hkey : ∀ (h : G) (v : W) (k' : ↥K'),
      ρ (k' : G) (ρ h v)
        = ρ h (ρ ((OddOrder.RepresentationTheory.conjNormalMulAut K' h⁻¹ k' : ↥K') : G) v) := by
    intro h v k'
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    rw [OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe]; group
  ext w
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_weightSpace] at hv ⊢
    intro k'
    rw [hkey g v k', hv (OddOrder.RepresentationTheory.conjNormalMulAut K' g⁻¹ k'), map_smul]
    rfl
  · intro hw
    rw [mem_weightSpace] at hw
    refine ⟨ρ g⁻¹ w, ?_, ?_⟩
    · rw [mem_weightSpace]
      intro k'
      rw [hkey g⁻¹ w k']
      have hcc : conjChar K' g χ
          (OddOrder.RepresentationTheory.conjNormalMulAut K' (g⁻¹)⁻¹ k') = χ k' := by
        simp only [conjChar]
        rw [OddOrder.RepresentationTheory.conjNormalMulAut_conjNormalMulAut_inv]
      rw [hw (OddOrder.RepresentationTheory.conjNormalMulAut K' (g⁻¹)⁻¹ k'), hcc, map_smul]
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- **Weight spaces are independent** (distinct characters ⟹ independent eigenspaces).  For a
commuting family `{ρ k' : k' ∈ K'}` the simultaneous maximal generalised eigenspaces are independent
(`Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`); the weight spaces are
contained in them, so are independent too. -/
theorem iSupIndep_weightSpace (ρ : Representation F G W) {K' : Subgroup G}
    (hcomm : ∀ a b : ↥K', (a : G) * (b : G) = (b : G) * (a : G)) :
    iSupIndep (weightSpace ρ K') := by
  have hC : ∀ a b : ↥K', Commute (ρ (a : G)) (ρ (b : G)) := fun a b => by
    change ρ (a : G) * ρ (b : G) = ρ (b : G) * ρ (a : G)
    rw [← map_mul, ← map_mul, hcomm a b]
  refine (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun k' : ↥K' => ρ (k' : G))
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hC j i) φ)).mono ?_
  intro χ
  exact iInf_mono (fun _ => Module.End.eigenspace_le_maxGenEigenspace)

/-- **Irreducibility ⟹ transitivity on weights** (Clifford's transitivity, weight-space form).
If `ρ` restricted to `H` is irreducible and the weight spaces are independent, then `H` acts
transitively (by conjugation of characters) on the set of weights: any two characters `χ₁, χ₂` with
nonzero weight spaces are `H`-conjugate.

Proof: the sum `V = ⨆_{χ ∈ H·χ₁} weightSpace χ` over the `H`-orbit of `χ₁` is `H`-invariant
(`map_weightSpace`, `conjChar_mul`), hence a subrepresentation; it is nonzero (`χ₁`'s weight space),
so by irreducibility it is `⊤`.  Then `weightSpace χ₂ ≤ ⊤ = V`; were `χ₂` outside the orbit,
independence (`iSupIndep`) would force `weightSpace χ₂ = ⊥`, contradicting `h₂`. -/
theorem exists_conjChar_eq_of_irreducible (ρ : Representation F G W) {H K' : Subgroup G}
    [K'.Normal] (hHirr : Representation.IsIrreducible (ρ.comp H.subtype))
    (hindep : iSupIndep (weightSpace ρ K'))
    {χ₁ χ₂ : ↥K' → F} (h₁ : weightSpace ρ K' χ₁ ≠ ⊥) (h₂ : weightSpace ρ K' χ₂ ≠ ⊥) :
    ∃ h : ↥H, conjChar K' (h : G) χ₁ = χ₂ := by
  classical
  have := hHirr
  set O : Set (↥K' → F) := {χ | ∃ h : ↥H, conjChar K' (h : G) χ₁ = χ} with hO
  set V : Submodule F W := ⨆ χ ∈ O, weightSpace ρ K' χ with hV
  have hmemO : ∀ χ, χ ∈ O → weightSpace ρ K' χ ≤ V :=
    fun χ hχ => le_iSup₂ (f := fun χ (_ : χ ∈ O) => weightSpace ρ K' χ) χ hχ
  -- `V` is `H`-invariant.
  have hVinv : ∀ h : ↥H, V.map (ρ (h : G)) ≤ V := by
    intro h
    rw [hV, Submodule.map_iSup]
    refine iSup_le (fun χ => ?_)
    rw [Submodule.map_iSup]
    refine iSup_le (fun hχ => ?_)
    rw [map_weightSpace]
    obtain ⟨h', hh'⟩ := hχ
    refine hmemO (conjChar K' (h : G) χ) ⟨h * h', ?_⟩
    rw [Subgroup.coe_mul, conjChar_mul, hh']
  -- `V` carries a subrepresentation of `ρ|_H`.
  let Vsub : Subrepresentation (ρ.comp H.subtype) :=
    { toSubmodule := V
      apply_mem_toSubmodule := fun h v hv => hVinv h (Submodule.mem_map_of_mem hv) }
  -- `χ₁ ∈ O`, so `V ≠ ⊥`.
  have hχ₁O : χ₁ ∈ O := ⟨1, by rw [OneMemClass.coe_one, conjChar_one]⟩
  have hVne : V ≠ ⊥ := fun hbot => h₁ (le_bot_iff.mp (hbot ▸ hmemO χ₁ hχ₁O))
  -- irreducibility forces `V = ⊤`.
  have hVtop : V = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top Vsub with hb | ht
    · exact absurd (congrArg Subrepresentation.toSubmodule hb) hVne
    · exact congrArg Subrepresentation.toSubmodule ht
  -- `χ₂ ∈ O`.
  by_contra hχ₂
  push Not at hχ₂
  have hle : weightSpace ρ K' χ₂ ≤ ⨆ j, ⨆ _ : j ≠ χ₂, weightSpace ρ K' j := by
    calc weightSpace ρ K' χ₂ ≤ V := le_top.trans_eq hVtop.symm
      _ = ⨆ χ ∈ O, weightSpace ρ K' χ := hV
      _ ≤ ⨆ j, ⨆ _ : j ≠ χ₂, weightSpace ρ K' j := by
          refine iSup₂_mono' (fun χ hχ => ⟨χ, ?_, le_rfl⟩)
          obtain ⟨h, hh⟩ := hχ
          exact fun heq => hχ₂ h (heq ▸ hh)
  exact h₂ ((hindep χ₂).eq_bot_of_le hle)

/-- **(O) orbit count contradiction** (NONISO branch of step 9).  Suppose `ρ` is irreducible both
over `K` and over `K' ⊔ R`, `K'` is abelian and normal, `|K|` and `|R|` are coprime, and there are
**two distinct weights** `χ₁ ≠ χ₂` (the NONISO data `M'ˣ ≇ M'`).  This is impossible.

Both `K` and `R` act transitively on the (finite) weight set `Ω`
(`exists_conjChar_eq_of_irreducible`; for `R` the transitivity is inherited from `K' ⊔ R` because
`K'` acts trivially on characters, `K'` being abelian).  Hence `|Ω|` — the common orbit size —
divides both `|K|` and `|R|`, so divides `gcd(|K|, |R|) = 1`; but `χ₁ ≠ χ₂` forces `|Ω| ≥ 2`. -/
theorem false_of_two_weights (ρ : Representation F G W) [FiniteDimensional F W] [Finite G]
    {K K' R : Subgroup G} [K'.Normal]
    (hcomm : ∀ a b : ↥K', (a : G) * (b : G) = (b : G) * (a : G))
    (hKirr : Representation.IsIrreducible (ρ.comp K.subtype))
    (hKRirr : Representation.IsIrreducible (ρ.comp (K' ⊔ R).subtype))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥R))
    {χ₁ χ₂ : ↥K' → F}
    (h₁ : weightSpace ρ K' χ₁ ≠ ⊥) (h₂ : weightSpace ρ K' χ₂ ≠ ⊥) (hne : χ₁ ≠ χ₂) :
    False := by
  classical
  have hindep := iSupIndep_weightSpace ρ hcomm
  -- conjugation preserves "being a weight".
  have hconj_wt : ∀ (g : G) (χ : ↥K' → F),
      weightSpace ρ K' χ ≠ ⊥ → weightSpace ρ K' (conjChar K' g χ) ≠ ⊥ := by
    intro g χ hχ
    rw [← map_weightSpace ρ g χ]
    intro hbot
    refine hχ (eq_bot_iff.mpr fun v hv => ?_)
    have hmem : ρ g v ∈ (weightSpace ρ K' χ).map (ρ g) := Submodule.mem_map_of_mem hv
    rw [hbot, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    exact (ρ.apply_bijective g).injective (by rw [hmem, map_zero])
  -- `K'` acts trivially on characters (abelian).
  have hK'triv : ∀ (k' : G), k' ∈ K' → ∀ χ : ↥K' → F, conjChar K' k' χ = χ := by
    intro k' hk' χ
    funext k''
    simp only [conjChar]
    congr 1
    apply Subtype.ext
    rw [OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe, inv_inv]
    have hc := hcomm k'' ⟨k', hk'⟩
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  -- MulActions of `↥K` and `↥R` on characters via conjugation.
  let actK : MulAction ↥K (↥K' → F) :=
    { smul := fun k χ => conjChar K' (k : G) χ
      one_smul := fun χ => by
        change conjChar K' ((1 : ↥K) : G) χ = χ; rw [OneMemClass.coe_one, conjChar_one]
      mul_smul := fun a b χ => by
        change conjChar K' ((a * b : ↥K) : G) χ = conjChar K' (a : G) (conjChar K' (b : G) χ)
        rw [Subgroup.coe_mul, conjChar_mul] }
  let actR : MulAction ↥R (↥K' → F) :=
    { smul := fun r χ => conjChar K' (r : G) χ
      one_smul := fun χ => by
        change conjChar K' ((1 : ↥R) : G) χ = χ; rw [OneMemClass.coe_one, conjChar_one]
      mul_smul := fun a b χ => by
        change conjChar K' ((a * b : ↥R) : G) χ = conjChar K' (a : G) (conjChar K' (b : G) χ)
        rw [Subgroup.coe_mul, conjChar_mul] }
  have hsmulK : ∀ (k : ↥K) (χ : ↥K' → F), k • χ = conjChar K' (k : G) χ := fun _ _ => rfl
  have hsmulR : ∀ (r : ↥R) (χ : ↥K' → F), r • χ = conjChar K' (r : G) χ := fun _ _ => rfl
  set Ω : Set (↥K' → F) := {χ | weightSpace ρ K' χ ≠ ⊥} with hΩ
  -- both orbits of `χ₁` equal `Ω`.
  have horbK : MulAction.orbit ↥K χ₁ = Ω := by
    ext χ
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨k, rfl⟩
      change weightSpace ρ K' (k • χ₁) ≠ ⊥
      rw [hsmulK]; exact hconj_wt (k : G) χ₁ h₁
    · intro hχ
      obtain ⟨k, hk⟩ := exists_conjChar_eq_of_irreducible ρ hKirr hindep h₁ hχ
      exact ⟨k, by rw [hsmulK]; exact hk⟩
  have horbR : MulAction.orbit ↥R χ₁ = Ω := by
    ext χ
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨r, rfl⟩
      change weightSpace ρ K' (r • χ₁) ≠ ⊥
      rw [hsmulR]; exact hconj_wt (r : G) χ₁ h₁
    · intro hχ
      obtain ⟨h, hh⟩ := exists_conjChar_eq_of_irreducible ρ hKRirr hindep h₁ hχ
      -- decompose `h ∈ K' ⊔ R` as `k' * r`, with `k'` acting trivially.
      have hmem : (h : G) ∈ (↑(K' ⊔ R) : Set G) := h.2
      rw [Subgroup.normal_mul] at hmem
      obtain ⟨k', hk', r, hr, hkr⟩ := hmem
      refine ⟨⟨r, hr⟩, ?_⟩
      rw [hsmulR]
      have hcr : conjChar K' (h : G) χ₁ = conjChar K' r χ₁ := by
        rw [← hkr, conjChar_mul, hK'triv k' hk']
      rw [← hcr]; exact hh
  -- the common orbit size divides `|K|` and `|R|`.
  have hcardK : Nat.card ↥(MulAction.orbit ↥K χ₁) ∣ Nat.card ↥K := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (G := ↥K) χ₁)]
    exact (MulAction.stabilizer ↥K χ₁).index_dvd_card
  have hcardR : Nat.card ↥(MulAction.orbit ↥R χ₁) ∣ Nat.card ↥R := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (G := ↥R) χ₁)]
    exact (MulAction.stabilizer ↥R χ₁).index_dvd_card
  rw [horbK] at hcardK
  rw [horbR] at hcardR
  -- `|Ω| ∣ gcd(|K|, |R|) = 1`.
  have hΩ1 : Nat.card ↥Ω = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hcardK hcardR)
  -- but `χ₁, χ₂ ∈ Ω` are distinct, so `|Ω| ≥ 2`.
  have hΩfin : Finite ↥Ω := by
    rw [← horbK]; exact Set.finite_coe_iff.mpr (Set.finite_range _)
  have hnt : Nontrivial ↥Ω := ⟨⟨χ₁, h₁⟩, ⟨χ₂, h₂⟩, fun h => hne (Subtype.ext_iff.mp h)⟩
  rw [← Finite.one_lt_card_iff_nontrivial, hΩ1] at hnt
  exact lt_irrefl 1 hnt

end WeightSpace

section Step9Bridges

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable {W : Type*} [AddCommGroup W] [Module F W]

open OddOrder.RepresentationTheory in
set_option backward.isDefEq.respectTransparency false in
/-- **A simple one-dimensional `F[K']`-constituent is a weight space.**  If `M'` is a nonzero
`F[K']`-submodule of the restriction that is one-dimensional over `F`, then `K'` acts on it by a
single character `χ`, so `M' ⊆ weightSpace χ` (in particular `weightSpace χ ≠ ⊥`).  Bridges the
constituent picture of step 9's `K'`-analysis to the weight-space contradiction
`false_of_two_weights`. -/
theorem exists_weightSpace_ge_of_finrank_one [FiniteDimensional F W] (σ : Representation F G W)
    {K' : Subgroup G}
    (M' : Submodule (MonoidAlgebra F ↥K') (resRep σ K').asModule)
    (hM'ne : M' ≠ ⊥) (hM'dim : Module.finrank F ↥M' = 1) :
    ∃ χ : ↥K' → F, M'.restrictScalars F ≤ weightSpace σ K' χ := by
  classical
  obtain ⟨m₀, hm₀M, hm₀0⟩ := (Submodule.ne_bot_iff M').mp hM'ne
  -- `M'.restrictScalars F = span F {m₀}` (one-dimensional, `m₀ ≠ 0`).
  have hspan : M'.restrictScalars F = Submodule.span F {m₀} := by
    refine (Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hm₀M)) ?_).symm
    rw [finrank_span_singleton hm₀0]
    exact hM'dim.symm
  -- `σ k' m₀ ∈ M'` (it is the `single k' 1`-action), so `= χ k' • m₀`.
  have hσmem : ∀ k' : ↥K', σ (k' : G) m₀ ∈ M'.restrictScalars F := by
    intro k'
    have h := M'.smul_mem (MonoidAlgebra.single k' (1 : F)) hm₀M
    rwa [Representation.single_smul, one_smul, resRep_apply] at h
  choose χ hχ using fun k' => Submodule.mem_span_singleton.mp (hspan ▸ hσmem k')
  refine ⟨χ, ?_⟩
  rw [hspan]
  intro m hm
  rw [Submodule.mem_span_singleton] at hm
  obtain ⟨c, rfl⟩ := hm
  rw [mem_weightSpace]
  intro k'
  change σ (k' : G) (c • m₀) = χ k' • (c • m₀)
  rw [map_smul, ← hχ k', smul_smul, smul_smul, mul_comm]

open OddOrder.RepresentationTheory in
set_option backward.isDefEq.respectTransparency false in
/-- **A one-dimensional `K`-constituent is fixed by `K' = ⁅K, K⁆`.**  If `M` is an `F[K]`-submodule
of the restriction that is one-dimensional over `F`, then every element of `⁅K, K⁆` acts trivially
on `M` (scalars commute), so `M ⊆ C_W(⁅K, K⁆)`.  This finishes the NONISO `K`-analysis of step 9:
`(P)` gives `dim M = 1`, so `M ⊆ C_U(K')`, hence `C_U(K') ≠ 0`. -/
theorem restrictScalars_le_invariants_of_finrank_one [FiniteDimensional F W]
    (σ : Representation F G W) {K : Subgroup G}
    (M : Submodule (MonoidAlgebra F ↥K) (resRep σ K).asModule)
    (hMdim : Module.finrank F ↥M = 1) :
    M.restrictScalars F ≤ Representation.invariants (σ.comp (⁅K, K⁆ : Subgroup G).subtype) := by
  -- the subrepresentation carried by `M` over `K` is one-dimensional, so `⁅⊤, ⊤⁆` acts trivially.
  set Mρ := (Subrepresentation.ofSubmodule' M).toRepresentation with hMρ
  have hdim1 : Module.finrank F ↥(Subrepresentation.ofSubmodule' M).toSubmodule = 1 := hMdim
  have htriv := trivial_on_commutator_of_finrank_eq_one Mρ hdim1 (⊤ : Subgroup ↥K)
  -- transport to `⁅K, K⁆ ≤ G`.
  intro v hv
  rw [Representation.mem_invariants]
  intro k'
  have hk'mem : (k' : G) ∈ (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K).map K.subtype := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact k'.2
  obtain ⟨g, hg, hgk⟩ := hk'mem
  have hg1 : Mρ g = 1 := htriv g hg
  have hvmem : v ∈ (Subrepresentation.ofSubmodule' M).toSubmodule := hv
  have h2 : Mρ g ⟨v, hvmem⟩ = ⟨v, hvmem⟩ := by rw [hg1]; rfl
  have h3 := congrArg (Subtype.val) h2
  change σ (k' : G) v = v
  rw [← hgk]
  simpa [hMρ, Subrepresentation.toRepresentation] using h3

open OddOrder.RepresentationTheory in
set_option backward.isDefEq.respectTransparency false in
/-- **The reducible `N R`-case of step 9** (`N = K'`).  If `ρ` restricted to `N ⊔ R` is *not*
irreducible, then `N` has a nonzero fixed vector: `C_W(N) ≠ 0`.

A simple `F[N⊔R]`-submodule `A` is proper (else `ρ|_{NR}` would be irreducible) and nonzero; Maschke
gives a complement `B` (also nonzero).  Both are `NR`-invariant and disjoint, so the dichotomy
`dichotomy_3_5` makes `N` act trivially on `A` or on `B`; that summand lies in `C_W(N)`. -/
theorem invariants_ne_bot_of_not_irreducible_sup [Finite G] [FiniteDimensional F W] [Nontrivial W]
    (σ : Representation F G W) {K R N : Subgroup G} [N.Normal]
    (hFrob : IsFrobeniusGroup G K R) (hNK : N ≤ K) (hNinv : R ≤ Subgroup.normalizer N)
    (hNne : N ≠ ⊥) (hchar : (Nat.card G : F) ≠ 0) (hcharNR : (Nat.card ↥(N ⊔ R) : F) ≠ 0)
    (hCV1 : Module.finrank F (Representation.invariants (σ.comp R.subtype)) = 1)
    (hNRnotirr : ¬ Representation.IsIrreducible (σ.comp (N ⊔ R).subtype)) :
    Representation.invariants (σ.comp N.subtype) ≠ ⊥ := by
  have : NeZero (Nat.card ↥(N ⊔ R) : F) := ⟨hcharNR⟩
  have : Nontrivial (resRep σ (N ⊔ R)).asModule := inferInstanceAs (Nontrivial W)
  have hss : IsSemisimpleModule (MonoidAlgebra F ↥(N ⊔ R)) (resRep σ (N ⊔ R)).asModule := by
    rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]; infer_instance
  -- a simple `F[N⊔R]`-submodule `A`, necessarily proper (else `ρ|_{NR}` irreducible).
  obtain ⟨A, hAsimple⟩ :=
    IsSemisimpleModule.exists_simple_submodule (MonoidAlgebra F ↥(N ⊔ R))
      (resRep σ (N ⊔ R)).asModule
  have := hAsimple
  have hAne : A ≠ ⊥ := IsSimpleModule.isAtom.1
  have hAtop : A ≠ ⊤ := by
    rintro rfl
    refine hNRnotirr ((Representation.irreducible_iff_isSimpleModule_asModule _).mpr ?_)
    exact IsSimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨B, hAB⟩ := exists_isCompl A
  have hBne : B ≠ ⊥ := by
    rintro rfl
    exact hAtop (by simpa using codisjoint_iff.mp hAB.codisjoint)
  -- invariance bridge: `F[N⊔R]`-submodules are `σ`-invariant on `N ⊔ R`.
  have hinv : ∀ (D : Submodule (MonoidAlgebra F ↥(N ⊔ R)) (resRep σ (N ⊔ R)).asModule),
      ∀ g ∈ N ⊔ R, ∀ a ∈ D.restrictScalars F, σ g a ∈ D.restrictScalars F := by
    intro D g hg a ha
    have h := D.smul_mem (MonoidAlgebra.single (⟨g, hg⟩ : ↥(N ⊔ R)) (1 : F)) ha
    rwa [Representation.single_smul, one_smul, resRep_apply] at h
  have hdisj : Disjoint (A.restrictScalars F) (B.restrictScalars F) :=
    Submodule.disjoint_def.mpr fun v hvA hvB =>
      (Submodule.disjoint_def.mp hAB.disjoint) v hvA hvB
  -- `dichotomy_3_5`: `N` acts trivially on `A` or on `B`; that summand lies in `C_W(N)`.
  have hmemInv : ∀ (D : Submodule (MonoidAlgebra F ↥(N ⊔ R)) (resRep σ (N ⊔ R)).asModule),
      D ≠ ⊥ → (∀ n : ↥N, ∀ a ∈ D.restrictScalars F, σ (n : G) a = a) →
      Representation.invariants (σ.comp N.subtype) ≠ ⊥ := by
    intro D hDne hDtriv hcontra
    obtain ⟨a₀, ha₀D, ha₀0⟩ := (Submodule.ne_bot_iff _).mp hDne
    have : a₀ ∈ Representation.invariants (σ.comp N.subtype) := by
      rw [Representation.mem_invariants]; intro n; exact hDtriv n a₀ ha₀D
    rw [hcontra, Submodule.mem_bot] at this
    exact ha₀0 this
  rcases dichotomy_3_5 hFrob hNK hNinv hNne σ hchar hCV1 (hinv A) (hinv B) hdisj with hA | hB
  · exact hmemInv A hAne hA
  · exact hmemInv B hBne hB

open OddOrder.RepresentationTheory in
set_option backward.isDefEq.respectTransparency false in
/-- **The single-weight (ISO) case of step 9's `K'`-analysis.**  Suppose `ρ` restricted to `K' ⊔ R`
is irreducible, `K'` is abelian and normal, `R = ⟨x⟩`, and there is a character `χ` with nonzero
weight space that is *fixed* by `x` (`conjChar x χ = χ`).  Then `W` is one-dimensional.

The `χ`-weight space is `K' ⊔ R`-invariant (`K'` acts trivially on characters, `x` fixes `χ`), hence
all of `W` (irreducibility); so `K'` acts by the scalar `χ`.  An eigenvalue `λ` of `ρ x` then has a
`K' ⊔ R`-invariant eigenspace (the scalars `ρ k'` commute with `ρ x`), hence all of `W`, so `ρ x` is
also scalar.  With every `ρ g` (`g ∈ K' ⊔ R`) scalar, any line is `K' ⊔ R`-invariant, forcing
`dim W = 1`. -/
theorem finrank_eq_one_of_weight_fixed [Finite G] [FiniteDimensional F W] [Nontrivial W]
    [IsAlgClosed F] (σ : Representation F G W) {K' R : Subgroup G} [K'.Normal]
    (hcomm : ∀ a b : ↥K', (a : G) * (b : G) = (b : G) * (a : G))
    (x : G) (hxR : Subgroup.zpowers x = R)
    (hKRirr : Representation.IsIrreducible (σ.comp (K' ⊔ R).subtype))
    {χ : ↥K' → F} (hχne : weightSpace σ K' χ ≠ ⊥) (hχfix : conjChar K' x χ = χ) :
    Module.finrank F W = 1 := by
  have := hKRirr
  -- `K' ⊔ R = ⟨K', x⟩`.
  have hgen : Subgroup.closure ((K' : Set G) ∪ {x}) = K' ⊔ R := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure, hxR]
  -- `K' ⊔ R`-invariant submodules are `⊥` or `⊤`.
  have hsub : ∀ D : Submodule F W, (∀ g ∈ K' ⊔ R, ∀ d ∈ D, σ g d ∈ D) → D = ⊥ ∨ D = ⊤ := by
    intro D hD
    let Dρ : Subrepresentation (σ.comp (K' ⊔ R).subtype) :=
      { toSubmodule := D
        apply_mem_toSubmodule := fun g d hd => hD (g : G) g.2 d hd }
    rcases IsSimpleOrder.eq_bot_or_eq_top Dρ with h | h
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
  -- every `g ∈ K' ⊔ R` fixes the character `χ`.
  have hK'fix : ∀ k' : ↥K', conjChar K' (k' : G) χ = χ := by
    intro k'
    funext k''
    simp only [conjChar]
    congr 1
    apply Subtype.ext
    rw [conjNormalMulAut_apply_coe, inv_inv]
    have hc := hcomm k'' k'
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hSfix : ∀ g ∈ K' ⊔ R, conjChar K' g χ = χ := by
    have hle : (K' ⊔ R : Subgroup G) ≤
        { carrier := {g | conjChar K' g χ = χ}
          one_mem' := conjChar_one K' χ
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_ofPred_eq] at *; rw [conjChar_mul, hb, ha]
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_ofPred_eq] at *
            conv_lhs => rw [← ha]
            rw [← conjChar_mul, inv_mul_cancel, conjChar_one] } := by
      rw [← hgen, Subgroup.closure_le]
      rintro s (hsK' | hsx)
      · exact hK'fix ⟨s, hsK'⟩
      · rw [Set.mem_singleton_iff] at hsx; subst hsx; exact hχfix
    exact fun g hg => hle hg
  -- `weightSpace χ = ⊤`: it is `K' ⊔ R`-invariant and nonzero.
  have hwtop : weightSpace σ K' χ = ⊤ := by
    refine (hsub _ ?_).resolve_left hχne
    intro g hg d hd
    have : σ g d ∈ (weightSpace σ K' χ).map (σ g) := Submodule.mem_map_of_mem hd
    rwa [map_weightSpace, hSfix g hg] at this
  -- `K'` acts by the scalar `χ` on all of `W`.
  have hK'scalar : ∀ (k' : ↥K') (w : W), σ (k' : G) w = χ k' • w := by
    intro k' w
    have hw : w ∈ weightSpace σ K' χ := by rw [hwtop]; exact Submodule.mem_top
    rw [mem_weightSpace] at hw
    exact hw k'
  -- `ρ x` commutes with every `ρ g` (`g ∈ K' ⊔ R`).
  have hcommx : ∀ g ∈ K' ⊔ R, σ g * σ x = σ x * σ g := by
    have hle : (K' ⊔ R : Subgroup G) ≤
        { carrier := {g | σ g * σ x = σ x * σ g}
          one_mem' := by simp only [Set.mem_ofPred_eq, map_one, one_mul, mul_one]
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_ofPred_eq, map_mul] at *
            rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_ofPred_eq] at *
            have hcomm : Commute (↑(σ.asGroupHom a)) (σ x) := by
              rw [σ.asGroupHom_apply]; exact ha
            have hinv := hcomm.units_inv_left
            have heq : (↑((σ.asGroupHom a)⁻¹) : Module.End F W) = σ a⁻¹ := by
              rw [← map_inv, σ.asGroupHom_apply]
            rwa [heq] at hinv } := by
      rw [← hgen, Subgroup.closure_le]
      rintro s (hsK' | hsx)
      · refine LinearMap.ext fun w => ?_
        simp only [Module.End.mul_apply, hK'scalar ⟨s, hsK'⟩, map_smul]
      · rw [Set.mem_singleton_iff] at hsx; subst hsx; rfl
    exact fun g hg => hle hg
  -- `ρ x` is scalar (its eigenspace is `K' ⊔ R`-invariant, hence `⊤`).
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue (σ x)
  have hEtop : Module.End.eigenspace (σ x) lam = ⊤ := by
    refine (hsub _ ?_).resolve_left hlam
    intro g hg d hd
    rw [Module.End.mem_eigenspace_iff] at hd ⊢
    have hcg := LinearMap.congr_fun (hcommx g hg) d
    simp only [Module.End.mul_apply] at hcg
    rw [← hcg, hd, map_smul]
  have hxscalar : ∀ w : W, σ x w = lam • w := by
    intro w
    have hw : w ∈ Module.End.eigenspace (σ x) lam := by rw [hEtop]; exact Submodule.mem_top
    rwa [Module.End.mem_eigenspace_iff] at hw
  -- every `g ∈ K' ⊔ R` maps a fixed nonzero `v` into the line `F • v`.
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  have hgv : ∀ g ∈ K' ⊔ R, σ g v ∈ Submodule.span F {v} := by
    have hle : (K' ⊔ R : Subgroup G) ≤
        { carrier := {g | σ g v ∈ Submodule.span F {v}}
          one_mem' := by
            simp only [Set.mem_ofPred_eq, map_one, Module.End.one_apply]
            exact Submodule.mem_span_singleton_self v
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_ofPred_eq] at *
            rw [map_mul, Module.End.mul_apply]
            obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
            rw [← hc, map_smul]
            exact Submodule.smul_mem _ c ha
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_ofPred_eq] at *
            obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
            have hc0 : c ≠ 0 := by
              rintro rfl
              rw [zero_smul] at hc
              exact hv ((σ.apply_bijective a).injective (by rw [← hc, map_zero]))
            rw [Submodule.mem_span_singleton]
            refine ⟨c⁻¹, ?_⟩
            have hcav : c • σ a⁻¹ v = v := by
              rw [← map_smul, hc, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                Module.End.one_apply]
            rw [inv_smul_eq_iff₀ hc0]; exact hcav.symm } := by
      rw [← hgen, Subgroup.closure_le]
      rintro s (hsK' | hsx)
      · change σ s v ∈ Submodule.span F {v}
        rw [hK'scalar ⟨s, hsK'⟩]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
      · rw [Set.mem_singleton_iff] at hsx; subst hsx
        change σ s v ∈ Submodule.span F {v}
        rw [hxscalar]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    exact fun g hg => hle hg
  -- `F • v` is `K' ⊔ R`-invariant and nonzero, hence `⊤`; so `dim W = 1`.
  have hspan : Submodule.span F {v} = ⊤ := by
    refine (hsub _ ?_).resolve_left (by rw [Submodule.span_singleton_eq_bot]; exact hv)
    intro g hg d hd
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hd
    rw [← ha, map_smul]
    exact Submodule.smul_mem _ a (hgv g hg)
  have hfr := finrank_span_singleton (K := F) hv
  rw [hspan, finrank_top] at hfr
  exact hfr

open OddOrder.RepresentationTheory in
set_option backward.isDefEq.respectTransparency false in
/-- **Step 9 capstone (mmd L945-951): `C_W(K') ≠ 0`.**  Let `σ` be an *irreducible*
representation of the Frobenius group `G = K R` (`R = ⟨x⟩` of prime order, `gcd(|K|, |R|) = 1`)
over an algebraically
closed field, with `dim C_W(R) = 1` and `K' = ⁅K, K⁆` nontrivial and abelian.  Then `C_W(K') ≠ 0`.

This is the Clifford-theoretic core of Theorem 3.5, assembled from the step-9 pieces:
* **`K`-analysis.**  A simple `F[K]`-constituent `M` is either isomorphic to its conjugate `M^x`
  (then `Res^G_K σ` is irreducible, `resRep_isIrreducible_of_iso_generator`) or not (then
  `dim M = 1` by the projection argument `finrank_eq_one_of_not_iso_generator`, so
  `M ⊆ C_W(K')`, done).
* **`K'R`-analysis.**  If `Res^G_{K'R} σ` is reducible, `invariants_ne_bot_of_not_irreducible_sup`
  gives `C_W(K') ≠ 0`.
* **`K'`-analysis.**  Otherwise a simple `F[K']`-constituent `M'` is one-dimensional (`K'` abelian,
  alg-closed) with a weight `χ₁`.  If `x` fixes `χ₁` then `dim W = 1`
  (`finrank_eq_one_of_weight_fixed`), so `K'` acts trivially; if not, the two distinct weights `χ₁`,
  `x·χ₁` contradict the orbit count `false_of_two_weights`. -/
theorem invariants_commutator_ne_bot_of_irreducible
    [IsAlgClosed F] [FiniteDimensional F W] [Nontrivial W] [Finite G]
    (σ : Representation F G W) [σ.IsIrreducible]
    {K R : Subgroup G} (hFrob : IsFrobeniusGroup G K R)
    (x : G) (hxR : Subgroup.zpowers x = R) (hRp : (Nat.card ↥R).Prime)
    (hgen : Subgroup.closure ((K : Set G) ∪ {x}) = ⊤)
    (hchar : (Nat.card G : F) ≠ 0) (hcharK : (Nat.card ↥K : F) ≠ 0)
    (hcharKR : (Nat.card ↥((⁅K, K⁆ : Subgroup G) ⊔ R) : F) ≠ 0)
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥R))
    (hK'ne : (⁅K, K⁆ : Subgroup G) ≠ ⊥)
    (hcomm : ∀ a b : ↥(⁅K, K⁆ : Subgroup G), (a : G) * (b : G) = (b : G) * (a : G))
    (hCV1 : Module.finrank F (Representation.invariants (σ.comp R.subtype)) = 1) :
    Representation.invariants (σ.comp (⁅K, K⁆ : Subgroup G).subtype) ≠ ⊥ := by
  have hKnorm : K.Normal := hFrob.isNormal
  have hK'norm : (⁅K, K⁆ : Subgroup G).Normal := Subgroup.commutator_normal K K
  have hK'le : (⁅K, K⁆ : Subgroup G) ≤ K := Subgroup.commutator_le_right K K
  have hRnormK' : R ≤ Subgroup.normalizer (⁅K, K⁆ : Subgroup G) :=
    Subgroup.le_normalizer_of_normal
  have : NeZero (Nat.card ↥K : F) := ⟨hcharK⟩
  -- a simple `F[K]`-constituent `M`.
  have hssK : IsSemisimpleModule (MonoidAlgebra F ↥K) (resRep σ K).asModule := by
    rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]; infer_instance
  have : Nontrivial (resRep σ K).asModule := ‹Nontrivial W›
  obtain ⟨M, hMs⟩ :=
    IsSemisimpleModule.exists_simple_submodule (MonoidAlgebra F ↥K) (resRep σ K).asModule
  have := hMs
  have hMne : M ≠ ⊥ := by
    rintro rfl
    have : Nontrivial ↥(⊥ : Submodule (MonoidAlgebra F ↥K) (resRep σ K).asModule) :=
      IsSimpleModule.nontrivial (MonoidAlgebra F ↥K) _
    exact false_of_nontrivial_of_subsingleton
      ↥(⊥ : Submodule (MonoidAlgebra F ↥K) (resRep σ K).asModule)
  by_cases hMiso : Nonempty (↥M ≃ₗ[MonoidAlgebra F ↥K]
      ↥(M.map (conjSemilinearEnd (H := K) σ x)))
  · -- **`K`-analysis, ISO**: `Res^G_K σ` is irreducible.
    have hKirr : (resRep σ K).IsIrreducible :=
      resRep_isIrreducible_of_iso_generator σ hcharK M hMne x hgen hMiso
    by_cases hKRirr : Representation.IsIrreducible (σ.comp ((⁅K, K⁆ : Subgroup G) ⊔ R).subtype)
    · -- **`K'R`-analysis, irreducible**: pass to the `K'`-analysis.
      have hcharK' : (Nat.card ↥(⁅K, K⁆ : Subgroup G) : F) ≠ 0 := by
        obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hK'le
        intro h0; exact hcharK (by rw [hm, Nat.cast_mul, h0, zero_mul])
      have : NeZero (Nat.card ↥(⁅K, K⁆ : Subgroup G) : F) := ⟨hcharK'⟩
      have hssK' : IsSemisimpleModule (MonoidAlgebra F ↥(⁅K, K⁆ : Subgroup G))
          (resRep σ (⁅K, K⁆ : Subgroup G)).asModule := by
        rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
        infer_instance
      have : Nontrivial (resRep σ (⁅K, K⁆ : Subgroup G)).asModule := ‹Nontrivial W›
      obtain ⟨M', hM's⟩ := IsSemisimpleModule.exists_simple_submodule
        (MonoidAlgebra F ↥(⁅K, K⁆ : Subgroup G)) (resRep σ (⁅K, K⁆ : Subgroup G)).asModule
      have := hM's
      have hM'ne : M' ≠ ⊥ := by
        rintro rfl
        have : Nontrivial ↥(⊥ : Submodule (MonoidAlgebra F ↥(⁅K, K⁆ : Subgroup G))
            (resRep σ (⁅K, K⁆ : Subgroup G)).asModule) :=
          IsSimpleModule.nontrivial (MonoidAlgebra F ↥(⁅K, K⁆ : Subgroup G)) _
        exact false_of_nontrivial_of_subsingleton
          ↥(⊥ : Submodule (MonoidAlgebra F ↥(⁅K, K⁆ : Subgroup G))
            (resRep σ (⁅K, K⁆ : Subgroup G)).asModule)
      have : IsMulCommutative ↥(⁅K, K⁆ : Subgroup G) :=
        ⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩
      have := subRep_isIrreducible (resRep σ (⁅K, K⁆ : Subgroup G)) M'
      have : Module.Finite F ↥M' :=
        Module.Finite.of_injective ((M'.subtype).restrictScalars F) Subtype.val_injective
      have hM'dim : Module.finrank F ↥M' = 1 :=
        Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
          (Subrepresentation.ofSubmodule' M').toRepresentation
      obtain ⟨χ₁, hχ₁⟩ := exists_weightSpace_ge_of_finrank_one σ M' hM'ne hM'dim
      have hwt1 : weightSpace σ (⁅K, K⁆ : Subgroup G) χ₁ ≠ ⊥ := by
        intro hbot
        obtain ⟨m', hm'M, hm'0⟩ := (Submodule.ne_bot_iff M').mp hM'ne
        have hmem : m' ∈ weightSpace σ (⁅K, K⁆ : Subgroup G) χ₁ := hχ₁ hm'M
        rw [hbot, Submodule.mem_bot] at hmem
        exact hm'0 hmem
      by_cases hfix : conjChar (⁅K, K⁆ : Subgroup G) x χ₁ = χ₁
      · -- **`K'`-analysis, ISO**: `dim W = 1`, so `K'` acts trivially.
        have hUdim := finrank_eq_one_of_weight_fixed σ hcomm x hxR hKRirr hwt1 hfix
        have htriv := trivial_on_commutator_of_finrank_eq_one σ hUdim K
        obtain ⟨w, hw⟩ := exists_ne (0 : W)
        rw [Submodule.ne_bot_iff]
        refine ⟨w, ?_, hw⟩
        rw [Representation.mem_invariants]
        intro k'
        change σ (k' : G) w = w
        rw [htriv (k' : G) k'.2]; rfl
      · -- **`K'`-analysis, NONISO**: two distinct weights contradict the orbit count.
        have hwt2 : weightSpace σ (⁅K, K⁆ : Subgroup G)
            (conjChar (⁅K, K⁆ : Subgroup G) x χ₁) ≠ ⊥ := by
          rw [← map_weightSpace σ x χ₁]
          intro hbot
          apply hwt1
          rw [eq_bot_iff]
          intro v hv
          have hmem : σ x v ∈ (weightSpace σ (⁅K, K⁆ : Subgroup G) χ₁).map (σ x) :=
            Submodule.mem_map_of_mem hv
          rw [hbot, Submodule.mem_bot] at hmem
          rw [Submodule.mem_bot]
          exact (σ.apply_bijective x).injective (by rw [hmem, map_zero])
        exact (false_of_two_weights σ hcomm hKirr hKRirr hcop hwt1 hwt2
          (fun h => hfix h.symm)).elim
    · -- **`K'R`-analysis, reducible**: `C_W(K') ≠ 0` directly.
      exact invariants_ne_bot_of_not_irreducible_sup σ hFrob hK'le hRnormK' hK'ne hchar
        hcharKR hCV1 hKRirr
  · -- **`K`-analysis, NONISO**: `dim M = 1`, so `M ⊆ C_W(K')`.
    have hMdim : Module.finrank F ↥M = 1 :=
      finrank_eq_one_of_not_iso_generator σ hcharK M hxR hRp hgen hCV1 hMiso
    have hsub := restrictScalars_le_invariants_of_finrank_one σ M hMdim
    obtain ⟨m, hmM, hm0⟩ := (Submodule.ne_bot_iff M).mp hMne
    rw [Submodule.ne_bot_iff]
    exact ⟨m, hsub hmM, hm0⟩

end Step9Bridges

/-- **`dim C_U(R) = 1` for a `G`-submodule on which `K` acts nontrivially.**  If `dim C_V(R) = 1`
and `K` acts nontrivially on a subrepresentation `U`, then the fixed space `C_U(R)` is again
one-dimensional: it is nonzero by Lemma 3.3 (`centralizer_ne_bot_of_nontrivial_kernel`) and embeds
into the one-dimensional `C_V(R)` via the inclusion `U ↪ V`.

This is the bridge that lets step 9 (`invariants_commutator_ne_bot_of_irreducible`) run on the
irreducible summand `U` selected by Maschke, where `dim C_U(R) = 1` is required. -/
theorem finrank_invariants_subrep_eq_one {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ρ : Representation F G V) {K R : Subgroup G}
    (hFrob : IsFrobeniusGroup G K R) (hcharK : (Nat.card ↥K : F) ≠ 0)
    (hCV1 : Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1)
    (U : Subrepresentation ρ) (hKnt : ∃ k : ↥K, U.toRepresentation (k : G) ≠ 1) :
    Module.finrank F (Representation.invariants (U.toRepresentation.comp R.subtype)) = 1 := by
  -- `≥ 1`: Lemma 3.3 gives a nonzero `R`-fixed vector in `U`.
  obtain ⟨v, hv0, hvfix⟩ :=
    OddOrder.BG.Ch1.S03b.centralizer_ne_bot_of_nontrivial_kernel hFrob U.toRepresentation
      hcharK hKnt
  have hne : Representation.invariants (U.toRepresentation.comp R.subtype) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨v, (Representation.mem_invariants _ _).mpr hvfix, hv0⟩
  -- `≤ 1`: the inclusion `U ↪ V` carries `C_U(R)` into `C_V(R)`.
  have hsubset : (Representation.invariants (U.toRepresentation.comp R.subtype)).map
      U.toSubmodule.subtype ≤ Representation.invariants (ρ.comp R.subtype) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Representation.mem_invariants] at hw
    rw [Representation.mem_invariants]
    intro r
    exact congrArg Subtype.val (hw r)
  have hle : Module.finrank F
      (Representation.invariants (U.toRepresentation.comp R.subtype)) ≤ 1 := by
    rw [← hCV1, (Submodule.equivMapOfInjective U.toSubmodule.subtype
      U.toSubmodule.injective_subtype _).finrank_eq]
    exact Submodule.finrank_mono hsubset
  have : Nontrivial (Representation.invariants (U.toRepresentation.comp R.subtype)) :=
    Submodule.nontrivial_iff_ne_bot.mpr hne
  have hpos : 0 < Module.finrank F
      (Representation.invariants (U.toRepresentation.comp R.subtype)) :=
    Module.finrank_pos
  omega

end OddOrder.BG.Ch1.S03e


