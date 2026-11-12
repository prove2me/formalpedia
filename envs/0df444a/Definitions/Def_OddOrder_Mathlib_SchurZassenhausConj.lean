-- Prove2me | Definitions.Def_OddOrder_Mathlib_SchurZassenhausConj
-- name    : OddOrder_Mathlib_SchurZassenhausConj
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:22.507619+00:00
-- url     : https://prove2.me/theorems/9b6faa8e-7197-4be0-84a2-cf63e4f6a2e1
-- title:
--   Schur–Zassenhaus conjugacy (Isaacs Thm 3.12)
-- statement:
--   Mathlib provides existence of complements in the coprime case and conjugacy in the abelian case; this file fills the general-case conjugacy under a solvability hypothesis (Isaacs, *Finite Group Theory*, Thm 3.12). The main result `Subgroup.IsComplement'.exists_conj_of_coprime`: for a finite normal subgroup $N\trianglelefteq G$ with $\gcd(|N|,|G:N|)=1$ and $N$ or $G/N$ solvable, any two complements to $N$ are conjugate by an element of $N$. The proof is by strong induction on the group order.
--
--   Declarations include `IH` (the induction hypothesis form), `subgroupOfInclToN` and solvability transfer lemmas for `subgroupOf` and quotients, and lemmas on minimal normal subgroups of solvable groups being commutative and $p$-groups, plus `abelian_sz_conjugacy` and `isComplement'_conj`.
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Mathlib/SchurZassenhausConj.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Mathlib/SchurZassenhausConj.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow

open scoped Pointwise

open scoped IsMulCommutative

namespace Subgroup

variable {G : Type*} [Group G]

/-- If `K` complements `N ⊴ G` with coprime cardinalities, then the images of `N` and `K`
in `G/L` (any `L ⊴ G`) are also complements. (Isaacs Thm 3.12 proof, second paragraph.) -/
theorem IsComplement'.map_mk' {N K : Subgroup G} [Finite G] [N.Normal]
    (hK : IsComplement' N K) (h_cop : Nat.Coprime (Nat.card N) (Nat.card K))
    (L : Subgroup G) [L.Normal] :
    IsComplement' (N.map (QuotientGroup.mk' L)) (K.map (QuotientGroup.mk' L)) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · -- Disjoint via coprime cardinality.
    refine disjoint_of_coprime_natCard ?_
    refine h_cop.coprime_dvd_left ?_ |>.coprime_dvd_right ?_
    · exact Subgroup.card_map_dvd _ _
    · exact Subgroup.card_map_dvd _ _
  · -- mul = univ via mk' surjective + N ⊔ K = ⊤.
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg_top : g ∈ (N ⊔ K : Subgroup G) := by rw [hK.sup_eq_top]; trivial
    rw [mem_sup_of_normal_left] at hg_top
    obtain ⟨n, hn, k, hk, hnk⟩ := hg_top
    refine ⟨QuotientGroup.mk n, ?_, QuotientGroup.mk k, ?_, ?_⟩
    · exact mem_map.mpr ⟨n, hn, rfl⟩
    · exact mem_map.mpr ⟨k, hk, rfl⟩
    · change (QuotientGroup.mk n : G ⧸ L) * QuotientGroup.mk k = QuotientGroup.mk g
      rw [← QuotientGroup.mk_mul, hnk]

/-- If `K ≤ U ≤ G` and `K` complements `N ⊴ G`, then `K.subgroupOf U` complements
`N.subgroupOf U` in `U`. (Isaacs Thm 3.12 proof, first paragraph.) -/
theorem IsComplement'.subgroupOf_of_le {N K U : Subgroup G} [N.Normal]
    (hK : IsComplement' N K) (hKU : K ≤ U) :
    IsComplement' (N.subgroupOf U) (K.subgroupOf U) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · -- Disjoint (N.subgroupOf U) (K.subgroupOf U).
    rw [disjoint_iff]
    ext ⟨u, hu⟩
    simp only [mem_inf, mem_subgroupOf, mem_bot, Subtype.ext_iff, OneMemClass.coe_one]
    refine ⟨fun ⟨hN, hKmem⟩ => ?_, fun h => by simp [h]⟩
    have : u ∈ (N ⊓ K : Subgroup G) := ⟨hN, hKmem⟩
    rwa [hK.disjoint.eq_bot, mem_bot] at this
  · -- (N.subgroupOf U) * (K.subgroupOf U) = univ (in ↥U).
    rw [Set.eq_univ_iff_forall]
    rintro ⟨u, hu⟩
    -- Decompose u = n * k via N ⊔ K = ⊤ (N normal: use mem_sup_of_normal_left).
    have hu_top : (u : G) ∈ (N ⊔ K : Subgroup G) := by rw [hK.sup_eq_top]; trivial
    rw [mem_sup_of_normal_left] at hu_top
    obtain ⟨n, hn, k, hk, hnk⟩ := hu_top
    have hkU : k ∈ U := hKU hk
    have hnU : n ∈ U := by
      have heq : n = u * k⁻¹ := by rw [← hnk]; group
      rw [heq]
      exact U.mul_mem hu (U.inv_mem hkU)
    refine ⟨⟨n, hnU⟩, mem_subgroupOf.mpr hn, ⟨k, hkU⟩, mem_subgroupOf.mpr hk, ?_⟩
    ext; simpa using hnk

/-- **Centralizer descends through a complement** (mathcomp `subcent_sdprod`): if `K` and `H`
complement each other inside `N` (`IsComplement'` of `K.subgroupOf N` / `H.subgroupOf N`, with
`K ◁ N`), an element `a` normalizes both `K` and `H`, and `C_G(a) ≤ N`, then inside the centralizer
`C_G(a)` the subgroups `K ⊓ C_G(a)` and `H ⊓ C_G(a)` complement each other.

For `g ∈ C_G(a)`, factor `g = k·h` (`k ∈ K`, `h ∈ H`) via the `N`-complement; conjugating by `a`
gives `g = (a k a⁻¹)(a h a⁻¹)`, a second `K·H` factorization, so the uniqueness from `K ⊓ H = ⊥`
forces `a k a⁻¹ = k` and `a h a⁻¹ = h`, i.e. `k, h ∈ C_G(a)`.  This is the engine behind BG
Theorem 14.4(b) (`R ⋊ C_(M∩N)(x) = C(x)`), the complement conjunct of the FT signalizer `RData`. -/
theorem IsComplement'.inf_centralizer_of_normalizer {N K H : Subgroup G} {a : G}
    (hComp : IsComplement' (K.subgroupOf N) (H.subgroupOf N))
    (hKnorm : (K.subgroupOf N).Normal) (hKN : K ≤ N)
    (hCaN : Subgroup.centralizer ({a} : Set G) ≤ N)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haH : a ∈ Subgroup.normalizer (H : Set G)) :
    IsComplement'
      ((K ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (Subgroup.centralizer ({a} : Set G)))
      ((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf
        (Subgroup.centralizer ({a} : Set G))) := by
  have := hKnorm
  -- `K ⊓ H = ⊥` in `G`, from the `↥N`-disjointness of the complement.
  have hKHbot : Disjoint K H := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    rw [mem_inf] at hx
    have hxN : x ∈ N := hKN hx.1
    have hmem : (⟨x, hxN⟩ : N) ∈ (K.subgroupOf N) ⊓ (H.subgroupOf N) :=
      mem_inf.mpr ⟨mem_subgroupOf.mpr hx.1, mem_subgroupOf.mpr hx.2⟩
    rw [hComp.disjoint.eq_bot, mem_bot] at hmem
    rw [mem_bot]; exact Subtype.ext_iff.mp hmem
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · -- Disjoint inside the centralizer: `(K ⊓ Ca) ⊓ (H ⊓ Ca) ≤ K ⊓ H = ⊥`.
    rw [disjoint_iff, eq_bot_iff]
    rintro ⟨y, hyC⟩ hy
    rw [mem_inf, mem_subgroupOf, mem_subgroupOf] at hy
    have hyKH : (y : G) ∈ K ⊓ H := mem_inf.mpr ⟨(mem_inf.mp hy.1).1, (mem_inf.mp hy.2).1⟩
    rw [hKHbot.eq_bot, mem_bot] at hyKH
    rw [mem_bot]; exact Subtype.ext hyKH
  · -- Product fills the centralizer.
    rw [Set.eq_univ_iff_forall]
    rintro ⟨g, hgC⟩
    have hgN : g ∈ N := hCaN hgC
    -- factor `g = k'·h'` via the `N`-complement (`K.subgroupOf N` normal).
    have hgtop : (⟨g, hgN⟩ : N) ∈ (K.subgroupOf N) ⊔ (H.subgroupOf N) := by
      rw [hComp.sup_eq_top]; trivial
    rw [mem_sup_of_normal_left] at hgtop
    obtain ⟨k', hk', h', hh', hkh'⟩ := hgtop
    have hkK : (k' : G) ∈ K := mem_subgroupOf.mp hk'
    have hhH : (h' : G) ∈ H := mem_subgroupOf.mp hh'
    have hgkh : (k' : G) * (h' : G) = g := by
      have h2 := congrArg (N.subtype) hkh'
      rw [map_mul] at h2
      simpa using h2
    -- centralizer / normalizer facts.
    have hcomm_g : g * a = a * g := mem_centralizer_singleton_iff.mp hgC
    have hga : a * g * a⁻¹ = g := by rw [← hcomm_g]; group
    have hakK : a * (k' : G) * a⁻¹ ∈ K := (mem_normalizer_iff.mp haK _).mp hkK
    have hahH : a * (h' : G) * a⁻¹ ∈ H := (mem_normalizer_iff.mp haH _).mp hhH
    have hfact : a * (k' : G) * a⁻¹ * (a * (h' : G) * a⁻¹) = g := by
      have hrw : a * (k' : G) * a⁻¹ * (a * (h' : G) * a⁻¹)
          = a * ((k' : G) * (h' : G)) * a⁻¹ := by group
      rw [hrw, hgkh]; exact hga
    -- uniqueness of the factorization forces `a·(·)·a⁻¹` to fix both factors.
    have hstep : (k' : G) * ((h' : G) * (a * (h' : G) * a⁻¹)⁻¹) = a * (k' : G) * a⁻¹ := by
      rw [← mul_assoc, hgkh, ← hfact]; group
    have huH_eq : (k' : G)⁻¹ * (a * (k' : G) * a⁻¹) = (h' : G) * (a * (h' : G) * a⁻¹)⁻¹ := by
      rw [← hstep]; group
    have huK : (k' : G)⁻¹ * (a * (k' : G) * a⁻¹) ∈ K := K.mul_mem (K.inv_mem hkK) hakK
    have huH : (k' : G)⁻¹ * (a * (k' : G) * a⁻¹) ∈ H := by
      rw [huH_eq]; exact H.mul_mem hhH (H.inv_mem hahH)
    have hu1 : (k' : G)⁻¹ * (a * (k' : G) * a⁻¹) = 1 := by
      have : (k' : G)⁻¹ * (a * (k' : G) * a⁻¹) ∈ K ⊓ H := mem_inf.mpr ⟨huK, huH⟩
      rw [hKHbot.eq_bot, mem_bot] at this; exact this
    have hapa : a * (k' : G) * a⁻¹ = (k' : G) := (inv_mul_eq_one.mp hu1).symm
    have haqa : a * (h' : G) * a⁻¹ = (h' : G) := by
      have h := hfact; rw [hapa, ← hgkh] at h; exact mul_left_cancel h
    -- hence both factors centralize `a`.
    have hpCa : (k' : G) ∈ Subgroup.centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr (by conv_lhs => rw [← hapa]
                                            group)
    have hqCa : (h' : G) ∈ Subgroup.centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr (by conv_lhs => rw [← haqa]
                                            group)
    refine ⟨⟨(k' : G), hpCa⟩, ?_, ⟨(h' : G), hqCa⟩, ?_, ?_⟩
    · exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hkK, hpCa⟩)
    · exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hhH, hqCa⟩)
    · ext; simpa using hgkh

universe u

namespace SchurZassenhausConj

/-- Induction hypothesis form: SZ conjugacy for groups of strictly smaller cardinality. -/
private def IH (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (G' : Type u) [Group G'] [Finite G'],
    Nat.card G' < Nat.card G → ∀ {N' : Subgroup G'} [N'.Normal],
      Nat.Coprime (Nat.card N') N'.index →
      (Group.IsSolvable N' ∨ Group.IsSolvable (G' ⧸ N')) →
      ∀ {K K' : Subgroup G'}, IsComplement' N' K → IsComplement' N' K' →
      ∃ n : G', n ∈ N' ∧ K.map (MulAut.conj n).toMonoidHom = K'

variable {G : Type u} [Group G]

/-- Subgroup ⊆ inclusion of subgroupOf to N: `↥(N.subgroupOf U) →* ↥N`. -/
private def subgroupOfInclToN (N U : Subgroup G) : ↥(N.subgroupOf U) →* ↥N where
  toFun x := ⟨x.val.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem subgroupOfInclToN_injective (N U : Subgroup G) :
    Function.Injective (subgroupOfInclToN N U) := by
  intro x y h
  simp only [subgroupOfInclToN, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.mk.injEq] at h
  exact Subtype.ext (Subtype.ext h)

/-- `Group.IsSolvable N ⇒ Group.IsSolvable (N.subgroupOf U)`. -/
instance subgroupOf_isSolvable_of_isSolvable (N U : Subgroup G) [Group.IsSolvable N] :
    Group.IsSolvable (N.subgroupOf U) :=
  Group.isSolvable_of_isSolvable_injective (subgroupOfInclToN_injective N U)

set_option backward.isDefEq.respectTransparency false in
/-- `Group.IsSolvable (G ⧸ N) ⇒ Group.IsSolvable (U ⧸ N.subgroupOf U)` for any `U ≤ G`.
Proof: `U ⧸ N.subgroupOf U ≃ (U ⊔ N) ⧸ N.subgroupOf (U ⊔ N)` (second iso theorem), and
the latter embeds into `G ⧸ N` via `QuotientGroup.lift`. -/
instance quotient_subgroupOf_isSolvable_of_quotient {U N : Subgroup G} [N.Normal]
    [Group.IsSolvable (G ⧸ N)] : Group.IsSolvable (U ⧸ N.subgroupOf U) := by
  -- Step 1: define φ : (U ⊔ N) ⧸ N.subgroupOf (U ⊔ N) →* G ⧸ N via lift.
  let φ : ((U ⊔ N : Subgroup G) ⧸ N.subgroupOf (U ⊔ N)) →* G ⧸ N :=
    QuotientGroup.lift (N.subgroupOf (U ⊔ N))
      ((QuotientGroup.mk' N).comp (U ⊔ N).subtype)
      (fun x hx => by
        change (QuotientGroup.mk x.val : G ⧸ N) = 1
        exact (QuotientGroup.eq_one_iff _).mpr hx)
  have hφ_inj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x⟩ hx
    rw [MonoidHom.mem_ker] at hx
    change (QuotientGroup.mk x.val : G ⧸ N) = 1 at hx
    rw [QuotientGroup.eq_one_iff] at hx
    -- ⟦x⟧ = 1 in (U ⊔ N) ⧸ N.subgroupOf (U ⊔ N): x ∈ N.subgroupOf (U ⊔ N).
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff _).mpr hx
  have hUN : Group.IsSolvable ((U ⊔ N : Subgroup G) ⧸ N.subgroupOf (U ⊔ N)) :=
    Group.isSolvable_of_isSolvable_injective hφ_inj
  -- Step 2: Transfer back via second iso (direction U ⧸ ... → (U ⊔ N) ⧸ ...).
  let e := QuotientGroup.quotientInfEquivProdNormalQuotient U N
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

variable [Finite G]

variable {N : Subgroup G} [N.Normal]

omit [Finite G] in
/-- `(K.subgroupOf U).map U.subtype = K` when `K ≤ U`. -/
private theorem subgroupOf_map_subtype_eq {U K : Subgroup G} (hKU : K ≤ U) :
    (K.subgroupOf U).map U.subtype = K := by
  rw [subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hKU]

omit [Finite G] in
/-- Conjugation by `n' : ↥U` in `↥U` corresponds via `U.subtype`
to conjugation by `n'.val` in `G`. -/
private theorem subtype_comp_conj_eq {U : Subgroup G} (n' : ↥U) :
    U.subtype.comp ((MulAut.conj n').toMonoidHom) =
      ((MulAut.conj (n'.val : G)).toMonoidHom).comp U.subtype := by
  ext ⟨x, hx⟩
  rfl

omit [Finite G] in
/-- Pushing `((K.subgroupOf U).map (conj n')).map U.subtype` equals `K.map (conj n'.val)`. -/
private theorem map_subtype_conj_subgroupOf {U : Subgroup G} (n' : ↥U) (K : Subgroup G)
    (hKU : K ≤ U) :
    ((K.subgroupOf U).map (MulAut.conj n').toMonoidHom).map U.subtype =
      K.map (MulAut.conj (n'.val : G)).toMonoidHom := by
  rw [Subgroup.map_map, subtype_comp_conj_eq, ← Subgroup.map_map, subgroupOf_map_subtype_eq hKU]

/-- **Step 1 (Restriction)**: if `K, K' ≤ U < ⊤`, the inductive hypothesis applied to `↥U`
gives an element `n ∈ N` conjugating `K` to `K'`. -/
private theorem step_restriction
    (h1 : Nat.Coprime (Nat.card N) N.index)
    (hSolv : Group.IsSolvable N ∨ Group.IsSolvable (G ⧸ N))
    (ih : IH G)
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K')
    {U : Subgroup G} (hKU : K ≤ U) (hK'U : K' ≤ U) (hU_lt : U ≠ ⊤) :
    ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' := by
  -- |↥U| < |G| via Lagrange + index > 1.
  have hcard_lt : Nat.card ↥U < Nat.card G := by
    have h_idx : 1 < U.index := Subgroup.one_lt_index_of_ne_top hU_lt
    calc Nat.card ↥U = Nat.card ↥U * 1 := (mul_one _).symm
      _ < Nat.card ↥U * U.index := (Nat.mul_lt_mul_left Nat.card_pos).mpr h_idx
      _ = Nat.card G := Subgroup.card_mul_index U
  -- Coprime |N.subgroupOf U| (N.subgroupOf U).index.
  have h_card_dvd : Nat.card (N.subgroupOf U) ∣ Nat.card N :=
    Subgroup.card_comap_dvd_of_injective N U.subtype U.subtype_injective
  have h_index_dvd : (N.subgroupOf U).index ∣ N.index :=
    Subgroup.relIndex_dvd_index_of_normal N U
  have h_cop : Nat.Coprime (Nat.card (N.subgroupOf U)) (N.subgroupOf U).index :=
    (h1.coprime_dvd_left h_card_dvd).coprime_dvd_right h_index_dvd
  -- Solvability transfer.
  have h_solv : Group.IsSolvable (N.subgroupOf U) ∨ Group.IsSolvable (↥U ⧸ N.subgroupOf U) := by
    rcases hSolv with h | h
    · left; have := h; infer_instance
    · right; have := h; infer_instance
  -- Helper A: restrict complements to ↥U.
  have hK_U : IsComplement' (N.subgroupOf U) (K.subgroupOf U) := hK.subgroupOf_of_le hKU
  have hK'_U : IsComplement' (N.subgroupOf U) (K'.subgroupOf U) := hK'.subgroupOf_of_le hK'U
  -- Apply IH.
  obtain ⟨n', hn'_mem, hconj⟩ := ih ↥U hcard_lt h_cop h_solv hK_U hK'_U
  -- Lift n' to n'.val ∈ G (which is ∈ N via mem_subgroupOf).
  refine ⟨n'.val, hn'_mem, ?_⟩
  -- Push hconj via U.subtype.
  have hpush : ((K.subgroupOf U).map (MulAut.conj n').toMonoidHom).map U.subtype =
               (K'.subgroupOf U).map U.subtype := by rw [hconj]
  rw [map_subtype_conj_subgroupOf n' K hKU, subgroupOf_map_subtype_eq hK'U] at hpush
  exact hpush

omit [Finite G] in
/-- Conjugation `mk'_comp_conj_eq`: in `G ⧸ L`, conjugation by `mk' g` agrees with `mk'` applied
to conjugation by `g`. Used in the lift-back step of `step_factor`. -/
private theorem mk'_comp_conj_eq {L : Subgroup G} [L.Normal] (g : G) :
    (QuotientGroup.mk' L).comp (MulAut.conj g).toMonoidHom =
      ((MulAut.conj (QuotientGroup.mk g : G ⧸ L)).toMonoidHom).comp (QuotientGroup.mk' L) := by
  ext x
  change (QuotientGroup.mk (g * x * g⁻¹) : G ⧸ L) =
       (QuotientGroup.mk g) * (QuotientGroup.mk x) * (QuotientGroup.mk g)⁻¹
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

/-- **Step 2 (Factor)**: for nontrivial `L ⊴ G`, IH on `G ⧸ L` gives `g ∈ N` with
`(K^g) ⊔ L = K' ⊔ L`. -/
private theorem step_factor
    (h1 : Nat.Coprime (Nat.card N) N.index)
    (hSolv : Group.IsSolvable N ∨ Group.IsSolvable (G ⧸ N))
    (ih : IH G)
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K')
    {L : Subgroup G} [L.Normal] (hL_ne_bot : L ≠ ⊥) :
    ∃ g : G, g ∈ N ∧ (K.map (MulAut.conj g).toMonoidHom) ⊔ L = K' ⊔ L := by
  -- |G/L| < |G|.
  have hcard_lt := Subgroup.card_quotient_lt_of_ne_bot hL_ne_bot
  -- Coprime cardinalities for Helper B.
  have h_NK_cop : Nat.Coprime (Nat.card N) (Nat.card K) := by
    rw [show Nat.card K = N.index from hK.symm.index_eq_card.symm]
    exact h1
  have h_NK'_cop : Nat.Coprime (Nat.card N) (Nat.card K') := by
    rw [show Nat.card K' = N.index from hK'.symm.index_eq_card.symm]
    exact h1
  -- Helper B: complements in G/L.
  have hK_q : IsComplement' (N.map (QuotientGroup.mk' L)) (K.map (QuotientGroup.mk' L)) :=
    hK.map_mk' h_NK_cop L
  have hK'_q : IsComplement' (N.map (QuotientGroup.mk' L)) (K'.map (QuotientGroup.mk' L)) :=
    hK'.map_mk' h_NK'_cop L
  -- Coprime in G/L.
  have h_cop_q : Nat.Coprime (Nat.card (N.map (QuotientGroup.mk' L)))
                  (N.map (QuotientGroup.mk' L)).index :=
    (h1.coprime_dvd_left (Subgroup.card_map_dvd _ _)).coprime_dvd_right
      (N.index_map_dvd (QuotientGroup.mk'_surjective L))
  -- Solvability transfer to G/L.
  have h_solv_q : Group.IsSolvable (N.map (QuotientGroup.mk' L)) ∨
                   Group.IsSolvable ((G ⧸ L) ⧸ (N.map (QuotientGroup.mk' L))) := by
    rcases hSolv with h | h
    · left
      have : Group.IsSolvable N := h
      -- N → N.map mk' is surjective.
      let f : N →* ↥(N.map (QuotientGroup.mk' L)) :=
        ((QuotientGroup.mk' L).comp N.subtype).codRestrict _ (fun x =>
          Subgroup.mem_map.mpr ⟨x.val, x.property, rfl⟩)
      have hf_surj : Function.Surjective f := by
        rintro ⟨y, hy⟩
        obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨n, hn⟩, by ext; exact hny⟩
      exact Group.isSolvable_of_surjective hf_surj
    · right
      have : Group.IsSolvable (G ⧸ N) := h
      -- (G ⧸ L) ⧸ (N.map mk') is quotient of (G ⧸ N) via lift.
      -- φ : G ⧸ N →* (G ⧸ L) ⧸ (N.map mk') sending ⟦g⟧_N ↦ ⟦⟦g⟧_L⟧_{N.map mk'}.
      let φ : G ⧸ N →* (G ⧸ L) ⧸ (N.map (QuotientGroup.mk' L)) :=
        QuotientGroup.lift N
          ((QuotientGroup.mk' (N.map (QuotientGroup.mk' L))).comp (QuotientGroup.mk' L))
          (fun n hn => by
            change (QuotientGroup.mk (QuotientGroup.mk n : G ⧸ L) :
                  (G ⧸ L) ⧸ (N.map (QuotientGroup.mk' L))) = 1
            rw [QuotientGroup.eq_one_iff]
            exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
      have hφ_surj : Function.Surjective φ := by
        rintro ⟨⟨g⟩⟩
        exact ⟨QuotientGroup.mk g, rfl⟩
      exact Group.isSolvable_of_surjective hφ_surj
  -- Apply IH on G/L.
  obtain ⟨x, hx_mem, hx_conj⟩ := ih (G ⧸ L) hcard_lt h_cop_q h_solv_q hK_q hK'_q
  -- Lift x to g ∈ N.
  obtain ⟨g, hg_N, hg_eq⟩ := Subgroup.mem_map.mp hx_mem
  refine ⟨g, hg_N, ?_⟩
  -- Translate (K.map (conj g)).map mk' = K'.map mk' to G level via map_eq_map_iff.
  have key : (K.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' L) =
             K'.map (QuotientGroup.mk' L) := by
    rw [Subgroup.map_map, mk'_comp_conj_eq, ← Subgroup.map_map]
    rw [show (QuotientGroup.mk g : G ⧸ L) = x from hg_eq]
    exact hx_conj
  have heq := (Subgroup.map_eq_map_iff (f := QuotientGroup.mk' L)).mp key
  rwa [QuotientGroup.ker_mk'] at heq

omit [Finite G] in
/-- Isaacs Lem 3.11: minimal `G`-normal of solvable group is commutative.
mathlib v4.29.1 にこの形の lemma がないため自前. -/
private theorem minimal_normal_isCommutative_of_solvable
    {N L : Subgroup G} [N.Normal] [L.Normal] (hL_le : L ≤ N) (hL_ne : L ≠ ⊥)
    (hL_min : ∀ L' : Subgroup G, L'.Normal → L' ≤ L → L' ≠ ⊥ → L' = L)
    (hN_solv : Group.IsSolvable N) : IsMulCommutative L := by
  have hN_solv' : Group.IsSolvable N := hN_solv
  -- [L, L] ≤ L, [L, L] is G-normal.
  have h_LL_le : ⁅L, L⁆ ≤ L := Subgroup.commutator_le_self L
  have h_LL_normal : (⁅L, L⁆ : Subgroup G).Normal := Subgroup.commutator_normal L L
  -- By minimality, [L, L] = ⊥ or [L, L] = L.
  by_cases h : (⁅L, L⁆ : Subgroup G) = ⊥
  · -- [L, L] = ⊥ ⇒ L is commutative in G ⇒ IsMulCommutative L.
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha_cent : (a : G) ∈ Subgroup.centralizer L := h a.property
    rw [Subgroup.mem_centralizer_iff] at ha_cent
    apply Subtype.ext
    exact (ha_cent b.val b.property).symm
  · -- [L, L] = L, contradiction with solvability of L (subgroup of solvable N).
    exfalso
    have h_eq : (⁅L, L⁆ : Subgroup G) = L := hL_min _ h_LL_normal h_LL_le h
    -- L ≃* L.subgroupOf N, the latter is solvable, hence L solvable.
    have hL_solv : Group.IsSolvable L := by
      have : Group.IsSolvable (L.subgroupOf N) := inferInstance
      let e := (subgroupOfEquivOfLe hL_le).symm
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    -- ⁅⊤_L, ⊤_L⁆.map L.subtype = ⁅L, L⁆.
    have h_comm_map : (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L).map L.subtype = ⁅L, L⁆ := by
      rw [Subgroup.map_commutator, ← L.subtype.range_eq_map, Subgroup.range_subtype]
    -- ⁅L, L⁆ = L = L.subtype.range.
    have h_map_range : (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L).map L.subtype = L.subtype.range := by
      rw [h_comm_map, h_eq, Subgroup.range_subtype]
    -- ⁅⊤_L, ⊤_L⁆ = ⊤ in ↥L (via map_eq_range_iff).
    have h_comm_top : (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L) = ⊤ := by
      have := Subgroup.map_eq_range_iff.mp h_map_range
      rw [show L.subtype.ker = ⊥ from L.ker_subtype] at this
      exact codisjoint_bot.mp this
    -- By induction, derivedSeries L n = ⊤ for all n.
    have h_ds_top : ∀ n, derivedSeries L n = ⊤ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [derivedSeries_succ]; rw [ih]; exact h_comm_top
    -- L is nontrivial (since L ≠ ⊥ in G).
    have : Nontrivial ↥L := (Subgroup.bot_or_nontrivial L).resolve_left hL_ne
    -- L solvable: derivedSeries L n = ⊥ for some n.
    obtain ⟨n, hn⟩ := hL_solv.solvable
    -- Contradiction: (⊤ : Subgroup ↥L) = ⊥.
    rw [h_ds_top] at hn
    exact bot_lt_top.ne' hn

omit [Finite G] in
/-- **Isaacs Lemma 3.11** (`p`-group part): for `L` a minimal normal subgroup of a
finite group with `L` solvable, `L` is a `p`-group for some prime `p`.
The commutativity follows from `minimal_normal_isCommutative_of_solvable`; the
`p`-group structure follows from the `p`-primary component being characteristic in `L`
(and hence normal in the ambient group), then minimality forces the `p`-primary = `L`. -/
private theorem minimal_normal_isPGroup_of_solvable
    {L : Subgroup G} [Finite G] [L.Normal] [Group.IsSolvable L]
    (hL_ne : L ≠ ⊥)
    (hL_min : ∀ L' : Subgroup G, L'.Normal → L' ≤ L → L' ≠ ⊥ → L' = L) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p L := by
  -- L commutative.
  have hL_comm : IsMulCommutative L :=
    minimal_normal_isCommutative_of_solvable (N := L) le_rfl hL_ne hL_min inferInstance
  have hL_nontriv : Nontrivial L := (Subgroup.bot_or_nontrivial L).resolve_left hL_ne
  have hL_card_pos : 1 < Nat.card L := Finite.one_lt_card
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hL_card_pos.ne'
  refine ⟨p, hp_prime, ?_⟩
  have : Fact p.Prime := ⟨hp_prime⟩
  -- T := p-torsion of L as a Subgroup of ↥L.
  let T : Subgroup ↥L :=
    { carrier := {x | x ^ p = 1}
      one_mem' := one_pow p
      mul_mem' := by
        intro a b ha hb
        change (a * b) ^ p = 1
        change a ^ p = 1 at ha
        change b ^ p = 1 at hb
        rw [mul_pow, ha, hb, one_mul]
      inv_mem' := by
        intro a ha
        change a⁻¹ ^ p = 1
        change a ^ p = 1 at ha
        rw [inv_pow, ha, inv_one] }
  -- T characteristic in ↥L (image of p-torsion under any automorphism is p-torsion).
  have hT_char : T.Characteristic := by
    rw [Subgroup.characteristic_iff_le_comap]
    intro φ x hx
    rw [Subgroup.mem_comap]
    change (φ x) ^ p = 1
    change x ^ p = 1 at hx
    rw [← map_pow, hx, map_one]
  -- T ≠ ⊥ by Cauchy.
  obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) p hp_dvd
  have hx_pow : x ^ p = 1 := by rw [← hx_ord]; exact pow_orderOf_eq_one x
  have hx_ne_one : x ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at hx_ord
    exact hp_prime.ne_one hx_ord.symm
  have hT_ne_bot : T ≠ ⊥ := by
    intro hbot
    have hx_T : x ∈ T := hx_pow
    rw [hbot, Subgroup.mem_bot] at hx_T
    exact hx_ne_one hx_T
  -- T.map L.subtype ⊴ G (characteristic in normal), ≤ L, ≠ ⊥.
  have hTL_normal : (T.map L.subtype).Normal := inferInstance
  have hTL_le : T.map L.subtype ≤ L := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hTL_ne_bot : T.map L.subtype ≠ ⊥ := by
    intro hbot
    have hT_eq : T = ⊥ := by
      have h : T.map L.subtype = (⊥ : Subgroup ↥L).map L.subtype := by
        rw [hbot, Subgroup.map_bot]
      exact Subgroup.map_injective L.subtype_injective h
    exact hT_ne_bot hT_eq
  -- Minimality of L: T.map L.subtype = L.
  have hTL_eq : T.map L.subtype = L := hL_min _ hTL_normal hTL_le hTL_ne_bot
  -- Hence T = ⊤ in ↥L (via map_injective).
  have hT_top : T = ⊤ := by
    have h_top_map : (⊤ : Subgroup ↥L).map L.subtype = L := by
      rw [← L.subtype.range_eq_map, Subgroup.range_subtype]
    have hh : T.map L.subtype = (⊤ : Subgroup ↥L).map L.subtype := by
      rw [h_top_map, hTL_eq]
    exact Subgroup.map_injective L.subtype_injective hh
  -- Each x : ↥L satisfies x^p = 1, hence x^(p^1) = 1.
  intro x
  refine ⟨1, ?_⟩
  have hxT : x ∈ T := by rw [hT_top]; trivial
  change x ^ p = 1 at hxT
  rw [pow_one]
  exact hxT

omit [Finite G] [N.Normal] in
/-- Helper: for `K` complement of abelian normal `N`, the stabilizer (under the
`G`-action on `N.QuotientDiff`) of the equivalence class of `K`'s transversal equals `K`.

The result is stated for an explicit `αK : N.QuotientDiff` plus an equation `αK = ⟦⟨K, _⟩⟧`,
to avoid Lean's instance-synthesis difficulty with embedded `Quotient.mk''`-expressions
of type `N.QuotientDiff` (the def is not reducible, so the `MulAction G _` instance does
not match against the unfolded `Quotient {...}` form).

Proof: (⊆) because for `k ∈ K`, `op k⁻¹ • (K : Set G) = K` as sets, so the LeftTransversal
is unchanged in the QuotientDiff; (⊇) by cardinality (both `K` and the stabilizer are
complements of `N` of cardinality `N.index`). -/
private theorem stabilizer_quotientDiff_eq_self {K : Subgroup G} [N.Normal]
    [IsMulCommutative N] [Finite G]
    (hN : Nat.Coprime (Nat.card N) N.index) (hK : IsComplement' N K)
    (αK : N.QuotientDiff)
    (hαK : αK =
      (Quotient.mk'' (⟨(K : Set G), hK.symm⟩ : N.LeftTransversal) : N.QuotientDiff)) :
    MulAction.stabilizer G αK = K := by
  -- Step 1: K ≤ stabilizer αK.
  have hK_le : K ≤ MulAction.stabilizer G αK := by
    intro k hkK
    rw [MulAction.mem_stabilizer_iff, hαK]
    -- k • ⟦⟨K, _⟩⟧ = ⟦⟨K, _⟩⟧ via op k⁻¹ • (K : Set G) = K as a set.
    have h_set : (MulOpposite.op (k⁻¹ : G)) • (K : Set G) = (K : Set G) := by
      ext x
      refine ⟨?_, fun hxK => ⟨x * k, K.mul_mem hxK hkK, ?_⟩⟩
      · rintro ⟨y, hyK, hxy⟩
        -- hxy : (fun z ↦ MulOpposite.op k⁻¹ • z) y = x, which is y * k⁻¹ = x.
        change (y * k⁻¹ : G) = x at hxy
        rw [← hxy]
        exact K.mul_mem hyK (K.inv_mem hkK)
      · -- Goal: (fun z ↦ MulOpposite.op k⁻¹ • z) (x * k) = x, i.e., (x * k) * k⁻¹ = x.
        change ((x * k) * k⁻¹ : G) = x
        group
    have h_trans :
        (MulOpposite.op (k⁻¹ : G)) • (⟨(K : Set G), hK.symm⟩ : N.LeftTransversal)
          = ⟨(K : Set G), hK.symm⟩ := Subtype.ext h_set
    exact congrArg Quotient.mk'' h_trans
  -- Step 2: cardinality equality forces stabilizer = K.
  have hStab_compl : IsComplement' N (MulAction.stabilizer G αK) :=
    isComplement'_stabilizer_of_coprime hN
  have h_card_K : Nat.card K = N.index := hK.symm.index_eq_card.symm
  have h_card_stab : Nat.card (MulAction.stabilizer G αK) = N.index :=
    hStab_compl.symm.index_eq_card.symm
  have h_eq : Nat.card (MulAction.stabilizer G αK) = Nat.card K := by
    rw [h_card_stab, ← h_card_K]
  exact (Subgroup.eq_of_le_of_card_ge hK_le h_eq.le).symm

omit [Finite G] in
/-- **Abelian SZ conjugacy** (Isaacs Thm 3.5 / part of Thm 3.12): for `N` abelian normal
in `G` with coprime order/index, any two complements are conjugate by an element of `N`.

Proof: realize `K, K'` as `MulAction.stabilizer G αK`, `MulAction.stabilizer G αK'` for
`αK, αK' ∈ N.QuotientDiff` (via `stabilizer_quotientDiff_eq_self`). Apply mathlib's
`Subgroup.exists_smul_eq` to get `⟨n, hn⟩ • αK = αK'`, and conclude via
`MulAction.stabilizer_smul_eq_stabilizer_map_conj`. -/
private theorem abelian_sz_conjugacy
    {N : Subgroup G} [N.Normal] [Finite G] [IsMulCommutative N]
    (hN : Nat.Coprime (Nat.card N) N.index)
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K') :
    ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' := by
  let αK : N.QuotientDiff :=
    Quotient.mk'' (⟨(K : Set G), hK.symm⟩ : N.LeftTransversal)
  let αK' : N.QuotientDiff :=
    Quotient.mk'' (⟨(K' : Set G), hK'.symm⟩ : N.LeftTransversal)
  have hαK : αK = (Quotient.mk'' (⟨(K : Set G), hK.symm⟩ : N.LeftTransversal)
      : N.QuotientDiff) := rfl
  have hαK' : αK' = (Quotient.mk'' (⟨(K' : Set G), hK'.symm⟩ : N.LeftTransversal)
      : N.QuotientDiff) := rfl
  -- Apply mathlib exists_smul_eq.
  obtain ⟨⟨n, hn⟩, hsmul⟩ := Subgroup.exists_smul_eq hN αK αK'
  refine ⟨n, hn, ?_⟩
  -- hsmul : (⟨n, hn⟩ : ↥N) • αK = αK'.
  -- Subgroup-induced action coincides with G-action on Subtype.val.
  have hsmul_G : (n : G) • αK = αK' := hsmul
  -- Apply stabilizer_smul_eq_stabilizer_map_conj.
  have hstab :
      MulAction.stabilizer G ((n : G) • αK)
        = (MulAction.stabilizer G αK).map (MulAut.conj n).toMonoidHom :=
    MulAction.stabilizer_smul_eq_stabilizer_map_conj n αK
  rw [hsmul_G] at hstab
  -- Now hstab : stabilizer αK' = (stabilizer αK).map (conj n).
  rw [stabilizer_quotientDiff_eq_self hN hK' αK' hαK',
      stabilizer_quotientDiff_eq_self hN hK αK hαK] at hstab
  exact hstab.symm

/-- Existence of a minimal `G`-normal subgroup contained in nontrivial `N`.

(Public: also used by BG Theorem 15.2's step 3, applied to the quotient `N_M(Q₀)/Q₀` to obtain the
minimal normal `Q₁/Q₀` — the same quotient-instantiation pattern as `step_caseB` below.) -/
theorem exists_minimal_normal_le {N : Subgroup G} (hN_normal : N.Normal) (hN : N ≠ ⊥) :
    ∃ L : Subgroup G, L.Normal ∧ L ≤ N ∧ L ≠ ⊥ ∧
      ∀ L' : Subgroup G, L'.Normal → L' ≤ L → L' ≠ ⊥ → L' = L := by
  let S : Set (Subgroup G) := {L | L.Normal ∧ L ≤ N ∧ L ≠ ⊥}
  have hS_fin : S.Finite := Set.toFinite S
  have hS_ne : S.Nonempty := ⟨N, hN_normal, le_refl N, hN⟩
  obtain ⟨L, hL_min⟩ := hS_fin.exists_minimal hS_ne
  -- hL_min : Minimal (· ∈ S) L
  obtain ⟨⟨hL_normal, hL_le, hL_ne⟩, hL_minimal⟩ := hL_min
  refine ⟨L, hL_normal, hL_le, hL_ne, ?_⟩
  intro L' hL'_normal hL'_le hL'_ne
  have hL'_mem : L' ∈ S := ⟨hL'_normal, hL'_le.trans hL_le, hL'_ne⟩
  -- hL_minimal : ∀ b ∈ S, b ≤ L → L ≤ b
  exact le_antisymm hL'_le (hL_minimal hL'_mem hL'_le)

/-- **Case A (N solvable)**: full SZ conjugacy when `N` is solvable.

Strategy: take minimal normal `L ⊆ N` in `G`, which is abelian (Isaacs Lem 3.11). Apply
step_factor with `L` to get `g ∈ N` with `K^g · L = K' · L =: HL`. If `HL < G`, apply
step_restriction. If `HL = G`, then `L = N` (cardinality), so `N` is abelian and we use
mathlib `Subgroup.exists_smul_eq` (abelian SZ conjugacy). -/
private theorem step_caseA
    (h1 : Nat.Coprime (Nat.card N) N.index)
    (hN_solv : Group.IsSolvable N)
    (ih : IH G)
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K') :
    ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' := by
  -- Trivial case: N = ⊥ ⇒ K = K' = ⊤.
  by_cases hN_bot : N = ⊥
  · subst hN_bot
    have hK_top : K = ⊤ := by
      have := hK.sup_eq_top
      rwa [bot_sup_eq] at this
    have hK'_top : K' = ⊤ := by
      have := hK'.sup_eq_top
      rwa [bot_sup_eq] at this
    refine ⟨1, (⊥ : Subgroup G).one_mem, ?_⟩
    rw [hK_top, hK'_top]
    ext x
    simp
  -- Nontrivial case: take minimal normal L ⊆ N, abelian, then case split on K^g ⊔ L.
  have hN_normal_inst : N.Normal := inferInstance
  obtain ⟨L, hL_normal, hL_le, hL_ne_bot, hL_min⟩ :=
    exists_minimal_normal_le hN_normal_inst hN_bot
  have : L.Normal := hL_normal
  have hL_comm : IsMulCommutative L :=
    minimal_normal_isCommutative_of_solvable hL_le hL_ne_bot hL_min hN_solv
  -- Apply step_factor with L.
  obtain ⟨g_f, hg_f_N, h_factor⟩ :=
    step_factor h1 (Or.inl hN_solv) ih hK hK' hL_ne_bot
  -- h_factor : (K.map (conj g_f)) ⊔ L = K' ⊔ L
  -- Need: IsComplement' N K^g (K conjugated by g_f ∈ N, N normal preserves complement).
  have hK_g_compl : IsComplement' N (K.map (MulAut.conj g_f).toMonoidHom) := by
    apply isComplement'_of_disjoint_and_mul_eq_univ
    · -- Disjoint: N ⊓ K^g_f = ⊥.
      rw [disjoint_iff]
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_bot, Subgroup.mem_map,
                 MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine ⟨fun ⟨hxN, k, hkK, hkx⟩ => ?_, fun h => ?_⟩
      · -- k = g_f⁻¹ * x * g_f. Both x ∈ N and g_f ∈ N ⇒ k ∈ N. K ⊓ N = ⊥ ⇒ k = 1 ⇒ x = 1.
        have hk_eq : k = g_f⁻¹ * x * g_f := by rw [← hkx]; group
        have hkN : k ∈ N := by
          rw [hk_eq]
          exact N.mul_mem (N.mul_mem (N.inv_mem hg_f_N) hxN) hg_f_N
        have hk_inter : k ∈ N ⊓ K := ⟨hkN, hkK⟩
        rw [hK.disjoint.eq_bot, Subgroup.mem_bot] at hk_inter
        rw [hk_inter, mul_one, mul_inv_cancel] at hkx
        exact hkx.symm
      · subst h
        exact ⟨N.one_mem, 1, K.one_mem, by simp⟩
    · -- (N : Set G) * (K^g_f : Set G) = univ.
      rw [Set.eq_univ_iff_forall]
      intro x
      -- Decompose g_f⁻¹ x g_f = n' * k' in N + K, then conjugate back.
      have h_conj_in_sup : g_f⁻¹ * x * g_f ∈ (N ⊔ K : Subgroup G) := by
        rw [hK.sup_eq_top]; trivial
      rw [mem_sup_of_normal_left] at h_conj_in_sup
      obtain ⟨n', hn'_N, k', hk'_K, hnk'⟩ := h_conj_in_sup
      have hN_normal_inst' : N.Normal := inferInstance
      refine ⟨g_f * n' * g_f⁻¹, hN_normal_inst'.conj_mem n' hn'_N g_f,
              g_f * k' * g_f⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨k', hk'_K, rfl⟩
      · -- (g_f n' g_f⁻¹) * (g_f k' g_f⁻¹) = g_f (n' k') g_f⁻¹ = g_f (g_f⁻¹ x g_f) g_f⁻¹ = x.
        change g_f * n' * g_f⁻¹ * (g_f * k' * g_f⁻¹) = x
        have : g_f * n' * g_f⁻¹ * (g_f * k' * g_f⁻¹) = g_f * (n' * k') * g_f⁻¹ := by group
        rw [this, hnk']
        group
  -- Case split on K^g ⊔ L = ⊤.
  by_cases hH_top : (K.map (MulAut.conj g_f).toMonoidHom) ⊔ L = ⊤
  · -- N = L (cardinality), N abelian, abelian SZ conjugacy.
    -- K^g_f ⊓ L ⊆ K^g_f ⊓ N = ⊥.
    have h_inter_bot : (K.map (MulAut.conj g_f).toMonoidHom) ⊓ L = ⊥ := by
      apply le_bot_iff.mp
      have h_KgN : (K.map (MulAut.conj g_f).toMonoidHom) ⊓ N = ⊥ := by
        rw [inf_comm]; exact hK_g_compl.disjoint.eq_bot
      calc (K.map (MulAut.conj g_f).toMonoidHom) ⊓ L
          ≤ (K.map (MulAut.conj g_f).toMonoidHom) ⊓ N := inf_le_inf_left _ hL_le
        _ = ⊥ := h_KgN
    -- |K^g_f| * |L| = |G| (from disjoint + sup_eq_top via IsComplement').
    have hKgL_compl : IsComplement' (K.map (MulAut.conj g_f).toMonoidHom) L := by
      apply isComplement'_of_disjoint_and_mul_eq_univ
      · rw [disjoint_iff]; exact h_inter_bot
      · -- Set product = univ via mem_sup_of_normal_right (L normal).
        rw [Set.eq_univ_iff_forall]
        intro x
        have hx_top : x ∈ (K.map (MulAut.conj g_f).toMonoidHom ⊔ L : Subgroup G) := by
          rw [hH_top]; trivial
        rw [mem_sup_of_normal_right] at hx_top
        obtain ⟨k, hk, l, hl, hkl⟩ := hx_top
        exact ⟨k, hk, l, hl, hkl⟩
    -- |L| = |N| from |K^g_f| * |L| = |G| = |N| * |K^g_f|.
    have h_card_L_eq_N : Nat.card ↥L = Nat.card N := by
      have h1' : Nat.card (K.map (MulAut.conj g_f).toMonoidHom) * Nat.card ↥L = Nat.card G :=
        hKgL_compl.card_mul_card
      have h2' : Nat.card ↥N * Nat.card (K.map (MulAut.conj g_f).toMonoidHom) = Nat.card G :=
        hK_g_compl.card_mul_card
      have h_swap : Nat.card (K.map (MulAut.conj g_f).toMonoidHom) * Nat.card ↥N = Nat.card G := by
        rw [mul_comm]; exact h2'
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1'.trans h_swap.symm)
    -- L = N (from L ≤ N + |L| = |N|).
    have hL_eq_N : L = N :=
      Subgroup.eq_of_le_of_card_ge hL_le h_card_L_eq_N.ge
    -- Now N = L abelian. Use abelian SZ conjugacy.
    subst hL_eq_N
    -- hL_comm : IsMulCommutative L = IsMulCommutative N. Original hK, hK' still in scope.
    exact abelian_sz_conjugacy h1 hK hK'
  · -- H = K^g ⊔ L is proper, apply step_restriction.
    have hKgU : K.map (MulAut.conj g_f).toMonoidHom ≤
                K.map (MulAut.conj g_f).toMonoidHom ⊔ L := le_sup_left
    have hK'U : K' ≤ K.map (MulAut.conj g_f).toMonoidHom ⊔ L := by
      rw [h_factor]; exact le_sup_left
    obtain ⟨n', hn'_N, h_conj⟩ :=
      step_restriction h1 (Or.inl hN_solv) ih hK_g_compl hK' hKgU hK'U hH_top
    -- Compose conjugations: K.map (conj (n' * g_f)) = (K.map (conj g_f)).map (conj n') = K'
    refine ⟨n' * g_f, N.mul_mem hn'_N hg_f_N, ?_⟩
    rw [show (MulAut.conj (n' * g_f)).toMonoidHom =
          (MulAut.conj n').toMonoidHom.comp (MulAut.conj g_f).toMonoidHom from ?_,
        ← Subgroup.map_map]
    · exact h_conj
    · ext x
      change n' * g_f * x * (n' * g_f)⁻¹ = n' * (g_f * x * g_f⁻¹) * n'⁻¹
      group

omit [Finite G] in
/-- A conjugate of a complement is a complement. The conjugating element lies in `G`,
not necessarily in `N`. (Also generalizes the inline proof in `step_caseA`.) -/
theorem isComplement'_conj {N K : Subgroup G} [N.Normal]
    (hK : IsComplement' N K) (g : G) :
    IsComplement' N (K.map (MulAut.conj g).toMonoidHom) := by
  have hN_normal : N.Normal := inferInstance
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · -- Disjoint: N ⊓ K^g = ⊥.
    rw [disjoint_iff]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_bot, Subgroup.mem_map,
               MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨fun ⟨hxN, k, hkK, hkx⟩ => ?_, fun h => ?_⟩
    · have hk_eq : k = g⁻¹ * x * g := by rw [← hkx]; group
      have hkN : k ∈ N := by
        rw [hk_eq]
        -- g⁻¹ * x * g ∈ N since N is normal.
        have := hN_normal.conj_mem x hxN g⁻¹
        simpa [mul_assoc] using this
      have hk_inter : k ∈ N ⊓ K := ⟨hkN, hkK⟩
      rw [hK.disjoint.eq_bot, Subgroup.mem_bot] at hk_inter
      rw [hk_inter, mul_one, mul_inv_cancel] at hkx
      exact hkx.symm
    · subst h
      exact ⟨N.one_mem, 1, K.one_mem, by simp⟩
  · -- (N : Set G) * (K^g : Set G) = univ.
    rw [Set.eq_univ_iff_forall]
    intro x
    have h_conj_in_sup : g⁻¹ * x * g ∈ (N ⊔ K : Subgroup G) := by
      rw [hK.sup_eq_top]; trivial
    rw [mem_sup_of_normal_left] at h_conj_in_sup
    obtain ⟨n', hn'_N, k', hk'_K, hnk'⟩ := h_conj_in_sup
    refine ⟨g * n' * g⁻¹, hN_normal.conj_mem n' hn'_N g,
            g * k' * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨k', hk'_K, rfl⟩
    · change g * n' * g⁻¹ * (g * k' * g⁻¹) = x
      have hcalc : g * n' * g⁻¹ * (g * k' * g⁻¹) = g * (n' * k') * g⁻¹ := by group
      rw [hcalc, hnk']
      group

/-- **Case B (G/N solvable)**: full SZ conjugacy when `G ⧸ N` is solvable.

Proof outline (Isaacs Thm 3.12, mmd L1644-1660):
- Trivial cases: `N = ⊤` (then `K = K' = ⊥`) and `N = ⊥` (then `K = K' = ⊤`).
- Main case: take `M̄` minimal normal in `G ⧸ N`, `M := M̄.comap (mk' N)`. By Isaacs Lem 3.11
  (`minimal_normal_isPGroup_of_solvable`), `M̄` is a `p`-group for some prime `p`. Since
  `p ∣ |G : N|` and `|N|, |G : N|` coprime, `p ∤ |N|`. Apply `step_factor` with `M` to
  get `g_f ∈ N` with `H ⊔ M = K' ⊔ M` where `H := K^{g_f}`.
  - If `H ⊔ M < ⊤`: `step_restriction` on `H ⊔ M` with `H, K'` as complements.
  - If `H ⊔ M = ⊤` (i.e., `HM = G`): then `M ∩ H` and `M ∩ K'` are both Sylow `p`-subgroups
    of `M` (Dedekind + coprime); Sylow C in `M` gives `m ∈ M` with `M ∩ H = (M ∩ K')^m`.
    Set `L := M ∩ H = M ∩ K'^m`. Both `H` and `K'^m` are contained in `N_G(L)`.
    - If `N_G(L) < G`: `step_restriction` on `N_G(L)` with `H, K'^m`; then promote the
      conjugating element via `g_M = m⁻¹ * n * g_f`, decompose in `N · K` to land in `N`.
    - If `N_G(L) = G` (so `L ⊴ G, L > 1, L ⊆ H`): apply `step_factor` again, this time
      with `H, K'` and `L`. Since `L ⊆ H ⊴ G ⇒ L ⊆ H^g'` for the resulting `g' ∈ N`, the
      join collapses: `H^{g'} = K' ⊔ L`, hence `K' ⊆ H^{g'}` and by cardinality `K' = H^{g'}`,
      giving `K^{g' * g_f} = K'` with `g' * g_f ∈ N`. -/
private theorem step_caseB
    (h1 : Nat.Coprime (Nat.card N) N.index)
    (hQN_solv : Group.IsSolvable (G ⧸ N))
    (ih : IH G)
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K') :
    ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' := by
  -- Trivial: N = ⊤ ⇒ K = K' = ⊥.
  by_cases hN_top : N = ⊤
  · subst hN_top
    have hK_bot : K = ⊥ := by
      have h_inf : ⊤ ⊓ K = ⊥ := hK.disjoint.eq_bot
      rwa [top_inf_eq] at h_inf
    have hK'_bot : K' = ⊥ := by
      have h_inf : ⊤ ⊓ K' = ⊥ := hK'.disjoint.eq_bot
      rwa [top_inf_eq] at h_inf
    refine ⟨1, (⊤ : Subgroup G).one_mem, ?_⟩
    rw [hK_bot, hK'_bot]
    ext x
    simp [Subgroup.mem_bot]
  -- Trivial: N = ⊥ ⇒ K = K' = ⊤.
  by_cases hN_bot : N = ⊥
  · subst hN_bot
    have hK_top : K = ⊤ := by
      have hsup := hK.sup_eq_top
      rwa [bot_sup_eq] at hsup
    have hK'_top : K' = ⊤ := by
      have hsup := hK'.sup_eq_top
      rwa [bot_sup_eq] at hsup
    refine ⟨1, (⊥ : Subgroup G).one_mem, ?_⟩
    rw [hK_top, hK'_top]
    ext x
    simp
  -- Main: N ≠ ⊥, N ≠ ⊤.
  have hGN_nontriv : Nontrivial (G ⧸ N) := by
    have h_idx : 1 < N.index := Subgroup.one_lt_index_of_ne_top hN_top
    have h_card : 1 < Nat.card (G ⧸ N) := h_idx
    exact Finite.one_lt_card_iff_nontrivial.mp h_card
  -- Take M̄ minimal normal in G/N.
  have h_top_ne_bot : (⊤ : Subgroup (G ⧸ N)) ≠ ⊥ := by
    intro h_eq
    obtain ⟨a, b, hab⟩ := exists_pair_ne (G ⧸ N)
    have ha : a ∈ (⊤ : Subgroup (G ⧸ N)) := trivial
    have hb : b ∈ (⊤ : Subgroup (G ⧸ N)) := trivial
    rw [h_eq, Subgroup.mem_bot] at ha hb
    exact hab (ha.trans hb.symm)
  obtain ⟨M_bar, hM_bar_normal, _, hM_bar_ne_bot, hM_bar_min⟩ :=
    exists_minimal_normal_le (N := (⊤ : Subgroup (G ⧸ N))) inferInstance h_top_ne_bot
  have : M_bar.Normal := hM_bar_normal
  -- M := M̄.comap (mk' N) ⊴ G.
  let M : Subgroup G := M_bar.comap (QuotientGroup.mk' N)
  have hM_normal : M.Normal := M_bar.normal_comap (QuotientGroup.mk' N)
  -- N ≤ M.
  have hN_le_M : N ≤ M := by
    intro n hn
    change (QuotientGroup.mk n : G ⧸ N) ∈ M_bar
    rw [(QuotientGroup.eq_one_iff n).mpr hn]
    exact M_bar.one_mem
  -- M ≠ ⊥ (since N ⊆ M and N ≠ ⊥).
  have hM_ne_bot : M ≠ ⊥ := fun hbot => hN_bot (le_bot_iff.mp (hN_le_M.trans hbot.le))
  -- M_bar is a p-group (Isaacs Lem 3.11).
  have : Group.IsSolvable M_bar := inferInstance
  obtain ⟨p, hp_prime, hp_pgroup⟩ :=
    minimal_normal_isPGroup_of_solvable (L := M_bar) hM_bar_ne_bot hM_bar_min
  have : Fact p.Prime := ⟨hp_prime⟩
  -- Apply step_factor with L := M.
  obtain ⟨g_f, hg_f_N, h_factor⟩ :=
    step_factor h1 (Or.inr hQN_solv) ih hK hK' hM_ne_bot
  -- H := K^{g_f}, complement of N.
  set H := K.map (MulAut.conj g_f).toMonoidHom with hH_def
  have hH_compl : IsComplement' N H := isComplement'_conj hK g_f
  -- Case split on H ⊔ M = ⊤.
  by_cases hHM_top : H ⊔ M = ⊤
  · -- Case ⊔ M = ⊤: HM = G. Use Sylow C in M.
    -- Step 1: |M ⊓ H| = |M̄| (Dedekind + complementarity in M).
    -- M = N ⊔ (M ⊓ H) by Dedekind (eq_sup_inf_of_le_sup_of_normal_of_le).
    have h_M_le_NH : M ≤ N ⊔ H := by
      rw [hH_compl.sup_eq_top]; exact le_top
    have h_M_eq : M = N ⊔ (M ⊓ H) := by
      exact Subgroup.eq_sup_inf_of_le_sup_of_normal_of_le hN_le_M h_M_le_NH
    -- (M ⊓ H) ⊓ N = ⊥ in G.
    have h_MH_inf_N : (M ⊓ H : Subgroup G) ⊓ N = ⊥ := by
      have h_le : (M ⊓ H : Subgroup G) ⊓ N ≤ H ⊓ N := by
        intro x ⟨⟨_, hxH⟩, hxN⟩
        exact ⟨hxH, hxN⟩
      have h_HN_bot : (H : Subgroup G) ⊓ N = ⊥ := by
        rw [inf_comm]; exact hH_compl.disjoint.eq_bot
      exact le_bot_iff.mp (h_le.trans h_HN_bot.le)
    have h_MH_sup_N : (M ⊓ H : Subgroup G) ⊔ N = M := by
      rw [sup_comm]; exact h_M_eq.symm
    -- Step 1: cardinality |M ⊓ H| · |N| = |M|.
    have h_MH_card : Nat.card (M ⊓ H : Subgroup G) * Nat.card N = Nat.card M := by
      have h_card := card_HK_mul_card_inf_eq_card_mul_card (M ⊓ H : Subgroup G) N
      rw [h_MH_inf_N, Subgroup.card_bot, mul_one] at h_card
      -- h_card : Nat.card (↑(M ⊓ H) * ↑N : Set G) = Nat.card (M ⊓ H) * Nat.card N
      have h_set_eq : (↑(M ⊓ H : Subgroup G) * ↑N : Set G) = (↑M : Set G) := by
        rw [← Subgroup.mul_normal, h_MH_sup_N]
      rw [h_set_eq] at h_card
      exact h_card.symm
    -- Step 2: |N| · |M̄| = |M|.
    have h_M_card : Nat.card N * Nat.card M_bar = Nat.card M := by
      have h_M_idx_eq : M.index = M_bar.index :=
        M_bar.index_comap_of_surjective (QuotientGroup.mk'_surjective N)
      have h_M_lagrange : Nat.card ↥M * M.index = Nat.card G := M.card_mul_index
      have h_M_bar_lagrange : Nat.card ↥M_bar * M_bar.index = N.index := by
        rw [show N.index = Nat.card (G ⧸ N) from rfl]
        exact M_bar.card_mul_index
      have h_N_lagrange : Nat.card ↥N * N.index = Nat.card G := N.card_mul_index
      have h_M_idx_pos : 0 < M.index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      apply Nat.eq_of_mul_eq_mul_right h_M_idx_pos
      calc Nat.card N * Nat.card M_bar * M.index
          = Nat.card N * (Nat.card M_bar * M_bar.index) := by rw [h_M_idx_eq]; ring
        _ = Nat.card N * N.index := by rw [h_M_bar_lagrange]
        _ = Nat.card G := h_N_lagrange
        _ = Nat.card M * M.index := h_M_lagrange.symm
    -- Step 3: |M ⊓ H| = |M̄|.
    have h_MH_card_eq_M_bar : Nat.card (M ⊓ H : Subgroup G) = Nat.card M_bar := by
      have hN_pos : 0 < Nat.card N := Nat.card_pos
      apply Nat.eq_of_mul_eq_mul_right hN_pos
      rw [h_MH_card, mul_comm, h_M_card]
    -- Step 4: |M ⊓ H| = p^k (where M_bar is a p-group of cardinality p^k).
    obtain ⟨k, hk_eq⟩ := hp_pgroup.exists_card_eq
    have h_MH_card_eq_pk : Nat.card ↥(M ⊓ H : Subgroup G) = p ^ k := by
      rw [h_MH_card_eq_M_bar, hk_eq]
    -- Step 5: p ∤ |N|.
    have hk_pos : 1 ≤ k := by
      by_contra h
      push Not at h
      interval_cases k
      rw [pow_zero] at hk_eq
      have hM_bar_nontriv : Nontrivial M_bar :=
        (Subgroup.bot_or_nontrivial _).resolve_left hM_bar_ne_bot
      have : 1 < Nat.card M_bar := Finite.one_lt_card
      omega
    have hp_dvd_M_bar : p ∣ Nat.card M_bar := by
      rw [hk_eq]
      exact dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hk_pos)
    have hp_dvd_idx : p ∣ N.index := by
      have h_dvd : Nat.card M_bar ∣ N.index := by
        have := Subgroup.card_subgroup_dvd_card M_bar
        rwa [show Nat.card (G ⧸ N) = N.index from rfl] at this
      exact hp_dvd_M_bar.trans h_dvd
    have hp_not_dvd_N : ¬ p ∣ Nat.card N := by
      intro h_dvd_N
      have h_dvd_gcd : p ∣ Nat.gcd (Nat.card N) N.index := Nat.dvd_gcd h_dvd_N hp_dvd_idx
      rw [h1] at h_dvd_gcd
      exact hp_prime.one_lt.ne' (Nat.dvd_one.mp h_dvd_gcd)
    -- Step 6: (Nat.card ↥M).factorization p = k.
    have h_N_card_ne_zero : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
    have h_M_bar_card_ne_zero : Nat.card ↥M_bar ≠ 0 := Nat.card_pos.ne'
    have h_M_factorization : (Nat.card ↥M).factorization p = k := by
      rw [← h_M_card]
      rw [Nat.factorization_mul h_N_card_ne_zero h_M_bar_card_ne_zero]
      rw [Finsupp.add_apply]
      rw [Nat.factorization_eq_zero_of_not_dvd hp_not_dvd_N, zero_add]
      rw [hk_eq, hp_prime.factorization_pow, Finsupp.single_apply, if_pos rfl]
    -- Step 7: Construct Sylow P_H : Sylow p ↥M.
    have h_MH_subgroupOf_card_eq :
        Nat.card ((M ⊓ H : Subgroup G).subgroupOf M) = Nat.card ↥(M ⊓ H : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : (M ⊓ H : Subgroup G) ≤ M)).toEquiv
    have h_MH_subgroupOf_card :
        Nat.card ((M ⊓ H : Subgroup G).subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
      rw [h_MH_subgroupOf_card_eq, h_MH_card_eq_pk, h_M_factorization]
    have : Fact p.Prime := ⟨hp_prime⟩
    let P_H : Sylow p ↥M := Sylow.ofCard ((M ⊓ H : Subgroup G).subgroupOf M) h_MH_subgroupOf_card
    -- Step 8: K' analog. K'M = G ⇒ |M ⊓ K'| = p^k.
    have hK'M_top : K' ⊔ M = ⊤ := by rw [← h_factor]; exact hHM_top
    have h_M_le_NK' : M ≤ N ⊔ K' := by rw [hK'.sup_eq_top]; exact le_top
    have h_M_eq_K' : M = N ⊔ (M ⊓ K') :=
      Subgroup.eq_sup_inf_of_le_sup_of_normal_of_le hN_le_M h_M_le_NK'
    have h_MK'_inf_N : (M ⊓ K' : Subgroup G) ⊓ N = ⊥ := by
      have h_le : (M ⊓ K' : Subgroup G) ⊓ N ≤ K' ⊓ N := by
        intro x ⟨⟨_, hxK'⟩, hxN⟩
        exact ⟨hxK', hxN⟩
      have h_K'N_bot : (K' : Subgroup G) ⊓ N = ⊥ := by
        rw [inf_comm]; exact hK'.disjoint.eq_bot
      exact le_bot_iff.mp (h_le.trans h_K'N_bot.le)
    have h_MK'_sup_N : (M ⊓ K' : Subgroup G) ⊔ N = M := by
      rw [sup_comm]; exact h_M_eq_K'.symm
    have h_MK'_card : Nat.card (M ⊓ K' : Subgroup G) * Nat.card N = Nat.card M := by
      have h_card := card_HK_mul_card_inf_eq_card_mul_card (M ⊓ K' : Subgroup G) N
      rw [h_MK'_inf_N, Subgroup.card_bot, mul_one] at h_card
      have h_set_eq : (↑(M ⊓ K' : Subgroup G) * ↑N : Set G) = (↑M : Set G) := by
        rw [← Subgroup.mul_normal, h_MK'_sup_N]
      rw [h_set_eq] at h_card
      exact h_card.symm
    have h_MK'_card_eq_M_bar : Nat.card (M ⊓ K' : Subgroup G) = Nat.card M_bar := by
      have hN_pos : 0 < Nat.card N := Nat.card_pos
      apply Nat.eq_of_mul_eq_mul_right hN_pos
      rw [h_MK'_card, mul_comm, h_M_card]
    have h_MK'_card_eq_pk : Nat.card ↥(M ⊓ K' : Subgroup G) = p ^ k := by
      rw [h_MK'_card_eq_M_bar, hk_eq]
    have h_MK'_subgroupOf_card_eq :
        Nat.card ((M ⊓ K' : Subgroup G).subgroupOf M) =
          Nat.card ↥(M ⊓ K' : Subgroup G) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (inf_le_left : (M ⊓ K' : Subgroup G) ≤ M)).toEquiv
    have h_MK'_subgroupOf_card :
        Nat.card ((M ⊓ K' : Subgroup G).subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
      rw [h_MK'_subgroupOf_card_eq, h_MK'_card_eq_pk, h_M_factorization]
    let P_K' : Sylow p ↥M := Sylow.ofCard ((M ⊓ K' : Subgroup G).subgroupOf M) h_MK'_subgroupOf_card
    -- Step 9: Sylow C in M: ∃ m_M : ↥M, m_M • P_K' = P_H.
    obtain ⟨m_M, h_mM_smul⟩ : ∃ m_M : ↥M, m_M • P_K' = P_H :=
      MulAction.exists_smul_eq ↥M P_K' P_H
    -- Step 10: extract m ∈ M and derive M ⊓ K'^m = M ⊓ H.
    let m : G := m_M.val
    have hm_M : m ∈ M := m_M.2
    -- Sylow conjugation at subgroup level (in ↥M).
    have h_conj_in_M :
        ((M ⊓ K' : Subgroup G).subgroupOf M).map (MulAut.conj m_M).toMonoidHom =
          (M ⊓ H : Subgroup G).subgroupOf M := by
      have h := congr_arg (Sylow.toSubgroup) h_mM_smul
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
      exact h
    -- Push to G via M.subtype: (M ⊓ K').map (conj m) = M ⊓ H.
    have h_push : (M ⊓ K' : Subgroup G).map (MulAut.conj m).toMonoidHom = M ⊓ H := by
      have h_rhs : ((M ⊓ H : Subgroup G).subgroupOf M).map M.subtype = M ⊓ H :=
        subgroupOf_map_subtype_eq (inf_le_left : (M ⊓ H : Subgroup G) ≤ M)
      have h_lhs_eq :
          (((M ⊓ K' : Subgroup G).subgroupOf M).map (MulAut.conj m_M).toMonoidHom).map M.subtype =
            (M ⊓ K' : Subgroup G).map (MulAut.conj m).toMonoidHom :=
        map_subtype_conj_subgroupOf m_M (M ⊓ K' : Subgroup G)
          (inf_le_left : (M ⊓ K' : Subgroup G) ≤ M)
      rw [← h_rhs, ← h_conj_in_M, h_lhs_eq]
    -- Use M normal to derive M ⊓ K'^m = M ⊓ H.
    set K'm : Subgroup G := K'.map (MulAut.conj m).toMonoidHom with hK'm_def
    have h_M_inter_K'm : M ⊓ K'm = M ⊓ H := by
      rw [← h_push]
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have : M.Normal := inferInstance
      constructor
      · rintro ⟨hxM, y, hyK', rfl⟩
        refine ⟨y, ⟨?_, hyK'⟩, rfl⟩
        -- m * y * m⁻¹ ∈ M ⇒ y = m⁻¹ * (m y m⁻¹) * m ∈ M (m, m⁻¹ ∈ M).
        have : m⁻¹ * (m * y * m⁻¹) * m ∈ M :=
          M.mul_mem (M.mul_mem (M.inv_mem hm_M) hxM) hm_M
        simpa [mul_assoc] using this
      · rintro ⟨y, ⟨hyM, hyK'⟩, rfl⟩
        refine ⟨?_, y, hyK', rfl⟩
        exact (inferInstance : M.Normal).conj_mem _ hyM _
    -- Step 11: L := M ⊓ H. Properties: L = M ⊓ K'm, L > 1, L ≤ H, L ≤ K'm.
    set L : Subgroup G := M ⊓ H with hL_def
    have hL_eq : L = M ⊓ K'm := h_M_inter_K'm.symm
    have hL_le_H : L ≤ H := inf_le_right
    have hL_le_K'm : L ≤ K'm := hL_eq ▸ inf_le_right
    have hL_ne_bot : L ≠ ⊥ := by
      intro hbot
      have h_card : Nat.card ↥L = 1 := by rw [hbot]; exact Subgroup.card_bot
      have : Nat.card ↥L = p ^ k := h_MH_card_eq_pk
      rw [h_card] at this
      have : p ^ k = 1 := this.symm
      have hk_pos' := Nat.one_le_iff_ne_zero.mp hk_pos
      have hp_gt_one : 1 < p := hp_prime.one_lt
      exact absurd this (Nat.ne_of_gt (Nat.one_lt_pow hk_pos' hp_gt_one))
    -- H ≤ N_G(L) (since L = M ⊓ H, M normal in G, H closed under self-conjugation).
    have hH_le_NL : H ≤ normalizer (L : Set G) := by
      intro h hHmem
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have : M.Normal := inferInstance
      constructor
      · rintro ⟨hxM, hxH⟩
        refine ⟨(inferInstance : M.Normal).conj_mem _ hxM _, ?_⟩
        exact H.mul_mem (H.mul_mem hHmem hxH) (H.inv_mem hHmem)
      · rintro ⟨hcM, hcH⟩
        refine ⟨?_, ?_⟩
        · have : h⁻¹ * (h * x * h⁻¹) * h ∈ M := by
            have hin := (inferInstance : M.Normal).conj_mem (h * x * h⁻¹) hcM h⁻¹
            simpa [mul_assoc] using hin
          simpa [mul_assoc] using this
        · have : h⁻¹ * (h * x * h⁻¹) * h ∈ H :=
            H.mul_mem (H.mul_mem (H.inv_mem hHmem) hcH) hHmem
          simpa [mul_assoc] using this
    -- K'm ≤ N_G(L) (similar via L = M ⊓ K'm).
    have hK'm_le_NL : K'm ≤ normalizer (L : Set G) := by
      intro k hKmem
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have : M.Normal := inferInstance
      constructor
      · intro hxL
        have hxL' : x ∈ (M ⊓ K'm : Subgroup G) := hL_eq ▸ hxL
        obtain ⟨hxM, hxK'm⟩ := hxL'
        have hL_form : (M ⊓ K'm : Subgroup G) = L := hL_eq.symm
        rw [← hL_form]
        refine ⟨(inferInstance : M.Normal).conj_mem _ hxM _, ?_⟩
        exact K'm.mul_mem (K'm.mul_mem hKmem hxK'm) (K'm.inv_mem hKmem)
      · intro hL
        have hL' : k * x * k⁻¹ ∈ (M ⊓ K'm : Subgroup G) := hL_eq ▸ hL
        obtain ⟨hcM, hcKm⟩ := hL'
        have hL_form : (M ⊓ K'm : Subgroup G) = L := hL_eq.symm
        rw [← hL_form]
        refine ⟨?_, ?_⟩
        · have : k⁻¹ * (k * x * k⁻¹) * k ∈ M := by
            have hin := (inferInstance : M.Normal).conj_mem (k * x * k⁻¹) hcM k⁻¹
            simpa [mul_assoc] using hin
          simpa [mul_assoc] using this
        · have : k⁻¹ * (k * x * k⁻¹) * k ∈ K'm :=
            K'm.mul_mem (K'm.mul_mem (K'm.inv_mem hKmem) hcKm) hKmem
          simpa [mul_assoc] using this
    -- Step 12: Case split on N_G(L) = ⊤ vs N_G(L) < ⊤.
    have hK'm_compl : IsComplement' N K'm := isComplement'_conj hK' m
    by_cases hNL_top : normalizer (L : Set G) = ⊤
    · -- Case N_G(L) = G: L ⊴ G, apply step_factor with H, K', L.
      have hL_normal : L.Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hg_mem : g ∈ normalizer (L : Set G) := by rw [hNL_top]; trivial
        exact (Subgroup.mem_normalizer_iff.mp hg_mem n).mp hn
      obtain ⟨g', hg'_N, h_factor_L⟩ :=
        step_factor h1 (Or.inr hQN_solv) ih hH_compl hK' hL_ne_bot
      -- L ⊴ G + L ⊆ H ⇒ L = L^g' ⊆ H^g'.
      have hL_le_Hg : L ≤ H.map (MulAut.conj g').toMonoidHom := by
        intro x hxL
        rw [Subgroup.mem_map]
        refine ⟨g'⁻¹ * x * g', ?_, ?_⟩
        · -- g'⁻¹ * x * g' ∈ L (L ⊴ G), then ∈ H (L ≤ H).
          have h_in_L : g'⁻¹ * x * g' ∈ L := by
            have := hL_normal.conj_mem x hxL g'⁻¹
            simpa [mul_assoc] using this
          exact hL_le_H h_in_L
        · change g' * (g'⁻¹ * x * g') * g'⁻¹ = x; group
      -- H^g' ⊔ L = H^g'.
      have hHg_sup : (H.map (MulAut.conj g').toMonoidHom) ⊔ L =
          H.map (MulAut.conj g').toMonoidHom :=
        sup_eq_left.mpr hL_le_Hg
      -- Combined with h_factor_L: H^g' = K' ⊔ L.
      have hHg_eq_K'L : H.map (MulAut.conj g').toMonoidHom = K' ⊔ L := by
        rw [← hHg_sup, h_factor_L]
      -- K' ⊆ H^g'.
      have hK'_le_Hg : K' ≤ H.map (MulAut.conj g').toMonoidHom := by
        rw [hHg_eq_K'L]; exact le_sup_left
      -- |K'| = |H^g'| (both complements of N).
      have hHg_compl : IsComplement' N (H.map (MulAut.conj g').toMonoidHom) :=
        isComplement'_conj hH_compl g'
      have h_K'_card_eq_Hg : Nat.card ↥K' = Nat.card ↥(H.map (MulAut.conj g').toMonoidHom) :=
        hK'.symm.index_eq_card.symm.trans hHg_compl.symm.index_eq_card
      -- K' = H^g'.
      have hK'_eq_Hg : K' = H.map (MulAut.conj g').toMonoidHom :=
        Subgroup.eq_of_le_of_card_ge hK'_le_Hg h_K'_card_eq_Hg.symm.le
      -- Conclusion: K^(g' * g_f) = K'.
      refine ⟨g' * g_f, N.mul_mem hg'_N hg_f_N, ?_⟩
      have hcomp : (MulAut.conj (g' * g_f)).toMonoidHom =
            (MulAut.conj g').toMonoidHom.comp (MulAut.conj g_f).toMonoidHom := by
        ext x
        change g' * g_f * x * (g' * g_f)⁻¹ = g' * (g_f * x * g_f⁻¹) * g'⁻¹
        group
      rw [hcomp, ← Subgroup.map_map]
      exact hK'_eq_Hg.symm
    · -- Case N_G(L) < G: step_restriction on N_G(L) with H, K'm as complements.
      obtain ⟨n', hn'_N, h_conj⟩ :=
        step_restriction h1 (Or.inr hQN_solv) ih hH_compl hK'm_compl hH_le_NL hK'm_le_NL hNL_top
      -- h_conj : H.map (conj n') = K'm = K'.map (conj m).
      -- Then K.map (conj (n' * g_f)) = H.map (conj n') = K'.map (conj m).
      -- Goal: ∃ n0 ∈ N, K.map (conj n0) = K'.
      -- Strategy: K.map (conj (m⁻¹ * n' * g_f)) = K', then promote via N · K decomposition.
      have h_chain : K.map (MulAut.conj (m⁻¹ * n' * g_f)).toMonoidHom = K' := by
        -- K^(m⁻¹ n' g_f) = K^g_f^(m⁻¹ n') = H^(m⁻¹ n') = ?
        -- We need K^(m⁻¹ n' g_f) = K'.
        -- From h_conj: H^n' = K'^m (K'm = K'.map (conj m)).
        -- K^g_f^n' = H^n' = K'^m. Conjugate both by m⁻¹:
        -- K^g_f^n'^(m⁻¹) = K'^m^(m⁻¹) = K'.
        -- K^g_f^n'^(m⁻¹) = K^(m⁻¹ * n' * g_f).
        have h1 : K.map (MulAut.conj g_f).toMonoidHom = H := rfl
        have h2 : H.map (MulAut.conj n').toMonoidHom = K'm := h_conj
        have h3 : K'm.map (MulAut.conj m⁻¹).toMonoidHom = K' := by
          rw [hK'm_def, Subgroup.map_map]
          have h_inv_comp : (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
              MonoidHom.id G := by
            ext x
            change m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x
            group
          rw [h_inv_comp]
          ext; simp
        -- Chain: K.map (...) = K^(g_f) (= H) .map (conj n').map (conj m⁻¹) = K'm.map (...) = K'.
        have hcomp : (MulAut.conj (m⁻¹ * n' * g_f)).toMonoidHom =
              (MulAut.conj m⁻¹).toMonoidHom.comp
                ((MulAut.conj n').toMonoidHom.comp (MulAut.conj g_f).toMonoidHom) := by
          ext x
          change m⁻¹ * n' * g_f * x * (m⁻¹ * n' * g_f)⁻¹ =
            m⁻¹ * (n' * (g_f * x * g_f⁻¹) * n'⁻¹) * m⁻¹⁻¹
          group
        rw [hcomp, ← Subgroup.map_map, ← Subgroup.map_map, h1, h2, h3]
      -- Promote: decompose m⁻¹ * n' * g_f = n_N * k_K (n_N ∈ N, k_K ∈ K) via IsComplement.
      have h_g_in_sup : (m⁻¹ * n' * g_f) ∈ (N ⊔ K : Subgroup G) := by
        rw [hK.sup_eq_top]; trivial
      rw [mem_sup_of_normal_left] at h_g_in_sup
      obtain ⟨n_N, hn_N_N, k_K, hk_K_K, hg_decomp⟩ := h_g_in_sup
      -- K.map (conj (n_N * k_K)) = K.map (conj n_N) since conj k_K preserves K.
      refine ⟨n_N, hn_N_N, ?_⟩
      have hcomp_NK : (MulAut.conj (n_N * k_K)).toMonoidHom =
            (MulAut.conj n_N).toMonoidHom.comp (MulAut.conj k_K).toMonoidHom := by
        ext x
        change n_N * k_K * x * (n_N * k_K)⁻¹ = n_N * (k_K * x * k_K⁻¹) * n_N⁻¹
        group
      have h_K_conj_kK : K.map (MulAut.conj k_K).toMonoidHom = K := by
        ext y
        simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        constructor
        · rintro ⟨z, hzK, rfl⟩
          exact K.mul_mem (K.mul_mem hk_K_K hzK) (K.inv_mem hk_K_K)
        · intro hyK
          refine ⟨k_K⁻¹ * y * k_K, ?_, ?_⟩
          · exact K.mul_mem (K.mul_mem (K.inv_mem hk_K_K) hyK) hk_K_K
          · group
      calc K.map (MulAut.conj n_N).toMonoidHom
          = (K.map (MulAut.conj k_K).toMonoidHom).map (MulAut.conj n_N).toMonoidHom := by
              rw [h_K_conj_kK]
        _ = K.map (MulAut.conj (n_N * k_K)).toMonoidHom := by
              rw [hcomp_NK, ← Subgroup.map_map]
        _ = K.map (MulAut.conj (m⁻¹ * n' * g_f)).toMonoidHom := by rw [hg_decomp]
        _ = K' := h_chain
  · -- Case ⊔ M < ⊤: step_restriction on H ⊔ M.
    have hHU : H ≤ H ⊔ M := le_sup_left
    have hK'U : K' ≤ H ⊔ M := by rw [h_factor]; exact le_sup_left
    obtain ⟨n', hn'_N, h_conj⟩ :=
      step_restriction h1 (Or.inr hQN_solv) ih hH_compl hK' hHU hK'U hHM_top
    -- H.map (conj n') = K'. Compose: K.map (conj (n' * g_f)) = K'.
    refine ⟨n' * g_f, N.mul_mem hn'_N hg_f_N, ?_⟩
    have hcomp : (MulAut.conj (n' * g_f)).toMonoidHom =
          (MulAut.conj n').toMonoidHom.comp (MulAut.conj g_f).toMonoidHom := by
      ext x
      change n' * g_f * x * (n' * g_f)⁻¹ = n' * (g_f * x * g_f⁻¹) * n'⁻¹
      group
    rw [hcomp, ← Subgroup.map_map]
    exact h_conj

/-- **Main induction**: combines `step_caseA` and `step_caseB` via strong induction. -/
private theorem main_aux {n : ℕ} :
    ∀ {G : Type u} [Group G] [Finite G] (_hG : Nat.card G = n)
      {N : Subgroup G} [N.Normal]
      (_h1 : Nat.Coprime (Nat.card N) N.index)
      (_hSolv : Group.IsSolvable N ∨ Group.IsSolvable (G ⧸ N))
      {K K' : Subgroup G} (_hK : IsComplement' N K) (_hK' : IsComplement' N K'),
      ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G _ _ hG N _ h1 hSolv K K' hK hK'
    -- Build IH G from outer ih.
    have ih_G : IH G := by
      intro G' _ _ hcard_G' N' _ h1' hSolv' K1 K2 hK1 hK2
      exact ih (Nat.card G') (hG ▸ hcard_G') rfl h1' hSolv' hK1 hK2
    rcases hSolv with hN | hGN
    · exact step_caseA h1 hN ih_G hK hK'
    · exact step_caseB h1 hGN ih_G hK hK'

end SchurZassenhausConj

/-- **Schur-Zassenhaus conjugacy** (Isaacs Thm 3.12): for `N ⊴ G` finite with coprime order
and index, assuming `N` or `G ⧸ N` is solvable, any two complements are conjugate by an
element of `N`. -/
theorem IsComplement'.exists_conj_of_coprime {G : Type u} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index)
    (hSolv : Group.IsSolvable N ∨ Group.IsSolvable (G ⧸ N))
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K') :
    ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' :=
  SchurZassenhausConj.main_aux rfl hN hSolv hK hK'

end Subgroup


