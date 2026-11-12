-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_SelfCentralizingEnlargement
-- name    : OddOrder_Isaacs_Ch06_FrobeniusActions_SelfCentralizingEnlargement
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:36:58.52141+00:00
-- url     : https://prove2.me/theorems/b5a91aff-fd70-41fc-ac0b-1cc31c7556af
-- title:
--   Isaacs Thm 6.12: self-centralizing subgroup enlargement steps
-- statement:
--   The self-centralizing-subgroup machinery for Isaacs, *Finite Group Theory*, Thm 6.12 (pp. 192–193): enlarging a normal abelian subgroup below its centralizer ($C<B\le C_P(C)$ with $|B:C|=p$), maximal normal abelian subgroups are self-centralizing, the bound $|P/C|\le|\mathrm{Aut}\,C|$, and center-index facts for the noncommutative relative-index-$p$ step.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/SelfCentralizingEnlargement.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/SelfCentralizingEnlargement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_InvolutionRecognition

namespace OddOrder.Isaacs.Ch06

open OddOrder.GroupTheory

/-- **Isaacs Thm 6.12 setup**: if `C` is a normal subgroup of a finite `p`-group `P` and
`C < C_P(C)`, then there is a normal abelian subgroup `B` with `C < B ≤ C_P(C)` and
`|B : C| = p`.

This is the formal version of the first paragraph of the proof of Thm 6.12.  Ch.1 Lemma 1.23
supplies the normal intermediate subgroup of prime relative index; since `B ≤ C_P(C)`,
`C` is central in `B`, and the prime quotient `B/C` is cyclic, so `B` is abelian by
`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`. -/
theorem exists_normal_isMulCommutative_relIndex_prime_of_lt_centralizer
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P)
    {C : Subgroup P} [C.Normal]
    (hC_lt_cent : C < Subgroup.centralizer (C : Set P)) :
    ∃ B : Subgroup P, B.Normal ∧ C < B ∧ B ≤ Subgroup.centralizer (C : Set P) ∧
      C.relIndex B = p ∧ IsMulCommutative B := by
  have hCent_normal : (Subgroup.centralizer (C : Set P)).Normal :=
    Subgroup.normal_centralizer
  obtain ⟨B, hB_normal, hC_lt_B, hB_le_cent, hC_rel⟩ :=
    OddOrder.Isaacs.Ch01.IsPGroup.exists_normal_index_eq_prime
      hP (N := C) (M := Subgroup.centralizer (C : Set P)) hC_lt_cent
  have hC_sub_normal : (C.subgroupOf B).Normal := inferInstance
  have hC_sub_le_center : C.subgroupOf B ≤ Subgroup.center B := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    have hb_cent : ((b : B) : P) ∈ Subgroup.centralizer (C : Set P) :=
      hB_le_cent b.2
    have hc_mem : ((c : B) : P) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using hc
    have h_comm :
        ((c : B) : P) * ((b : B) : P) = ((b : B) : P) * ((c : B) : P) :=
      (Subgroup.mem_centralizer_iff.mp hb_cent) ((c : B) : P) hc_mem
    exact h_comm.symm
  have h_card_quot : Nat.card (B ⧸ C.subgroupOf B) = p := by
    rw [← Subgroup.index_eq_card]
    simpa [Subgroup.relIndex] using hC_rel
  have h_cyclic_quot : IsCyclic (B ⧸ C.subgroupOf B) :=
    isCyclic_of_prime_card h_card_quot
  have hB_comm : ∀ x y : B, x * y = y * x := by
    have : IsCyclic (B ⧸ C.subgroupOf B) := h_cyclic_quot
    exact (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (C.subgroupOf B)) (by
        rw [QuotientGroup.ker_mk']
        exact hC_sub_le_center)).is_comm.comm
  exact ⟨B, hB_normal, hC_lt_B, hB_le_cent, hC_rel, ⟨⟨hB_comm⟩⟩⟩

/-- **Isaacs Thm 6.12 setup**: in a finite group, choose a maximal normal abelian
subgroup.

The conclusion is in the strict-maximality form used by the proof of Theorem 6.12: no
strictly larger normal abelian subgroup contains the chosen subgroup. -/
theorem exists_maximal_normal_isMulCommutative
    {P : Type*} [Group P] [Finite P] :
    ∃ C : Subgroup P, C.Normal ∧ IsMulCommutative C ∧
      ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False := by
  classical
  let S : Set (Subgroup P) := {C | C.Normal ∧ IsMulCommutative C}
  have hS_nonempty : S.Nonempty := by
    refine ⟨⊥, ?_⟩
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨C, hC_max⟩ := (Set.toFinite S).exists_maximal hS_nonempty
  refine ⟨C, hC_max.1.1, hC_max.1.2, ?_⟩
  intro B hB_normal hB_comm hC_lt_B
  have hB_mem : B ∈ S := ⟨hB_normal, hB_comm⟩
  exact hC_lt_B.not_ge (hC_max.2 hB_mem hC_lt_B.le)

/-- **Isaacs Thm 6.12 setup**: a maximal normal abelian subgroup `C` of a finite `p`-group
is self-centralizing.

The maximality hypothesis is stated in the form needed for the proof: no strictly larger
normal abelian subgroup contains `C`.  If `C < C_P(C)`, the preceding theorem produces such
a larger normal abelian subgroup, contradiction. -/
theorem centralizer_eq_of_maximal_normal_isMulCommutative
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P)
    {C : Subgroup P} [C.Normal] (hC_comm : IsMulCommutative C)
    (hC_max : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False) :
    Subgroup.centralizer (C : Set P) = C := by
  have hC_le_cent : C ≤ Subgroup.centralizer (C : Set P) := by
    have : IsMulCommutative C := hC_comm
    exact Subgroup.le_centralizer (H := C)
  have hcent_le_C : Subgroup.centralizer (C : Set P) ≤ C := by
    by_contra hnot
    have hne : C ≠ Subgroup.centralizer (C : Set P) := by
      intro h_eq
      exact hnot (le_of_eq h_eq.symm)
    have hlt : C < Subgroup.centralizer (C : Set P) := lt_of_le_of_ne hC_le_cent hne
    obtain ⟨B, hB_normal, hC_lt_B, _hB_le_cent, _hC_rel, hB_comm⟩ :=
      exists_normal_isMulCommutative_relIndex_prime_of_lt_centralizer hP hlt
    exact hC_max B hB_normal hB_comm hC_lt_B
  exact le_antisymm hcent_le_C hC_le_cent

private lemma conjNormal_ker_eq_of_self_centralizing
    {P : Type*} [Group P]
    {C : Subgroup P} [C.Normal]
    (hCent : Subgroup.centralizer (C : Set P) = C) :
    (MulAut.conjNormal (H := C) : P →* MulAut C).ker = C := by
  let φ : P →* MulAut C := MulAut.conjNormal (H := C)
  change φ.ker = C
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker] at hg
    have hg_cent : g ∈ Subgroup.centralizer (C : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      let cC : C := ⟨c, hc⟩
      have hfix : φ g cC = cC := by
        have h := congrArg (fun ψ : MulAut C => ψ cC) hg
        simpa using h
      have hconj : g * c * g⁻¹ = c := by
        have hval := congrArg Subtype.val hfix
        simpa [φ, cC] using hval
      have hgc : g * c = c * g := by
        calc g * c = (g * c * g⁻¹) * g := by simp [mul_assoc]
          _ = c * g := by rw [hconj]
      exact hgc.symm
    simpa [hCent] using hg_cent
  · intro hgC
    rw [MonoidHom.mem_ker]
    ext c
    have hg_cent : g ∈ Subgroup.centralizer (C : Set P) := by
      simpa [hCent] using hgC
    have hcomm : (c : P) * g = g * (c : P) :=
      (Subgroup.mem_centralizer_iff.mp hg_cent) (c : P) c.2
    calc ((φ g c : C) : P) = g * (c : P) * g⁻¹ := by rfl
      _ = ((c : P) * g) * g⁻¹ := by rw [← hcomm]
      _ = (c : P) := by simp [mul_assoc]
      _ = (((1 : MulAut C) c : C) : P) := by rfl

/-- **Isaacs Thm 6.12 setup**: if `C` is self-centralizing in `P`, then
`|P/C| ≤ |Aut(C)|`.

The conjugation homomorphism `P → Aut(C)` has kernel `C_P(C)`. Under the
self-centralizing hypothesis this kernel is exactly `C`, so it induces an embedding
`P/C ↪ Aut(C)`. -/
theorem quotient_card_le_mulAut_of_self_centralizing
    {P : Type*} [Group P] [Finite P]
    {C : Subgroup P} [C.Normal]
    (hCent : Subgroup.centralizer (C : Set P) = C) :
    Nat.card (P ⧸ C) ≤ Nat.card (MulAut C) := by
  let φ : P →* MulAut C := MulAut.conjNormal (H := C)
  have hker : φ.ker = C := conjNormal_ker_eq_of_self_centralizing hCent
  let ψ : P ⧸ C →* MulAut C := QuotientGroup.lift C φ (by rw [hker])
  have hψ_inj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    dsimp [ψ]
    rw [QuotientGroup.ker_lift, hker]
    simp
  exact Nat.card_le_card_of_injective ψ hψ_inj

/-- **Isaacs Thm 6.12 setup**: if `C` is cyclic and self-centralizing in `P`, then
`P/C` is abelian.

The conjugation homomorphism `P → Aut(C)` has kernel `C_P(C)`.  Under the self-centralizing
hypothesis this kernel is exactly `C`, so it induces an embedding `P/C ↪ Aut(C)`.  Since the
automorphism group of a cyclic group is abelian, the quotient `P/C` is abelian. -/
theorem quotient_commutative_of_isCyclic_of_self_centralizing
    {P : Type*} [Group P]
    {C : Subgroup P} [C.Normal] (hC_cyclic : IsCyclic C)
    (hCent : Subgroup.centralizer (C : Set P) = C) :
    ∀ x y : P ⧸ C, x * y = y * x := by
  let φ : P →* MulAut C := MulAut.conjNormal (H := C)
  have hker : φ.ker = C := conjNormal_ker_eq_of_self_centralizing hCent
  let ψ : P ⧸ C →* MulAut C := QuotientGroup.lift C φ (by rw [hker])
  have hψ_inj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    dsimp [ψ]
    rw [QuotientGroup.ker_lift, hker]
    simp
  have : IsCyclic C := hC_cyclic
  let e := IsCyclic.mulAutMulEquiv C
  let : CommGroup (MulAut C) := e.toMonoidHom.commGroupOfInjective e.injective
  let : CommGroup (P ⧸ C) := ψ.commGroupOfInjective hψ_inj
  exact mul_comm

/-- **Isaacs Thm 6.12 setup**: from a proper maximal normal cyclic subgroup `C`, choose
the nonabelian normal subgroup `T` with `|T : C| = p`.

This packages the choice of `T/C` of order `p` in the proof of Theorem 6.12.  Ch.1
Lemma 1.23 supplies the normal intermediate subgroup, and maximality of `C` among normal
abelian subgroups makes `T` nonabelian. -/
theorem exists_normal_noncomm_relIndex_prime_of_maximal_normal_zpowers_lt_top
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P)
    {C : Subgroup P} [C.Normal] {c : P}
    (hC_eq : C = Subgroup.zpowers c)
    (hC_max : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False)
    (hC_lt_top : C < ⊤) :
    ∃ T : Subgroup P, T.Normal ∧ c ∈ T ∧ C ≤ T ∧ C.relIndex T = p ∧
      ¬ IsMulCommutative T := by
  obtain ⟨T, hT_normal, hC_lt_T, _hT_le_top, hC_rel⟩ :=
    OddOrder.Isaacs.Ch01.IsPGroup.exists_normal_index_eq_prime
      hP (N := C) (M := ⊤) hC_lt_top
  have hcC : c ∈ C := by
    rw [hC_eq]
    exact Subgroup.mem_zpowers c
  have hT_not_comm : ¬ IsMulCommutative T := by
    intro hT_comm
    exact hC_max T hT_normal hT_comm hC_lt_T
  exact ⟨T, hT_normal, hC_lt_T.le hcC, hC_lt_T.le, hC_rel, hT_not_comm⟩

/-- **Isaacs Thm 6.12 setup**: if `|T : C| = p` and `|C| ≠ 4`, then `|T| ≠ 8`.

This is the small cardinal step in the proof of Theorem 6.12: after excluding the
`|C| = 4` case, the chosen subgroup `T/C` of order `p` cannot have total order `8`. -/
theorem card_ne_eight_of_relIndex_prime_of_card_ne_four
    {P : Type*} [Group P] {p : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} (hC_le_T : C ≤ T) (hC_rel : C.relIndex T = p)
    (hC_card_ne : Nat.card C ≠ 4) :
    Nat.card T ≠ 8 := by
  intro hT_card
  let Csub : Subgroup T := C.subgroupOf T
  have hCsub_index : Csub.index = p := hC_rel
  have hquot_card : Nat.card (T ⧸ Csub) = p := by
    rw [← Subgroup.index_eq_card]
    exact hCsub_index
  have hCsub_card : Nat.card Csub = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_le_T).toEquiv
  have hsplit : Nat.card T = Nat.card (T ⧸ Csub) * Nat.card Csub :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Csub
  have hp_mul : p * Nat.card C = 8 := by
    rw [hquot_card, hCsub_card] at hsplit
    exact hsplit.symm.trans hT_card
  have hp_dvd : p ∣ 8 := ⟨Nat.card C, hp_mul.symm⟩
  have hp_eq_two : p = 2 :=
    Nat.prime_eq_prime_of_dvd_pow (m := 3) (p := p) (q := 2)
      (Fact.out : p.Prime) Nat.prime_two (by simpa using hp_dvd)
  rw [hp_eq_two] at hp_mul
  have hC_card : Nat.card C = 4 := by omega
  exact hC_card_ne hC_card

/-- **Isaacs Thm 6.12 setup**: if `C ≤ T` and `P/C` is abelian, then `T ⊴ P`.

This is the quotient-correspondence step used after choosing `T/C ≤ P/C`: in an abelian
quotient every subgroup is normal, and normality pulls back along the quotient map. -/
theorem normal_of_le_of_quotient_commutative
    {P : Type*} [Group P] {C T : Subgroup P} [C.Normal]
    (hC_le_T : C ≤ T) (hquot_comm : ∀ x y : P ⧸ C, x * y = y * x) :
    T.Normal := by
  let Q : Subgroup (P ⧸ C) := T.map (QuotientGroup.mk' C)
  have hQ_normal : Q.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hconj : g * n * g⁻¹ = n := by
      rw [hquot_comm g n, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
    exact hn
  have hcomap : Q.comap (QuotientGroup.mk' C) = T := by
    dsimp [Q]
    rw [QuotientGroup.comap_map_mk']
    exact sup_eq_right.mpr hC_le_T
  rw [← hcomap]
  exact hQ_normal.comap (QuotientGroup.mk' C)

/-- **Isaacs Thm 6.12 setup**: after choosing `T/C` of order `p`, a self-centralizing
`C` satisfies `Z(T) < C`.

The inclusion `Z(T) ≤ C` comes from self-centralizing: any central element of `T` centralizes
`C`.  It is strict because otherwise `T/C` is cyclic of prime order and central, forcing `T`
to be abelian. -/
theorem center_lt_subgroupOf_of_self_centralizing_of_relIndex_prime_of_not_isMulCommutative
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} [C.Normal]
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_rel : C.relIndex T = p) (hT_not_comm : ¬ IsMulCommutative T) :
    Subgroup.center T < C.subgroupOf T := by
  have hZ_le_C : Subgroup.center T ≤ C.subgroupOf T := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    have hz_cent : ((z : T) : P) ∈ Subgroup.centralizer (C : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcomm_T :
          (⟨c, hC_le_T hc⟩ : T) * z = z * ⟨c, hC_le_T hc⟩ :=
        Subgroup.mem_center_iff.mp hz ⟨c, hC_le_T hc⟩
      exact congrArg Subtype.val hcomm_T
    simpa [hCent] using hz_cent
  have hne : Subgroup.center T ≠ C.subgroupOf T := by
    intro hEq
    have hCsub_normal : (C.subgroupOf T).Normal := inferInstance
    have h_card_quot : Nat.card (T ⧸ C.subgroupOf T) = p := by
      rw [← Subgroup.index_eq_card]
      simpa [Subgroup.relIndex] using hC_rel
    have : IsCyclic (T ⧸ C.subgroupOf T) := isCyclic_of_prime_card h_card_quot
    have hker_le : (QuotientGroup.mk' (C.subgroupOf T)).ker ≤ Subgroup.center T := by
      rw [QuotientGroup.ker_mk']
      exact le_of_eq hEq.symm
    have hT_comm : ∀ x y : T, x * y = y * x :=
      (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' (C.subgroupOf T)) hker_le).is_comm.comm
    exact hT_not_comm ⟨⟨hT_comm⟩⟩
  exact lt_of_le_of_ne hZ_le_C hne

/-- **Isaacs Thm 6.12 setup**: the relative-index computation used before applying
Lemma 6.15.

If `C.subgroupOf T` has index `p` in `T` and `Z(T)` has index `p` in `C.subgroupOf T`,
then `|T : Z(T)| = p²`. -/
theorem center_index_eq_prime_sq_of_subgroupOf_relIndex_prime
    {P : Type*} [Group P] {p : ℕ}
    {C T : Subgroup P}
    (hC_rel : C.relIndex T = p)
    (hZ_le_C : Subgroup.center T ≤ C.subgroupOf T)
    (hZ_rel : (Subgroup.center T).relIndex (C.subgroupOf T) = p) :
    (Subgroup.center T).index = p ^ 2 := by
  have hCsub_index : (C.subgroupOf T).index = p := by
    simpa [Subgroup.relIndex] using hC_rel
  have hmul :
      (Subgroup.center T).relIndex (C.subgroupOf T) * (C.subgroupOf T).index =
        (Subgroup.center T).index :=
    Subgroup.relIndex_mul_index hZ_le_C
  rw [hZ_rel, hCsub_index] at hmul
  simpa [pow_two] using hmul.symm

/-- **Isaacs Thm 6.12 setup**: if `C = ⟨c⟩` and `c^p ∈ Z(T)`, then
`|C : Z(T)| = p`.

The quotient `C / (Z(T) ∩ C)` is cyclic.  The image of `c` has `p`-th power `1`, so
the quotient cardinal divides `p`; because it is also a nontrivial quotient of a `p`-group,
`p` divides its cardinal. -/
theorem center_relIndex_zpowers_eq_prime_of_pow_mem_center
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hT : IsPGroup p T) {c : T}
    (hZ_lt_C : Subgroup.center T < Subgroup.zpowers c)
    (hcp : c ^ p ∈ Subgroup.center T) :
    (Subgroup.center T).relIndex (Subgroup.zpowers c) = p := by
  let C : Subgroup T := Subgroup.zpowers c
  let ZC : Subgroup C := (Subgroup.center T).subgroupOf C
  change (Subgroup.center T).relIndex C = p
  have hZC_le_center : ZC ≤ Subgroup.center C := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hz_center : ((z : C) : T) ∈ Subgroup.center T := by
      simpa [ZC, Subgroup.mem_subgroupOf] using hz
    exact Subgroup.mem_center_iff.mp hz_center ((x : C) : T)
  have hZC_normal : ZC.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn_center : n ∈ Subgroup.center C := hZC_le_center hn
    have hgn : g * n = n * g := Subgroup.mem_center_iff.mp hn_center g
    have hconj : g * n * g⁻¹ = n := by
      calc
        g * n * g⁻¹ = n * g * g⁻¹ := by rw [hgn]
        _ = n := by simp
    rwa [hconj]
  let Q := C ⧸ ZC
  have hC_cyclic : IsCyclic C := Subgroup.isCyclic_zpowers c
  have hQ_cyclic : IsCyclic Q :=
    isCyclic_of_surjective (QuotientGroup.mk' ZC) (QuotientGroup.mk'_surjective ZC)
  have hQ_exp_dvd : Monoid.exponent Q ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ZC q
    rw [← map_pow]
    refine (QuotientGroup.eq_one_iff (N := ZC) (x ^ p)).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    change ((x : T) ^ p) ∈ Subgroup.center T
    have hx_mem : (x : T) ∈ Subgroup.zpowers c := x.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx_mem
    have hxpow : (x : T) ^ p = (c ^ p) ^ k := by
      rw [← hk]
      calc
        (c ^ k) ^ p = (c ^ k) ^ (p : ℤ) := by rw [zpow_natCast]
        _ = c ^ (k * (p : ℤ)) := by rw [← zpow_mul]
        _ = c ^ ((p : ℤ) * k) := by rw [mul_comm]
        _ = (c ^ (p : ℤ)) ^ k := by rw [zpow_mul]
        _ = (c ^ p) ^ k := by rw [zpow_natCast]
    simpa [hxpow] using zpow_mem hcp k
  have hQ_card_dvd_p : Nat.card Q ∣ p := by
    have hcard_exp : Nat.card Q = Monoid.exponent Q :=
      (IsCyclic.exponent_eq_card (α := Q)).symm
    rw [hcard_exp]
    exact hQ_exp_dvd
  have hrel_card : (Subgroup.center T).relIndex C = Nat.card Q := by
    change ZC.index = Nat.card (C ⧸ ZC)
    rw [Subgroup.index_eq_card]
  have hrel_ne_one : (Subgroup.center T).relIndex C ≠ 1 := by
    intro hrel
    have hC_le_Z : C ≤ Subgroup.center T := Subgroup.relIndex_eq_one.mp hrel
    exact hZ_lt_C.ne (le_antisymm hZ_lt_C.le hC_le_Z)
  have hp_dvd_Q_card : p ∣ Nat.card Q := by
    have hQ_p : IsPGroup p Q := (hT.to_subgroup C).to_quotient ZC
    rcases hQ_p.card_eq_or_dvd with hQ_card_one | hdiv
    · exfalso
      exact hrel_ne_one (by rw [hrel_card, hQ_card_one])
    · exact hdiv
  rw [hrel_card]
  exact Nat.dvd_antisymm hQ_card_dvd_p hp_dvd_Q_card

end OddOrder.Isaacs.Ch06


