-- Prove2me | solution 1 for AddCommGroup.finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/e1b83325-fffd-5e33-b5bf-8ef0dafcaef7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P2mTorsionRank

open Function

theorem exists_linear_lt_pow (q : ℕ) (hq : 2 ≤ q) (r c : ℕ) : ∃ k : ℕ, r * k + c < q ^ k := by
  set m := r + c + 1 with hm
  refine ⟨3 * m, ?_⟩
  have h1 : m + 1 ≤ 2 ^ m := Nat.succ_le_of_lt m.lt_two_pow_self
  have h2 : (m + 1) ^ 3 ≤ (2 ^ m) ^ 3 := Nat.pow_le_pow_left h1 3
  have h3 : (2 ^ m) ^ 3 = 2 ^ (3 * m) := by rw [← pow_mul, mul_comm]
  have h4 : 2 ^ (3 * m) ≤ q ^ (3 * m) := Nat.pow_le_pow_left hq _
  have hr : r ≤ m := by omega
  have hc : c ≤ m := by omega
  have h6 : r * (3 * m) + c ≤ 3 * m * m + m := by
    have h := Nat.mul_le_mul_right (3 * m) hr
    have h' : m * (3 * m) = 3 * m * m := by ring
    rw [h'] at h
    exact Nat.add_le_add h hc
  have h7 : 3 * m * m + m < (m + 1) ^ 3 := by
    have hA : (m + 1) ^ 3 = m * m * m + (3 * m * m + 3 * m + 1) := by ring
    rw [hA]
    calc 3 * m * m + m < 3 * m * m + 3 * m + 1 := by omega
      _ ≤ m * m * m + (3 * m * m + 3 * m + 1) := Nat.le_add_left _ _
  calc r * (3 * m) + c ≤ 3 * m * m + m := h6
    _ < (m + 1) ^ 3 := h7
    _ ≤ (2 ^ m) ^ 3 := h2
    _ = 2 ^ (3 * m) := h3
    _ ≤ q ^ (3 * m) := h4

section VectorSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pow_add_apply (ν : V →ₗ[K] V) (n m : ℕ) (x : V) : (ν ^ (n + m)) x = (ν ^ m) ((ν ^ n) x) := by
  rw [add_comm, pow_add, Module.End.mul_apply]

theorem ker_pow_mono (ν : V →ₗ[K] V) {n m : ℕ} (h : n ≤ m) :
    LinearMap.ker (ν ^ n) ≤ LinearMap.ker (ν ^ m) := by
  intro x hx
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [LinearMap.mem_ker] at hx ⊢
  rw [pow_add_apply, hx, map_zero]

theorem ker_pow_eq_of_ker_pow_eq (ν : V →ₗ[K] V) {n : ℕ}
    (h : LinearMap.ker (ν ^ n) = LinearMap.ker (ν ^ (n + 1))) (m : ℕ) :
    LinearMap.ker (ν ^ (n + m)) = LinearMap.ker (ν ^ n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      have h1 : ν x ∈ LinearMap.ker (ν ^ (n + m)) := by
        rw [LinearMap.mem_ker]
        have : (ν ^ (n + m + 1)) x = (ν ^ (n + m)) (ν x) := by
          rw [pow_succ, Module.End.mul_apply]
        rw [← this]
        exact hx
      rw [ih, LinearMap.mem_ker] at h1
      have h2 : x ∈ LinearMap.ker (ν ^ (n + 1)) := by
        rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, h1]
      rw [← h] at h2
      exact h2
    · exact ker_pow_mono ν (by omega)

variable [Finite K]

theorem finite_of_exhaust_ker_pow (ν : V →ₗ[K] V) (r c : ℕ)
    (hexh : ∀ x : V, ∃ k : ℕ, (ν ^ Nat.card K ^ k) x = 0)
    (hfin : ∀ k : ℕ, Finite (LinearMap.ker (ν ^ Nat.card K ^ k)))
    (hle : ∀ k : ℕ, Nat.card (LinearMap.ker (ν ^ Nat.card K ^ k)) ≤ Nat.card K ^ (r * k + c)) :
    Finite V := by
  set q := Nat.card K with hqdef
  have hq : 1 < q := Finite.one_lt_card

  have hfin' : ∀ n : ℕ, Finite (LinearMap.ker (ν ^ n)) := by
    intro n
    have hle' : LinearMap.ker (ν ^ n) ≤ LinearMap.ker (ν ^ q ^ n) :=
      ker_pow_mono ν (Nat.lt_pow_self hq).le
    haveI := hfin n
    exact Finite.of_injective (Submodule.inclusion hle') (Submodule.inclusion_injective hle')
  by_cases hstab : ∃ n : ℕ, LinearMap.ker (ν ^ n) = LinearMap.ker (ν ^ (n + 1))
  · obtain ⟨n, hn⟩ := hstab
    have hall : ∀ x : V, x ∈ LinearMap.ker (ν ^ n) := by
      intro x
      obtain ⟨k, hk⟩ := hexh x
      have h1 : x ∈ LinearMap.ker (ν ^ (n + q ^ k)) :=
        ker_pow_mono ν (Nat.le_add_left _ _) (LinearMap.mem_ker.mpr hk)
      rwa [ker_pow_eq_of_ker_pow_eq ν hn] at h1
    haveI := hfin' n
    exact Finite.of_surjective (fun x : LinearMap.ker (ν ^ n) => (x : V))
      (fun x => ⟨⟨x, hall x⟩, rfl⟩)
  · exfalso
    push Not at hstab
    have hlt : ∀ n : ℕ, LinearMap.ker (ν ^ n) < LinearMap.ker (ν ^ (n + 1)) := fun n =>
      lt_of_le_of_ne (ker_pow_mono ν (Nat.le_succ n)) (hstab n)
    have hdim : ∀ n : ℕ, n ≤ Module.finrank K (LinearMap.ker (ν ^ n)) := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
        haveI := hfin' (n + 1)
        haveI : Module.Finite K (LinearMap.ker (ν ^ (n + 1))) := Module.Finite.of_finite
        have := Submodule.finrank_lt_finrank_of_lt (hlt n)
        omega
    have hcard : ∀ k : ℕ, q ^ q ^ k ≤ q ^ (r * k + c) := by
      intro k
      haveI := hfin (q ^ k)
      haveI : Module.Finite K (LinearMap.ker (ν ^ q ^ k)) := Module.Finite.of_finite
      calc q ^ q ^ k ≤ q ^ Module.finrank K (LinearMap.ker (ν ^ q ^ k)) :=
            Nat.pow_le_pow_right hq.le (hdim _)
        _ = Nat.card (LinearMap.ker (ν ^ q ^ k)) := by
            rw [Module.natCard_eq_pow_finrank (K := K)]
        _ ≤ q ^ (r * k + c) := hle k
    obtain ⟨k, hk⟩ := exists_linear_lt_pow q hq r c
    have h1 := (Nat.pow_le_pow_iff_right hq).mp (hcard k)
    have h2 : q ^ k ≤ r * k + c := h1
    have h3 : k < q ^ k := Nat.lt_pow_self hq
    omega

end VectorSpace

section Group

variable {A : Type*} [AddCommGroup A] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (τ : A →+ A)

variable (A) in

def L (n : ℕ) : AddSubgroup A where
  carrier := {x | ℓ ^ n • x = 0}
  zero_mem' := smul_zero _
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [smul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [smul_neg, ha, neg_zero]

variable {ℓ} in
theorem mem_L {n : ℕ} {x : A} : x ∈ L A ℓ n ↔ ℓ ^ n • x = 0 := Iff.rfl

theorem L_mono (n : ℕ) : L A ℓ n ≤ L A ℓ (n + 1) := by
  intro x hx
  rw [mem_L] at hx ⊢
  rw [pow_succ', mul_smul, hx, smul_zero]

theorem L_zero : L A ℓ 0 = ⊥ := by
  ext x
  rw [mem_L, pow_zero, one_smul, AddSubgroup.mem_bot]

theorem mem_primaryComponent_of_mem_L {n : ℕ} {x : A} (hx : x ∈ L A ℓ n) :
    x ∈ AddCommGroup.primaryComponent A ℓ :=
  (AddCommGroup.mem_primaryComponent).mpr ⟨n, hx⟩

def τL (n : ℕ) : L A ℓ n →+ L A ℓ n where
  toFun x := ⟨τ (x : A), by rw [mem_L, ← map_nsmul, mem_L.mp x.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero τ)
  map_add' a b := Subtype.ext (map_add τ (a : A) (b : A))

theorem coe_τL_iterate (n m : ℕ) (x : L A ℓ n) :
    (((⇑(τL ℓ τ n))^[m] x : L A ℓ n) : A) = (⇑τ)^[m] x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

def iterHom : ℕ → (A →+ A)
  | 0 => AddMonoidHom.id A
  | n + 1 => (iterHom n).comp τ

theorem coe_iterHom (n : ℕ) : ⇑(iterHom τ n) = (⇑τ)^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x
    show iterHom τ n (τ x) = τ^[n + 1] x
    rw [ih, Function.iterate_succ_apply]

variable {ℓ τ} in
theorem iterate_fixed_mono {x : A} {k k' : ℕ} (hk : k ≤ k') (h : (⇑τ)^[ℓ ^ k] x = x) :
    (⇑τ)^[ℓ ^ k'] x = x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, Function.iterate_mul]
  exact Function.iterate_fixed h _

theorem finite_L_one (r : ℕ)
    (hexh : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ k : ℕ, (⇑τ)^[ℓ ^ k] x = x)
    (hfix : ∃ c : ℕ, ∀ k : ℕ,
      Finite {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ∧
      Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ≤
        ℓ ^ (r * k + c)) :
    Finite (L A ℓ 1) := by
  classical
  obtain ⟨c, hc⟩ := hfix
  by_cases hV : Subsingleton (L A ℓ 1)
  · infer_instance
  rw [not_subsingleton_iff_nontrivial] at hV
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩

  haveI : Module (ZMod ℓ) (L A ℓ 1) := AddCommGroup.zmodModule (fun x => Subtype.ext (by
    rw [AddSubgroupClass.coe_nsmul, ZeroMemClass.coe_zero]
    have := mem_L.mp x.2
    rwa [pow_one] at this))
  set T : (L A ℓ 1) →ₗ[ZMod ℓ] (L A ℓ 1) := (τL ℓ τ 1).toZModLinearMap ℓ with hTdef
  have hTcoe : ∀ x : (L A ℓ 1), T x = τL ℓ τ 1 x := fun x => rfl
  have hTpow : ∀ (m : ℕ) (x : (L A ℓ 1)), (((T ^ m) x : (L A ℓ 1)) : A) = (⇑τ)^[m] x := by
    intro m x
    rw [Module.End.pow_apply]
    have : (⇑T)^[m] x = (⇑(τL ℓ τ 1))^[m] x := by
      induction m generalizing x with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hTcoe, ih]
    rw [this, coe_τL_iterate]
  set ν : (L A ℓ 1) →ₗ[ZMod ℓ] (L A ℓ 1) := T - 1 with hνdef

  haveI : CharP (Module.End (ZMod ℓ) (L A ℓ 1)) ℓ :=
    charP_of_injective_algebraMap (algebraMap (ZMod ℓ) (Module.End (ZMod ℓ) (L A ℓ 1))).injective ℓ
  have hνpow : ∀ k : ℕ, ν ^ ℓ ^ k = T ^ ℓ ^ k - 1 := by
    intro k
    rw [hνdef, sub_pow_char_pow_of_commute ℓ k (Commute.one_right T), one_pow]
  have hker : ∀ (k : ℕ) (x : (L A ℓ 1)), (ν ^ ℓ ^ k) x = 0 ↔ (⇑τ)^[ℓ ^ k] (x : A) = x := by
    intro k x
    rw [hνpow, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← hTpow]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcardK : Nat.card (ZMod ℓ) = ℓ := Nat.card_zmod ℓ
  refine finite_of_exhaust_ker_pow (K := ZMod ℓ) ν r c ?_ ?_ ?_
  · intro x
    obtain ⟨k, hk⟩ := hexh x (mem_primaryComponent_of_mem_L ℓ x.2)
    exact ⟨k, by rw [hcardK]; exact (hker k x).mpr hk⟩
  · intro k
    rw [hcardK]
    haveI := (hc k).1
    refine Finite.of_injective (fun x : LinearMap.ker (ν ^ ℓ ^ k) =>
      (⟨(x : (L A ℓ 1)), mem_primaryComponent_of_mem_L ℓ (x : (L A ℓ 1)).2,
        (hker k _).mp (LinearMap.mem_ker.mp x.2)⟩ :
        {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x})) ?_
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  · intro k
    rw [hcardK]
    haveI := (hc k).1
    refine le_trans (Nat.card_le_card_of_injective (fun x : LinearMap.ker (ν ^ ℓ ^ k) =>
      (⟨(x : (L A ℓ 1)), mem_primaryComponent_of_mem_L ℓ (x : (L A ℓ 1)).2,
        (hker k _).mp (LinearMap.mem_ker.mp x.2)⟩ :
        {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x})) ?_) (hc k).2
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)

variable {ℓ τ} in
theorem iterate_fixed_of_fixed_L_one {k₁ : ℕ} (hθ : ∀ x ∈ L A ℓ 1, (⇑τ)^[ℓ ^ k₁] x = x)
    (k : ℕ) : ∀ x ∈ L A ℓ (k + 1), (⇑τ)^[ℓ ^ (k₁ + k)] x = x := by
  induction k with
  | zero => intro x hx; rw [add_zero]; exact hθ x hx
  | succ k ih =>
    intro x hx
    set σ : A →+ A := iterHom τ (ℓ ^ (k₁ + k)) with hσdef
    have hσ : ⇑σ = (⇑τ)^[ℓ ^ (k₁ + k)] := coe_iterHom τ _

    set e := σ x - x with hedef
    have hℓx : ℓ • x ∈ L A ℓ (k + 1) := by
      rw [mem_L] at hx ⊢
      rw [← mul_smul, ← pow_succ, hx]
    have he1 : e ∈ L A ℓ 1 := by
      rw [mem_L, pow_one, hedef, smul_sub, ← map_nsmul, hσ, ih _ hℓx, sub_self]
    have hσe : σ e = e := by rw [hσ]; exact iterate_fixed_mono (Nat.le_add_right k₁ k) (hθ e he1)
    have hxe : σ x = x + e := by rw [hedef]; abel
    have hiter : ∀ i : ℕ, (⇑σ)^[i] x = x + i • e := by
      intro i
      induction i with
      | zero => rw [Function.iterate_zero_apply, zero_smul, add_zero]
      | succ i ih2 =>
        rw [Function.iterate_succ_apply', ih2, map_add, map_nsmul, hσe, hxe, add_smul, one_smul]
        abel
    have hℓe : ℓ • e = 0 := by have := mem_L.mp he1; rwa [pow_one] at this
    have h := hiter ℓ
    rw [hℓe, add_zero, hσ, ← Function.iterate_mul, ← pow_succ] at h
    exact h

variable (A) in

def layerMap (n : ℕ) : L A ℓ (n + 1) →+ L A ℓ 1 where
  toFun x := ⟨ℓ ^ n • (x : A), by
    rw [mem_L, pow_one, ← mul_smul, ← pow_succ', mem_L.mp x.2]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp [smul_add])

theorem ker_layerMap (n : ℕ) : (layerMap A ℓ n).ker = (L A ℓ n).addSubgroupOf (L A ℓ (n + 1)) := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_L]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem layerMap_surjective
    (hdiv : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ y : A, ℓ • y = x) (n : ℕ) :
    Function.Surjective (layerMap A ℓ n) := by

  have key : ∀ n : ℕ, ∀ v ∈ L A ℓ 1, ∃ y ∈ L A ℓ (n + 1), ℓ ^ n • y = v := by
    intro n
    induction n with
    | zero => intro v hv; exact ⟨v, hv, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
      intro v hv
      obtain ⟨y, hy, hyv⟩ := ih v hv
      obtain ⟨z, hz⟩ := hdiv y (mem_primaryComponent_of_mem_L ℓ hy)
      refine ⟨z, ?_, ?_⟩
      · rw [mem_L, pow_succ, mul_smul, hz]
        exact mem_L.mp hy
      · rw [pow_succ, mul_smul, hz, hyv]
  intro v
  obtain ⟨y, hy, hyv⟩ := key n v v.2
  exact ⟨⟨y, hy⟩, Subtype.ext hyv⟩

theorem finite_and_card_L
    (hdiv : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ y : A, ℓ • y = x)
    (h1 : Finite (L A ℓ 1)) (n : ℕ) :
    Finite (L A ℓ n) ∧ Nat.card (L A ℓ n) = Nat.card (L A ℓ 1) ^ n := by
  induction n with
  | zero =>
    rw [L_zero, pow_zero, AddSubgroup.card_bot]
    exact ⟨Nat.finite_of_card_ne_zero (by rw [AddSubgroup.card_bot]; exact one_ne_zero), rfl⟩
  | succ n ih =>
    obtain ⟨hfin, hcard⟩ := ih
    set f := layerMap A ℓ n with hfdef
    have hsurj := layerMap_surjective ℓ hdiv n
    have eQ : (L A ℓ (n + 1) ⧸ f.ker) ≃ L A ℓ 1 :=
      (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
    have eK : f.ker ≃ L A ℓ n := by
      rw [hfdef, ker_layerMap]
      exact (AddSubgroup.addSubgroupOfEquivOfLe (L_mono ℓ n)).toEquiv
    haveI : Finite (L A ℓ (n + 1) ⧸ f.ker) := Finite.of_equiv _ eQ.symm
    haveI : Finite f.ker := Finite.of_equiv _ eK.symm
    have hfin' : Finite (L A ℓ (n + 1)) :=
      Finite.of_equiv _ (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := f.ker)).symm
    refine ⟨hfin', ?_⟩
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker, Nat.card_congr eQ,
      Nat.card_congr eK, hcard, pow_succ']

theorem main (r : ℕ)
    (hexh : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ k : ℕ, (⇑τ)^[ℓ ^ k] x = x)
    (hfix : ∃ c : ℕ, ∀ k : ℕ,
      Finite {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ∧
      Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ≤
        ℓ ^ (r * k + c))
    (hdiv : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ y : A, ℓ • y = x) :
    Finite (L A ℓ 1) ∧ Nat.card (L A ℓ 1) ≤ ℓ ^ r := by
  classical
  have hV : Finite (L A ℓ 1) := finite_L_one ℓ τ r hexh hfix
  obtain ⟨c, hc⟩ := hfix
  refine ⟨hV, ?_⟩
  haveI := hV

  choose kx hkx using fun x : L A ℓ 1 => hexh x (mem_primaryComponent_of_mem_L ℓ x.2)
  obtain ⟨k₁, hk₁⟩ := (Set.finite_range kx).bddAbove
  have hθ : ∀ x ∈ L A ℓ 1, (⇑τ)^[ℓ ^ k₁] x = x := fun x hx =>
    iterate_fixed_mono (hk₁ ⟨⟨x, hx⟩, rfl⟩) (hkx ⟨x, hx⟩)

  have hineq : ∀ k : ℕ, Nat.card (L A ℓ 1) ^ (k + 1) ≤ ℓ ^ (r * (k₁ + k) + c) := by
    intro k
    obtain ⟨_, hcard⟩ := finite_and_card_L ℓ hdiv hV (k + 1)
    rw [← hcard]
    haveI := (hc (k₁ + k)).1
    refine le_trans (Nat.card_le_card_of_injective (fun x : L A ℓ (k + 1) =>
      (⟨(x : A), mem_primaryComponent_of_mem_L ℓ x.2, iterate_fixed_of_fixed_L_one hθ k x x.2⟩ :
        {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ (k₁ + k)] x = x})) ?_)
      (hc (k₁ + k)).2
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext this

  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : Module (ZMod ℓ) (L A ℓ 1) := AddCommGroup.zmodModule (fun x => Subtype.ext (by
    rw [AddSubgroupClass.coe_nsmul, ZeroMemClass.coe_zero]
    have := mem_L.mp x.2
    rwa [pow_one] at this))
  haveI : Module.Finite (ZMod ℓ) (L A ℓ 1) := Module.Finite.of_finite
  set s := Module.finrank (ZMod ℓ) (L A ℓ 1) with hsdef
  have hcardV : Nat.card (L A ℓ 1) = ℓ ^ s := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := L A ℓ 1)
    rwa [Nat.card_zmod] at h
  rw [hcardV]
  have hℓ1 : 1 < ℓ := hℓ.out.one_lt
  refine Nat.pow_le_pow_right hℓ.out.pos ?_
  have hsk : ∀ k : ℕ, s * (k + 1) ≤ r * (k₁ + k) + c := by
    intro k
    have h := hineq k
    rw [hcardV, ← pow_mul] at h
    exact (Nat.pow_le_pow_iff_right hℓ1).mp h
  by_contra hsr
  push Not at hsr
  have h := hsk (r * k₁ + c)
  have h' : (r + 1) * (r * k₁ + c + 1) ≤ s * (r * k₁ + c + 1) :=
    Nat.mul_le_mul_right _ hsr
  nlinarith

end Group

end P2mTorsionRank

theorem solution
    {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (τ : A →+ A)
    (hexh : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ k : ℕ, (⇑τ)^[ℓ ^ k] x = x)
    (hfix : ∃ c : ℕ, ∀ k : ℕ,
      Finite {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ∧
      Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ≤
        ℓ ^ (r * k + c))
    (hdiv : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ y : A, ℓ • y = x) :
    Finite (Submodule.torsionBy ℤ A (ℓ : ℤ)) ∧
      Nat.card (Submodule.torsionBy ℤ A (ℓ : ℤ)) ≤ ℓ ^ r := by
  obtain ⟨hfin, hle⟩ := P2mTorsionRank.main ℓ τ r hexh hfix hdiv
  have e : P2mTorsionRank.L A ℓ 1 ≃ Submodule.torsionBy ℤ A (ℓ : ℤ) :=
    Equiv.subtypeEquivRight (fun x => by
      show x ∈ P2mTorsionRank.L A ℓ 1 ↔ x ∈ Submodule.torsionBy ℤ A (ℓ : ℤ)
      rw [Submodule.mem_torsionBy_iff, P2mTorsionRank.mem_L, pow_one, ← natCast_zsmul])
  haveI := hfin
  exact ⟨Finite.of_equiv _ e, by rw [← Nat.card_congr e]; exact hle⟩

end S_AddCommGroup_finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible
end P2MW
export P2MW.S_AddCommGroup_finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible (solution)
