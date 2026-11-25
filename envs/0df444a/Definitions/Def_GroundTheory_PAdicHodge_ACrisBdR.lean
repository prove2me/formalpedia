-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR
-- name    : GroundTheory_PAdicHodge_ACrisBdR
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:28.614456+00:00
-- url     : https://prove2.me/theorems/8c21bcf0-e918-4023-b6d3-affa0d2998e6
-- title:
--   ACris Bd R
-- statement:
--   Definitions and structural lemmas for ACris Bd R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdR.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PrecompleteOfSurjective
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_acrisZero_eq_adjoin
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_dpow_mul_dpow
import Theorems.Thm_GroundTheory_PAdicHodge_AdicCompletion_mk_extendRingHom
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_p_pow_mul_mem_of_dvd
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mem_span_xi_pow_of_forall_mem_sup
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mem_span_xi_pow_of_p_pow_mul_mem
import Theorems.Thm_GroundTheory_PAdicHodge_smodEq_span_singleton_pow_iff
import Theorems.Thm_P2M_GroundTheory_Variant__N1_isPrecomplete_of_surjective_5aad9bc9b7f9
import Theorems.Thm_P2M_GroundTheory_Variant__N1_smodEq_span_singleton_pow_iff_1a3f4e200796

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.PAdicHodge
open _root_.WittVector
namespace ACris
section Span
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
def dpowSpan (ξ : AInf K p) : Submodule (AInf K p) 𝔸 :=
  Submodule.span (AInf K p) (Set.range fun n => dpow n ξ)
theorem dpow_mem_dpowSpan (ξ : AInf K p) (n : ℕ) : dpow n ξ ∈ dpowSpan ξ :=
  Submodule.subset_span ⟨n, rfl⟩
theorem one_mem_dpowSpan (ξ : AInf K p) : (1 : 𝔸) ∈ dpowSpan ξ := by
  rw [← dpow_zero ξ]
  exact dpow_mem_dpowSpan ξ 0
theorem mul_mem_dpowSpan (ξ : AInf K p) {a b : 𝔸} (ha : a ∈ dpowSpan ξ) (hb : b ∈ dpowSpan ξ) :
    a * b ∈ dpowSpan ξ := by
  have h : dpowSpan ξ * dpowSpan ξ ≤ dpowSpan ξ := by
    rw [dpowSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    show dpow i ξ * dpow j ξ ∈ _
    rw [dpow_mul_dpow, ← nsmul_eq_mul]
    exact Submodule.smul_of_tower_mem _ _ (dpow_mem_dpowSpan ξ (i + j))
  exact h (Submodule.mul_mem_mul ha hb)
theorem mem_dpowSpan {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) {y : 𝔸}
    (hy : y ∈ ACrisZero K p) : y ∈ dpowSpan ξ := by
  let S : Subalgebra (AInf K p) 𝔸 := (dpowSpan ξ).toSubalgebra (one_mem_dpowSpan ξ)
    (fun _ _ ha hb => mul_mem_dpowSpan ξ ha hb)
  have h : ACrisZero K p ≤ S := by
    rw [acrisZero_eq_adjoin hξ]
    apply Algebra.adjoin_le
    rintro _ ⟨n, rfl⟩
    exact dpow_mem_dpowSpan ξ n
  exact h hy
theorem exists_decomp_of_mem_dpowSpan {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) (m : ℕ)
    {y : 𝔸} (hy : y ∈ dpowSpan ξ) :
    ∃ y' ∈ ACrisZero K p, ∃ w : AInf K p, ∃ r : 𝔸,
      ((m - 1).factorial : 𝔸) * y' = algebraMap (AInf K p) 𝔸 w ∧
        y = y' + algebraMap (AInf K p) 𝔸 (ξ ^ m) * r := by
  have hξm : ξ ∈ RingHom.ker θ := hξ ▸ Ideal.mem_span_singleton_self ξ
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    show ∃ y' ∈ ACrisZero K p, ∃ w : AInf K p, ∃ r : 𝔸,
      ((m - 1).factorial : 𝔸) * y' = algebraMap (AInf K p) 𝔸 w ∧
        dpow n ξ = y' + algebraMap (AInf K p) 𝔸 (ξ ^ m) * r
    by_cases hn : n < m
    · refine ⟨dpow n ξ, dpow_mem hξm n, (((m - 1).factorial / n.factorial : ℕ) : AInf K p) * ξ ^ n,
        0, ?_, by simp⟩
      have hdvd : n.factorial ∣ (m - 1).factorial := Nat.factorial_dvd_factorial (by omega)
      rw [map_mul, map_natCast, map_pow, ← factorial_mul_dpow, ← mul_assoc, ← Nat.cast_mul,
        Nat.div_mul_cancel hdvd]
    · refine ⟨0, zero_mem _, 0, Ring.inverse (n.factorial : 𝔸) *
        algebraMap (AInf K p) 𝔸 ξ ^ (n - m), by simp, ?_⟩
      rw [zero_add, show dpow n ξ = Ring.inverse (n.factorial : 𝔸) * algebraMap (AInf K p) 𝔸 ξ ^ n
        from rfl, map_pow, ← mul_assoc, mul_comm (algebraMap (AInf K p) 𝔸 ξ ^ m),
        mul_assoc, ← pow_add, Nat.add_sub_cancel' (not_lt.1 hn)]
  | zero => exact ⟨0, zero_mem _, 0, 0, by simp, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨x', hx', wx, rx, hwx, hrx⟩ := hx
    obtain ⟨z', hz', wz, rz, hwz, hrz⟩ := hz
    exact ⟨x' + z', add_mem hx' hz', wx + wz, rx + rz, by rw [mul_add, hwx, hwz, map_add],
      by rw [hrx, hrz]; ring⟩
  | smul a x _ hx =>
    obtain ⟨x', hx', wx, rx, hwx, hrx⟩ := hx
    refine ⟨algebraMap (AInf K p) 𝔸 a * x', Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) hx',
      a * wx, algebraMap (AInf K p) 𝔸 a * rx, ?_, ?_⟩
    · rw [map_mul, ← hwx]; ring
    · rw [Algebra.smul_def, hrx]; ring
theorem exists_decomp {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) (m : ℕ) {y : 𝔸}
    (hy : y ∈ ACrisZero K p) :
    ∃ y' ∈ ACrisZero K p, ∃ w : AInf K p, ∃ r : 𝔸,
      ((m - 1).factorial : 𝔸) * y' = algebraMap (AInf K p) 𝔸 w ∧
        y = y' + algebraMap (AInf K p) 𝔸 (ξ ^ m) * r :=
  exists_decomp_of_mem_dpowSpan hξ m (mem_dpowSpan hξ hy)
end Span
section Complete
variable {Q : Type*} [CommRing Q] (p : ℕ)
theorem subring_pow_dvd_iff {S : Subring Q} (n : ℕ) (x : S) :
    (p : S) ^ n ∣ x ↔ ∃ s ∈ S, (x : Q) = (p : Q) ^ n * s := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, s.2, by simp⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨⟨s, hs⟩, Subtype.ext (by simpa using h)⟩
theorem isPrecomplete_of_surjective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (a : A) [IsPrecomplete (Ideal.span {a}) A] :
    IsPrecomplete (Ideal.span {f a}) B := by
  first
  | exact GroundTheory.Variant₂.N1.isPrecomplete_of_surjective ..
  | (apply GroundTheory.Variant₂.N1.isPrecomplete_of_surjective <;> assumption)
theorem isAdicComplete_of_pow_mul_mem {T S : Subring Q} (hTS : T ≤ S) (hp : IsUnit (p : Q)) (v : ℕ)
    (hv : ∀ s ∈ S, (p : Q) ^ v * s ∈ T) [hT : IsAdicComplete (Ideal.span {(p : T)}) T] :
    IsAdicComplete (Ideal.span {(p : S)}) S := by
  have hpv : IsUnit ((p : Q) ^ v) := hp.pow v

  have haus : IsHausdorff (Ideal.span {(p : S)}) S := by
    refine ⟨fun x hx => ?_⟩
    simp only [smodEq_span_singleton_pow_iff, sub_zero] at hx
    let y : T := ⟨(p : Q) ^ v * x, hv x x.2⟩
    have hy : y = 0 := by
      refine IsHausdorff.haus' (I := Ideal.span {(p : T)}) y fun n => ?_
      rw [smodEq_span_singleton_pow_iff, sub_zero, subring_pow_dvd_iff]
      obtain ⟨s, hs, h⟩ := (subring_pow_dvd_iff p n x).1 (hx n)
      exact ⟨(p : Q) ^ v * s, hv s hs, by simp only [y]; rw [h]; ring⟩
    apply Subtype.ext
    have h0 : (p : Q) ^ v * x = 0 := congrArg Subtype.val hy
    simpa using (hpv.mul_right_eq_zero).1 h0

  have prec : IsPrecomplete (Ideal.span {(p : S)}) S := by
    refine ⟨fun f hf => ?_⟩
    simp only [smodEq_span_singleton_pow_iff] at hf ⊢
    let g : ℕ → T := fun k => ⟨(p : Q) ^ v * f k, hv _ (f k).2⟩
    have hg : ∀ {m n}, m ≤ n → g m ≡ g n [SMOD (Ideal.span {(p : T)} ^ m • ⊤ : Submodule T T)] :=
      fun {m n} hmn => by
        rw [smodEq_span_singleton_pow_iff, subring_pow_dvd_iff]
        obtain ⟨s, hs, h⟩ := (subring_pow_dvd_iff p m _).1 (hf hmn)
        refine ⟨(p : Q) ^ v * s, hv s hs, ?_⟩
        simp only [g]
        push_cast at h ⊢
        rw [← mul_sub, h]; ring
    obtain ⟨LT, hLT⟩ := IsPrecomplete.prec (I := Ideal.span {(p : T)}) inferInstance hg
    have hLT' : ∀ k, ∃ t ∈ T, (p : Q) ^ v * f k - LT = (p : Q) ^ k * t := fun k => by
      obtain ⟨t, ht, h⟩ := (subring_pow_dvd_iff p k _).1
        ((smodEq_span_singleton_pow_iff _ _ _ _).1 (hLT k))
      exact ⟨t, ht, by simpa [g] using h⟩
    obtain ⟨tv, htv, hv'⟩ := hLT' v

    have hL : (f v : Q) - tv ∈ S := sub_mem (f v).2 (hTS htv)
    refine ⟨⟨(f v : Q) - tv, hL⟩, fun k => ?_⟩
    rw [subring_pow_dvd_iff]
    obtain ⟨t, ht, h⟩ := hLT' (k + v)
    obtain ⟨s, hs, hs'⟩ := (subring_pow_dvd_iff p k _).1 (hf (Nat.le_add_right k v))
    refine ⟨s + t, add_mem hs (hTS ht), ?_⟩
    have e1 : (p : Q) ^ v * ((f (k + v) : Q) - ((f v : Q) - tv)) =
        (p : Q) ^ v * ((p : Q) ^ k * t) := by
      linear_combination h - hv'
    have e2 : (f (k + v) : Q) - ((f v : Q) - tv) = (p : Q) ^ k * t := hpv.mul_left_cancel e1
    push_cast at hs' ⊢
    linear_combination hs' + e2
  exact ⟨⟩
end Complete
section ExtendComp
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
theorem _root_.GroundTheory.PAdicHodge.AdicCompletion.extendRingHom_comp (J : Ideal A) (I : Ideal B)
    (I' : Ideal C) [IsAdicComplete I B] [IsAdicComplete I' C] (f : A →+* B) (hf : J ≤ I.comap f)
    (g : B →+* C) (hg : I ≤ I'.comap g) :
    g.comp (AdicCompletion.extendRingHom J I f hf) =
      AdicCompletion.extendRingHom J I' (g.comp f)
        (hf.trans (by rw [← Ideal.comap_comap]; exact Ideal.comap_mono hg)) := by
  apply DFunLike.coe_injective
  refine IsHausdorff.funext' I' fun n x => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (_root_.AdicCompletion.evalₐ J n x)
  have h1 : Ideal.Quotient.mk (I ^ n) (AdicCompletion.extendRingHom J I f hf x) =
      Ideal.Quotient.mk (I ^ n) (f a) := by
    rw [AdicCompletion.mk_extendRingHom, ← ha, Ideal.quotientMap_mk]
  have h2 := Ideal.Quotient.eq.1 h1
  have h3 : g (AdicCompletion.extendRingHom J I f hf x) - g (f a) ∈ I' ^ n := by
    rw [← map_sub]
    exact (Ideal.pow_right_mono hg n).trans (Ideal.le_comap_pow g n) h2
  rw [RingHom.coe_comp, Function.comp_apply, AdicCompletion.mk_extendRingHom, ← ha,
    Ideal.quotientMap_mk, Ideal.Quotient.eq.2 h3]
  rfl
end ExtendComp
section Quot
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
variable (K p) in

abbrev kerAway : Ideal 𝔸 := RingHom.ker (fontaineThetaInvertP (normInteger K) p)
variable (K p) in

abbrev xiGen : AInf K p := IsPerfectoidField.kerThetaGenerator K p
theorem ker_eq_span_xiGen : RingHom.ker θ = Ideal.span {xiGen K p} :=
  IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator K p
theorem kerAway_pow (m : ℕ) :
    kerAway K p ^ m = Ideal.span {algebraMap (AInf K p) 𝔸 (xiGen K p ^ m)} := by
  rw [kerAway, ker_fontaineThetaInvertP ker_eq_span_xiGen, Ideal.span_singleton_pow, map_pow]
theorem mk_eq_zero_iff (m : ℕ) (a : 𝔸) :
    Ideal.Quotient.mk (kerAway K p ^ m) a = 0 ↔ algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) ∣ a := by
  rw [Ideal.Quotient.eq_zero_iff_mem, kerAway_pow, Ideal.mem_span_singleton]
theorem algebraMap_dvd_iff (m : ℕ) (w : AInf K p) :
    algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) ∣ algebraMap (AInf K p) 𝔸 w ↔
      w ∈ Ideal.span {xiGen K p ^ m} := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := IsPerfectoidField.exists_p_pow_mul_mem_of_dvd h
    exact IsPerfectoidField.mem_span_xi_pow_of_p_pow_mul_mem ker_eq_span_xiGen hs
  · intro h
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 h
    rw [map_mul]
    exact dvd_mul_right _ _
variable (K p) in

def latticeQ (m : ℕ) : Subring (𝔸 ⧸ kerAway K p ^ m) :=
  ((Ideal.Quotient.mk (kerAway K p ^ m)).comp (algebraMap (AInf K p) 𝔸)).range
variable (K p) in

def acrisQ (m : ℕ) : Subring (𝔸 ⧸ kerAway K p ^ m) :=
  (ACrisZero K p).toSubring.map (Ideal.Quotient.mk (kerAway K p ^ m))
theorem mk_mem_acrisQ (m : ℕ) {y : 𝔸} (hy : y ∈ ACrisZero K p) :
    Ideal.Quotient.mk (kerAway K p ^ m) y ∈ acrisQ K p m :=
  ⟨y, hy, rfl⟩
theorem latticeQ_le (m : ℕ) : latticeQ K p m ≤ acrisQ K p m := by
  rintro _ ⟨w, rfl⟩
  exact mk_mem_acrisQ m (Subalgebra.algebraMap_mem _ w)
theorem isUnit_p_quot (m : ℕ) : IsUnit (p : 𝔸 ⧸ kerAway K p ^ m) := by
  have := (isUnit_natCast (K := K) (p := p) hp.out.ne_zero).map (Ideal.Quotient.mk (kerAway K p ^ m))
  rwa [map_natCast] at this
theorem pow_mul_mem_latticeQ (m : ℕ) :
    ∀ s ∈ acrisQ K p m, (p : 𝔸 ⧸ kerAway K p ^ m) ^ ((m - 1).factorial.factorization p) * s ∈
      latticeQ K p m := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨y', -, w, r, hw, rfl⟩ := exists_decomp ker_eq_span_xiGen m hy
  set v := (m - 1).factorial.factorization p
  have hcop : (ordCompl[p] (m - 1).factorial).Coprime p :=
    Nat.coprime_comm.mp (Nat.coprime_ordCompl hp.out (Nat.factorial_ne_zero _))
  have hu := WittVector.isUnit_natCast_of_coprime (R := PreTilt (normInteger K) p) hcop
  refine ⟨↑hu.unit⁻¹ * w, ?_⟩
  have hfac : ((p : 𝔸) ^ v * ((ordCompl[p] (m - 1).factorial : ℕ) : 𝔸)) = ((m - 1).factorial : 𝔸) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  have hinv : algebraMap (AInf K p) 𝔸 ↑hu.unit⁻¹ * ((ordCompl[p] (m - 1).factorial : ℕ) : 𝔸) = 1 := by
    rw [← map_natCast (algebraMap (AInf K p) 𝔸), ← map_mul, mul_comm, IsUnit.mul_val_inv, map_one]
  have hz : Ideal.Quotient.mk (kerAway K p ^ m) (algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) * r) = 0 := by
    rw [mk_eq_zero_iff]; exact dvd_mul_right _ _
  have hcalc : algebraMap (AInf K p) 𝔸 (↑hu.unit⁻¹ * w) = (p : 𝔸) ^ v * y' := by
    rw [map_mul]
    calc algebraMap (AInf K p) 𝔸 ↑hu.unit⁻¹ * algebraMap (AInf K p) 𝔸 w
        = algebraMap (AInf K p) 𝔸 ↑hu.unit⁻¹ * (((m - 1).factorial : 𝔸) * y') := by rw [hw]
      _ = (algebraMap (AInf K p) 𝔸 ↑hu.unit⁻¹ * ((ordCompl[p] (m - 1).factorial : ℕ) : 𝔸)) *
          ((p : 𝔸) ^ v * y') := by rw [← hfac]; ring
      _ = (p : 𝔸) ^ v * y' := by rw [hinv, one_mul]
  show Ideal.Quotient.mk _ (algebraMap (AInf K p) 𝔸 (↑hu.unit⁻¹ * w)) = _
  rw [hcalc, map_mul, map_pow, map_natCast, map_add, hz, add_zero]
variable (K p) in

instance isAdicComplete_latticeQ (m : ℕ) :
    IsAdicComplete (Ideal.span {(p : latticeQ K p m)}) (latticeQ K p m) := by
  set f := (Ideal.Quotient.mk (kerAway K p ^ m)).comp (algebraMap (AInf K p) 𝔸)
  haveI hprec : IsPrecomplete (Ideal.span {(p : latticeQ K p m)}) (latticeQ K p m) := by
    have := isPrecomplete_of_surjective f.rangeRestrict f.rangeRestrict_surjective (p : AInf K p)
    rwa [map_natCast] at this
  haveI haus : IsHausdorff (Ideal.span {(p : latticeQ K p m)}) (latticeQ K p m) := by
    refine ⟨fun x hx => ?_⟩
    simp only [smodEq_span_singleton_pow_iff, sub_zero] at hx
    obtain ⟨w, hw⟩ := x.2
    have hmem : ∀ n : ℕ, w ∈ Ideal.span {(p : AInf K p) ^ n} ⊔ Ideal.span {xiGen K p ^ m} := by
      intro n
      obtain ⟨s, hs, h⟩ := (subring_pow_dvd_iff p n x).1 (hx n)
      obtain ⟨wn, rfl⟩ := hs
      have h0 : f (w - (p : AInf K p) ^ n * wn) = 0 := by
        rw [map_sub, map_mul, map_pow, map_natCast, hw, h, sub_self]
      rw [RingHom.comp_apply, mk_eq_zero_iff, algebraMap_dvd_iff] at h0
      have := Submodule.add_mem_sup (Ideal.mul_mem_right wn (Ideal.span {(p : AInf K p) ^ n})
        (Ideal.mem_span_singleton_self ((p : AInf K p) ^ n))) h0
      rwa [add_sub_cancel] at this
    have := IsPerfectoidField.mem_span_xi_pow_of_forall_mem_sup ker_eq_span_xiGen hmem
    apply Subtype.ext
    rw [← hw, ZeroMemClass.coe_zero, RingHom.comp_apply, mk_eq_zero_iff]
    exact (algebraMap_dvd_iff m w).2 this
  exact ⟨⟩
variable (K p) in

instance isAdicComplete_acrisQ (m : ℕ) :
    IsAdicComplete (Ideal.span {(p : acrisQ K p m)}) (acrisQ K p m) :=
  isAdicComplete_of_pow_mul_mem p (latticeQ_le m) (isUnit_p_quot m) _ (pow_mul_mem_latticeQ m)
end Quot
section Iota
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
variable (K p) in

def iotaZero (m : ℕ) : ACrisZero K p →+* acrisQ K p m :=
  ((Ideal.Quotient.mk (kerAway K p ^ m)).comp (ACrisZero K p).val.toRingHom).codRestrict
    (acrisQ K p m) fun y => mk_mem_acrisQ m y.2
theorem span_p_le_comap_iotaZero (m : ℕ) :
    Ideal.span {(p : ACrisZero K p)} ≤ (Ideal.span {(p : acrisQ K p m)}).comap (iotaZero K p m) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _
variable (K p) in

def embedding₂ (m : ℕ) : ACris K p →+* acrisQ K p m :=
  AdicCompletion.extendRingHom _ _ (iotaZero K p m) (span_p_le_comap_iotaZero m)
variable (K p) in

def iotaQ (m : ℕ) : ACris K p →+* 𝔸 ⧸ kerAway K p ^ m :=
  (acrisQ K p m).subtype.comp (embedding₂ K p m)
def acrisQFactor {m n : ℕ} (hle : m ≤ n) : acrisQ K p n →+* acrisQ K p m :=
  ((Ideal.Quotient.factorPow (kerAway K p) hle).comp (acrisQ K p n).subtype).codRestrict
    (acrisQ K p m) fun s => by
      obtain ⟨y, hy, hys⟩ := s.2
      rw [RingHom.comp_apply, Subring.subtype_apply, ← hys]
      exact ⟨y, hy, rfl⟩
theorem acrisQFactor_comp_iotaZero {m n : ℕ} (hle : m ≤ n) :
    (acrisQFactor hle).comp (iotaZero K p n) = iotaZero K p m := by
  ext y
  rfl
theorem iotaQ_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (kerAway K p) hle).comp (iotaQ K p n) = iotaQ K p m := by
  have hg : Ideal.span {(p : acrisQ K p n)} ≤
      (Ideal.span {(p : acrisQ K p m)}).comap (acrisQFactor (K := K) hle) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  have h := AdicCompletion.extendRingHom_comp _ _ _ (iotaZero K p n) (span_p_le_comap_iotaZero n)
    (acrisQFactor hle) hg
  simp only [acrisQFactor_comp_iotaZero] at h
  rw [iotaQ, iotaQ, embedding₂, embedding₂, ← h]
  rfl
variable (K p) in

def iota : ACris K p →+* BDeRhamPlus (normInteger K) p :=
  _root_.AdicCompletion.liftRingHom (kerAway K p) (iotaQ K p) fun hle => iotaQ_compat hle
end Iota
end ACris
end GroundTheory.PAdicHodge


