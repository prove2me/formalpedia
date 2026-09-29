-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.natCard_torsion_quotient_lap_mul_pow_le_pow_of_forall_exists_src_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3ebf5ee6-0889-5b70-a3bb-53877c421693

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_natCard_torsion_quotient_lap_mul_pow_le_pow_of_forall_exists_src_mem_iff

set_option autoImplicit false

namespace TropCnt

variable {V Seg : Type} [Fintype V] [DecidableEq V] [Fintype Seg] (ends : Seg → V × V)

def bd : (Seg → ℤ) →+ (V → ℤ) where
  toFun y := ∑ ε, y ε • ((Pi.single (ends ε).1 1 : V → ℤ) - Pi.single (ends ε).2 1)
  map_zero' := by simp
  map_add' y y' := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

def cobd : (V → ℤ) →+ (Seg → ℤ) where
  toFun x ε := x (ends ε).1 - x (ends ε).2
  map_zero' := by ext; simp
  map_add' x x' := by ext; simp only [Pi.add_apply]; ring

def cobdN (N : ℕ) : (V → ZMod N) →+ (Seg → ZMod N) where
  toFun x ε := x (ends ε).1 - x (ends ε).2
  map_zero' := by ext; simp
  map_add' x y := by ext; simp only [Pi.add_apply]; ring

def lapRow (v : V) : V → ℤ := ∑ ε,
  ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
   (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))

theorem lapRow_eq (v : V) : lapRow ends v = bd ends (cobd ends (Pi.single v 1)) := by
  classical
  unfold lapRow bd cobd
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  apply Finset.sum_congr rfl
  intro ε _
  by_cases h1 : (ends ε).1 = v <;> by_cases h2 : (ends ε).2 = v
  · subst h1; simp [h2]
  · subst h1; simp [h2]
  · subst h2; simp [h1]
  · simp [h1, h2]

theorem closure_range_lapRow :
    AddSubgroup.closure (Set.range (lapRow ends)) = ((bd ends).comp (cobd ends)).range := by
  classical
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨v, rfl⟩
    exact AddMonoidHom.mem_range.mpr ⟨Pi.single v 1, (lapRow_eq ends v).symm⟩
  · rintro _ ⟨x, rfl⟩

    have hx : x = ∑ v, x v • (Pi.single v 1 : V → ℤ) := by
      ext u; simp [Finset.sum_apply, Pi.single_apply]
    rw [hx, map_sum]
    refine AddSubgroup.sum_mem _ fun v _ => ?_
    rw [map_zsmul]
    have hv : bd ends (cobd ends (Pi.single v 1)) ∈ AddSubgroup.closure (Set.range (lapRow ends)) :=
      AddSubgroup.subset_closure ⟨v, lapRow_eq ends v⟩
    exact AddSubgroup.zsmul_mem _ hv _

def deg : (V → ℤ) →+ ℤ where
  toFun x := ∑ v, x v
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem deg_bd (y : Seg → ℤ) : deg (bd ends y) = 0 := by
  classical
  unfold deg bd
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro ε _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [Pi.single_apply, Finset.sum_ite_eq']

theorem range_bd_eq_ker_deg (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range) :
    (bd ends).range = (deg (V := V)).ker := by
  classical
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker]
    exact deg_bd ends y
  · intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    change ∑ v, x v = 0 at hx
    rcases isEmpty_or_nonempty V with hV | ⟨⟨v₀⟩⟩
    · have : x = 0 := funext fun v => (IsEmpty.false v).elim
      rw [this]; exact zero_mem _
    · have h1 : x = ∑ v, x v • (Pi.single v 1 : V → ℤ) := by
        ext u; simp [Finset.sum_apply, Pi.single_apply]
      have h2 : x = ∑ v, x v • ((Pi.single v 1 : V → ℤ) - Pi.single v₀ 1) := by
        simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hx, zero_smul, sub_zero]
        exact h1
      rw [h2]
      exact AddSubgroup.sum_mem _ fun v _ => AddSubgroup.zsmul_mem _ (hconn v v₀) _

section L4

def cobdQ : (V → ℚ) →ₗ[ℚ] (Seg → ℚ) where
  toFun x ε := x (ends ε).1 - x (ends ε).2
  map_add' x y := by ext; simp only [Pi.add_apply]; ring
  map_smul' c x := by ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def bdQ : (Seg → ℚ) →ₗ[ℚ] (V → ℚ) where
  toFun y := ∑ ε, y ε • ((Pi.single (ends ε).1 1 : V → ℚ) - Pi.single (ends ε).2 1)
  map_add' y y' := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

def degQ : (V → ℚ) →ₗ[ℚ] ℚ where
  toFun x := ∑ v, x v
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

theorem cobdQ_apply (x : V → ℚ) (ε : Seg) : cobdQ ends x ε = x (ends ε).1 - x (ends ε).2 := rfl

theorem bdQ_apply (y : Seg → ℚ) (v : V) :
    bdQ ends y v = ∑ ε, y ε * ((if v = (ends ε).1 then 1 else 0) - (if v = (ends ε).2 then 1 else 0)) := by
  unfold bdQ
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply,
    smul_eq_mul]

theorem degQ_apply (x : V → ℚ) : degQ (V := V) x = ∑ v, x v := rfl

theorem sum_mul_bdQ (x : V → ℚ) (y : Seg → ℚ) :
    ∑ v, x v * bdQ ends y v = ∑ ε, cobdQ ends x ε * y ε := by
  simp only [bdQ_apply, cobdQ_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ε _
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem degQ_bdQ (y : Seg → ℚ) : degQ (bdQ ends y) = 0 := by
  have := sum_mul_bdQ ends (fun _ => (1 : ℚ)) y
  simp only [one_mul, cobdQ_apply, sub_self, zero_mul, Finset.sum_const_zero] at this
  rw [degQ_apply]
  exact this

theorem cast_cobd (z : V → ℤ) : (fun ε => ((cobd ends z ε : ℤ) : ℚ)) = cobdQ ends (fun v => (z v : ℚ)) := by
  ext ε
  unfold cobd
  simp only [cobdQ_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_sub]

theorem cast_bd (y : Seg → ℤ) : (fun v => ((bd ends y v : ℤ) : ℚ)) = bdQ ends (fun ε => (y ε : ℚ)) := by
  ext v
  unfold bd
  rw [bdQ_apply]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply,
    smul_eq_mul]
  push_cast
  rfl

theorem ker_lapQ_le (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range)
    (v₀ : V) : LinearMap.ker ((bdQ ends).comp (cobdQ ends)) ≤ Submodule.span ℚ {fun _ : V => (1 : ℚ)} := by
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx

  have hsq : ∑ ε, cobdQ ends x ε * cobdQ ends x ε = 0 := by
    rw [← sum_mul_bdQ ends x (cobdQ ends x), hx]
    simp
  have hzero : ∀ ε, cobdQ ends x ε = 0 := by
    intro ε
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun ε _ => mul_self_nonneg (cobdQ ends x ε))).1 hsq ε
      (Finset.mem_univ ε)
    exact mul_self_eq_zero.1 h

  have hconst : ∀ u v, x u = x v := by
    intro u v
    obtain ⟨y, hy⟩ := hconn u v
    have h1 : ∑ w, x w * bdQ ends (fun ε => (y ε : ℚ)) w = 0 := by
      rw [sum_mul_bdQ]; simp [hzero]
    rw [← cast_bd ends y, hy] at h1
    simp only [Pi.sub_apply, Pi.single_apply, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact sub_eq_zero.1 h1
  rw [Submodule.mem_span_singleton]
  exact ⟨x v₀, funext fun v => by simp [hconst v v₀]⟩

theorem range_lapQ_eq (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range)
    (v₀ : V) : LinearMap.range ((bdQ ends).comp (cobdQ ends)) = LinearMap.ker (degQ (V := V)) := by
  classical
  have hle : LinearMap.range ((bdQ ends).comp (cobdQ ends)) ≤ LinearMap.ker (degQ (V := V)) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact degQ_bdQ ends _
  have hV : Module.finrank ℚ (V → ℚ) = Fintype.card V := Module.finrank_fintype_fun_eq_card ℚ

  have hdeg_surj : LinearMap.range (degQ (V := V)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨Pi.single v₀ c, ?_⟩
    rw [degQ_apply]
    simp [Pi.single_apply]
  have hker_deg : Module.finrank ℚ (LinearMap.ker (degQ (V := V))) + 1 = Fintype.card V := by
    have := LinearMap.finrank_range_add_finrank_ker (degQ (V := V))
    rw [hdeg_surj, finrank_top, Module.finrank_self, hV] at this
    omega

  have hkerL : Module.finrank ℚ (LinearMap.ker ((bdQ ends).comp (cobdQ ends))) ≤ 1 := by
    calc Module.finrank ℚ (LinearMap.ker ((bdQ ends).comp (cobdQ ends)))
        ≤ Module.finrank ℚ (Submodule.span ℚ {fun _ : V => (1 : ℚ)}) :=
          Submodule.finrank_mono (ker_lapQ_le ends hconn v₀)
      _ = 1 := finrank_span_singleton (by
          intro h
          have := congrFun h v₀
          simp at this)
  have hrange : Module.finrank ℚ (LinearMap.range ((bdQ ends).comp (cobdQ ends))) + 1 ≥ Fintype.card V := by
    have := LinearMap.finrank_range_add_finrank_ker ((bdQ ends).comp (cobdQ ends))
    rw [hV] at this
    omega
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

theorem exists_nsmul_mem_range_lap_of_deg_eq_zero
    (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range)
    (h : V → ℤ) (hh : deg (V := V) h = 0) :
    ∃ d : ℕ, 0 < d ∧ (d : ℤ) • h ∈ ((bd ends).comp (cobd ends)).range := by
  classical
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v₀⟩⟩
  · refine ⟨1, one_pos, ⟨0, ?_⟩⟩
    ext v; exact (IsEmpty.false v).elim

  have hmem : (fun v => (h v : ℚ)) ∈ LinearMap.ker (degQ (V := V)) := by
    rw [LinearMap.mem_ker, degQ_apply]
    have : ((∑ v, h v : ℤ) : ℚ) = 0 := by
      have hh' : ∑ v, h v = 0 := hh
      rw [hh']; simp
    push_cast at this
    exact this
  rw [← range_lapQ_eq ends hconn v₀] at hmem
  obtain ⟨q, hq⟩ := hmem
  rw [LinearMap.comp_apply] at hq

  set d : ℕ := ∏ v, (q v).den with hd
  have hdpos : 0 < d := Finset.prod_pos fun v _ => (q v).den_pos
  have hdvd : ∀ v, (q v).den ∣ d := fun v => Finset.dvd_prod_of_mem _ (Finset.mem_univ v)
  set z : V → ℤ := fun v => (q v).num * ((d / (q v).den : ℕ) : ℤ) with hz
  have hzq : (fun v => (z v : ℚ)) = (d : ℚ) • q := by
    ext v
    simp only [hz, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hdvd v) (by exact_mod_cast (q v).den_pos.ne'), ← Rat.mul_den_eq_num (q v)]
    field_simp
  refine ⟨d, hdpos, z, ?_⟩

  have hcast : (fun v => (((bd ends).comp (cobd ends) z) v : ℚ)) = fun v => ((((d : ℕ) : ℤ) • h) v : ℚ) := by
    rw [AddMonoidHom.comp_apply]
    rw [show (fun v => ((bd ends (cobd ends z) v : ℤ) : ℚ)) = bdQ ends (fun ε => (cobd ends z ε : ℚ)) from cast_bd ends _,
      cast_cobd ends z, hzq, LinearMap.map_smul, LinearMap.map_smul, hq]
    ext v
    simp [Pi.smul_apply]
  ext v
  have := congrFun hcast v
  exact_mod_cast this

theorem finite_range_bd_quotient
    (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range) :
    Finite (↥(bd ends).range ⧸ (((bd ends).comp (cobd ends)).range).addSubgroupOf (bd ends).range) := by
  classical

  haveI : AddGroup.FG (Seg → ℤ) := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI : AddGroup.FG ↥(bd ends).range := AddGroup.fg_of_surjective (AddMonoidHom.rangeRestrict_surjective (bd ends))
  haveI : AddGroup.FG (↥(bd ends).range ⧸ (((bd ends).comp (cobd ends)).range).addSubgroupOf (bd ends).range) :=
    QuotientAddGroup.fg _

  apply AddCommGroup.finite_of_fg_torsion
  intro g
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective g
  have hdeg : deg (V := V) x = 0 := by
    obtain ⟨y, rfl⟩ := hx; exact deg_bd ends y
  obtain ⟨d, hd, hmem⟩ := exists_nsmul_mem_range_lap_of_deg_eq_zero ends hconn x hdeg
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine ⟨d, hd, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  simpa [natCast_zsmul] using hmem

theorem exists_nsmul_mem_range_of_mem_ker_deg [Nonempty V]
    (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range) :
    ∃ d : ℕ, 0 < d ∧ ∀ h : V → ℤ, h ∈ (deg (V := V)).ker → (d : ℤ) • h ∈ ((bd ends).comp (cobd ends)).range := by
  classical
  haveI := finite_range_bd_quotient ends hconn
  set J := ↥(bd ends).range ⧸ (((bd ends).comp (cobd ends)).range).addSubgroupOf (bd ends).range
  refine ⟨Nat.card J, Nat.card_pos, fun h hh => ?_⟩
  have hh' : h ∈ (bd ends).range := by rw [range_bd_eq_ker_deg ends hconn]; exact hh
  have hz : (Nat.card J) • (QuotientAddGroup.mk ⟨h, hh'⟩ : J) = 0 := card_nsmul_eq_zero'
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hz
  simpa [natCast_zsmul] using hz

end L4

theorem deg_eq_zero_of_nsmul_mem (N : ℕ) (hN : 0 < N) (x : V → ℤ)
    (hx : (N : ℤ) • x ∈ ((bd ends).comp (cobd ends)).range) : deg x = 0 := by
  obtain ⟨y, hy⟩ := hx
  have := congrArg deg hy
  rw [AddMonoidHom.comp_apply, deg_bd, map_zsmul] at this
  exact (smul_eq_zero_iff_right (by exact_mod_cast hN.ne')).mp this.symm

theorem natCard_torsionBy_eq_natCard_quotient_range_nsmul (G : Type) [AddCommGroup G] [Finite G] (N : ℕ) (hN : 0 < N) :
    Nat.card {g : G // (N : ℤ) • g = 0} = Nat.card (G ⧸ (zsmulAddGroupHom N : G →+ G).range) := by
  set f : G →+ G := zsmulAddGroupHom N with hf
  have hker : Nat.card {g : G // (N : ℤ) • g = 0} = Nat.card f.ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [AddMonoidHom.mem_ker]
    rfl
  have h1 : Nat.card G = Nat.card (G ⧸ f.ker) * Nat.card f.ker := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h2 : Nat.card G = Nat.card (G ⧸ f.range) * Nat.card f.range := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h3 : Nat.card (G ⧸ f.ker) = Nat.card f.range := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  rw [hker]
  rw [h3] at h1
  rw [h1, mul_comm] at h2
  exact Nat.eq_of_mul_eq_mul_right hpos h2

theorem natCard_range_mul_of_cobd (V Seg : Type) [Fintype V] [DecidableEq V] [Fintype Seg] [Nonempty V]
    (ends : Seg → V × V) (N : ℕ) (hN : 0 < N)
    (hconn : ∀ x : V → ZMod N, (∀ ε, x (ends ε).1 = x (ends ε).2) → ∀ u v, x u = x v)
    (φ : (V → ZMod N) →+ (Seg → ZMod N)) (hφ : ∀ x ε, φ x ε = x (ends ε).1 - x (ends ε).2) :
    Nat.card φ.range * N = N ^ Fintype.card V := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  have hmem : ∀ x : V → ZMod N, x ∈ φ.ker ↔ ∀ ε, x (ends ε).1 = x (ends ε).2 := by
    intro x
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro h ε
      have := congrFun h ε
      rw [hφ, Pi.zero_apply] at this
      exact sub_eq_zero.1 this
    · intro h
      ext ε
      rw [hφ, Pi.zero_apply, sub_eq_zero]
      exact h ε
  let e : φ.ker ≃ ZMod N :=
    { toFun := fun x => (x : V → ZMod N) v₀
      invFun := fun c => ⟨fun _ => c, (hmem _).2 fun _ => rfl⟩
      left_inv := fun x => Subtype.ext (funext fun v => hconn _ ((hmem _).1 x.2) v₀ v)
      right_inv := fun c => rfl }
  have hkerN : Nat.card φ.ker = N := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, ZMod.card]
  have h1 : Nat.card (V → ZMod N) = Nat.card ((V → ZMod N) ⧸ φ.ker) * Nat.card φ.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h3 : Nat.card ((V → ZMod N) ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
  have hV : Nat.card (V → ZMod N) = N ^ Fintype.card V := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  rw [← hV, h1, h3, hkerN]

theorem natCard_range_cobd_zmod_mul (V Seg : Type) [Fintype V] [DecidableEq V] [Fintype Seg] [Nonempty V]
    (ends : Seg → V × V) (N : ℕ) (hN : 0 < N)
    (hconn : ∀ x : V → ZMod N, (∀ ε, x (ends ε).1 = x (ends ε).2) → ∀ u v, x u = x v) :
    Nat.card (AddMonoidHom.range
      ({ toFun := fun x : V → ZMod N => fun ε : Seg => x (ends ε).1 - x (ends ε).2,
         map_zero' := by ext; simp,
         map_add' := fun x y => by ext; simp only [Pi.add_apply]; ring } : (V → ZMod N) →+ (Seg → ZMod N))) * N =
      N ^ Fintype.card V :=
  natCard_range_mul_of_cobd V Seg ends N hN hconn _ (fun _ _ => rfl)

theorem natCard_quotient_range_cobd_zmod_mul (V Seg : Type) [Fintype V] [DecidableEq V] [Fintype Seg] [Nonempty V]
    (ends : Seg → V × V) (N : ℕ) (hN : 0 < N)
    (hconn : ∀ x : V → ZMod N, (∀ ε, x (ends ε).1 = x (ends ε).2) → ∀ u v, x u = x v) :
    Nat.card ((Seg → ZMod N) ⧸ AddMonoidHom.range
      ({ toFun := fun x : V → ZMod N => fun ε : Seg => x (ends ε).1 - x (ends ε).2,
         map_zero' := by ext; simp,
         map_add' := fun x y => by ext; simp only [Pi.add_apply]; ring } : (V → ZMod N) →+ (Seg → ZMod N))) *
        N ^ Fintype.card V = N ^ Fintype.card Seg * N := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  have hL7 := natCard_range_cobd_zmod_mul V Seg ends N hN hconn
  set R := AddMonoidHom.range
      ({ toFun := fun x : V → ZMod N => fun ε : Seg => x (ends ε).1 - x (ends ε).2,
         map_zero' := by ext; simp,
         map_add' := fun x y => by ext; simp only [Pi.add_apply]; ring } : (V → ZMod N) →+ (Seg → ZMod N)) with hR
  have h2 : Nat.card (Seg → ZMod N) = Nat.card ((Seg → ZMod N) ⧸ R) * Nat.card R :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have hS : Nat.card (Seg → ZMod N) = N ^ Fintype.card Seg := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  rw [← hL7, ← mul_assoc, ← h2, hS]

theorem finite_quotient_range_cobdN (N : ℕ) (hN : 0 < N) : Finite ((Seg → ZMod N) ⧸ (cobdN ends N).range) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  exact Finite.of_surjective _ (QuotientAddGroup.mk'_surjective _)

def castN (N : ℕ) : (Seg → ℤ) →+ (Seg → ZMod N) where
  toFun y ε := (y ε : ZMod N)
  map_zero' := by ext; simp
  map_add' y y' := by ext; simp

theorem castN_cobd (N : ℕ) (x : V → ℤ) :
    castN (Seg := Seg) N (cobd ends x) = cobdN ends N (fun v => (x v : ZMod N)) := by
  ext ε
  show ((cobd ends x ε : ℤ) : ZMod N) = _
  unfold cobd cobdN
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_sub]

theorem natCard_quotient_cobd_sup_nsmul_eq (N : ℕ) (hN : 0 < N) :
    Nat.card ((Seg → ℤ) ⧸ ((cobd ends).range ⊔ (zsmulAddGroupHom (N : ℤ) : (Seg → ℤ) →+ (Seg → ℤ)).range)) =
      Nat.card ((Seg → ZMod N) ⧸ (cobdN ends N).range) := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  let ρ : (Seg → ℤ) →+ (Seg → ZMod N) ⧸ (cobdN ends N).range :=
    (QuotientAddGroup.mk' (cobdN ends N).range).comp (castN (Seg := Seg) N)
  have hρ : ∀ y, ρ y = QuotientAddGroup.mk' (cobdN ends N).range (castN (Seg := Seg) N y) := fun _ => rfl
  have hρsurj : Function.Surjective ρ := by
    intro w
    obtain ⟨ybar, rfl⟩ := QuotientAddGroup.mk'_surjective (cobdN ends N).range w
    refine ⟨fun ε => ((ybar ε).val : ℤ), ?_⟩
    rw [hρ]
    congr 1
    ext ε
    show (((ybar ε).val : ℤ) : ZMod N) = ybar ε
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hker : ρ.ker = (cobd ends).range ⊔ (zsmulAddGroupHom (N : ℤ) : (Seg → ℤ) →+ (Seg → ℤ)).range := by
    apply le_antisymm
    · intro y hy
      rw [AddMonoidHom.mem_ker, hρ, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hy
      obtain ⟨xbar, hx⟩ := hy
      set x : V → ℤ := fun v => ((xbar v).val : ℤ) with hxdef
      have hxcast : (fun v => (x v : ZMod N)) = xbar := by
        ext v; show (((xbar v).val : ℤ) : ZMod N) = xbar v; rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      have hz : ∀ ε, ((N : ℕ) : ℤ) ∣ (y - cobd ends x) ε := by
        intro ε
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have h1 : castN (Seg := Seg) N (y - cobd ends x) = 0 := by
          rw [map_sub, castN_cobd, hxcast, hx, sub_self]
        exact congrFun h1 ε
      choose w hw using hz
      have hy' : y = cobd ends x + (N : ℤ) • (fun ε => w ε) := by
        ext ε
        have := hw ε
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [← this, Pi.sub_apply]; ring
      rw [hy']
      exact AddSubgroup.add_mem_sup ⟨x, rfl⟩ ⟨fun ε => w ε, rfl⟩
    · apply sup_le
      · rintro _ ⟨x, rfl⟩
        rw [AddMonoidHom.mem_ker, hρ, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, castN_cobd]
        exact ⟨_, rfl⟩
      · rintro _ ⟨y, rfl⟩
        rw [AddMonoidHom.mem_ker, hρ, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
        have : castN (Seg := Seg) N ((zsmulAddGroupHom (N : ℤ) : (Seg → ℤ) →+ (Seg → ℤ)) y) = 0 := by
          ext ε
          show (((N : ℤ) • y) ε : ZMod N) = 0
          rw [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
        rw [this]; exact zero_mem _
  rw [← hker]
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ρ hρsurj).toEquiv

theorem single_sub_single_ends_mem (ε : Seg) :
    (Pi.single (ends ε).1 1 : V → ℤ) - Pi.single (ends ε).2 1 ∈ (bd ends).range := by
  classical
  refine ⟨Pi.single ε 1, ?_⟩
  show ∑ ε', (Pi.single ε (1 : ℤ) : Seg → ℤ) ε' • ((Pi.single (ends ε').1 1 : V → ℤ) - Pi.single (ends ε').2 1) = _
  rw [Finset.sum_eq_single_of_mem ε (Finset.mem_univ _)
    (fun ε' _ h => by rw [Pi.single_eq_of_ne h, zero_smul])]
  rw [Pi.single_eq_same, one_smul]

theorem apply_eq_of_forall_ends {M : Type} [AddCommGroup M]
    (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range)
    (x : V → M) (hx : ∀ ε, x (ends ε).1 = x (ends ε).2) (u v : V) : x u = x v := by
  classical
  let P : (V → ℤ) →+ M :=
    { toFun := fun z => ∑ w, z w • x w
      map_zero' := by simp
      map_add' := fun a b => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib] }
  have hP1 : ∀ w₀ : V, P (Pi.single w₀ 1) = x w₀ := by
    intro w₀
    show ∑ w, (Pi.single w₀ (1 : ℤ) : V → ℤ) w • x w = x w₀
    rw [Finset.sum_eq_single_of_mem w₀ (Finset.mem_univ _)
      (fun w _ hw => by rw [Pi.single_eq_of_ne hw, zero_smul])]
    rw [Pi.single_eq_same, one_smul]
  have hPbd : ∀ y, P (bd ends y) = 0 := by
    intro y
    have hbdy : bd ends y = ∑ ε, y ε • ((Pi.single (ends ε).1 1 : V → ℤ) - Pi.single (ends ε).2 1) := rfl
    rw [hbdy, map_sum]
    refine Finset.sum_eq_zero fun ε _ => ?_
    rw [map_zsmul, map_sub, hP1, hP1, hx ε, sub_self, smul_zero]
  obtain ⟨y, hy⟩ := hconn u v
  have h := congrArg P hy
  rw [hPbd, map_sub, hP1, hP1] at h
  exact sub_eq_zero.mp h.symm

theorem mem_range_of_zsmul_eq_zero
    (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range)
    (N : ℕ) (hN : 0 < N) (x : (V → ℤ) ⧸ ((bd ends).comp (cobd ends)).range) (hx : (N : ℤ) • x = 0) :
    x ∈ ((QuotientAddGroup.mk' ((bd ends).comp (cobd ends)).range).comp (bd ends)).range := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hmem : (N : ℤ) • x ∈ ((bd ends).comp (cobd ends)).range := by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_zsmul]; exact hx
  have hker : x ∈ (deg (V := V)).ker := deg_eq_zero_of_nsmul_mem ends N hN x hmem
  rw [← range_bd_eq_ker_deg ends hconn] at hker
  obtain ⟨y, hy⟩ := hker
  exact ⟨y, by rw [AddMonoidHom.comp_apply, hy]; rfl⟩

theorem finite_range_mk_comp_bd
    (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range) :
    Finite ↥(((QuotientAddGroup.mk' ((bd ends).comp (cobd ends)).range).comp (bd ends)).range) := by
  classical
  haveI : AddGroup.FG (Seg → ℤ) := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI : AddGroup.FG ↥(((QuotientAddGroup.mk' ((bd ends).comp (cobd ends)).range).comp (bd ends)).range) :=
    AddGroup.fg_of_surjective (AddMonoidHom.rangeRestrict_surjective _)
  apply AddCommGroup.finite_of_fg_torsion
  rintro ⟨g, ⟨y, rfl⟩⟩
  obtain ⟨d, hd, hmem⟩ := exists_nsmul_mem_range_lap_of_deg_eq_zero ends hconn (bd ends y) (deg_bd ends y)
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine ⟨d, hd, Subtype.ext ?_⟩
  show d • ((QuotientAddGroup.mk' ((bd ends).comp (cobd ends)).range).comp (bd ends)) y = 0
  rw [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  simpa [natCast_zsmul] using hmem

theorem card_torsion_mul_pow_le [Nonempty V]
    (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range) (N : ℕ) (hN : 0 < N) :
    Finite {x : (V → ℤ) ⧸ ((bd ends).comp (cobd ends)).range // (N : ℤ) • x = 0} ∧
      Nat.card {x : (V → ℤ) ⧸ ((bd ends).comp (cobd ends)).range // (N : ℤ) • x = 0} * N ^ Fintype.card V ≤
        N ^ Fintype.card Seg * N := by
  classical
  set L : AddSubgroup (V → ℤ) := ((bd ends).comp (cobd ends)).range with hL
  set ψ : (Seg → ℤ) →+ (V → ℤ) ⧸ L := (QuotientAddGroup.mk' L).comp (bd ends) with hψ
  haveI hfin : Finite ↥ψ.range := finite_range_mk_comp_bd ends hconn

  let eKT : {x : (V → ℤ) ⧸ L // (N : ℤ) • x = 0} ≃ {g : ↥ψ.range // (N : ℤ) • g = 0} :=
    { toFun := fun x => ⟨⟨x.1, mem_range_of_zsmul_eq_zero ends hconn N hN x.1 x.2⟩, Subtype.ext x.2⟩
      invFun := fun g => ⟨g.1.1, congrArg Subtype.val g.2⟩
      left_inv := fun x => rfl
      right_inv := fun g => rfl }
  set NJ : AddSubgroup ↥ψ.range := (zsmulAddGroupHom (N : ℤ) : ↥ψ.range →+ ↥ψ.range).range with hNJ
  set M : AddSubgroup (Seg → ℤ) :=
    (cobd ends).range ⊔ (zsmulAddGroupHom (N : ℤ) : (Seg → ℤ) →+ (Seg → ℤ)).range with hM
  refine ⟨Finite.of_equiv _ eKT.symm, ?_⟩
  rw [Nat.card_congr eKT, natCard_torsionBy_eq_natCard_quotient_range_nsmul _ N hN]

  let Φ : (Seg → ℤ) →+ ↥ψ.range ⧸ NJ := (QuotientAddGroup.mk' NJ).comp ψ.rangeRestrict
  have hΦsurj : Function.Surjective Φ :=
    (QuotientAddGroup.mk'_surjective NJ).comp (AddMonoidHom.rangeRestrict_surjective ψ)
  have hMker : M ≤ Φ.ker := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [AddMonoidHom.mem_ker]
      have h0 : ψ.rangeRestrict (cobd ends x) = 0 := Subtype.ext (by
        show ψ (cobd ends x) = 0
        rw [hψ, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
        exact ⟨x, rfl⟩)
      show QuotientAddGroup.mk' NJ (ψ.rangeRestrict (cobd ends x)) = 0
      rw [h0, map_zero]
    · rintro _ ⟨y, rfl⟩
      rw [AddMonoidHom.mem_ker]
      show QuotientAddGroup.mk' NJ (ψ.rangeRestrict (zsmulAddGroupHom (N : ℤ) y)) = 0
      rw [zsmulAddGroupHom_apply, map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact ⟨ψ.rangeRestrict y, rfl⟩
  have hcardJ : Nat.card (↥ψ.range ⧸ NJ) = Nat.card ((Seg → ℤ) ⧸ Φ.ker) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective Φ hΦsurj).symm.toEquiv
  have hmapsurj : Function.Surjective
      (QuotientAddGroup.map M Φ.ker (AddMonoidHom.id (Seg → ℤ)) (fun z hz => hMker hz)) := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨QuotientAddGroup.mk z, rfl⟩
  haveI hfinR : Finite ((Seg → ZMod N) ⧸ (cobdN ends N).range) := finite_quotient_range_cobdN ends N hN
  have hcardM : Nat.card ((Seg → ℤ) ⧸ M) = Nat.card ((Seg → ZMod N) ⧸ (cobdN ends N).range) :=
    natCard_quotient_cobd_sup_nsmul_eq ends N hN
  haveI hfinM : Finite ((Seg → ℤ) ⧸ M) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcardM]
    exact Nat.card_pos.ne'
  have hle : Nat.card (↥ψ.range ⧸ NJ) ≤ Nat.card ((Seg → ZMod N) ⧸ (cobdN ends N).range) := by
    rw [hcardJ, ← hcardM]
    exact Nat.card_le_card_of_surjective _ hmapsurj

  have hconnZ : ∀ x : V → ZMod N, (∀ ε, x (ends ε).1 = x (ends ε).2) → ∀ u v, x u = x v :=
    fun x hx u v => apply_eq_of_forall_ends ends hconn x hx u v
  have hL7 : Nat.card ((Seg → ZMod N) ⧸ (cobdN ends N).range) * N ^ Fintype.card V =
      N ^ Fintype.card Seg * N :=
    natCard_quotient_range_cobd_zmod_mul V Seg ends N hN hconnZ
  calc Nat.card (↥ψ.range ⧸ NJ) * N ^ Fintype.card V
      ≤ Nat.card ((Seg → ZMod N) ⧸ (cobdN ends N).range) * N ^ Fintype.card V := Nat.mul_le_mul_right _ hle
    _ = N ^ Fintype.card Seg * N := hL7

theorem single_sub_single_mem_of_cut {n m : ℕ} (src tgt : Fin m → Fin n) {I : Type} [Fintype I] [DecidableEq I]
    (en : Seg → (Fin n ⊕ I) × (Fin n ⊕ I))
    (hcut : ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S))
    (horig : ∀ e, (Pi.single (Sum.inl (src e)) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl (tgt e)) 1 ∈ (bd en).range)
    (hint : ∀ i : I, ∃ j : Fin n,
      (Pi.single (Sum.inr i) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl j) 1 ∈ (bd en).range) :
    ∀ u v : Fin n ⊕ I, (Pi.single u 1 : Fin n ⊕ I → ℤ) - Pi.single v 1 ∈ (bd en).range := by
  classical
  intro u v
  set B := (bd en).range with hB
  have hrefl : ∀ a : Fin n ⊕ I, (Pi.single a 1 : Fin n ⊕ I → ℤ) - Pi.single a 1 ∈ B := fun a => by
    rw [sub_self]; exact B.zero_mem
  have hsymm : ∀ a b : Fin n ⊕ I, (Pi.single a 1 : Fin n ⊕ I → ℤ) - Pi.single b 1 ∈ B →
      (Pi.single b 1 : Fin n ⊕ I → ℤ) - Pi.single a 1 ∈ B := fun a b h => by
    rw [← neg_sub]; exact B.neg_mem h
  have htrans : ∀ a b c : Fin n ⊕ I, (Pi.single a 1 : Fin n ⊕ I → ℤ) - Pi.single b 1 ∈ B →
      (Pi.single b 1 : Fin n ⊕ I → ℤ) - Pi.single c 1 ∈ B → (Pi.single a 1 : Fin n ⊕ I → ℤ) - Pi.single c 1 ∈ B :=
    fun a b c h1 h2 => by
      have := B.add_mem h1 h2
      rwa [sub_add_sub_cancel] at this
  have hbase : ∀ a : Fin n ⊕ I, ∃ j : Fin n, (Pi.single a 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl j) 1 ∈ B := by
    rintro (j | i)
    · exact ⟨j, hrefl _⟩
    · exact hint i
  have horig' : ∀ j j' : Fin n, (Pi.single (Sum.inl j) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl j') 1 ∈ B := by
    intro j j'
    by_contra hjj
    let S : Finset (Fin n) :=
      Finset.univ.filter fun i => (Pi.single (Sum.inl j) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl i) 1 ∈ B
    have hmemS : ∀ i, i ∈ S ↔ (Pi.single (Sum.inl j) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl i) 1 ∈ B := by
      intro i; simp [S]
    have hjS : j ∈ S := (hmemS j).2 (hrefl _)
    have hj'S : j' ∈ Sᶜ := by rw [Finset.mem_compl, hmemS]; exact hjj
    obtain ⟨e, he⟩ := hcut S ⟨j, hjS⟩ ⟨j', hj'S⟩
    rw [hmemS, hmemS] at he
    have hiff : (Pi.single (Sum.inl j) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl (src e)) 1 ∈ B ↔
        (Pi.single (Sum.inl j) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl (tgt e)) 1 ∈ B :=
      ⟨fun h => htrans _ _ _ h (horig e), fun h => htrans _ _ _ h (hsymm _ _ (horig e))⟩
    rw [hiff] at he
    exact iff_not_self he
  obtain ⟨j, hj⟩ := hbase u
  obtain ⟨j', hj'⟩ := hbase v
  exact htrans _ _ _ hj (htrans _ _ _ (horig' j j') (hsymm _ _ hj'))

end TropCnt

namespace TropCnt

section Subdiv

abbrev SV (n m : ℕ) (W : Fin m → ℕ) : Type := Fin n ⊕ (Σ e : Fin m, Fin (W e - 1))

abbrev SSeg (m : ℕ) (W : Fin m → ℕ) : Type := Σ e : Fin m, Fin (W e)

variable {n m : ℕ} (src tgt : Fin m → Fin n) (W : Fin m → ℕ)

def subdivEnds : SSeg m W → SV n m W × SV n m W := fun ε =>
  (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
    else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
   if h1 : ε.2.1 + 1 = W ε.1 then Sum.inl (tgt ε.1)
    else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)

theorem subdivEnds_fst_zero (e : Fin m) (h : 0 < W e) :
    (subdivEnds src tgt W ⟨e, ⟨0, h⟩⟩).1 = Sum.inl (src e) := by
  simp [subdivEnds]

theorem subdivEnds_fst_succ (e : Fin m) (j : ℕ) (h : j + 1 < W e) :
    (subdivEnds src tgt W ⟨e, ⟨j + 1, h⟩⟩).1 =
      (subdivEnds src tgt W ⟨e, ⟨j, (Nat.lt_succ_self j).trans h⟩⟩).2 := by
  have h' : ¬ (j + 1 = W e) := h.ne
  simp [subdivEnds, h']

theorem subdivEnds_snd_last (e : Fin m) (h : 0 < W e) :
    (subdivEnds src tgt W ⟨e, ⟨W e - 1, Nat.sub_lt h one_pos⟩⟩).2 = Sum.inl (tgt e) := by
  have h' : W e - 1 + 1 = W e := Nat.sub_add_cancel h
  simp [subdivEnds, h']

theorem subdivEnds_snd_int (e : Fin m) (i : Fin (W e - 1)) :
    (subdivEnds src tgt W ⟨e, ⟨i.1, by have := i.2; omega⟩⟩).2 = Sum.inr ⟨e, i⟩ := by
  have h' : ¬ (i.1 + 1 = W e) := by have := i.2; omega
  simp [subdivEnds, h']

theorem single_src_sub_single_snd_mem (e : Fin m) : ∀ (j : ℕ) (h : j < W e),
    (Pi.single (Sum.inl (src e)) 1 : SV n m W → ℤ) - Pi.single ((subdivEnds src tgt W ⟨e, ⟨j, h⟩⟩).2) 1 ∈
      (bd (subdivEnds src tgt W)).range := by
  intro j
  induction j with
  | zero =>
    intro h
    have := single_sub_single_ends_mem (subdivEnds src tgt W) ⟨e, ⟨0, h⟩⟩
    rwa [subdivEnds_fst_zero] at this
  | succ j ih =>
    intro h
    have h1 := ih ((Nat.lt_succ_self j).trans h)
    have h2 := single_sub_single_ends_mem (subdivEnds src tgt W) ⟨e, ⟨j + 1, h⟩⟩
    rw [subdivEnds_fst_succ] at h2
    have := AddSubgroup.add_mem _ h1 h2
    rwa [sub_add_sub_cancel] at this

theorem subdiv_conn (hW : ∀ e, 0 < W e)
    (hcut : ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S)) :
    ∀ u v : SV n m W, (Pi.single u 1 : SV n m W → ℤ) - Pi.single v 1 ∈ (bd (subdivEnds src tgt W)).range := by
  apply single_sub_single_mem_of_cut src tgt (subdivEnds src tgt W) hcut
  · intro e
    have := single_src_sub_single_snd_mem src tgt W e (W e - 1) (Nat.sub_lt (hW e) one_pos)
    rwa [subdivEnds_snd_last src tgt W e (hW e)] at this
  · rintro ⟨e, i⟩
    refine ⟨src e, ?_⟩
    have := single_src_sub_single_snd_mem src tgt W e i.1 (by have := i.2; omega)
    rw [subdivEnds_snd_int] at this
    rw [← neg_sub]; exact AddSubgroup.neg_mem _ this

theorem card_SV : Fintype.card (SV n m W) = n + ∑ e, (W e - 1) := by
  simp [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]

theorem card_SSeg : Fintype.card (SSeg m W) = ∑ e, W e := by
  simp [Fintype.card_sigma, Fintype.card_fin]

theorem sum_W_eq (hW : ∀ e, 0 < W e) : ∑ e, W e = m + ∑ e, (W e - 1) := by
  calc ∑ e, W e = ∑ e, ((W e - 1) + 1) := Finset.sum_congr rfl (fun e _ => (Nat.sub_add_cancel (hW e)).symm)
    _ = ∑ e, (W e - 1) + ∑ e : Fin m, 1 := Finset.sum_add_distrib
    _ = m + ∑ e, (W e - 1) := by simp [add_comm]

end Subdiv

theorem main (n m : ℕ) (src tgt : Fin m → Fin n) (W : Fin m → ℕ) (hW : ∀ e, 0 < W e)
    (hconn : ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S))
    (N : ℕ) (hN : 0 < N) :
    Finite {x : (SV n m W → ℤ) ⧸ AddSubgroup.closure (Set.range (lapRow (subdivEnds src tgt W))) //
        ((N : ℕ) : ℤ) • x = 0} ∧
      Nat.card {x : (SV n m W → ℤ) ⧸ AddSubgroup.closure (Set.range (lapRow (subdivEnds src tgt W))) //
        ((N : ℕ) : ℤ) • x = 0} * N ^ n ≤ N ^ (m + 1) := by
  classical
  rw [closure_range_lapRow]
  rcases Nat.eq_zero_or_pos n with hn | hn
  ·
    subst hn
    have hm : m = 0 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact h
      · exact (src ⟨0, h⟩).elim0
    subst hm
    haveI : IsEmpty (SV 0 0 W) :=
      ⟨fun v => match v with
        | Sum.inl i => i.elim0
        | Sum.inr ⟨e, _⟩ => e.elim0⟩
    haveI : Unique (SV 0 0 W → ℤ) := Pi.uniqueOfIsEmpty _
    set L := ((bd (subdivEnds src tgt W)).comp (cobd (subdivEnds src tgt W))).range with hL
    haveI hfq : Finite ((SV 0 0 W → ℤ) ⧸ L) := Finite.of_surjective _ (QuotientAddGroup.mk'_surjective L)
    refine ⟨inferInstance, ?_⟩
    rw [pow_zero, mul_one, zero_add, pow_one]
    calc Nat.card {x : (SV 0 0 W → ℤ) ⧸ L // ((N : ℕ) : ℤ) • x = 0}
        ≤ Nat.card ((SV 0 0 W → ℤ) ⧸ L) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ ≤ Nat.card (SV 0 0 W → ℤ) := Nat.card_le_card_of_surjective _ (QuotientAddGroup.mk'_surjective L)
      _ = 1 := Nat.card_unique
      _ ≤ N := hN
  · haveI : Nonempty (SV n m W) := ⟨Sum.inl ⟨0, hn⟩⟩
    obtain ⟨hfin, hle⟩ :=
      card_torsion_mul_pow_le (subdivEnds src tgt W) (subdiv_conn src tgt W hW hconn) N hN
    refine ⟨hfin, ?_⟩
    rw [card_SV, card_SSeg, sum_W_eq W hW] at hle
    have hS : 0 < N ^ ∑ e, (W e - 1) := pow_pos hN _
    apply Nat.le_of_mul_le_mul_right _ hS
    calc Nat.card {x : (SV n m W → ℤ) ⧸ ((bd (subdivEnds src tgt W)).comp (cobd (subdivEnds src tgt W))).range //
            ((N : ℕ) : ℤ) • x = 0} * N ^ n * N ^ ∑ e, (W e - 1)
        = Nat.card {x : (SV n m W → ℤ) ⧸ ((bd (subdivEnds src tgt W)).comp (cobd (subdivEnds src tgt W))).range //
            ((N : ℕ) : ℤ) • x = 0} * N ^ (n + ∑ e, (W e - 1)) := by rw [pow_add, mul_assoc]
      _ ≤ N ^ (m + ∑ e, (W e - 1)) * N := hle
      _ = N ^ (m + 1) * N ^ ∑ e, (W e - 1) := by ring

end TropCnt

theorem solution
    (n m : ℕ) (src tgt : Fin m → Fin n) (W : Fin m → ℕ) (hW : ∀ e, 0 < W e)
    (hconn : ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S))
    (N : ℕ) (hN : 0 < N) :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (W e - 1))
    let ends : (Σ e : Fin m, Fin (W e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = W ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (W e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    Finite {x : (V → ℤ) ⧸ AddSubgroup.closure (Set.range lap) // ((N : ℕ) : ℤ) • x = 0} ∧
      Nat.card {x : (V → ℤ) ⧸ AddSubgroup.closure (Set.range lap) // ((N : ℕ) : ℤ) • x = 0} * N ^ n ≤
        N ^ (m + 1) := by
  intro V ends lap
  exact TropCnt.main n m src tgt W hW hconn N hN

end S_AlgebraicCurve_SemistableCovering_natCard_torsion_quotient_lap_mul_pow_le_pow_of_forall_exists_src_mem_iff
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_natCard_torsion_quotient_lap_mul_pow_le_pow_of_forall_exists_src_mem_iff (solution)
