-- Prove2me | solution 1 for AlgebraicGeometry.isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/97757c16-ec9b-5a03-9130-686c84c8895a

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus

set_option autoImplicit false

open AddMonoidAlgebra

universe u

noncomputable section

namespace LenBound

variable (k : Type u) [Field k] (t m : ℕ)

abbrev R : Type u := AddMonoidAlgebra k (Fin t → ℤ)

abbrev Rm : Type u := AddMonoidAlgebra k (Fin t → ZMod m)

abbrev redHom : (Fin t → ℤ) →+ (Fin t → ZMod m) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ => ℤ) i)

abbrev red : R k t →ₐ[k] Rm k t m :=
  AddMonoidAlgebra.mapDomainAlgHom k k (redHom t m)

theorem red_surjective [NeZero m] : Function.Surjective (red k t m) := by
  intro x
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy => obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, map_add _ _ _⟩
  | single v c =>
    refine ⟨single (fun i => (v i).val) c, ?_⟩
    rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
    congr 1
    funext i
    simp [redHom]

theorem finrank_Rm [NeZero m] : Module.finrank k (Rm k t m) = m ^ t := by
  rw [show Module.finrank k (Rm k t m) = Fintype.card (Fin t → ZMod m) from ?_]
  · simp [ZMod.card]
  · exact (Module.finrank_eq_card_basis (AddMonoidAlgebra.basis (Fin t → ZMod m) k)).trans rfl

abbrev I : Ideal (R k t) :=
  Ideal.span (Set.range fun i : Fin t => single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k) - 1)

theorem mk_single_single (i : Fin t) :
    Ideal.Quotient.mk (I k t m) (single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k)) = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk (I k t m)), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

theorem mk_single_single_mul (i : Fin t) (a : ℤ) :
    Ideal.Quotient.mk (I k t m) (single (Pi.single i ((m : ℤ) * a) : Fin t → ℤ) (1 : k)) = 1 := by

  have hpos : ∀ n : ℕ, Ideal.Quotient.mk (I k t m) (single (Pi.single i ((m : ℤ) * n) : Fin t → ℤ) (1 : k)) = 1 := by
    intro n
    have : single (Pi.single i ((m : ℤ) * n) : Fin t → ℤ) (1 : k) = (single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k)) ^ n := by
      rw [AddMonoidAlgebra.single_pow, one_pow]
      congr 1
      ext j
      by_cases hj : j = i
      · subst hj; simp [mul_comm]
      · simp [hj]
    rw [this, map_pow, mk_single_single, one_pow]
  rcases Int.eq_nat_or_neg a with ⟨n, rfl | rfl⟩
  · exact hpos n
  ·
    have hmul : single (Pi.single i ((m : ℤ) * -(n : ℤ)) : Fin t → ℤ) (1 : k) * single (Pi.single i ((m : ℤ) * n) : Fin t → ℤ) (1 : k) = 1 := by
      rw [AddMonoidAlgebra.single_mul_single, one_mul, ← Pi.single_add]
      simp [AddMonoidAlgebra.one_def]
    have := congrArg (Ideal.Quotient.mk (I k t m)) hmul
    rwa [map_mul, map_one, hpos n, mul_one] at this

theorem mk_single_eq_one_of_dvd (w : Fin t → ℤ) (hw : ∀ i, (m : ℤ) ∣ w i) :
    Ideal.Quotient.mk (I k t m) (single w 1) = 1 := by
  classical
  choose a ha using hw
  have hw' : w = ∑ i, (Pi.single i ((m : ℤ) * a i) : Fin t → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, ha j]
  have hprod : single w (1 : k) = ∏ i, single (Pi.single i ((m : ℤ) * a i) : Fin t → ℤ) (1 : k) := by
    rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one, ← hw']
  rw [hprod, map_prod]
  exact Finset.prod_eq_one fun i _ => mk_single_single_mul k t m i (a i)

theorem mk_single_add (v q : Fin t → ℤ) :
    Ideal.Quotient.mk (I k t m) (single (v + (m : ℤ) • q) 1) = Ideal.Quotient.mk (I k t m) (single v 1) := by
  have : single (v + (m : ℤ) • q) (1 : k) = single v 1 * single ((m : ℤ) • q) 1 := by
    rw [AddMonoidAlgebra.single_mul_single, one_mul]
  rw [this, map_mul, mk_single_eq_one_of_dvd k t m ((m : ℤ) • q) (fun i => ⟨q i, by simp⟩), mul_one]

section Iso

variable [NeZero m]

abbrev liftZ (w : Fin t → ZMod m) : Fin t → ℤ := fun i => ((w i).val : ℤ)

theorem redHom_liftZ (w : Fin t → ZMod m) : redHom t m (liftZ t m w) = w := by
  funext i
  simp [redHom, liftZ]

theorem liftZ_add (w w' : Fin t → ZMod m) :
    ∃ q : Fin t → ℤ, liftZ t m (w + w') = liftZ t m w + liftZ t m w' + (m : ℤ) • q := by
  refine ⟨fun i => -(((w i).val + (w' i).val) / m : ℕ), funext fun i => ?_⟩
  simp only [liftZ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ZMod.val_add]
  have h := Nat.mod_add_div ((w i).val + (w' i).val) m
  have h' : (((w i).val + (w' i).val) % m : ℕ) = ((w i).val + (w' i).val : ℤ) - (m : ℤ) * (((w i).val + (w' i).val) / m : ℕ) := by
    omega
  push_cast at h' ⊢
  rw [h']
  ring

def unitMap : Multiplicative (Fin t → ZMod m) →* (R k t ⧸ I k t m) where
  toFun w := Ideal.Quotient.mk (I k t m) (single (liftZ t m w.toAdd) 1)
  map_one' := by
    change Ideal.Quotient.mk (I k t m) (single (liftZ t m 0) 1) = 1
    have : liftZ t m 0 = 0 := by funext i; simp [liftZ]
    rw [this]
    exact map_one _
  map_mul' w w' := by
    change Ideal.Quotient.mk (I k t m) (single (liftZ t m (w.toAdd + w'.toAdd)) 1) =
      Ideal.Quotient.mk (I k t m) (single (liftZ t m w.toAdd) 1) * Ideal.Quotient.mk (I k t m) (single (liftZ t m w'.toAdd) 1)
    obtain ⟨q, hq⟩ := liftZ_add t m w.toAdd w'.toAdd
    rw [hq, mk_single_add, ← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]

private def _root_.LenBound.inv : Rm k t m →ₐ[k] (R k t ⧸ I k t m) :=
  AddMonoidAlgebra.lift k (R k t ⧸ I k t m) (Fin t → ZMod m) (unitMap k t m)

p2m_export "LenBound" "inv"
theorem inv_single (w : Fin t → ZMod m) :
    inv k t m (single w 1) = Ideal.Quotient.mk (I k t m) (single (liftZ t m w) 1) := by
  rw [inv, AddMonoidAlgebra.lift_single, one_smul]
  rfl

omit [NeZero m] in
theorem I_le_ker : I k t m ≤ RingHom.ker (red k t m).toRingHom := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  change red k t m (single _ 1 - 1) = 0
  rw [map_sub, map_one, sub_eq_zero]
  have hred : red k t m (single (Pi.single i (m : ℤ) : Fin t → ℤ) 1) =
      single (redHom t m (Pi.single i (m : ℤ) : Fin t → ℤ)) 1 := by
    rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  rw [hred, AddMonoidAlgebra.one_def]
  congr 1
  funext j
  simp [redHom, Pi.single_apply]

def fwd : (R k t ⧸ I k t m) →ₐ[k] Rm k t m :=
  Ideal.Quotient.liftₐ (I k t m) (red k t m) fun a ha => by
    have := I_le_ker k t m ha
    rwa [RingHom.mem_ker] at this

omit [NeZero m] in
theorem fwd_mk (x : R k t) : fwd k t m (Ideal.Quotient.mk (I k t m) x) = red k t m x := rfl

theorem fwd_inv : (fwd k t m).comp (inv k t m) = AlgHom.id k _ := by
  refine AddMonoidAlgebra.algHom_ext (fun w => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, inv_single, fwd_mk, AlgHom.id_apply]
  rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  congr 1
  exact redHom_liftZ t m w

theorem inv_fwd : (inv k t m).comp (fwd k t m) = AlgHom.id k _ := by
  refine Ideal.Quotient.algHom_ext _ (AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _))
  change inv k t m (fwd k t m (Ideal.Quotient.mk (I k t m) (single v 1))) = Ideal.Quotient.mk (I k t m) (single v 1)
  rw [fwd_mk]
  rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  change inv k t m (single (redHom t m v) 1) = _
  rw [inv_single]

  have : ∃ q : Fin t → ℤ, liftZ t m (redHom t m v) = v + (m : ℤ) • q := by
    refine ⟨fun i => -(v i / m), funext fun i => ?_⟩
    simp only [liftZ, redHom, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    simp only [AddMonoidHom.pi_apply, AddMonoidHom.coe_comp, Function.comp_apply, Pi.evalAddMonoidHom_apply,
      Int.coe_castAddHom, ZMod.val_intCast]
    have := Int.emod_add_mul_ediv (v i) m
    linarith [Int.emod_emod_of_dvd (v i) (dvd_refl (m : ℤ))]
  obtain ⟨q, hq⟩ := this
  rw [hq, mk_single_add]

def quotEquiv : (R k t ⧸ I k t m) ≃ₐ[k] Rm k t m :=
  AlgEquiv.ofAlgHom (fwd k t m) (inv k t m) (fwd_inv k t m) (inv_fwd k t m)

theorem finrank_quot : Module.finrank k (R k t ⧸ I k t m) = m ^ t := by
  rw [(quotEquiv k t m).toLinearEquiv.finrank_eq, finrank_Rm]

scoped instance finite_quot : Module.Finite k (R k t ⧸ I k t m) :=
  Module.Finite.equiv (quotEquiv k t m).toLinearEquiv.symm

end Iso

section Twist

abbrev Ic (c : Fin t → kˣ) : Ideal (R k t) :=
  Ideal.span (Set.range fun i : Fin t => single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k) - single 0 ((c i : k)))

def chi (d : Fin t → kˣ) : Multiplicative (Fin t → ℤ) →* kˣ where
  toFun v := ∏ i, d i ^ (v.toAdd i)
  map_one' := by simp
  map_mul' v w := by
    change ∏ i, d i ^ ((v.toAdd + w.toAdd) i) = _
    simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

def twist (d : Fin t → kˣ) : R k t →ₐ[k] R k t :=
  AddMonoidAlgebra.lift k (R k t) (Fin t → ℤ)
    { toFun := fun v => ((chi k t d v : kˣ) : k) • single v.toAdd (1 : k)
      map_one' := by simp [AddMonoidAlgebra.one_def]
      map_mul' := fun v w => by
        simp only [map_mul, Units.val_mul]
        rw [smul_mul_smul_comm, AddMonoidAlgebra.single_mul_single, one_mul]
        rfl }

theorem twist_single (d : Fin t → kˣ) (v : Fin t → ℤ) (a : k) :
    twist k t d (single v a) = single v (a * (chi k t d (Multiplicative.ofAdd v) : kˣ)) := by
  rw [twist, AddMonoidAlgebra.lift_single]
  change a • (((chi k t d (Multiplicative.ofAdd v) : kˣ) : k) • single v (1 : k)) = _
  rw [smul_smul, AddMonoidAlgebra.smul_single', mul_one]

theorem twist_twist_inv (d : Fin t → kˣ) : (twist k t d).comp (twist k t d⁻¹) = AlgHom.id k _ := by
  refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
  have hone : chi k t d⁻¹ (Multiplicative.ofAdd v) * chi k t d (Multiplicative.ofAdd v) = 1 := by
    change (∏ i, (d⁻¹) i ^ (v i)) * ∏ i, d i ^ (v i) = 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => by rw [Pi.inv_apply, inv_zpow, inv_mul_cancel]
  rw [AlgHom.comp_apply, twist_single, twist_single, AlgHom.id_apply, one_mul, ← Units.val_mul, hone, Units.val_one]

def twistEquiv (d : Fin t → kˣ) : R k t ≃ₐ[k] R k t :=
  AlgEquiv.ofAlgHom (twist k t d) (twist k t d⁻¹) (twist_twist_inv k t d) (by simpa using twist_twist_inv k t d⁻¹)

theorem map_twist_I (d c : Fin t → kˣ) (hdc : ∀ i, d i ^ m = c i) :
    Ideal.map (twist k t d) (I k t m) = Ic k t m c⁻¹ := by
  have hchi : ∀ i, ((chi k t d (Multiplicative.ofAdd (Pi.single i (m : ℤ) : Fin t → ℤ)) : kˣ) : k) = c i := by
    intro i
    change ((∏ j, d j ^ ((Pi.single i (m : ℤ) : Fin t → ℤ) j) : kˣ) : k) = c i
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp [← hdc i]
  have hgen : ∀ i, twist k t d (single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k) - 1) =
      algebraMap k (R k t) (c i : k) *
        (single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k) - single 0 (((c⁻¹) i : kˣ) : k)) := by
    intro i
    rw [map_sub, map_one, twist_single, one_mul, hchi, mul_sub]
    have h1 : algebraMap k (R k t) (c i : k) * single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k) =
        single (Pi.single i (m : ℤ) : Fin t → ℤ) (c i : k) := by
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, AddMonoidAlgebra.smul_single', mul_one]
    have h2 : algebraMap k (R k t) (c i : k) * single (0 : Fin t → ℤ) (((c⁻¹) i : kˣ) : k) = 1 := by
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, AddMonoidAlgebra.smul_single', Pi.inv_apply,
        Units.val_inv_eq_inv_val, mul_inv_cancel₀ (c i).ne_zero, AddMonoidAlgebra.one_def]
    rw [h1, h2]

  apply le_antisymm
  · rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, hgen]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hmem : twist k t d (single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k) - 1) ∈ Ideal.map (twist k t d) (I k t m) :=
      Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
    rw [hgen] at hmem
    have := Ideal.mul_mem_left _ (algebraMap k (R k t) ((c i)⁻¹ : kˣ)) hmem
    rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at this

end Twist

section Fibre

variable [NeZero m] [IsAlgClosed k]

theorem exists_root (c : Fin t → kˣ) : ∃ d : Fin t → kˣ, ∀ i, d i ^ m = c i := by
  have h : ∀ i, ∃ z : k, z ^ m = c i := fun i => IsAlgClosed.exists_pow_nat_eq _ (NeZero.pos m)
  choose z hz using h
  have hz0 : ∀ i, z i ≠ 0 := fun i h0 => (c i).ne_zero (by rw [← hz i, h0, zero_pow (NeZero.ne m)])
  exact ⟨fun i => Units.mk0 (z i) (hz0 i), fun i => Units.ext (by simp [hz i])⟩

def quotIcEquiv (c : Fin t → kˣ) : (R k t ⧸ Ic k t m c) ≃ₐ[k] (R k t ⧸ I k t m) := by
  let d := (exists_root k t m c⁻¹).choose
  have hd : ∀ i, d i ^ m = c⁻¹ i := (exists_root k t m c⁻¹).choose_spec
  have hmap : Ic k t m c = Ideal.map (twistEquiv k t d) (I k t m) := by
    have : Ideal.map (twistEquiv k t d) (I k t m) = Ideal.map (twist k t d) (I k t m) := rfl
    rw [this, map_twist_I k t m d c⁻¹ hd, inv_inv]
  exact (Ideal.quotientEquivAlg (I k t m) (Ic k t m c) (twistEquiv k t d) hmap).symm

theorem finrank_quot_Ic (c : Fin t → kˣ) : Module.finrank k (R k t ⧸ Ic k t m c) = m ^ t := by
  rw [(quotIcEquiv k t m c).toLinearEquiv.finrank_eq, finrank_quot]

scoped instance finite_quot_Ic (c : Fin t → kˣ) : Module.Finite k (R k t ⧸ Ic k t m c) :=
  Module.Finite.equiv (quotIcEquiv k t m c).toLinearEquiv.symm

end Fibre

section Square

variable [NeZero m]

def ev (c : Fin t → kˣ) : R k t →ₐ[k] k :=
  AddMonoidAlgebra.lift k k (Fin t → ℤ) ((Units.coeHom k).comp (chi k t c))

theorem ev_single (c : Fin t → kˣ) (v : Fin t → ℤ) (a : k) :
    ev k t c (single v a) = a * (chi k t c (Multiplicative.ofAdd v) : kˣ) := by
  rw [ev, AddMonoidAlgebra.lift_single, smul_eq_mul]
  rfl

abbrev pow : R k t →+* R k t := AddMonoidAlgebra.mapDomainRingHom k (m • AddMonoidHom.id (Fin t → ℤ))

omit [NeZero m] in
theorem pow_single (v : Fin t → ℤ) (a : k) : pow k t m (single v a) = single ((m : ℤ) • v) a := by
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
  rfl

omit [NeZero m] in

theorem mk_pow_single_one (c : Fin t → kˣ) (v : Fin t → ℤ) :
    Ideal.Quotient.mk (Ic k t m c) (single ((m : ℤ) • v) 1) =
      algebraMap k _ ((chi k t c (Multiplicative.ofAdd v) : kˣ) : k) := by

  let F : Multiplicative (Fin t → ℤ) →* (R k t ⧸ Ic k t m c) :=
    { toFun := fun v => Ideal.Quotient.mk (Ic k t m c) (single ((m : ℤ) • v.toAdd) 1)
      map_one' := by
        change Ideal.Quotient.mk _ (single ((m : ℤ) • (0 : Fin t → ℤ)) 1) = 1
        rw [smul_zero, ← AddMonoidAlgebra.one_def, map_one]
      map_mul' := fun v w => by
        change Ideal.Quotient.mk _ (single ((m : ℤ) • (v.toAdd + w.toAdd)) 1) = _
        rw [smul_add, ← map_mul, AddMonoidAlgebra.single_mul_single, one_mul] }
  let G : Multiplicative (Fin t → ℤ) →* (R k t ⧸ Ic k t m c) :=
    ((algebraMap k (R k t ⧸ Ic k t m c) : k →* _).comp ((Units.coeHom k).comp (chi k t c)))
  suffices h : F = G from DFunLike.congr_fun h (Multiplicative.ofAdd v)

  have key : ∀ (i : Fin t) (x : ℤ), F (Multiplicative.ofAdd (Pi.single i x)) = G (Multiplicative.ofAdd (Pi.single i x)) := by
    intro i x

    have hchi : chi k t c (Multiplicative.ofAdd (Pi.single i x)) = c i ^ x := by
      change ∏ j, c j ^ ((Pi.single i x : Fin t → ℤ) j) = _
      rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
      simp
    have hG : G (Multiplicative.ofAdd (Pi.single i x)) = algebraMap k _ (((c i) ^ x : kˣ) : k) := by
      change algebraMap k (R k t ⧸ Ic k t m c) ((chi k t c (Multiplicative.ofAdd (Pi.single i x)) : kˣ) : k) = _
      rw [hchi]
    rw [hG]

    have hgen : Ideal.Quotient.mk (Ic k t m c) (single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k)) = algebraMap k _ (c i : k) := by
      have halg : algebraMap k (R k t ⧸ Ic k t m c) (c i : k) = Ideal.Quotient.mk (Ic k t m c) (single 0 (c i : k)) := by
        rw [← Ideal.Quotient.mk_algebraMap]
        rfl
      rw [halg, Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨i, rfl⟩
    have hpos : ∀ n : ℕ, F (Multiplicative.ofAdd (Pi.single i (n : ℤ))) = algebraMap k _ (((c i) ^ (n : ℤ) : kˣ) : k) := by
      intro n
      change Ideal.Quotient.mk _ (single ((m : ℤ) • (Pi.single i (n : ℤ) : Fin t → ℤ)) 1) = _
      have : single ((m : ℤ) • (Pi.single i (n : ℤ) : Fin t → ℤ)) (1 : k) = (single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k)) ^ n := by
        rw [AddMonoidAlgebra.single_pow, one_pow]
        congr 1
        ext j
        by_cases hj : j = i
        · subst hj; simp [mul_comm]
        · simp [hj]
      rw [this, map_pow, hgen, ← map_pow, zpow_natCast, Units.val_pow_eq_pow_val]
    rcases Int.eq_nat_or_neg x with ⟨n, rfl | rfl⟩
    · exact hpos n
    · have h1 := map_mul F (Multiplicative.ofAdd (Pi.single i (-(n : ℤ)))) (Multiplicative.ofAdd (Pi.single i (n : ℤ)))
      rw [← ofAdd_add, ← Pi.single_add, neg_add_cancel, Pi.single_zero, ofAdd_zero, map_one, hpos] at h1

      have hu : algebraMap k (R k t ⧸ Ic k t m c) (((c i) ^ (n : ℤ) : kˣ) : k) * algebraMap k _ (((c i) ^ (-(n : ℤ)) : kˣ) : k) = 1 := by
        rw [← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, map_one]
      calc F (Multiplicative.ofAdd (Pi.single i (-(n : ℤ))))
          = F (Multiplicative.ofAdd (Pi.single i (-(n : ℤ)))) * (algebraMap k (R k t ⧸ Ic k t m c) (((c i) ^ (n : ℤ) : kˣ) : k) *
              algebraMap k _ (((c i) ^ (-(n : ℤ)) : kˣ) : k)) := by rw [hu, mul_one]
        _ = algebraMap k _ (((c i) ^ (-(n : ℤ)) : kˣ) : k) := by rw [← mul_assoc, ← h1, one_mul]

  refine MonoidHom.ext fun w => ?_
  have hw : w = ∏ i, Multiplicative.ofAdd (Pi.single i (w.toAdd i)) := by
    rw [← ofAdd_sum, Finset.univ_sum_single]
    rfl
  rw [hw, map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ => key i (w.toAdd i)

omit [NeZero m] in

theorem mk_comp_pow (c : Fin t → kˣ) :
    (Ideal.Quotient.mk (Ic k t m c)).comp (pow k t m) = (algebraMap k (R k t ⧸ Ic k t m c)).comp (ev k t c).toRingHom := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun a => ?_)
  · rw [RingHom.comp_apply, RingHom.comp_apply, pow_single, smul_zero]
    change _ = algebraMap k _ (ev k t c (single 0 b))
    rw [ev_single]
    change _ = algebraMap k _ (b * ((chi k t c 1 : kˣ) : k))
    rw [map_one, Units.val_one, mul_one, ← Ideal.Quotient.mk_algebraMap]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, pow_single, mk_pow_single_one]
    change _ = algebraMap k _ (ev k t c (single a 1))
    rw [ev_single, one_mul]

end Square

section Pushout

open CategoryTheory CategoryTheory.Limits

theorem pow_algebraMap (b : k) : pow k t m (algebraMap k (R k t) b) = algebraMap k (R k t) b := by
  change pow k t m (single 0 b) = single 0 b
  rw [pow_single, smul_zero]

theorem ev_algebraMap (c : Fin t → kˣ) (b : k) : ev k t c (algebraMap k (R k t) b) = b := AlgHom.commutes _ b

theorem inl_apply_eq_zero (c : Fin t → kˣ)
    (sq : PushoutCocone (CommRingCat.ofHom (pow k t m)) (CommRingCat.ofHom (ev k t c).toRingHom)) :
    ∀ a ∈ Ic k t m c, sq.inl.hom a = 0 := by
  have hk : ∀ b : k, sq.inl.hom (algebraMap k (R k t) b) = sq.inr.hom b := by
    intro b
    have := CategoryTheory.congr_fun sq.condition (algebraMap k (R k t) b)
    change sq.inl.hom (pow k t m (algebraMap k (R k t) b)) = sq.inr.hom (ev k t c (algebraMap k (R k t) b)) at this
    rwa [pow_algebraMap, ev_algebraMap] at this
  have hle : Ic k t m c ≤ RingHom.ker sq.inl.hom := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have hchi1 : ((chi k t c (Multiplicative.ofAdd (Pi.single i (1 : ℤ) : Fin t → ℤ)) : kˣ) : k) = c i := by
      have : chi k t c (Multiplicative.ofAdd (Pi.single i (1 : ℤ) : Fin t → ℤ)) = c i := by
        change ∏ j, c j ^ ((Pi.single i (1 : ℤ) : Fin t → ℤ) j) = c i
        rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
        simp
      rw [this]
    have hsingle : (m : ℤ) • (Pi.single i (1 : ℤ) : Fin t → ℤ) = Pi.single i (m : ℤ) := by
      ext j; by_cases hj : j = i <;> simp [hj, Pi.single_apply]
    have h1 : sq.inl.hom (single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k)) = sq.inr.hom (c i : k) := by
      have := CategoryTheory.congr_fun sq.condition (single (Pi.single i (1 : ℤ) : Fin t → ℤ) (1 : k))
      change sq.inl.hom (pow k t m (single _ 1)) = sq.inr.hom (ev k t c (single _ 1)) at this
      rwa [pow_single, ev_single, one_mul, hsingle, hchi1] at this
    have h2 : sq.inl.hom (single (0 : Fin t → ℤ) ((c i : k))) = sq.inr.hom (c i : k) := hk (c i)
    rw [map_sub, h1, h2, sub_self]
  intro a ha
  exact hle ha

theorem isPushout_fibre (c : Fin t → kˣ) :
    IsPushout (CommRingCat.ofHom (pow k t m)) (CommRingCat.ofHom (ev k t c).toRingHom)
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ic k t m c)))
      (CommRingCat.ofHom (algebraMap k (R k t ⧸ Ic k t m c))) := by
  have hsq : CommRingCat.ofHom (pow k t m) ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Ic k t m c)) =
      CommRingCat.ofHom (ev k t c).toRingHom ≫ CommRingCat.ofHom (algebraMap k (R k t ⧸ Ic k t m c)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, mk_comp_pow]
  refine IsPushout.of_isColimit' ⟨hsq⟩ (PushoutCocone.IsColimit.mk hsq
    (fun sq => CommRingCat.ofHom (Ideal.Quotient.lift (Ic k t m c) sq.inl.hom (inl_apply_eq_zero k t m c sq)))
    ?facl ?facr ?uniq)
  · intro sq
    apply CommRingCat.hom_ext
    refine RingHom.ext fun a => ?_
    rfl
  · intro sq
    apply CommRingCat.hom_ext
    refine RingHom.ext fun b => ?_
    change Ideal.Quotient.lift _ sq.inl.hom (inl_apply_eq_zero k t m c sq) (algebraMap k (R k t ⧸ Ic k t m c) b) = sq.inr.hom b
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.lift_mk]
    have := CategoryTheory.congr_fun sq.condition (algebraMap k (R k t) b)
    change sq.inl.hom (pow k t m (algebraMap k (R k t) b)) = sq.inr.hom (ev k t c (algebraMap k (R k t) b)) at this
    rwa [pow_algebraMap, ev_algebraMap] at this
  · intro sq g hg₁ _
    apply CommRingCat.hom_ext
    refine Ideal.Quotient.ringHom_ext ?_
    refine RingHom.ext fun a => ?_
    change g.hom (Ideal.Quotient.mk _ a) = Ideal.Quotient.lift _ sq.inl.hom (inl_apply_eq_zero k t m c sq) (Ideal.Quotient.mk _ a)
    rw [Ideal.Quotient.lift_mk]
    exact CategoryTheory.congr_fun hg₁ a

end Pushout

section Piece

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable [NeZero m] [IsAlgClosed k]

theorem finrank_of_isPullback_pow (c : Fin t → kˣ) {P : Scheme.{u}}
    (a : P ⟶ Spec (CommRingCat.of (R k t))) (b : P ⟶ Spec (CommRingCat.of k))
    (h : IsPullback a b (Spec.map (CommRingCat.ofHom (pow k t m)))
      (Spec.map (CommRingCat.ofHom (ev k t c).toRingHom))) :
    IsFinite b ∧
    (letI := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ b.appTop).hom.toAlgebra
     Module.Finite k Γ(P, ⊤) ∧ Module.finrank k Γ(P, ⊤) = m ^ t) := by

  have h0 := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_fibre k t m c)

  let e : P ≅ Spec (CommRingCat.of (R k t ⧸ Ic k t m c)) := h.isoIsPullback _ _ h0
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (R k t ⧸ Ic k t m c))) = b :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  constructor
  ·
    rw [← he]
    haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (R k t ⧸ Ic k t m c)))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
    infer_instance
  ·
    letI : Algebra k Γ(P, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ b.appTop).hom.toAlgebra

    let ψ : CommRingCat.of (R k t ⧸ Ic k t m c) ≅ Γ(P, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (R k t ⧸ Ic k t m c))).symm ≪≫ Scheme.Γ.mapIso e.op
    have hψhom : ψ.hom = (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop := by
      change (Scheme.ΓSpecIso _).inv ≫ Scheme.Γ.map e.hom.op = _
      rw [Scheme.Γ_map]
      rfl

    have hψ : ∀ x : k, ψ.hom (algebraMap k (R k t ⧸ Ic k t m c) x) = algebraMap k Γ(P, ⊤) x := by
      intro x
      rw [hψhom]
      change ((Scheme.ΓSpecIso _).inv ≫ e.hom.appTop) (algebraMap k _ x) = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ b.appTop) x
      rw [← he, Scheme.Hom.comp_appTop]
      have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (R k t ⧸ Ic k t m c)))

      have : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap k (R k t ⧸ Ic k t m c)))).appTop ≫ e.hom.appTop =
          CommRingCat.ofHom (algebraMap k (R k t ⧸ Ic k t m c)) ≫ (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop := by
        rw [← Category.assoc, ← hnat, Category.assoc]
      rw [this]
      rfl
    let φ : (R k t ⧸ Ic k t m c) ≃ₗ[k] Γ(P, ⊤) :=
      { ψ.commRingCatIsoToRingEquiv with
        map_smul' := fun r x => by
          change ψ.hom (r • x) = algebraMap k Γ(P, ⊤) r * ψ.hom x
          rw [show r • x = algebraMap k (R k t ⧸ Ic k t m c) r * x from Algebra.smul_def r x, map_mul, hψ] }
    exact ⟨Module.Finite.equiv φ, by rw [← φ.finrank_eq, finrank_quot_Ic]⟩

end Piece

namespace Cover

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

variable {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
  {ι : Type u} [Fintype ι] (W : ι → Y.Opens) (hW : iSup W = ⊤)

abbrev alg {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k)) : Algebra k Γ(Z, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra

def resTo (i : ι) :
    letI := alg y; letI := alg ((W i).ι ≫ y)
    Γ(Y, ⊤) →ₗ[k] Γ((W i : Scheme.{u}), ⊤) :=
  letI := alg y; letI := alg ((W i).ι ≫ y)
  { toFun := fun s => (W i).ι.appTop s
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r s => by
      change (W i).ι.appTop (algebraMap k Γ(Y, ⊤) r * s) = algebraMap k _ r * (W i).ι.appTop s
      rw [map_mul]
      congr 1 }

omit [Fintype ι] in
include hW in
theorem injective_pi_resTo :
    letI := alg y; letI := fun i => alg ((W i).ι ≫ y)
    Function.Injective (LinearMap.pi fun i => resTo y W i) := by
  intro s t hst
  have hW' : (⊤ : Y.Opens) ≤ ⨆ i, (W i).ι ''ᵁ ⊤ := by
    rw [← hW]
    exact iSup_le fun i => le_iSup_of_le i (by rw [Scheme.Opens.ι_image_top])
  refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf (fun i => (W i).ι ''ᵁ ⊤) ⊤ (fun i => homOfLE le_top) hW' s t fun i => ?_
  have h := congrFun hst i
  change (W i).ι.appTop s = (W i).ι.appTop t at h
  rwa [Scheme.Opens.ι_appTop] at h

include hW in

theorem finrank_le_sum (d : ι → ℕ)
    (hfin : ∀ i, letI := alg ((W i).ι ≫ y); Module.Finite k Γ((W i : Scheme.{u}), ⊤))
    (hd : ∀ i, letI := alg ((W i).ι ≫ y); Module.finrank k Γ((W i : Scheme.{u}), ⊤) ≤ d i) :
    letI := alg y
    Module.Finite k Γ(Y, ⊤) ∧ Module.finrank k Γ(Y, ⊤) ≤ ∑ i, d i := by
  letI := alg y; letI := fun i => alg ((W i).ι ≫ y)
  haveI : ∀ i, Module.Finite k Γ((W i : Scheme.{u}), ⊤) := hfin
  have hinj := injective_pi_resTo y W hW
  refine ⟨Module.Finite.of_injective _ hinj, ?_⟩
  calc Module.finrank k Γ(Y, ⊤)
      ≤ Module.finrank k (∀ i, Γ((W i : Scheme.{u}), ⊤)) := LinearMap.finrank_le_finrank_of_injective hinj
    _ = ∑ i, Module.finrank k Γ((W i : Scheme.{u}), ⊤) := Module.finrank_pi_fintype k
    _ ≤ ∑ i, d i := Finset.sum_le_sum fun i _ => hd i

end Cover

end LenBound
p2m_reactivate "P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.LenBound"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.LenBound"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace LenBound
namespace Geom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace Opposite

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)

abbrev Pt (f : X ⟶ Spec (CommRingCat.of k)) : Type u := SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f

section Points

variable {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of k))

def cst (s : Pt f) : SchemeHomOver w f := schemeHomOverComp w (Category.comp_id w) s

@[scoped simp] theorem cst_coe (s : Pt f) : (cst w s).1 = w ≫ s.1 := rfl

theorem cst_id (s : Pt f) : cst (𝟙 _) s = s := Subtype.ext (Category.id_comp _)

theorem comp_cst {W' : Scheme.{u}} (w' : W' ⟶ Spec (CommRingCat.of k)) (ψ : W' ⟶ W) (hψ : ψ ≫ w = w')
    (s : Pt f) : schemeHomOverComp ψ hψ (cst w s) = cst w' s :=
  Subtype.ext (by simp only [schemeHomOverComp_coe, cst_coe, ← Category.assoc, hψ])

theorem cst_mul (s s' : Pt f) : cst w (L.mul (𝟙 _) s s') = L.mul w (cst w s) (cst w s') :=
  L.mul_natural _ _ w (Category.comp_id w) s s'

theorem cst_one : cst w (L.one (𝟙 _)) = L.one w :=
  L.one_natural _ _ w (Category.comp_id w)

theorem cst_nsmul (n : ℕ) (s : Pt f) : cst w (L.nsmul (𝟙 _) n s) = L.nsmul w n (cst w s) :=
  L.nsmul_natural _ _ w (Category.comp_id w) n s

theorem comp_schemeNsmul (n : ℕ) (x : SchemeHomOver w f) :
    x.1 ≫ L.schemeNsmul n = (L.nsmul w n x).1 := by
  have h := L.nsmul_natural f w x.1 x.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hid] at h
  exact congrArg Subtype.val h

theorem nsmul_mul (hc : L.IsCommutative) (n : ℕ) (x y : SchemeHomOver w f) :
    L.nsmul w n (L.mul w x y) = L.mul w (L.nsmul w n x) (L.nsmul w n y) := by
  induction n with
  | zero => simp only [RelativeGroupLaw.nsmul_zero]; exact (L.one_mul w _).symm
  | succ n ih =>
    simp only [RelativeGroupLaw.nsmul_succ, ih]
    rw [L.mul_assoc w (L.nsmul w n x) (L.nsmul w n y) (L.mul w x y),
      L.mul_assoc w (L.nsmul w n x) x (L.mul w (L.nsmul w n y) y),
      ← L.mul_assoc w (L.nsmul w n y) x y, hc w (L.nsmul w n y) x, L.mul_assoc w x (L.nsmul w n y) y]

end Points
p2m_reactivate "P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.LenBound"

def transl (s : Pt f) : X ⟶ X := (L.mul f (cst f s) RelativeGroupLaw.idPoint).1

theorem transl_over (s : Pt f) : transl L s ≫ f = f := (L.mul f (cst f s) RelativeGroupLaw.idPoint).2

theorem comp_transl {W : Scheme.{u}} {w : W ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver w f) (s : Pt f) :
    x.1 ≫ transl L s = (L.mul w (cst w s) x).1 := by
  have h := L.mul_natural f w x.1 x.2 (cst f s) RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [comp_cst, hid] at h
  exact congrArg Subtype.val h

theorem transl_one : transl L (L.one (𝟙 _)) = 𝟙 X := by
  change (L.mul f (cst f (L.one (𝟙 _))) RelativeGroupLaw.idPoint).1 = _
  rw [cst_one, L.one_mul]

theorem transl_comp_transl (s s' : Pt f) :
    transl L s ≫ transl L s' = transl L (L.mul (𝟙 _) s' s) := by
  change (L.mul f (cst f s) RelativeGroupLaw.idPoint).1 ≫ transl L s' =
    (L.mul f (cst f (L.mul (𝟙 _) s' s)) RelativeGroupLaw.idPoint).1
  rw [comp_transl, cst_mul, L.mul_assoc]

def translIso (s : Pt f) : X ≅ X where
  hom := transl L s
  inv := transl L (L.inv (𝟙 _) s)
  hom_inv_id := by rw [transl_comp_transl, L.inv_mul_cancel, transl_one]
  inv_hom_id := by rw [transl_comp_transl, L.mul_inv_cancel, transl_one]

scoped instance isIso_transl (s : Pt f) : IsIso (transl L s) := (inferInstance : IsIso (translIso L s).hom)

theorem transl_schemeNsmul (hc : L.IsCommutative) (s : Pt f) (n : ℕ) :
    transl L s ≫ L.schemeNsmul n = L.schemeNsmul n ≫ transl L (L.nsmul (𝟙 _) n s) := by
  have h1 := comp_schemeNsmul L f n (L.mul f (cst f s) RelativeGroupLaw.idPoint)
  have h2 := comp_transl L (L.nsmul f n RelativeGroupLaw.idPoint) (L.nsmul (𝟙 _) n s)
  change (L.mul f (cst f s) RelativeGroupLaw.idPoint).1 ≫ _ = (L.nsmul f n RelativeGroupLaw.idPoint).1 ≫ _
  rw [h1, h2, nsmul_mul L f hc, cst_nsmul]

section Torus

variable (t : ℕ) (ι : Spec (CommRingCat.of (R k t)) ⟶ X)

def trι (s : Pt f) : Spec (CommRingCat.of (R k t)) ⟶ X := ι ≫ transl L s

scoped instance [IsOpenImmersion ι] (s : Pt f) : IsOpenImmersion (trι L t ι s) := by
  unfold trι; infer_instance

scoped instance [IsClosedImmersion ι] (s : Pt f) : IsClosedImmersion (trι L t ι s) := by
  unfold trι; infer_instance

theorem trι_comp_f (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (R k t)))) (s : Pt f) :
    trι L t ι s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (R k t))) := by
  simp only [trι, Category.assoc, transl_over]; exact hιf

variable (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (R k t))))
  (S : Finset (Pt f))
  (hidx : ∀ x : Pt f, ∃ s ∈ S,
    ∃ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (Spec.map (CommRingCat.ofHom (algebraMap k (R k t)))),
      x = L.mul (𝟙 _) s ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩)

include hidx in

theorem exists_eq_comp_trι (x : Pt f) :
    ∃ s ∈ S, ∃ τ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R k t)), x.1 = τ ≫ trι L t ι s := by
  obtain ⟨s, hs, τ, rfl⟩ := hidx x
  refine ⟨s, hs, τ.1, ?_⟩
  have h := comp_transl L (w := 𝟙 _) ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩ s
  rw [cst_id] at h
  exact h.symm.trans (Category.assoc _ _ _)

include hidx in

theorem iSup_opensRange_trι [IsAlgClosed k] [LocallyOfFiniteType f] [IsOpenImmersion ι] [IsClosedImmersion ι] :
    ⨆ s : S, (trι L t ι s).opensRange = ⊤ := by
  have hC : IsClosed (⋃ s ∈ (S : Set (Pt f)), Set.range (trι L t ι s)) :=
    S.finite_toSet.isClosed_biUnion fun s _ => (trι L t ι s).isClosedEmbedding.isClosed_range
  have hsub : {x : X | ∃ σ : Spec (.of k) ⟶ X, σ ≫ f = 𝟙 _ ∧ σ (IsLocalRing.closedPoint k) = x} ⊆
      ⋃ s ∈ (S : Set (Pt f)), Set.range (trι L t ι s) := by
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨s, hs, τ, hx⟩ := exists_eq_comp_trι L t ι hιf S hidx ⟨σ, hσ⟩
    refine Set.mem_biUnion hs ⟨τ (IsLocalRing.closedPoint k), ?_⟩
    have hx' : σ = τ ≫ trι L t ι s := hx
    change _ = σ _
    rw [hx']
    simp
  have huniv : (⋃ s ∈ (S : Set (Pt f)), Set.range (trι L t ι s)) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed f).closure_eq]
    exact closure_minimal hsub hC
  apply Opens.ext
  rw [Opens.coe_iSup, Opens.coe_top, ← huniv]
  ext x
  simp only [Set.mem_iUnion, Scheme.Hom.coe_opensRange, Finset.mem_coe, Subtype.exists, exists_prop]

section Piece

variable (m : ℕ)

abbrev e : Spec (CommRingCat.of k) ⟶ X := (L.one (𝟙 (Spec (CommRingCat.of k)))).1

abbrev jj : L.schemeKer m ⟶ X := pullback.fst (L.schemeNsmul m) (e L)

abbrev Wp [IsOpenImmersion ι] (s : Pt f) : (L.schemeKer m).Opens := jj L m ⁻¹ᵁ (trι L t ι s).opensRange

theorem monoidHom_ext_single {M : Type*} [CommGroup M] {G H : Multiplicative (Fin t → ℤ) →* M}
    (h : ∀ i, G (Multiplicative.ofAdd (Pi.single i 1)) = H (Multiplicative.ofAdd (Pi.single i 1))) :
    G = H := by
  refine MonoidHom.ext fun w => ?_
  have hw : w = ∏ i, Multiplicative.ofAdd (Pi.single i (w.toAdd i) : Fin t → ℤ) := by
    rw [← ofAdd_sum, Finset.univ_sum_single]; rfl
  have hi : ∀ (i : Fin t) (n : ℤ), Multiplicative.ofAdd (Pi.single i n : Fin t → ℤ) =
      Multiplicative.ofAdd (Pi.single i (1 : ℤ) : Fin t → ℤ) ^ n := by
    intro i n
    rw [← ofAdd_zsmul]
    congr 1
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [hw, map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [hi, map_zpow, map_zpow, h]

theorem exists_eq_SpecMap_ev [NeZero m] (c' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R k t)))
    (h : c' ≫ Spec.map (CommRingCat.ofHom (algebraMap k (R k t))) = 𝟙 _) :
    ∃ c : Fin t → kˣ, c' = Spec.map (CommRingCat.ofHom (ev k t c).toRingHom) := by
  let φ : CommRingCat.of (R k t) ⟶ CommRingCat.of k := Spec.preimage c'
  have hφ : Spec.map φ = c' := Spec.map_preimage c'
  have hφk : ∀ b : k, φ.hom (algebraMap k (R k t) b) = b := by
    intro b
    have h1 : CommRingCat.ofHom (algebraMap k (R k t)) ≫ φ = 𝟙 _ := by
      rw [← Spec.map_inj, Spec.map_comp, Spec.map_id, hφ, h]
    exact congrArg (fun ψ : CommRingCat.of k ⟶ CommRingCat.of k => ψ.hom b) h1
  let F : Multiplicative (Fin t → ℤ) →* kˣ :=
    (φ.hom.toMonoidHom.comp (AddMonoidAlgebra.of k (Fin t → ℤ))).toHomUnits
  have hF : ∀ v : Fin t → ℤ, ((F (Multiplicative.ofAdd v) : kˣ) : k) = φ.hom (single v 1) := fun v => rfl
  let c : Fin t → kˣ := fun i => F (Multiplicative.ofAdd (Pi.single i 1))
  have hchi : chi k t c = F := by
    refine monoidHom_ext_single t fun i => ?_
    change (∏ j, c j ^ ((Pi.single i (1 : ℤ) : Fin t → ℤ) j)) = c i
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  refine ⟨c, ?_⟩
  rw [← hφ]
  congr 1
  ext1
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun a => ?_)
  · change φ.hom (algebraMap k (R k t) b) = ev k t c (single 0 b)
    rw [hφk, ev_single, ofAdd_zero, map_one, Units.val_one, mul_one]
  · change φ.hom (single a 1) = ev k t c (single a 1)
    rw [ev_single, one_mul, hchi, hF]

theorem quasiCompact_of_finite {Y Z : Scheme.{u}} (g : Y ⟶ Z) [Finite Y] : QuasiCompact g :=
  ⟨fun U _ _ => (Set.toFinite _).isCompact⟩

variable (hιn : ∀ n : ℕ, ι ≫ L.schemeNsmul n =
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom k (n • AddMonoidHom.id (Fin t → ℤ)))) ≫ ι)

include hιf hιn in

theorem piece (hc : L.IsCommutative) [IsOpenImmersion ι] [NeZero m] (s : Pt f) :
    IsEmpty (Wp L t ι m s) ∨
    ∃ (c : Fin t → kˣ) (a : (Wp L t ι m s : Scheme.{u}) ⟶ Spec (CommRingCat.of (R k t))),
      IsPullback a ((Wp L t ι m s).ι ≫ L.schemeKerStr m) (Spec.map (CommRingCat.ofHom (pow k t m)))
        (Spec.map (CommRingCat.ofHom (ev k t c).toRingHom)) := by

  let a₀ : (Wp L t ι m s : Scheme.{u}) ⟶ Spec (CommRingCat.of (R k t)) :=
    IsOpenImmersion.lift (trι L t ι s) ((Wp L t ι m s).ι ≫ jj L m) (by
      rintro _ ⟨x, rfl⟩
      exact x.2)
  have sq1 : IsPullback a₀ (Wp L t ι m s).ι (trι L t ι s) (jj L m) :=
    IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm
      (by rw [Scheme.Opens.opensRange_ι])
  have sq2 : IsPullback (jj L m) (L.schemeKerStr m) (L.schemeNsmul m) (e L) := IsPullback.of_hasPullback _ _
  have big := sq1.paste_vert sq2
  have hleg : trι L t ι s ≫ L.schemeNsmul m =
      Spec.map (CommRingCat.ofHom (pow k t m)) ≫ trι L t ι (L.nsmul (𝟙 _) m s) := by
    simp only [trι, Category.assoc]
    rw [transl_schemeNsmul L hc, ← Category.assoc, hιn m, Category.assoc]
  rw [hleg] at big
  by_cases he : Set.range (e L) ⊆ Set.range (trι L t ι (L.nsmul (𝟙 _) m s))
  · right
    let c' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R k t)) :=
      IsOpenImmersion.lift (trι L t ι (L.nsmul (𝟙 _) m s)) (e L) he
    have hc' : c' ≫ trι L t ι (L.nsmul (𝟙 _) m s) = e L := IsOpenImmersion.lift_fac _ _ _
    have sqr : IsPullback (𝟙 _) c' (e L) (trι L t ι (L.nsmul (𝟙 _) m s)) :=
      IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, hc']⟩
    have p : ((Wp L t ι m s).ι ≫ L.schemeKerStr m) ≫ c' = a₀ ≫ Spec.map (CommRingCat.ofHom (pow k t m)) := by
      have w := big.w
      rw [← cancel_mono (trι L t ι (L.nsmul (𝟙 _) m s))]
      simp only [Category.assoc, hc'] at w ⊢
      exact w.symm
    have sq : IsPullback ((Wp L t ι m s).ι ≫ L.schemeKerStr m) a₀ c' (Spec.map (CommRingCat.ofHom (pow k t m))) :=
      IsPullback.of_right (by simpa only [Category.comp_id] using big.flip) p sqr
    have hc'k : c' ≫ Spec.map (CommRingCat.ofHom (algebraMap k (R k t))) = 𝟙 _ := by
      rw [← trι_comp_f L t ι hιf (L.nsmul (𝟙 _) m s), ← Category.assoc, hc']
      exact (L.one (𝟙 _)).2
    obtain ⟨c, hcc⟩ := exists_eq_SpecMap_ev (k := k) t m c' hc'k
    refine ⟨c, a₀, ?_⟩
    rw [← hcc]
    exact sq.flip
  · left
    refine ⟨fun x => he ?_⟩
    rintro _ ⟨y, rfl⟩
    have hy : y = ((Wp L t ι m s).ι ≫ L.schemeKerStr m) x := Subsingleton.elim _ _
    have hw := congrArg (fun φ : ((Wp L t ι m s : Scheme.{u}) ⟶ X) => φ x) big.w
    simp only [Scheme.Hom.comp_apply] at hw
    rw [hy]
    exact ⟨_, hw⟩

theorem bound_of_isEmpty {P : Scheme.{u}} [IsEmpty P] (b : P ⟶ Spec (CommRingCat.of k)) :
    letI := Cover.alg b
    Module.Finite k Γ(P, ⊤) ∧ Module.finrank k Γ(P, ⊤) ≤ m ^ t := by
  letI := Cover.alg b
  haveI : Subsingleton Γ(P, ⊤) := inferInstance
  exact ⟨Module.Finite.of_finite, by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _⟩

include hιf hιn in

theorem piece_bound (hc : L.IsCommutative) [IsOpenImmersion ι] [NeZero m] [IsAlgClosed k] (s : Pt f) :
    (letI := Cover.alg ((Wp L t ι m s).ι ≫ L.schemeKerStr m)
     Module.Finite k Γ((Wp L t ι m s : Scheme.{u}), ⊤) ∧
       Module.finrank k Γ((Wp L t ι m s : Scheme.{u}), ⊤) ≤ m ^ t) ∧
    LocallyQuasiFinite ((Wp L t ι m s).ι ≫ L.schemeKerStr m) := by
  rcases piece L t ι hιf m hιn hc s with hE | ⟨c, a, h⟩
  · refine ⟨bound_of_isEmpty t m _, ?_⟩
    infer_instance
  · obtain ⟨hfin, hmod, hrk⟩ := finrank_of_isPullback_pow k t m c a _ h
    haveI := hfin
    refine ⟨⟨hmod, hrk.le⟩, ?_⟩
    infer_instance

include hιf hιn hidx in

theorem main [IsAlgClosed k] [LocallyOfFiniteType f] [QuasiCompact f] (hc : L.IsCommutative)
    [IsOpenImmersion ι] [IsClosedImmersion ι] (hm : 0 < m) :
    IsFinite (L.schemeKerStr m) ∧
    (letI := Cover.alg (L.schemeKerStr m)
     Module.finrank k Γ(L.schemeKer m, ⊤) ≤ S.card * m ^ t) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  have hW : ⨆ s : S, Wp L t ι m s = ⊤ := by
    change ⨆ s : S, jj L m ⁻¹ᵁ (trι L t ι s).opensRange = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_opensRange_trι L t ι hιf S hidx]
    rfl
  have hP := fun s : S => piece_bound L t ι hιf m hιn hc (s : Pt f)
  obtain ⟨hfin, hrank⟩ := Cover.finrank_le_sum (L.schemeKerStr m) (fun s : S => Wp L t ι m s) hW
    (fun _ => m ^ t) (fun s => (hP s).1.1) (fun s => (hP s).1.2)
  refine ⟨?_, hrank.trans (le_of_eq ?_)⟩
  · haveI : LocallyQuasiFinite (L.schemeKerStr m) :=
      (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyQuasiFinite) _ hW).mpr fun s => (hP s).2
    haveI : QuasiCompact (e L) := quasiCompact_of_finite _
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : CompactSpace (L.schemeKer m) := inferInstance
    haveI : QuasiCompact (L.schemeKerStr m) :=
      (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr ‹_›
    haveI : Finite (L.schemeKer m) :=
      Set.finite_univ_iff.mp (((L.schemeKerStr m).finite_preimage_singleton
        (IsLocalRing.closedPoint k)).subset fun x _ =>
          Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)))
    haveI : DiscreteTopology (L.schemeKer m) := by
      have hd := (L.schemeKerStr m).isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)
      refine isDiscrete_univ_iff.mp ?_
      convert hd using 1
      exact (Set.eq_univ_of_forall fun x =>
        Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))).symm
    haveI : IsAffine (L.schemeKer m) := inferInstance
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    exact ⟨inferInstance, RingHom.Finite.of_comp_finite hfin⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]

end Piece
p2m_reactivate "P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.LenBound"

end Torus
p2m_reactivate "P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.LenBound"

end Geom
p2m_reactivate "P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.LenBound P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.LenBound.Geom"
end LenBound
p2m_reactivate "P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.LenBound P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.LenBound.Geom"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.LenBound P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.LenBound.Geom"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian in

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : RelativeGroupLaw k f) (hcomm : L.IsCommutative)
    (t : ℕ) (ι : Spec (CommRingCat.of (AddMonoidAlgebra k (Fin t → ℤ))) ⟶ X) [IsOpenImmersion ι] [IsClosedImmersion ι]
    (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ)))))
    (hιn : ∀ n : ℕ, ι ≫ L.schemeNsmul n =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom k (n • AddMonoidHom.id (Fin t → ℤ)))) ≫ ι)
    (S : Finset (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f))
    (hidx : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, ∃ s ∈ S,
      ∃ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ))))),
        x = L.mul (𝟙 _) s ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩)
    (m : ℕ) (hm : 0 < m) :
    IsFinite (L.schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeKerStr m) ⊤
     Module.finrank k Γ(L.schemeKer m, ⊤) ≤ S.card * m ^ t) := by
  obtain ⟨h1, h2⟩ := LenBound.Geom.main L t ι hιf S hidx m hιn hcomm hm
  refine ⟨h1, ?_⟩
  have happ : (L.schemeKerStr m).appLE ⊤ ⊤ le_top = (L.schemeKerStr m).appTop :=
    ((L.schemeKerStr m).app_eq_appLE (U := ⊤)).symm
  have halg : Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeKerStr m) ⊤ = LenBound.Cover.alg (L.schemeKerStr m) := by
    delta Scheme.TwoAffineOpenCover.algebraOfHom LenBound.Cover.alg
    rw [happ]
  rw [halg]
  exact h2

end S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus
end P2MW
export P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus (solution)
