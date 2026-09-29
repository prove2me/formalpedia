-- Prove2me | solution 1 for AlgebraicGeometry.SplitTorus.isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/64207a64-b3cb-55c4-84d5-d11cdbb187c0

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SplitTorus_isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus

open AddMonoidAlgebra

noncomputable section

namespace TorusKerRank

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
    change AddMonoidAlgebra.mapDomain _ (single _ c) = _
    rw [AddMonoidAlgebra.mapDomain_single]
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

private def _root_.TorusKerRank.inv : Rm k t m →ₐ[k] (R k t ⧸ I k t m) :=
  AddMonoidAlgebra.lift k (R k t ⧸ I k t m) (Fin t → ZMod m) (unitMap k t m)

p2m_export "TorusKerRank" "inv"
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
      single (redHom t m (Pi.single i (m : ℤ) : Fin t → ℤ)) 1 := AddMonoidAlgebra.mapDomain_single
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
  refine AddMonoidAlgebra.algHom_ext (fun w => ?_) (Algebra.ext_id _ _ _)
  rw [AlgHom.comp_apply, inv_single, fwd_mk, AlgHom.id_apply]
  change AddMonoidAlgebra.mapDomain _ (single _ (1 : k)) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  congr 1
  exact redHom_liftZ t m w

theorem inv_fwd : (inv k t m).comp (fwd k t m) = AlgHom.id k _ := by
  refine Ideal.Quotient.algHom_ext _ (AddMonoidAlgebra.algHom_ext (fun v => ?_) (Algebra.ext_id _ _ _))
  change inv k t m (fwd k t m (Ideal.Quotient.mk (I k t m) (single v 1))) = Ideal.Quotient.mk (I k t m) (single v 1)
  rw [fwd_mk]
  change inv k t m (AddMonoidAlgebra.mapDomain _ (single v (1 : k))) = _
  rw [AddMonoidAlgebra.mapDomain_single]
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

section Square

abbrev pow : R k t →+* R k t := AddMonoidAlgebra.mapDomainRingHom k (m • AddMonoidHom.id (Fin t → ℤ))

theorem pow_single (v : Fin t → ℤ) (a : k) : pow k t m (single v a) = single ((m : ℤ) • v) a := by
  change AddMonoidAlgebra.mapDomain _ (single v a) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

theorem pow_algebraMap (b : k) : pow k t m (algebraMap k (R k t) b) = algebraMap k (R k t) b := by
  change pow k t m (single 0 b) = single 0 b
  rw [pow_single, smul_zero]

def aug : R k t →ₐ[k] k := AddMonoidAlgebra.lift k k (Fin t → ℤ) 1

theorem aug_single (v : Fin t → ℤ) (a : k) : aug k t (single v a) = a := by
  rw [aug, AddMonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]

theorem aug_algebraMap (b : k) : aug k t (algebraMap k (R k t) b) = b := AlgHom.commutes _ b

theorem pow_zero_eq : pow k t 0 = (algebraMap k (R k t)).comp (aug k t).toRingHom := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun a => ?_)
  · rw [RingHom.comp_apply]
    change pow k t 0 (algebraMap k (R k t) b) = algebraMap k (R k t) (aug k t (algebraMap k (R k t) b))
    rw [pow_algebraMap, aug_algebraMap]
  · rw [RingHom.comp_apply, pow_single]
    change single ((0 : ℤ) • a) (1 : k) = algebraMap k (R k t) (aug k t (single a 1))
    rw [aug_single, zero_smul, map_one, AddMonoidAlgebra.one_def]

theorem mk_comp_pow :
    (Ideal.Quotient.mk (I k t m)).comp (pow k t m) = (algebraMap k (R k t ⧸ I k t m)).comp (aug k t).toRingHom := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun a => ?_)
  · rw [RingHom.comp_apply, RingHom.comp_apply, pow_single, smul_zero]
    change _ = algebraMap k _ (aug k t (single 0 b))
    rw [aug_single, ← Ideal.Quotient.mk_algebraMap]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, pow_single,
      mk_single_eq_one_of_dvd k t m _ (fun i => ⟨a i, by simp⟩)]
    change _ = algebraMap k _ (aug k t (single a 1))
    rw [aug_single, map_one]

open CategoryTheory CategoryTheory.Limits

theorem inl_apply_eq_zero
    (sq : PushoutCocone (CommRingCat.ofHom (pow k t m)) (CommRingCat.ofHom (aug k t).toRingHom)) :
    ∀ a ∈ I k t m, sq.inl.hom a = 0 := by
  have hle : I k t m ≤ RingHom.ker sq.inl.hom := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have hsingle : (m : ℤ) • (Pi.single i (1 : ℤ) : Fin t → ℤ) = Pi.single i (m : ℤ) := by
      ext j; by_cases hj : j = i <;> simp [hj, Pi.single_apply]
    have h1 : sq.inl.hom (single (Pi.single i (m : ℤ) : Fin t → ℤ) (1 : k)) = sq.inr.hom 1 := by
      have := CategoryTheory.congr_fun sq.condition (single (Pi.single i (1 : ℤ) : Fin t → ℤ) (1 : k))
      change sq.inl.hom (pow k t m (single _ 1)) = sq.inr.hom (aug k t (single _ 1)) at this
      rwa [pow_single, aug_single, hsingle] at this
    rw [map_sub, h1, map_one, map_one, sub_self]
  intro a ha
  exact hle ha

theorem isPushout_unitFibre :
    IsPushout (CommRingCat.ofHom (pow k t m)) (CommRingCat.ofHom (aug k t).toRingHom)
      (CommRingCat.ofHom (Ideal.Quotient.mk (I k t m)))
      (CommRingCat.ofHom (algebraMap k (R k t ⧸ I k t m))) := by
  have hsq : CommRingCat.ofHom (pow k t m) ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I k t m)) =
      CommRingCat.ofHom (aug k t).toRingHom ≫ CommRingCat.ofHom (algebraMap k (R k t ⧸ I k t m)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, mk_comp_pow]
  refine IsPushout.of_isColimit' ⟨hsq⟩ (PushoutCocone.IsColimit.mk hsq
    (fun sq => CommRingCat.ofHom (Ideal.Quotient.lift (I k t m) sq.inl.hom (inl_apply_eq_zero k t m sq)))
    ?facl ?facr ?uniq)
  · intro sq
    apply CommRingCat.hom_ext
    refine RingHom.ext fun a => ?_
    rfl
  · intro sq
    apply CommRingCat.hom_ext
    refine RingHom.ext fun b => ?_
    change Ideal.Quotient.lift _ sq.inl.hom (inl_apply_eq_zero k t m sq) (algebraMap k (R k t ⧸ I k t m) b) = sq.inr.hom b
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.lift_mk]
    have := CategoryTheory.congr_fun sq.condition (algebraMap k (R k t) b)
    change sq.inl.hom (pow k t m (algebraMap k (R k t) b)) = sq.inr.hom (aug k t (algebraMap k (R k t) b)) at this
    rwa [pow_algebraMap, aug_algebraMap] at this
  · intro sq g hg₁ _
    apply CommRingCat.hom_ext
    refine Ideal.Quotient.ringHom_ext ?_
    refine RingHom.ext fun a => ?_
    change g.hom (Ideal.Quotient.mk _ a) = Ideal.Quotient.lift _ sq.inl.hom (inl_apply_eq_zero k t m sq) (Ideal.Quotient.mk _ a)
    rw [Ideal.Quotient.lift_mk]
    exact CategoryTheory.congr_fun hg₁ a

end Square

section Piece

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable [NeZero m]

def quotIso : CommRingCat.of (R k t ⧸ I k t m) ≅ CommRingCat.of (Rm k t m) :=
  (quotEquiv k t m).toRingEquiv.toCommRingCatIso

theorem quotIso_inv_comp_algebraMap :
    CommRingCat.ofHom (algebraMap k (Rm k t m)) ≫ (quotIso k t m).inv =
      CommRingCat.ofHom (algebraMap k (R k t ⧸ I k t m)) := by
  apply CommRingCat.hom_ext
  refine RingHom.ext fun b => ?_
  change (quotEquiv k t m).symm (algebraMap k (Rm k t m) b) = algebraMap k _ b
  exact (quotEquiv k t m).symm.commutes b

theorem finrank_of_isPullback_pow_aug {P : Scheme.{u}}
    (a : P ⟶ Spec (CommRingCat.of (R k t))) (b : P ⟶ Spec (CommRingCat.of k))
    (h : IsPullback a b (Spec.map (CommRingCat.ofHom (pow k t m)))
      (Spec.map (CommRingCat.ofHom (aug k t).toRingHom))) :
    IsFinite b ∧
    (∃ e' : P ≅ Spec (CommRingCat.of (Rm k t m)),
      e'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Rm k t m))) = b) ∧
    (letI := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ b.appTop).hom.toAlgebra
     Module.finrank k Γ(P, ⊤) = m ^ t) := by
  have h0 := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_unitFibre k t m)
  let e : P ≅ Spec (CommRingCat.of (R k t ⧸ I k t m)) := h.isoIsPullback _ _ h0
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (R k t ⧸ I k t m))) = b :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [← he]
    haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (R k t ⧸ I k t m)))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
    infer_instance
  · refine ⟨e ≪≫ Scheme.Spec.mapIso (quotIso k t m).symm.op, ?_⟩
    rw [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom, Category.assoc]
    change e.hom ≫ Spec.map (quotIso k t m).inv ≫ Spec.map _ = b
    rw [← Spec.map_comp, quotIso_inv_comp_algebraMap, he]
  · letI : Algebra k Γ(P, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ b.appTop).hom.toAlgebra
    let ψ : CommRingCat.of (R k t ⧸ I k t m) ≅ Γ(P, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (R k t ⧸ I k t m))).symm ≪≫ Scheme.Γ.mapIso e.op
    have hψhom : ψ.hom = (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop := by
      change (Scheme.ΓSpecIso _).inv ≫ Scheme.Γ.map e.hom.op = _
      rw [Scheme.Γ_map]
      rfl
    have hψ : ∀ x : k, ψ.hom (algebraMap k (R k t ⧸ I k t m) x) = algebraMap k Γ(P, ⊤) x := by
      intro x
      rw [hψhom]
      change ((Scheme.ΓSpecIso _).inv ≫ e.hom.appTop) (algebraMap k _ x) = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ b.appTop) x
      rw [← he, Scheme.Hom.comp_appTop]
      have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (R k t ⧸ I k t m)))
      have : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap k (R k t ⧸ I k t m)))).appTop ≫ e.hom.appTop =
          CommRingCat.ofHom (algebraMap k (R k t ⧸ I k t m)) ≫ (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop := by
        rw [← Category.assoc, ← hnat, Category.assoc]
      rw [this]
      rfl
    let φ : (R k t ⧸ I k t m) ≃ₗ[k] Γ(P, ⊤) :=
      { ψ.commRingCatIsoToRingEquiv with
        map_smul' := fun r x => by
          change ψ.hom (r • x) = algebraMap k Γ(P, ⊤) r * ψ.hom x
          rw [show r • x = algebraMap k (R k t ⧸ I k t m) r * x from Algebra.smul_def r x, map_mul, hψ] }
    rw [← φ.finrank_eq, finrank_quot]

end Piece

section Generic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)}

theorem one_coe_eq (G : RelativeGroupLaw S f) {T : Scheme.{u}} (w : T ⟶ Spec (CommRingCat.of S)) :
    (G.one w).1 = w ≫ (G.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  have h := G.one_natural (𝟙 _) w w (Category.comp_id w)
  rw [← h, schemeHomOverComp_coe]

theorem schemeNsmul_zero (G : RelativeGroupLaw S f) : G.schemeNsmul 0 = f ≫ (G.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  show (G.nsmul f 0 RelativeGroupLaw.idPoint).1 = _
  rw [RelativeGroupLaw.nsmul_zero, one_coe_eq]

end Generic

end TorusKerRank
p2m_reactivate "P2MW.S_AlgebraicGeometry_SplitTorus_isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme.TorusKerRank"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_SplitTorus_isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme.TorusKerRank"

open TorusKerRank in

theorem solution
    {κ : Type u} [Field κ] (t : ℕ) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of κ))
    (L : RelativeGroupLaw κ f)
    (e : torusScheme κ t ≅ X) (hef : e.hom ≫ f = torusStr κ t)
    (hen : ∀ n : ℕ, e.hom ≫ L.schemeNsmul n =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom κ (n • AddMonoidHom.id (Fin t → ℤ)))) ≫ e.hom)
    (m : ℕ) (hm : 0 < m) :
    IsFinite (L.schemeKerStr m) ∧
    (∃ e' : L.schemeKer m ≅ muScheme κ t m, e'.hom ≫ muStr κ t m = L.schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeKerStr m) ⊤
     Module.finrank κ Γ(L.schemeKer m, ⊤) = m ^ t) := by
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩

  let u : Spec (CommRingCat.of κ) ⟶ X := (L.one (𝟙 (Spec (CommRingCat.of κ)))).1
  let ε : torusScheme κ t ⟶ Spec (CommRingCat.of κ) := torusStr κ t
  let s : Spec (CommRingCat.of κ) ⟶ torusScheme κ t := Spec.map (CommRingCat.ofHom (aug κ t).toRingHom)

  have hsε : s ≫ torusStr κ t = 𝟙 _ := by
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (aug κ t).toRingHom.comp (algebraMap κ (R κ t)) = RingHom.id κ := RingHom.ext (aug_algebraMap κ t)
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  have hu : u = s ≫ e.hom := by
    have h0 := hen 0
    rw [schemeNsmul_zero, ← Category.assoc, hef] at h0

    have hp : Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom κ (0 • AddMonoidHom.id (Fin t → ℤ)))) = torusStr κ t ≫ s := by
      show Spec.map (CommRingCat.ofHom (pow κ t 0)) = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← pow_zero_eq]
    rw [hp, Category.assoc] at h0
    have := congrArg (fun φ => s ≫ φ) h0
    simp only [← Category.assoc, hsε, Category.id_comp] at this
    exact this

  have hsq : IsPullback (pullback.fst (L.schemeNsmul m) u) (L.schemeKerStr m) (L.schemeNsmul m) u :=
    IsPullback.of_hasPullback _ _
  have hm' : L.schemeNsmul m ≫ e.inv =
      e.inv ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ (m • AddMonoidHom.id (Fin t → ℤ)))) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, hen m, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hu' : u ≫ e.inv = s := by rw [hu, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hsq' : IsPullback (pullback.fst (L.schemeNsmul m) u ≫ e.inv) (L.schemeKerStr m)
      (Spec.map (CommRingCat.ofHom (pow κ t m))) (Spec.map (CommRingCat.ofHom (aug κ t).toRingHom)) := by
    refine IsPullback.of_iso hsq (Iso.refl _) e.symm (Iso.refl _) e.symm ?_ ?_ ?_ ?_ <;>
      first
      | exact hm'
      | exact hu'
      | (simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp, Category.comp_id])
  obtain ⟨hfin, ⟨e', he'⟩, hrank⟩ := finrank_of_isPullback_pow_aug κ t m _ _ hsq'
  refine ⟨hfin, ⟨e', he'⟩, ?_⟩
  have happ : (L.schemeKerStr m).appLE ⊤ ⊤ le_top = (L.schemeKerStr m).appTop :=
    ((L.schemeKerStr m).app_eq_appLE (U := ⊤)).symm
  have halg : Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeKerStr m) ⊤ =
      ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv ≫ (L.schemeKerStr m).appTop).hom.toAlgebra := by
    delta Scheme.TwoAffineOpenCover.algebraOfHom
    rw [happ]
  rw [halg]
  exact hrank

end S_AlgebraicGeometry_SplitTorus_isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme
end P2MW
export P2MW.S_AlgebraicGeometry_SplitTorus_isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme (solution)
