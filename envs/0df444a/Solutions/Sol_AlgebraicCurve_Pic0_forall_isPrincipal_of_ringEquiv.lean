-- Prove2me | solution 1 for AlgebraicCurve.Pic0.forall_isPrincipal_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6aeb1098-1a72-5434-890c-d8b40b5a7897

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degZero Divisor.principal Divisor.mem_principal Pic0"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg ord ord_unit_smul_zpow exists_unit_mul_zpow ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing'"
p2m_open "AlgebraicCurve.Place"

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F')

private def comapSymmRingEquiv (V : ValuationSubring F) :
    V ≃+* (V.comap (e.symm : F' →+* F)) where
  toFun x := ⟨e x, by
    rw [ValuationSubring.mem_comap]
    show e.symm (e x) ∈ V
    rw [e.symm_apply_apply]
    exact x.2⟩
  invFun y := ⟨e.symm y, y.2⟩
  left_inv x := by
    ext
    exact e.symm_apply_apply x
  right_inv y := by
    ext
    exact e.apply_symm_apply y
  map_mul' x y := by
    ext
    exact e.map_mul x y
  map_add' x y := by
    ext
    exact e.map_add x y

@[scoped simp]
private theorem coe_comapSymmRingEquiv_apply (V : ValuationSubring F) (x : V) :
    ((comapSymmRingEquiv e V x : (V.comap (e.symm : F' →+* F))) : F') = e x := rfl

variable (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include he

private theorem symm_algebraMap_comm (a : K) : e.symm (algebraMap K F' a) = algebraMap K F a := by
  rw [← he a, e.symm_apply_apply]

private def congrRingEquiv (v : Place K F) : Place K F' where
  toValuationSubring := v.toValuationSubring.comap (e.symm : F' →+* F)
  algebraMap_mem' a := by
    rw [ValuationSubring.mem_comap]
    show e.symm (algebraMap K F' a) ∈ v.toValuationSubring
    rw [symm_algebraMap_comm e he a]
    exact v.algebraMap_mem' a
  ne_top' := fun h =>
    v.ne_top' (SetLike.ext fun x =>
      ⟨fun _ => ValuationSubring.mem_top x, fun _ => by
        have hx : e x ∈ v.toValuationSubring.comap (e.symm : F' →+* F) := by
          rw [h]
          exact ValuationSubring.mem_top _
        rw [ValuationSubring.mem_comap] at hx
        have : e.symm (e x) ∈ v.toValuationSubring := hx
        rwa [e.symm_apply_apply] at this⟩)
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective
      (comapSymmRingEquiv e v.toValuationSubring : _ ≃+* _)
      (comapSymmRingEquiv e v.toValuationSubring).surjective

@[scoped simp]
private theorem congrRingEquiv_toValuationSubring (v : Place K F) :
    (congrRingEquiv e he v).toValuationSubring
      = v.toValuationSubring.comap (e.symm : F' →+* F) := rfl

private theorem ord_congrRingEquiv (v : Place K F) (f : F) :
    (congrRingEquiv e he v).ord (e f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ

  have hπ' : Irreducible (comapSymmRingEquiv e v.toValuationSubring π) :=
    (MulEquiv.irreducible_iff (comapSymmRingEquiv e v.toValuationSubring)).mpr hπ
  have hu' : IsUnit (comapSymmRingEquiv e v.toValuationSubring (u : v.toValuationSubring)) :=
    u.isUnit.map (comapSymmRingEquiv e v.toValuationSubring)
  have key : e f
      = ((hu'.unit : (v.toValuationSubring.comap (e.symm : F' →+* F))) : F')
        * (((comapSymmRingEquiv e v.toValuationSubring π :
            (v.toValuationSubring.comap (e.symm : F' →+* F))) : F') ^ (v.ord f)) := by
    rw [IsUnit.unit_spec, coe_comapSymmRingEquiv_apply, coe_comapSymmRingEquiv_apply,
      ← map_zpow₀, ← map_mul, ← hu]
  rw [key]
  exact (congrRingEquiv e he v).ord_unit_smul_zpow hu'.unit hπ' (v.ord f)

private def congrResidueAlgEquiv (v : Place K F) :
    v.ResidueField ≃ₐ[K] (congrRingEquiv e he v).ResidueField :=
  AlgEquiv.ofRingEquiv
    (f := IsLocalRing.ResidueField.mapEquiv (comapSymmRingEquiv e v.toValuationSubring))
    (fun a => by
      have h3 : (comapSymmRingEquiv e v.toValuationSubring)
            (algebraMap K v.toValuationSubring a)
          = algebraMap K (congrRingEquiv e he v).toValuationSubring a := by
        ext
        rw [coe_comapSymmRingEquiv_apply, coe_algebraMap, coe_algebraMap]
        exact he a
      show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _)
        = IsLocalRing.residue _ _
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      exact congrArg _ h3)

private theorem deg_congrRingEquiv (v : Place K F) : (congrRingEquiv e he v).deg = v.deg :=
  ((congrResidueAlgEquiv e he v).toLinearEquiv.finrank_eq).symm

private def congrEquiv : Place K F ≃ Place K F' where
  toFun := congrRingEquiv e he
  invFun := congrRingEquiv e.symm (symm_algebraMap_comm e he)
  left_inv v := by
    ext1
    refine SetLike.ext fun x => ?_
    show e.symm (e.symm.symm x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
    rw [RingEquiv.symm_symm, e.symm_apply_apply]
  right_inv v := by
    ext1
    refine SetLike.ext fun x => ?_
    show e.symm.symm (e.symm x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
    rw [RingEquiv.symm_symm, e.apply_symm_apply]

@[scoped simp]
private theorem congrEquiv_apply (v : Place K F) : congrEquiv e he v = congrRingEquiv e he v := rfl

@[scoped simp]
private theorem congrEquiv_symm_apply (v : Place K F') :
    (congrEquiv e he).symm v = congrRingEquiv e.symm (symm_algebraMap_comm e he) v := rfl

end Congr

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv.AlgebraicCurve.Place"

section SubsingletonCriterion

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Pic0
p2m_open_scoped "AlgebraicCurve.Pic0" in
private theorem _root_.AlgebraicCurve.Pic0.subsingleton_iff :
    Subsingleton (Pic0 K F) ↔
      Divisor.degZero (K := K) (F := F) ≤ Divisor.principal (K := K) (F := F) :=
  QuotientAddGroup.subsingleton_iff.trans AddSubgroup.addSubgroupOf_eq_top

end Pic0
p2m_export "AlgebraicCurve" "Pic0.subsingleton_iff"
p2m_open_scoped "AlgebraicCurve.Pic0" in
private theorem Pic0.subsingleton_of_forall_isPrincipal
    (h : ∀ D : Divisor K F, Divisor.degree D = 0 → D.IsPrincipal) :
    Subsingleton (Pic0 K F) :=
  (Pic0.subsingleton_iff K F).mpr fun D hD => Divisor.mem_principal.mpr (h D hD)

end SubsingletonCriterion
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv.AlgebraicCurve.Place"

namespace Pic0
p2m_open "AlgebraicCurve.Pic0"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include e he

private theorem forall_isPrincipal_of_ringEquiv
    (h : ∀ D : Divisor K F, Divisor.degree D = 0 → D.IsPrincipal)
    (D' : Divisor K F') (hD' : Divisor.degree D' = 0) : D'.IsPrincipal := by
  classical

  set c := Place.congrEquiv e he with hc
  set D : Divisor K F := Finsupp.equivMapDomain c.symm D' with hD_def

  have happly : ∀ v' : Place K F', D (c.symm v') = D' v' := by
    intro v'
    rw [hD_def, Finsupp.equivMapDomain_apply, Equiv.symm_symm, c.apply_symm_apply]

  have hdeg : Divisor.degree D = 0 := by
    rw [← hD']
    rw [hD_def]
    have h1 : Divisor.degree (Finsupp.equivMapDomain c.symm D')
        = (Finsupp.equivMapDomain c.symm D').sum fun v n => n * (v.deg : ℤ) :=
      Finsupp.liftAddHom_apply _ _
    have h2 : Divisor.degree D' = D'.sum fun v n => n * (v.deg : ℤ) :=
      Finsupp.liftAddHom_apply _ _
    rw [h1, h2, Finsupp.sum_equivMapDomain]
    refine Finsupp.sum_congr fun v' _ => ?_
    congr 1
    exact_mod_cast congrArg (Nat.cast (R := ℤ))
      (Place.deg_congrRingEquiv e.symm (Place.symm_algebraMap_comm e he) v')

  obtain ⟨f, hf, hf_ord⟩ := h D hdeg

  refine ⟨e f, by simpa using hf, fun v' => ?_⟩
  calc D' v' = D (c.symm v') := (happly v').symm
    _ = (c.symm v').ord f := hf_ord (c.symm v')
    _ = (Place.congrRingEquiv e he (c.symm v')).ord (e f) :=
        (Place.ord_congrRingEquiv e he (c.symm v') f).symm
    _ = v'.ord (e f) := by rw [show Place.congrRingEquiv e he (c.symm v') = v' from
        c.apply_symm_apply v']

private theorem subsingleton_of_ringEquiv (h : Subsingleton (Pic0 K F)) :
    Subsingleton (Pic0 K F') :=
  Pic0.subsingleton_of_forall_isPrincipal K F'
    (forall_isPrincipal_of_ringEquiv e he fun _ hD =>
      Divisor.mem_principal.mp ((Pic0.subsingleton_iff K F).mp h hD))

end Pic0
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv.AlgebraicCurve"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv.AlgebraicCurve in
theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (h : ∀ D : Divisor K F, Divisor.degree D = 0 → D.IsPrincipal)
    (D' : Divisor K F') (hD' : Divisor.degree D' = 0) :
    D'.IsPrincipal :=
  AlgebraicCurve.Pic0.forall_isPrincipal_of_ringEquiv e he h D' hD'

end S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv (solution)
