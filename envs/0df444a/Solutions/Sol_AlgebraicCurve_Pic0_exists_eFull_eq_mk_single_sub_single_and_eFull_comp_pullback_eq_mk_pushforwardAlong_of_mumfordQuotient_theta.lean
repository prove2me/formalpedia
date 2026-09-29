-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/2f971ff9-599f-5b66-8de4-12a9a078f8ed

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Mathlib.GroupTheory.Abelianization.Defs

import Theorems.Thm_CerednikDrinfeld_Omega_restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff
import Theorems.Thm_CerednikDrinfeld_Mumford_existsUnique_ribbonKernel_hom_comp_eq_of_forall_mem_stabilizer
import Theorems.Thm_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq
import Theorems.Thm_CerednikDrinfeld_Omega_countable_of_isDiscrete
import Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_eq_theta_of_mulEquiv_of_apply_eq_conj
import Theorems.Thm_CerednikDrinfeld_Omega_eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype
import Theorems.Thm_MonoidHom_map_transfer_eq_transfer_comp
import Mathlib.GroupTheory.Transfer
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Mumford_finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Theorems.Thm_ValuationSubring_not_countable_upperHalfPlane_ratClosure_completion_of_liesOverPrime
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart
import Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime
import Theorems.Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve

namespace Skel7A
open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem card_stabilizer_inv_smul_eq {P : Type} [Group P] {W : Type} [MulAction P W] (𝒯 : SimpleGraph W)
    [GraphAction P 𝒯] (H G₂ : Subgroup P) [GraphAction ↥H 𝒯] [GraphAction ↥G₂ 𝒯] (p : P)
    (Γ' : Subgroup ↥G₂) [GraphAction ↥Γ' 𝒯]
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ G₂) (d : 𝒯.Dart) :
    Nat.card (stabilizer ↥Γ' (p⁻¹ • d)) = Nat.card (stabilizer ↥H d) := by
  refine Nat.card_congr
    { toFun := fun γ => ⟨⟨p * ((γ.1 : ↥G₂) : P) * p⁻¹, (hΓ' γ.1).1 γ.1.2⟩, ?_⟩
      invFun := fun h => ⟨⟨⟨p⁻¹ * (h.1 : P) * p, hHG₂ _ h.1.2⟩, (hΓ' _).2 ?_⟩, ?_⟩
      left_inv := fun γ => Subtype.ext (Subtype.ext (Subtype.ext (by
        show p⁻¹ * (p * ((γ.1 : ↥G₂) : P) * p⁻¹) * p = ((γ.1 : ↥G₂) : P); group)))
      right_inv := fun h => Subtype.ext (Subtype.ext (by
        show p * (p⁻¹ * (h.1 : P) * p) * p⁻¹ = (h.1 : P); group)) }
  ·
    have hγ : ((γ.1 : ↥G₂) : P) • (p⁻¹ • d) = p⁻¹ • d := mem_stabilizer_iff.mp γ.2
    show (p * ((γ.1 : ↥G₂) : P) * p⁻¹) • d = d
    rw [mul_smul, mul_smul, hγ, smul_inv_smul]
  · show p * (p⁻¹ * (h.1 : P) * p) * p⁻¹ ∈ H
    rw [show p * (p⁻¹ * (h.1 : P) * p) * p⁻¹ = (h.1 : P) by group]; exact h.1.2
  · have hh : (h.1 : P) • d = d := mem_stabilizer_iff.mp h.2
    show (p⁻¹ * (h.1 : P) * p) • (p⁻¹ • d) = p⁻¹ • d
    rw [mul_smul, mul_smul, smul_inv_smul, hh]

theorem finiteIndex_of_finite_orbitQuotient_of_finite_stabilizer {H X : Type} [Group H] [MulAction H X]
    (K : Subgroup H) (x₀ : X) [Finite (orbitRel.Quotient ↥K X)] [Finite (stabilizer H x₀)] :
    K.FiniteIndex := by
  classical

  let g : H ⧸ K → orbitRel.Quotient ↥K X :=
    Quotient.lift (fun h : H => (Quotient.mk _ (h⁻¹ • x₀) : orbitRel.Quotient ↥K X)) (by
      intro a b hab
      apply Quotient.sound
      refine ⟨⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩, ?_⟩
      show (a⁻¹ * b) • (b⁻¹ • x₀) = a⁻¹ • x₀
      rw [mul_smul, smul_inv_smul])

  have hfib : ∀ h₁ h₂ : H, g (QuotientGroup.mk h₁) = g (QuotientGroup.mk h₂) →
      ∃ s : stabilizer H x₀, (QuotientGroup.mk h₂ : H ⧸ K) = QuotientGroup.mk ((s : H)⁻¹ * h₁) := by
    intro h₁ h₂ h12
    obtain ⟨k, hk⟩ : ∃ k : ↥K, k • (h₂⁻¹ • x₀) = h₁⁻¹ • x₀ := Quotient.exact h12
    have hk' : (k : H) • (h₂⁻¹ • x₀) = h₁⁻¹ • x₀ := hk
    refine ⟨⟨h₁ * (k : H) * h₂⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, hk', smul_inv_smul]
    · apply Quotient.sound
      refine QuotientGroup.leftRel_apply.mpr ?_
      rw [show h₂⁻¹ * ((h₁ * (k : H) * h₂⁻¹)⁻¹ * h₁) = ((k⁻¹ : ↥K) : H) by
        rw [Subgroup.coe_inv]; group]
      exact (k⁻¹).2

  haveI : Finite (H ⧸ K) := by
    let sec : orbitRel.Quotient ↥K X → H ⧸ K := fun q =>
      if hq : ∃ c : H ⧸ K, g c = q then hq.choose else QuotientGroup.mk 1
    refine Finite.of_surjective (fun sq : stabilizer H x₀ × orbitRel.Quotient ↥K X =>
      Quotient.map' (fun h : H => (sq.1 : H)⁻¹ * h) (fun a b hab => QuotientGroup.leftRel_apply.mpr (by
        rw [show ((sq.1 : H)⁻¹ * a)⁻¹ * ((sq.1 : H)⁻¹ * b) = a⁻¹ * b by group]
        exact QuotientGroup.leftRel_apply.mp hab)) (sec (sq.2))) ?_
    intro c
    induction c using QuotientGroup.induction_on with
    | H h =>
      have hq : ∃ c : H ⧸ K, g c = g (QuotientGroup.mk h) := ⟨_, rfl⟩
      have hsec : sec (g (QuotientGroup.mk h)) = hq.choose := dif_pos hq
      obtain ⟨h₀, hh₀⟩ := Quotient.exists_rep hq.choose
      have hg : g (QuotientGroup.mk h₀) = g (QuotientGroup.mk h) := by
        rw [show (QuotientGroup.mk h₀ : H ⧸ K) = hq.choose from hh₀]; exact hq.choose_spec
      obtain ⟨s, hs⟩ := hfib h₀ h hg
      refine ⟨(s, g (QuotientGroup.mk h)), ?_⟩
      show Quotient.map' _ _ (sec (g (QuotientGroup.mk h))) = QuotientGroup.mk h
      rw [hsec, ← hh₀, hs]
      rfl
  exact Subgroup.finiteIndex_of_finite_quotient

theorem card_stabilizer_smul_eq {G X : Type} [Group G] [MulAction G X] (g : G) (x : X) :
    Nat.card (stabilizer G (g • x)) = Nat.card (stabilizer G x) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

end Skel7A

set_option maxHeartbeats 4000000 in
theorem solution

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)

    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)
    (hϖr : Valued.v (algebraMap K₀ A.valuation.Completion ϖ.ϖ) = Valued.v ((r : ℕ) : A.valuation.Completion))

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]
    [DecidablePred (· ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)

    (Γd : Subgroup G) (htpd : Γd.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfind : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γd.map ρ)) d))

    (Fd : Type) [Field Fd] [Algebra A.valuation.Completion Fd] [hcurved : IsCurveOver A.valuation.Completion Fd]
    (eFd : Fd ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd))

    (Ed Vd : Type) [Fintype Ed] [Fintype Vd] [DecidableEq Ed] [DecidableEq Vd]
    (Dd : DegeneracyData Ed Vd)
    (eVd : Mumford.QuotVert ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ Vd)
    (eEd : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ Ed)
    (hDad : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dd.a (eEd e) = eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDbd : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dd.b (eEd e) = eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDwd : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (Dd.w (eEd e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γd.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀))]
    (Φd : Additive (Abelianization ↥(Γd.map ρ)) →+ ↥(ribbonKernel Dd))
    (hΦd : ∀ γ : ↥(Γd.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φd (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel Dd)) : Ed → ℤ) (eEd e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (ptd : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion Fd)
    (hpt_fibd : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), ptd z = ptd z' ↔ ∃ γ : ↥(Γd.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_ontod : Function.Surjective ptd)

    (hptd : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : Fd),
        x ∈ (ptd z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFd x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (ptd z).evalAt (eFd.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFd.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (ptd z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (Γc : Subgroup G) (htpc : Γc.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfinc : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γc.map ρ)) d))

    (Fc : Type) [Field Fc] [Algebra A.valuation.Completion Fc] [hcurvec : IsCurveOver A.valuation.Completion Fc]
    (eFc : Fc ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc))

    (Ec Vc : Type) [Fintype Ec] [Fintype Vc] [DecidableEq Ec] [DecidableEq Vc]
    (Dc : DegeneracyData Ec Vc)
    (eVc : Mumford.QuotVert ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ Vc)
    (eEc : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ Ec)
    (hDac : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dc.a (eEc e) = eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDbc : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dc.b (eEc e) = eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDwc : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (Dc.w (eEc e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γc.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀))]
    (Φc : Additive (Abelianization ↥(Γc.map ρ)) →+ ↥(ribbonKernel Dc))
    (hΦc : ∀ γ : ↥(Γc.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φc (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel Dc)) : Ec → ℤ) (eEc e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (ptc : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion Fc)
    (hpt_fibc : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), ptc z = ptc z' ↔ ∃ γ : ↥(Γc.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_ontoc : Function.Surjective ptc)

    (hptc : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : Fc),
        x ∈ (ptc z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFc x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (ptc z).evalAt (eFc.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFc.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (ptc z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (actZd : S →* (↥(ribbonKernel Dd) ≃ₗ[ℤ] ↥(ribbonKernel Dd))) (gald : S →* SemilinearAut A.valuation.Completion Fd)
    (actZc : S →* (↥(ribbonKernel Dc) ≃ₗ[ℤ] ↥(ribbonKernel Dc))) (galc : S →* SemilinearAut A.valuation.Completion Fc)
    (𝒰d : EquivariantUniformization r Dd A hA (Pic0 A.valuation.Completion Fd) S scalar actZd
      ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion Fd) (Pic0 A.valuation.Completion Fd)).comp gald))
    (𝒰c : EquivariantUniformization r Dc A hA (Pic0 A.valuation.Completion Fc) S scalar actZc
      ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion Fc) (Pic0 A.valuation.Completion Fc)).comp galc))
    (hQd : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γd.map ρ),
          ((((Additive.toMul (𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of α))) (Φd (Additive.ofMul (Abelianization.of β))))) :
              (↥𝒰d.K)ˣ) : ↥𝒰d.K) : A.valuation.Completion) * Omega.period (Γd.map ρ).subtype x y α β = 1))
    (hΘd : (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γd.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γd.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γd.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : 𝒰d.P.TorusPoints), (∀ γ : ↥(Γd.map ρ), u (Φd (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := Fd),
          (Dv : Divisor A.valuation.Completion Fd) = Finsupp.single (ptd ⟨a, ha⟩) 1 - Finsupp.single (ptd ⟨b, hb⟩) 1 →
          𝒰d.eFull u = Pic0.mk Dv))
    (hQc : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γc.map ρ),
          ((((Additive.toMul (𝒰c.P.Q (Φc (Additive.ofMul (Abelianization.of α))) (Φc (Additive.ofMul (Abelianization.of β))))) :
              (↥𝒰c.K)ˣ) : ↥𝒰c.K) : A.valuation.Completion) * Omega.period (Γc.map ρ).subtype x y α β = 1))
    (hΘc : (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γc.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γc.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γc.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : 𝒰c.P.TorusPoints), (∀ γ : ↥(Γc.map ρ), u (Φc (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := Fc),
          (Dv : Divisor A.valuation.Completion Fc) = Finsupp.single (ptc ⟨a, ha⟩) 1 - Finsupp.single (ptc ⟨b, hb⟩) 1 →
          𝒰c.eFull u = Pic0.mk Dv))

    (g : G) (hg : ρ g ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) (hArr : Γd ≤ Γc.map (MulAut.conj g).toMonoidHom)
    (φ : Fc →ₐ[A.valuation.Completion] Fd)
    (hφ : ∀ x : Fc, ((eFd (φ x) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd)) : FractionRing (Omega.HolRingOf ϖ ρ)) =
      g • ((eFc x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc)) : FractionRing (Omega.HolRingOf ϖ ρ)))
    (hφC : φ.toRingHom.IsIntegral) (hfinC : FiniteAlong A.valuation.Completion φ) (hsepC : SeparableAlong A.valuation.Completion φ)
    (μ : Dd.FiniteHom Dc)
    (hμV : ∀ v : LT.LatticeTree.Vertex R₀ K₀, μ.mapV (eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) =
      eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) ((ρ g)⁻¹ • v)))
    (hμE : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, ((eEc.symm (μ.mapE (eEd e))).1) = Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀).Dart) ((ρ g)⁻¹ • e.1.out))
    (hdeg : ((μ.degTotal : ℕ)) = finrankAlong A.valuation.Completion φ) :
    ∀ (a b : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (Dv : Divisor.degZero (K := A.valuation.Completion) (F := Fd))
      (Dv' : Divisor.degZero (K := A.valuation.Completion) (F := Fc)),
      (Dv : Divisor A.valuation.Completion Fd) = Finsupp.single (ptd a) 1 - Finsupp.single (ptd b) 1 →
      (Dv' : Divisor A.valuation.Completion Fc) = Divisor.pushforwardAlong φ hφC (Dv : Divisor A.valuation.Completion Fd) →
      ∃ w₀ : 𝒰d.P.TorusPoints, 𝒰d.eFull w₀ = Pic0.mk Dv ∧ 𝒰c.eFull (w₀.comp μ.pullback) = Pic0.mk Dv' := by
  classical
  intro a b Dv Dv' hDv hDv'

  let a' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) := (ρ g)⁻¹ • a
  let b' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) := (ρ g)⁻¹ • b

  have hPT : ∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (n : ℤ), Divisor.pushforwardAlong φ hφC (Finsupp.single (ptd z) n) = Finsupp.single (ptc ((ρ g)⁻¹ • z)) n :=
    fun z => (CerednikDrinfeld.Omega.restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff
      K₀ A.valuation.Completion ϖ G ρ Γd Γc Fd eFd Fc eFc g φ hφ hφC ptd hptd ptc hptc z).2.2
  have hDv'eq : (Dv' : Divisor A.valuation.Completion Fc) = Finsupp.single (ptc a') 1 - Finsupp.single (ptc b') 1 := by
    rw [hDv', hDv, map_sub, hPT, hPT]

  have N3_disc : Omega.IsDiscrete A.valuation.Completion (Γd.map ρ).subtype ∧ Omega.IsDiscrete A.valuation.Completion (Γc.map ρ).subtype := by

    have hmax : IsLocalRing.maximalIdeal R₀ = Ideal.span {ϖ₀} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).1 hϖ₀
    haveI : Finite (R₀ ⧸ Ideal.span {ϖ₀}) := by
      rw [← hmax]; exact inferInstanceAs (Finite (IsLocalRing.ResidueField R₀))
    have hint : ∀ a : R₀, Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ a)) ≤ 1 :=
      fun a => (hR₀ _).1 ⟨a, rfl⟩
    have hv : ∀ a : K₀, Valued.v (algebraMap K₀ A.valuation.Completion a) ≤ 1 → IsLocalization.IsInteger R₀ a :=
      fun a ha => (hR₀ a).2 ha

    have hsmall := ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime r A hA
    have hq : ∀ ε : A.ValueGroup, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ ϖ₀)) ^ N ≤ ε := by
      intro ε hε
      obtain ⟨x, hx⟩ := A.valuation_surjective ε
      have hx0 : x ≠ 0 := by rintro rfl; exact hε (by rw [← hx, map_zero])
      have hy0 : ((x : AlgebraicClosure ℚ) : A.valuation.Completion) ≠ 0 := by
        intro h
        apply hx0
        have h' : (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion) ((WithVal.equiv A.valuation).symm x) = 0 := h
        have hinj := (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion).injective
        simpa using hinj (h'.trans (map_zero _).symm)
      have hyv : Valued.v ((x : AlgebraicClosure ℚ) : A.valuation.Completion) = ε := by
        show Valued.v ((((WithVal.equiv A.valuation).symm x : WithVal A.valuation)) : A.valuation.Completion) = ε
        rw [Valued.valuedCompletion_apply, ← hx]; rfl
      obtain ⟨N, hN⟩ := hsmall.2.2 (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ ϖ₀)) _
        (by rw [hϖ, hϖr]; exact hsmall.2.1) hy0
      exact ⟨N, hyv ▸ hN⟩
    have hst : ∀ (Γ : Subgroup G) [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)],
        (∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d)) →
        {γ : ↥(Γ.map ρ) | (Γ.map ρ).subtype γ • LT.LatticeTree.stdVertex R₀ K₀ = LT.LatticeTree.stdVertex R₀ K₀}.Finite := by
      intro Γ _ hfinΓ
      haveI := CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart R₀ K₀ ↥(Γ.map ρ) hfinΓ
        (LT.LatticeTree.stdVertex R₀ K₀)
      exact (MulAction.stabilizer ↥(Γ.map ρ) (LT.LatticeTree.stdVertex R₀ K₀) : Set ↥(Γ.map ρ)).toFinite
    exact ⟨CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion hint hv hq (Γd.map ρ).subtype
        (hst Γd hfind),
      CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion hint hv hq (Γc.map ρ).subtype
        (hst Γc hfinc)⟩
  haveI _hAC : IsAlgClosed A.valuation.Completion := ValuationSubring.isAlgClosed_completion_of_liesOverPrime r Fact.out A hA
  haveI _hdom : IsDomain ↥(Omega.holRing ϖ) := (Omega.HolRingOf.isDomain_iff ϖ ρ).1 inferInstance

  have N3_base : ∃ z₀ : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion),
      (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a : A.valuation.Completion) ≠ (z₀ : A.valuation.Completion)) ∧
      (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b : A.valuation.Completion) ≠ (z₀ : A.valuation.Completion)) ∧
      (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a' : A.valuation.Completion) ≠ (((ρ g)⁻¹ • z₀ : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) : A.valuation.Completion)) ∧
      (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b' : A.valuation.Completion) ≠ (((ρ g)⁻¹ • z₀ : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) : A.valuation.Completion)) := by
    haveI : Countable ↥(Γd.map ρ) := CerednikDrinfeld.Omega.countable_of_isDiscrete ϖ _ N3_disc.1
    haveI : Countable ↥(Γc.map ρ) := CerednikDrinfeld.Omega.countable_of_isDiscrete ϖ _ N3_disc.2

    let S : Set A.valuation.Completion :=
      (Set.range fun γ : ↥(Γd.map ρ) => (((γ : PGL(2, K₀)) • a : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) : A.valuation.Completion)) ∪
      (Set.range fun γ : ↥(Γd.map ρ) => (((γ : PGL(2, K₀)) • b : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) : A.valuation.Completion)) ∪
      (Set.range fun γ : ↥(Γc.map ρ) => ((ρ g • ((γ : PGL(2, K₀)) • a') : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) : A.valuation.Completion)) ∪
      (Set.range fun γ : ↥(Γc.map ρ) => ((ρ g • ((γ : PGL(2, K₀)) • b') : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) : A.valuation.Completion))
    have hS : S.Countable :=
      (((Set.countable_range _).union (Set.countable_range _)).union (Set.countable_range _)).union (Set.countable_range _)

    have hC : ¬ (Set.univ : Set A.valuation.Completion).Countable := fun h =>
      ValuationSubring.not_countable_upperHalfPlane_ratClosure_completion_of_liesOverPrime r A hA (h.mono (Set.subset_univ _))
    have hΩ : ¬ (Omega.upperHalfPlane K₀ A.valuation.Completion).Countable := by
      intro hΩc

      have hL : (Set.range (algebraMap K₀ A.valuation.Completion)).Countable := by
        refine Set.MapsTo.countable_of_injOn (f := fun x : A.valuation.Completion => (a : A.valuation.Completion) + x) ?_ (fun x _ y _ h => add_left_cancel h) hΩc
        rintro x ⟨c, rfl⟩
        rw [Omega.mem_upperHalfPlane_iff]
        intro c' h
        have ha := a.2
        rw [Omega.mem_upperHalfPlane_iff] at ha
        exact ha (c' - c) (by rw [map_sub, h]; ring)
      apply hC
      have : (Set.univ : Set A.valuation.Completion) ⊆ Set.range (algebraMap K₀ A.valuation.Completion) ∪ Omega.upperHalfPlane K₀ A.valuation.Completion := by
        intro z _
        by_cases hz : z ∈ Set.range (algebraMap K₀ A.valuation.Completion)
        · exact Or.inl hz
        · exact Or.inr (by rw [Omega.mem_upperHalfPlane_iff]; rintro c rfl; exact hz ⟨c, rfl⟩)
      exact (hL.union hΩc).mono this

    obtain ⟨z₀, hz₀Ω, hz₀S⟩ : ∃ z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion, z₀ ∉ S := by
      by_contra h; push Not at h; exact hΩ (hS.mono fun x hx => h x hx)
    refine ⟨⟨z₀, hz₀Ω⟩, ?_, ?_, ?_, ?_⟩
    · intro γ h; exact hz₀S (Or.inl (Or.inl (Or.inl ⟨γ, h⟩)))
    · intro γ h; exact hz₀S (Or.inl (Or.inl (Or.inr ⟨γ, h⟩)))
    · intro γ h
      apply hz₀S; refine Or.inl (Or.inr ⟨γ, ?_⟩)
      have h' : ((γ : PGL(2, K₀)) • a' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) = (ρ g)⁻¹ • ⟨z₀, hz₀Ω⟩ := Subtype.ext h
      show ((ρ g • ((γ : PGL(2, K₀)) • a') : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) : A.valuation.Completion) = z₀
      rw [h', smul_inv_smul]
    · intro γ h
      apply hz₀S; refine Or.inr ⟨γ, ?_⟩
      have h' : ((γ : PGL(2, K₀)) • b' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) = (ρ g)⁻¹ • ⟨z₀, hz₀Ω⟩ := Subtype.ext h
      show ((ρ g • ((γ : PGL(2, K₀)) • b') : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) : A.valuation.Completion) = z₀
      rw [h', smul_inv_smul]
  obtain ⟨z₀, hz₀a, hz₀b, hz₀a', hz₀b'⟩ := N3_base
  let z₀' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) := (ρ g)⁻¹ • z₀

  have N3_mult :
      (∃ cd : ↥(Γd.map ρ) →* (A.valuation.Completion)ˣ, ∀ β : ↥(Γd.map ρ),
        ((cd β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γd.map ρ).subtype (a : A.valuation.Completion) (b : A.valuation.Completion) (z₀ : A.valuation.Completion) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (z₀ : A.valuation.Completion))) ∧
      (∃ cc : ↥(Γc.map ρ) →* (A.valuation.Completion)ˣ, ∀ β : ↥(Γc.map ρ),
        ((cc β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γc.map ρ).subtype (a' : A.valuation.Completion) (b' : A.valuation.Completion) (z₀' : A.valuation.Completion) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (z₀' : A.valuation.Completion))) := by
    constructor
    · obtain ⟨c, hc, -⟩ := CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq K₀ A.valuation.Completion ϖ hex (Γd.map ρ).subtype
        N3_disc.1 a.2 b.2 z₀.2 hz₀a hz₀b
      exact ⟨c, hc⟩
    · obtain ⟨c, hc, -⟩ := CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq K₀ A.valuation.Completion ϖ hex (Γc.map ρ).subtype
        N3_disc.2 a'.2 b'.2 z₀'.2 hz₀a' hz₀b'
      exact ⟨c, hc⟩
  obtain ⟨⟨cd, hcd⟩, ⟨cc, hcc⟩⟩ := N3_mult

  have N3_lift : ∃ w₀ : 𝒰d.P.TorusPoints, ∀ γ : ↥(Γd.map ρ), w₀ (Φd (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (cd γ) := by

    have hc : ∀ (w : LT.LatticeTree.Vertex R₀ K₀) (γ : ↥(Γd.map ρ)), γ ∈ MulAction.stabilizer ↥(Γd.map ρ) w → cd γ = 1 := by
      intro w γ hγ
      haveI : Finite ↥(MulAction.stabilizer ↥(Γd.map ρ) w) :=
        CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart R₀ K₀ ↥(Γd.map ρ) hfind w
      have hfo : IsOfFinOrder γ := by
        have h1 : IsOfFinOrder (⟨γ, hγ⟩ : ↥(MulAction.stabilizer ↥(Γd.map ρ) w)) := isOfFinOrder_of_finite _
        exact MonoidHom.isOfFinOrder (MulAction.stabilizer ↥(Γd.map ρ) w).subtype h1
      apply Units.ext
      rw [hcd, Units.val_one]
      exact CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder K₀ A.valuation.Completion ϖ hex
        (Γd.map ρ).subtype N3_disc.1 a.2 b.2 z₀.2 hz₀a hz₀b γ hfo
    exact (CerednikDrinfeld.Mumford.existsUnique_ribbonKernel_hom_comp_eq_of_forall_mem_stabilizer K₀ R₀ G ρ Γd htpd
      Ed Vd Dd eVd eEd hDad hDbd v₀ Φd hΦd A.valuation.Completion cd hc).exists
  obtain ⟨w₀, hw₀⟩ := N3_lift

  let p : PGL(2, K₀) := ρ g
  let Γ' : Subgroup ↥(Γc.map ρ) := (Γd.map ρ).comap ((MulAut.conj p).toMonoidHom.comp (Γc.map ρ).subtype)
  have hΓ' : ∀ x : ↥(Γc.map ρ), x ∈ Γ' ↔ p * (x : PGL(2, K₀)) * p⁻¹ ∈ Γd.map ρ := fun x => by
    simp only [Γ', Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

  have hconj : ∀ y : ↥(Γd.map ρ), p⁻¹ * (y : PGL(2, K₀)) * p ∈ Γc.map ρ := by
    rintro ⟨_, δ, hδ, rfl⟩
    obtain ⟨γ, hγ, hγδ⟩ := Subgroup.mem_map.1 (hArr hδ)
    refine ⟨γ, hγ, ?_⟩
    have : δ = g * γ * g⁻¹ := by rw [← hγδ]; rfl
    show ρ γ = (ρ g)⁻¹ * ρ δ * ρ g
    rw [this, map_mul, map_mul, map_inv]
    group
  let eFun : ↥Γ' → ↥(Γd.map ρ) := fun x => ⟨p * ((x : ↥(Γc.map ρ)) : PGL(2, K₀)) * p⁻¹, (hΓ' x).1 x.2⟩
  have heFun_mul : ∀ x y : ↥Γ', eFun (x * y) = eFun x * eFun y := fun x y => Subtype.ext (by
    show p * (((x * y : ↥Γ') : ↥(Γc.map ρ)) : PGL(2, K₀)) * p⁻¹ = (p * _ * p⁻¹) * (p * _ * p⁻¹)
    rw [Subgroup.coe_mul, Subgroup.coe_mul]; group)
  let eHom : ↥Γ' →* ↥(Γd.map ρ) := MonoidHom.mk' eFun heFun_mul
  have heHom : ∀ x : ↥Γ', ((eHom x : ↥(Γd.map ρ)) : PGL(2, K₀)) = p * ((x : ↥(Γc.map ρ)) : PGL(2, K₀)) * p⁻¹ := fun _ => rfl
  have hebij : Function.Bijective eHom := by
    constructor
    · intro x y h
      have h' := congrArg (fun t : ↥(Γd.map ρ) => p⁻¹ * (t : PGL(2, K₀)) * p) h
      simp only [heHom] at h'
      apply Subtype.ext; apply Subtype.ext
      simpa [mul_assoc] using h'
    · intro y
      refine ⟨⟨⟨p⁻¹ * (y : PGL(2, K₀)) * p, hconj y⟩, (hΓ' _).2 ?_⟩, Subtype.ext ?_⟩
      · show p * (p⁻¹ * (y : PGL(2, K₀)) * p) * p⁻¹ ∈ Γd.map ρ
        rw [show p * (p⁻¹ * (y : PGL(2, K₀)) * p) * p⁻¹ = y by group]; exact y.2
      · show p * (p⁻¹ * (y : PGL(2, K₀)) * p) * p⁻¹ = y
        group
  let e : ↥Γ' ≃* ↥(Γd.map ρ) := MulEquiv.ofBijective eHom hebij
  have he : ∀ x : ↥Γ', (Γd.map ρ).subtype (e x) = p * ((Γc.map ρ).subtype.comp Γ'.subtype) x * p⁻¹ := fun x => heHom x

  let ρ' : ↥Γ' →* PGL(2, K₀) := (Γc.map ρ).subtype.comp Γ'.subtype
  have hdisc' : Omega.IsDiscrete A.valuation.Completion ρ' := by
    intro ε hε
    refine ((N3_disc.2 ε hε).preimage (Γ'.subtype_injective.injOn)).subset ?_
    rintro x ⟨g₁, hg₁, h1, h2⟩
    exact ⟨g₁, hg₁, h1, h2⟩
  have hz₀a'' : ∀ γ : ↥Γ', Omega.pmoebius K₀ (ρ' γ) (a' : A.valuation.Completion) ≠ (z₀' : A.valuation.Completion) := fun γ => hz₀a' γ
  have hz₀b'' : ∀ γ : ↥Γ', Omega.pmoebius K₀ (ρ' γ) (b' : A.valuation.Completion) ≠ (z₀' : A.valuation.Completion) := fun γ => hz₀b' γ
  obtain ⟨c', hc', -⟩ := CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq K₀ A.valuation.Completion ϖ hex ρ' hdisc'
    a'.2 b'.2 z₀'.2 hz₀a'' hz₀b''

  have P3a : ∀ β : ↥Γ', cd (e β) = c' β := by
    intro β
    apply Units.ext
    rw [hcd, hc']
    have ht := CerednikDrinfeld.Omega.theta_pmoebius_eq_theta_of_mulEquiv_of_apply_eq_conj ρ' (Γd.map ρ).subtype e p he
      a'.2 b'.2 z₀'.2 (Omega.pmoebius K₀ (ρ' β) (z₀' : A.valuation.Completion)) (((ρ' β) • z₀' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion))).2

    have e1 : Omega.pmoebius K₀ p (a' : A.valuation.Completion) = (a : A.valuation.Completion) := congrArg Subtype.val (smul_inv_smul p a)
    have e2 : Omega.pmoebius K₀ p (b' : A.valuation.Completion) = (b : A.valuation.Completion) := congrArg Subtype.val (smul_inv_smul p b)
    have e3 : Omega.pmoebius K₀ p (z₀' : A.valuation.Completion) = (z₀ : A.valuation.Completion) := congrArg Subtype.val (smul_inv_smul p z₀)
    have e4 : Omega.pmoebius K₀ p (Omega.pmoebius K₀ (ρ' β) (z₀' : A.valuation.Completion)) =
        Omega.pmoebius K₀ ((Γd.map ρ).subtype (e β)) (z₀ : A.valuation.Completion) := by
      rw [he, ← e3]
      show ((p • ((ρ' β) • z₀') : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) : A.valuation.Completion) = (((p * ρ' β * p⁻¹) • (p • z₀')) : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion))
      rw [mul_smul, mul_smul, inv_smul_smul]
    rw [e1, e2, e3, e4] at ht
    exact ht

  have P3b : ∀ [Γ'.FiniteIndex], cc = MonoidHom.transfer c' := fun {_} =>
    CerednikDrinfeld.Omega.eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype K₀ A.valuation.Completion ϖ hex (Γc.map ρ).subtype
      N3_disc.2 Γ' a'.2 b'.2 z₀'.2 hz₀a' hz₀b' c' hc' cc hcc

  have P3c : ∀ [Γ'.FiniteIndex] (γ : ↥(Γc.map ρ)),
      Abelianization.lift c' (MonoidHom.transfer (Abelianization.of : ↥Γ' →* Abelianization ↥Γ') γ) = MonoidHom.transfer c' γ := by
    intro _ γ
    rw [MonoidHom.map_transfer_eq_transfer_comp]
    congr 1

  have N3_transfer : ∀ γ : ↥(Γc.map ρ), (w₀.comp μ.pullback) (Φc (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (cc γ) := by

    have hT : (BruhatTits.tree R₀ K₀).IsTree := CerednikDrinfeld.BruhatTits.tree_isTree R₀ K₀
    have hadj : ∀ u w : (LT.LatticeTree.Vertex R₀ K₀), (BruhatTits.tree R₀ K₀).Adj u w → Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) u ≠ Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w := by
      obtain ⟨hc, hb⟩ := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀
      have hadj' := (CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
        PGL(2, K₀) (BruhatTits.tree R₀ K₀) hc hb (LT.LatticeTree.stdVertex R₀ K₀)).1
      intro u w huw h
      have h1 := hadj' u w huw
      rw [← h] at h1
      exact one_ne_zero (add_left_cancel (h1.symm.trans (add_zero _).symm))
    have hτd : ∀ (γ : ↥(Γd.map ρ)) (w : (LT.LatticeTree.Vertex R₀ K₀)), Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (γ • w) = Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
      fun γ w => (Mumford.mem_typePreserving_iff (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (γ : PGL(2, K₀))).1 (htpd γ.2) w
    have hτc : ∀ (γ : ↥(Γc.map ρ)) (w : (LT.LatticeTree.Vertex R₀ K₀)), Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (γ • w) = Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
      fun γ w => (Mumford.mem_typePreserving_iff (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (γ : PGL(2, K₀))).1 (htpc γ.2) w
    have hp : ∀ w : (LT.LatticeTree.Vertex R₀ K₀), Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (p • w) = Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w := (Mumford.mem_typePreserving_iff _ _ _).1 hg
    have hHG₂ : ∀ h : PGL(2, K₀), h ∈ Γd.map ρ → p⁻¹ * h * p ∈ Γc.map ρ := fun h hh => hconj ⟨h, hh⟩

    have haBSd : ∀ e : Ed, eVd.symm (Dd.a e) = Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eEd.symm e).1.out.fst :=
      fun e => eVd.symm_apply_eq.mpr (by have h := hDad (eEd.symm e); rwa [Equiv.apply_symm_apply] at h)
    have hbBSd : ∀ e : Ed, eVd.symm (Dd.b e) = Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eEd.symm e).1.out.snd :=
      fun e => eVd.symm_apply_eq.mpr (by have h := hDbd (eEd.symm e); rwa [Equiv.apply_symm_apply] at h)
    have hΦdBS : ∀ γ : ↥(Γd.map ρ), (Φd (Additive.ofMul (Abelianization.of γ)) : Ed → ℤ) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e : Ed => (eEd.symm e).1) v₀ γ := by
      intro γ; funext e
      have h := hΦd γ (eEd.symm e)
      rw [Equiv.apply_symm_apply] at h
      rw [h]
      unfold Mumford.pathCycle Mumford.walkCycle
      split_ifs <;> simp
    have hΦcBS : ∀ γ : ↥(Γc.map ρ), (Φc (Additive.ofMul (Abelianization.of γ)) : Ec → ℤ) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e : Ec => (eEc.symm e).1) v₀ γ := by
      intro γ; funext e
      have h := hΦc γ (eEc.symm e)
      rw [Equiv.apply_symm_apply] at h
      rw [h]
      unfold Mumford.pathCycle Mumford.walkCycle
      split_ifs <;> simp

    obtain ⟨eE', eV', Φ', heE', heV', ha', hb', hΦ', hΦ'conj⟩ :=
      CerednikDrinfeld.Mumford.exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
        (BruhatTits.tree R₀ K₀) hT (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hadj (Γd.map ρ) hτd p hp (Γc.map ρ) hHG₂ Γ' hΓ'
        Dd eEd.symm eVd.symm haBSd hbBSd v₀ Φd hΦdBS

    haveI : Finite (MulAction.orbitRel.Quotient ↥Γ' (LT.LatticeTree.Vertex R₀ K₀)) := Finite.of_equiv _ eV'
    haveI : Finite ↥(MulAction.stabilizer ↥(Γc.map ρ) (LT.LatticeTree.stdVertex R₀ K₀)) :=
      CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart R₀ K₀ ↥(Γc.map ρ) hfinc _
    haveI hFI : Γ'.FiniteIndex := Skel7A.finiteIndex_of_finite_orbitQuotient_of_finite_stabilizer Γ' (LT.LatticeTree.stdVertex R₀ K₀)

    have hμE' : ∀ e₁ : Ed,
        ((eEc.symm (μ.mapE e₁)).1 : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀)) =
          Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀).Dart) ((eE' e₁).1).out := by
      intro e₁
      have h1 := hμE (eEd.symm e₁)
      rw [Equiv.apply_symm_apply] at h1
      rw [h1]
      have h2 := heE' e₁
      obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥Γ', γ' • (p⁻¹ • (eEd.symm e₁).1.out) = ((eE' e₁).1).out :=
        Quotient.exact ((Quotient.out_eq ((eE' e₁).1)).trans h2)
      refine Quotient.sound ⟨((γ'⁻¹ : ↥Γ') : ↥(Γc.map ρ)), ?_⟩
      rw [← hγ']
      show ((γ'⁻¹ : ↥Γ') : ↥(Γc.map ρ)) • ((γ' : ↥(Γc.map ρ)) • (p⁻¹ • (eEd.symm e₁).1.out)) = _
      rw [Subgroup.coe_inv, inv_smul_smul]
    have hw₂ : ∀ e₂ : Ec, (Dc.w e₂ : ℕ) =
        Nat.card (MulAction.stabilizer ↥(Γc.map ρ) (((eEc.symm e₂).1).out : (BruhatTits.tree R₀ K₀).Dart)) := by
      intro e₂
      have h := hDwc (eEc.symm e₂)
      rwa [Equiv.apply_symm_apply] at h
    have hw₁ : ∀ e₁ : Ed, (Dd.w e₁ : ℕ) = Nat.card (MulAction.stabilizer ↥Γ' (((eE' e₁).1).out : (BruhatTits.tree R₀ K₀).Dart)) := by
      intro e₁
      have h := hDwd (eEd.symm e₁)
      rw [Equiv.apply_symm_apply] at h
      rw [h, ← Skel7A.card_stabilizer_inv_smul_eq (BruhatTits.tree R₀ K₀) (Γd.map ρ) (Γc.map ρ) p Γ' hΓ' hHG₂]
      obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥Γ', γ' • (p⁻¹ • (eEd.symm e₁).1.out) = ((eE' e₁).1).out :=
        Quotient.exact ((Quotient.out_eq ((eE' e₁).1)).trans (heE' e₁))
      rw [← hγ', Skel7A.card_stabilizer_smul_eq]
    have hfinV : ∀ w : (LT.LatticeTree.Vertex R₀ K₀), Finite (MulAction.stabilizer ↥(Γc.map ρ) w) :=
      fun w => CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart R₀ K₀ ↥(Γc.map ρ) hfinc w
    have hPULL := CerednikDrinfeld.Mumford.finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer
      (BruhatTits.tree R₀ K₀) hT hfinV (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτc hadj Γ' Dd eE' hw₁ Dc eEc.symm hw₂ μ hμE' v₀ Φ' hΦ' Φc hΦcBS
    have hΦ'conj : ∀ x : ↥Γ', Φ' (Additive.ofMul (Abelianization.of x)) = Φd (Additive.ofMul (Abelianization.of (e x))) :=
      fun x => hΦ'conj x

    intro γ
    rw [LinearMap.comp_apply, hPULL]
    let ψ : Abelianization ↥Γ' →* (A.valuation.Completion)ˣ :=
      MonoidHom.toAdditive.symm (w₀.toAddMonoidHom.comp Φ')
    have hψ : ψ = Abelianization.lift c' := by
      apply Abelianization.hom_ext
      refine MonoidHom.ext fun x => ?_
      show Additive.toMul (w₀ (Φ' (Additive.ofMul (Abelianization.of x)))) = Abelianization.lift c' (Abelianization.of x)
      rw [hΦ'conj, hw₀, P3a, Abelianization.lift_apply_of]; rfl
    have hval : ∀ x : Abelianization ↥Γ', w₀ (Φ' (Additive.ofMul x)) = Additive.ofMul (ψ x) := fun x => rfl
    rw [hval, hψ, P3c, ← P3b]

  refine ⟨w₀, ?_, ?_⟩
  · exact hΘd a b z₀ a.2 b.2 z₀.2 hz₀a hz₀b cd hcd w₀ hw₀ Dv hDv
  · exact hΘc a' b' z₀' a'.2 b'.2 z₀'.2 hz₀a' hz₀b' cc hcc (w₀.comp μ.pullback) N3_transfer Dv' hDv'eq

end S_AlgebraicCurve_Pic0_exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta (solution)
