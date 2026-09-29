-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/56c799dc-1c4d-509d-ba71-47eb9b87977e

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Mathlib.GroupTheory.Abelianization.Defs
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_periodField_completion
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_symm_mul_period_eq_one_v_eq_zpow_stabWidth
import Theorems.Thm_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker
import Theorems.Thm_CerednikDrinfeld_Omega_period_eq_period_of_mem_upperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Theorems.Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted
import Theorems.Thm_CerednikDrinfeld_Omega_exists_adj_min_le_v_apply_le_max_of_isUnit
import Theorems.Thm_CerednikDrinfeld_Omega_period_eq_one_of_smul_vertex_eq
import Theorems.Thm_CerednikDrinfeld_Mumford_pathCycle_eq_pathCycle_of_isTree
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Theorems.Thm_CerednikDrinfeld_Omega_theta_isometricAut
import Theorems.Thm_CerednikDrinfeld_Omega_smul_stdVertex_eq_of_mem_affinoid_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve

noncomputable section

section GapC
open MulAction
namespace UAP

section GapCGeneric

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

theorem finite_stabilizer_of_finite_stabilizer_dart (w : W)
    (hnbr : (𝒯.neighborSet w).Finite) (hne : (𝒯.neighborSet w).Nonempty)
    (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d)) : Finite (stabilizer G w) := by
  classical
  obtain ⟨u, hu⟩ := hne
  let d₀ : 𝒯.Dart := ⟨(w, u), hu⟩
  haveI : Finite ↥(𝒯.neighborSet w) := hnbr.to_subtype
  haveI := hfin d₀

  have hsec : ∀ u' : ↥(𝒯.neighborSet w), ∃ s : G, (∃ g : stabilizer G w, (g : G) • u = u') → (s • w = w ∧ s • u = u') := by
    intro u'
    by_cases h : ∃ g : stabilizer G w, (g : G) • u = u'
    · obtain ⟨g, hg⟩ := h
      exact ⟨g, fun _ => ⟨g.2, hg⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose σ hσ using hsec

  have hmem : ∀ g : stabilizer G w, (g : G) • u ∈ 𝒯.neighborSet w := fun g => by
    rw [SimpleGraph.mem_neighborSet]
    have := GraphAction.smul_adj (𝒯 := 𝒯) (g : G) hu
    rwa [show (g : G) • w = w from g.2] at this
  let F : stabilizer G w → ↥(𝒯.neighborSet w) × stabilizer G d₀ := fun g =>
    ⟨⟨(g : G) • u, hmem g⟩,
      ⟨(σ ⟨(g : G) • u, hmem g⟩)⁻¹ * g, by
        obtain ⟨hw, hu'⟩ := hσ ⟨(g : G) • u, hmem g⟩ ⟨g, rfl⟩
        rw [mem_stabilizer_iff]
        apply SimpleGraph.Dart.ext
        refine Prod.ext ?_ ?_
        · show ((σ ⟨(g : G) • u, hmem g⟩)⁻¹ * g) • w = w
          rw [mul_smul, show (g : G) • w = w from g.2, inv_smul_eq_iff, hw]
        · show ((σ ⟨(g : G) • u, hmem g⟩)⁻¹ * g) • u = u
          rw [mul_smul, inv_smul_eq_iff]
          exact hu'.symm⟩⟩
  refine Finite.of_injective F (fun g g' hgg' => ?_)
  simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hgg'
  obtain ⟨h1, h2⟩ := hgg'
  apply Subtype.ext
  have : (σ ⟨(g : G) • u, hmem g⟩ : G) = σ ⟨(g' : G) • u, hmem g'⟩ := by
    congr 1; exact Subtype.ext h1
  rw [this] at h2
  exact mul_left_cancel h2

theorem smul_neighborSet (g : G) (w : W) : 𝒯.neighborSet (g • w) = (fun x => g • x) '' 𝒯.neighborSet w := by
  ext x
  rw [SimpleGraph.mem_neighborSet, Set.mem_image]
  constructor
  · intro h
    refine ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
    rw [SimpleGraph.mem_neighborSet]
    have := GraphAction.smul_adj (𝒯 := 𝒯) g⁻¹ h
    rwa [inv_smul_smul] at this
  · rintro ⟨y, hy, rfl⟩
    rw [SimpleGraph.mem_neighborSet] at hy
    exact GraphAction.smul_adj g hy

end GapCGeneric

section GapCTree

variable (R₀ K₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Field K₀] [Algebra R₀ K₀]
  [IsFractionRing R₀ K₀]

theorem neighborSet_finite_nonempty [Finite (IsLocalRing.ResidueField R₀)] (w : LT.LatticeTree.Vertex R₀ K₀) :
    ((BruhatTits.tree R₀ K₀).neighborSet w).Finite ∧ ((BruhatTits.tree R₀ K₀).neighborSet w).Nonempty := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  have hϖ0 : algebraMap R₀ K₀ ϖ ≠ 0 := fun h => hϖ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K₀)).mp h)

  let n : GL (Fin 2) K₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, algebraMap R₀ K₀ ϖ]
    (by simp [Matrix.det_fin_two, hϖ0])
  let s : R₀ → GL (Fin 2) K₀ := fun t => Matrix.GeneralLinearGroup.mkOfDetNeZero !![algebraMap R₀ K₀ t, 1; 1, 0]
    (by simp [Matrix.det_fin_two])
  obtain ⟨hadj, -, hall, hcong, -⟩ := CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer R₀ K₀ ϖ hϖ
    n (by simp [n, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]) s (fun t => by simp [s, Matrix.GeneralLinearGroup.val_mkOfDetNeZero])

  haveI : Finite (R₀ ⧸ Ideal.span {ϖ}) := by
    have hmax : IsLocalRing.maximalIdeal R₀ = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ
    exact Finite.of_equiv (IsLocalRing.ResidueField R₀) (Ideal.quotEquivOfEq hmax).toEquiv

  have hv₀fin : ((BruhatTits.tree R₀ K₀).neighborSet (LT.LatticeTree.stdVertex R₀ K₀)).Finite := by

    let σ : R₀ ⧸ Ideal.span {ϖ} → R₀ := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}))
    have hσ : ∀ q, Ideal.Quotient.mk (Ideal.span {ϖ}) (σ q) = q :=
      Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}))
    let φ : R₀ ⧸ Ideal.span {ϖ} → LT.LatticeTree.Vertex R₀ K₀ := fun q => (s (σ q) * n) • LT.LatticeTree.stdVertex R₀ K₀
    refine ((Set.finite_range φ).insert (n • LT.LatticeTree.stdVertex R₀ K₀)).subset ?_
    intro y hy
    rw [SimpleGraph.mem_neighborSet] at hy
    rcases hall y hy with h | ⟨t, h⟩
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · refine Set.mem_insert_iff.mpr (Or.inr ⟨Ideal.Quotient.mk _ t, ?_⟩)
      rw [h]
      show (s (σ (Ideal.Quotient.mk _ t)) * n) • LT.LatticeTree.stdVertex R₀ K₀ = (s t * n) • LT.LatticeTree.stdVertex R₀ K₀
      rw [hcong, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, hσ]
  have hv₀ne : ((BruhatTits.tree R₀ K₀).neighborSet (LT.LatticeTree.stdVertex R₀ K₀)).Nonempty :=
    ⟨_, (SimpleGraph.mem_neighborSet _ _ _).mpr hadj⟩

  obtain ⟨g, hg⟩ := LT.LatticeTree.exists_act_stdVertex_eq R₀ K₀ w
  rw [← CerednikDrinfeld.BruhatTits.gl_smul_def] at hg
  rw [← hg, smul_neighborSet]
  exact ⟨hv₀fin.image _, hv₀ne.image _⟩

theorem finite_stabilizer_vertex_of_finite_stabilizer_dart' [Finite (IsLocalRing.ResidueField R₀)]
    {G : Type} [Group G] [MulAction G (LT.LatticeTree.Vertex R₀ K₀)] [GraphAction G (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (stabilizer G d)) (w : LT.LatticeTree.Vertex R₀ K₀) :
    Finite (stabilizer G w) :=
  finite_stabilizer_of_finite_stabilizer_dart (BruhatTits.tree R₀ K₀) w
    (neighborSet_finite_nonempty R₀ K₀ w).1 (neighborSet_finite_nonempty R₀ K₀ w).2 hfin

theorem finite_stabilizer_vertex_of_finite_stabilizer_dart [Finite (IsLocalRing.ResidueField R₀)]
    (H : Subgroup PGL(2, K₀)) [GraphAction ↥H (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (stabilizer (↥H) d))
    (w : LT.LatticeTree.Vertex R₀ K₀) :
    Finite (stabilizer (↥H) w) :=
  finite_stabilizer_vertex_of_finite_stabilizer_dart' R₀ K₀ hfin w

end GapCTree

end UAP

end GapC

namespace ECOmega

theorem exists_isometricAut_apply_eq_smul

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)

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

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))

    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [hcurve : IsCurveOver A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    (hfg : ∃ x : FC, Transcendental A.valuation.Completion x ∧ FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set FC)) FC)

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eV : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDw : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γ.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_fib : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_onto : Function.Surjective pt)

    (hpt : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (galFC : S →* SemilinearAut A.valuation.Completion FC)
    (hgalFC_base : ∀ (σ : S) (c : A.valuation.Completion), SemilinearAut.baseAut (galFC σ) c = (scalar σ) • c)
    (hgal : ∀ σ : S, ∃ (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion),
      n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) ∧ (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))))
    :
    ∀ τ : ↥(A.decompositionSubgroup ℚ), ∃ t : Omega.IsometricAut K₀ A.valuation.Completion,
      ∀ c : A.valuation.Completion, t.toRingEquiv c = τ • c := by
  intro τ
  obtain ⟨n, t, -, hgalσ⟩ := hgal (ι τ)
  refine ⟨t, fun c => ?_⟩
  have h := hgalσ (algebraMap A.valuation.Completion FC c)

  rw [AlgebraicCurve.SemilinearAut.smul_algebraMap, hgalFC_base, hι, AlgEquiv.commutes, AlgEquiv.commutes,
    Mumford.algebraMap_invariantFieldOf_coe, Mumford.algebraMap_invariantFieldOf_coe,
    Mumford.AmbientSemilinearAut.fracMap_algebraMap_const, Mumford.smul_algebraMap_const] at h

  exact ((algebraMap A.valuation.Completion (FractionRing (Omega.HolRingOf ϖ ρ))).injective h).symm

end ECOmega

namespace ECOmega

theorem apply_period_eq_period_of_forall_eq_smul
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K] {Γ₀ : Type}
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (t : Omega.IsometricAut K₀ K)
    {x y : K} (hx : x ∈ Omega.upperHalfPlane K₀ K) (hy : y ∈ Omega.upperHalfPlane K₀ K) (α β : G) :
    t.toRingEquiv (Omega.period ρ x y α β) = Omega.period ρ (t.toRingEquiv x) (t.toRingEquiv y) α β := by
  unfold Omega.period
  rw [← t.comm_pmoebius (ρ α) hx, ← t.comm_pmoebius (ρ β) hy]
  exact (CerednikDrinfeld.Omega.theta_isometricAut ρ t hx (pmoebius_mem_upperHalfPlane K₀ hx (ρ α)) hy
    (pmoebius_mem_upperHalfPlane K₀ hy (ρ β))).symm

end ECOmega

namespace ECOmega
namespace S1

theorem lift_toMul_eq_one_of_mem_closure {H A : Type} [Group H] [CommGroup A] (Q : H →* A) (S : Set H)
    (hS : ∀ g ∈ S, Q g = 1) (x : Additive (Abelianization H))
    (hx : x ∈ AddSubgroup.closure ((fun g : H => Additive.ofMul (Abelianization.of g)) '' S)) :
    Abelianization.lift Q (Additive.toMul x) = 1 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [toMul_ofMul, Abelianization.lift_apply_of]
    exact hS g hg
  | zero => simp
  | add x y _ _ hx hy => rw [toMul_add, map_mul, hx, hy, one_mul]
  | neg x _ hx => rw [toMul_neg, map_inv, hx, inv_one]

theorem apply_apply_eq_one_of_mem_closure {H A : Type} [Group H] [CommGroup A] (Q : H →* H →* A) (S : Set H)
    (hS : ∀ g ∈ S, ∀ b : H, Q g b = 1) (x : Additive (Abelianization H))
    (hx : x ∈ AddSubgroup.closure ((fun g : H => Additive.ofMul (Abelianization.of g)) '' S))
    (h : H) (hh : Additive.ofMul (Abelianization.of h) = x) (b : H) : Q h b = 1 := by
  have hsuff := lift_toMul_eq_one_of_mem_closure Q S (fun g hg => MonoidHom.ext (hS g hg)) x hx
  rw [← hh, toMul_ofMul, Abelianization.lift_apply_of] at hsuff
  rw [hsuff, MonoidHom.one_apply]

section PUTree

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀] {ϖ : R}
  {K : Type} [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_algebraMap_units_eq_one
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (u : Rˣ) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) = 1 := by
  apply le_antisymm (hint u)
  have h1 : algebraMap K₀ K (algebraMap R K₀ (u : R)) * algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  calc (1 : Γ₀) = Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R))) := by rw [← Valuation.map_mul, h1, Valuation.map_one]
    _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) * 1 := mul_le_mul_right (hint _) _
    _ = _ := mul_one _

theorem algebraMap_ne_zero_of_irreducible (hϖ : Irreducible ϖ) : algebraMap R K₀ ϖ ≠ 0 := fun h =>
  hϖ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K₀)).mp h)

theorem v_algebraMap_pos (hϖ : Irreducible ϖ) : 0 < Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) :=
  lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff _).mpr
    ((map_ne_zero _).mpr (algebraMap_ne_zero_of_irreducible hϖ))))

theorem v_algebraMap_lt_one (hϖ : Irreducible ϖ)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < 1 := by
  by_contra h
  rw [not_lt] at h
  have hϖ0 := algebraMap_ne_zero_of_irreducible (K₀ := K₀) hϖ
  have hle : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)⁻¹) ≤ 1 := by
    rw [map_inv₀, Valuation.map_inv, inv_le_one₀ (v_algebraMap_pos hϖ)]
    exact h
  obtain ⟨b, hb⟩ := hv _ hle
  apply hϖ.not_isUnit
  refine isUnit_iff_exists_inv.mpr ⟨b, ?_⟩
  apply IsFractionRing.injective R K₀
  rw [map_mul, hb, map_one, mul_inv_cancel₀ hϖ0]

theorem exists_v_algebraMap_eq_zpow (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (a : K₀) (ha : a ≠ 0) :
    ∃ k : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k := by
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ ha
  refine ⟨k, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, Valuation.map_mul, map_zpow₀,
    v_algebraMap_units_eq_one hint, one_mul]

theorem v_algebraMap_le_or_one_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) :
    Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ∨
      1 ≤ Valued.v (algebraMap K₀ K a) := by
  by_cases ha : a = 0
  · left; rw [ha, map_zero, Valuation.map_zero]; exact zero_le'
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  rw [hk]
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  rcases le_or_gt k 0 with hk0 | hk0
  · exact Or.inr (one_le_zpow_of_nonpos₀ h0 h1 hk0)
  · left
    calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k
        ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ h0 h1 (by omega)
      _ = _ := zpow_one _

theorem exists_pow_le_v_algebraMap_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) (ha : a ≠ 0) :
    ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ Valued.v (algebraMap K₀ K a) ∧
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)))⁻¹ ^ N := by
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  refine ⟨k.natAbs, ?_, ?_⟩
  · rw [hk, ← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (Int.le_natAbs)
  · rw [hk, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (by rw [Int.natCast_natAbs]; exact neg_abs_le k)

def treePseudoUniformizer (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    PseudoUniformizer K₀ K where
  ϖ := algebraMap R K₀ ϖ
  pos := v_algebraMap_pos hϖ
  lt_one := v_algebraMap_lt_one hϖ hv
  scale := exists_pow_le_v_algebraMap_le hϖ hint hv

@[scoped simp] theorem treePseudoUniformizer_ϖ (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    (treePseudoUniformizer hϖ hint hv).ϖ = algebraMap R K₀ ϖ := rfl

end PUTree

section Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem mem_affinoid_of_v_sub_lt (ϖ : Omega.PseudoUniformizer K₀ K) {n : ℕ} {z w : K} (hz : z ∈ Omega.affinoid ϖ n)
    (hw : Valued.v (w - z) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n) : w ∈ Omega.affinoid ϖ n := by
  have hrr : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n :=
    (pow_le_one₀ ϖ.pos.le ϖ.lt_one.le).trans (one_le_pow₀ ((one_le_inv₀ ϖ.pos).2 ϖ.lt_one.le))
  rw [Omega.mem_affinoid_iff'] at hz ⊢
  refine ⟨?_, fun x => ?_⟩
  · have : w = z + (w - z) := by ring
    rw [this]
    exact Valuation.map_add_le _ hz.1 (hw.le.trans hrr)
  · have h1 : Valued.v (w - z) < Valued.v (z - algebraMap K₀ K x) := hw.trans_le (hz.2 x)
    have : w - algebraMap K₀ K x = (z - algebraMap K₀ K x) + (w - z) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ h1]
    exact hz.2 x

theorem exists_mem_upperHalfPlane_forall_pmoebius_ne (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hdisc : Omega.IsDiscrete K ρ)
    {x x' : K} (hx : x ∈ Omega.upperHalfPlane K₀ K) (hx' : x' ∈ Omega.upperHalfPlane K₀ K) :
    ∃ z₁ : K, z₁ ∈ Omega.upperHalfPlane K₀ K ∧ (∀ γ : G, Omega.pmoebius K₀ (ρ γ) x ≠ z₁) ∧
      (∀ γ : G, Omega.pmoebius K₀ (ρ γ) x' ≠ z₁) := by
  classical
  obtain ⟨n, hn⟩ := hex x hx
  obtain ⟨n', hn'⟩ := hex x' hx'
  set N := max n n' with hN
  have hxN : x ∈ Omega.affinoid ϖ N := Omega.affinoid_mono ϖ (le_max_left n n') hn
  have hx'N : x' ∈ Omega.affinoid ϖ N := Omega.affinoid_mono ϖ (le_max_right n n') hn'

  set z : ℕ → K := fun k => x + algebraMap K₀ K ϖ.ϖ ^ (k + N + 1) with hz
  have hzN : ∀ k, z k ∈ Omega.affinoid ϖ N := fun k => by
    refine mem_affinoid_of_v_sub_lt ϖ hxN ?_
    rw [hz]; dsimp only
    rw [add_sub_cancel_left, Valuation.map_pow]
    exact pow_lt_pow_right_of_lt_one₀ ϖ.pos ϖ.lt_one (by omega)
  have hzinj : Function.Injective z := by
    intro k k' h
    rw [hz] at h
    have h' : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (k + N + 1) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (k' + N + 1) := by
      rw [← Valuation.map_pow, ← Valuation.map_pow]; exact congrArg _ (add_left_cancel h)
    have := pow_right_injective₀ ϖ.pos ϖ.lt_one.ne h'
    omega

  have hfin : {γ : G | Omega.pmoebius K₀ (ρ γ) x ∈ Omega.affinoid ϖ N}.Finite :=
    CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid ϖ ρ hdisc N hxN
  have hfin' : {γ : G | Omega.pmoebius K₀ (ρ γ) x' ∈ Omega.affinoid ϖ N}.Finite :=
    CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid ϖ ρ hdisc N hx'N
  have hbad : {k : ℕ | ∃ γ : G, Omega.pmoebius K₀ (ρ γ) x = z k ∨ Omega.pmoebius K₀ (ρ γ) x' = z k}.Finite := by
    refine Set.Finite.subset ((((hfin.image fun γ => Omega.pmoebius K₀ (ρ γ) x).union
      (hfin'.image fun γ => Omega.pmoebius K₀ (ρ γ) x')).preimage (hzinj.injOn))) ?_
    rintro k ⟨γ, h | h⟩
    · exact Or.inl ⟨γ, by rw [Set.mem_setOf_eq, h]; exact hzN k, h⟩
    · exact Or.inr ⟨γ, by rw [Set.mem_setOf_eq, h]; exact hzN k, h⟩
  obtain ⟨k, -, hk⟩ := Set.Infinite.exists_notMem_finite (Set.infinite_univ (α := ℕ)) hbad
  simp only [Set.mem_setOf_eq, not_exists, not_or] at hk
  exact ⟨z k, Omega.affinoid_subset_upperHalfPlane ϖ N (hzN k), fun γ => (hk γ).1, fun γ => (hk γ).2⟩

theorem period_eq_period (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hdisc : Omega.IsDiscrete K ρ)
    (hΘ : ∀ x ∈ Omega.upperHalfPlane K₀ K, ∀ y ∈ Omega.upperHalfPlane K₀ K, ∀ u ∈ Omega.upperHalfPlane K₀ K,
      ∀ z ∈ Omega.upperHalfPlane K₀ K, Omega.ThetaMultipliable ρ x y u z)
    {x y x' y' : K} (hx : x ∈ Omega.upperHalfPlane K₀ K) (hy : y ∈ Omega.upperHalfPlane K₀ K)
    (hx' : x' ∈ Omega.upperHalfPlane K₀ K) (hy' : y' ∈ Omega.upperHalfPlane K₀ K)
    (hxy : ∀ γ : G, Omega.pmoebius K₀ (ρ γ) x ≠ y) (hx'y' : ∀ γ : G, Omega.pmoebius K₀ (ρ γ) x' ≠ y') (α β : G) :
    Omega.period ρ x y α β = Omega.period ρ x' y' α β := by
  obtain ⟨z₁, hz₁, h1, h1'⟩ := exists_mem_upperHalfPlane_forall_pmoebius_ne ϖ hex ρ hdisc hx hx'

  have hg : ∀ {a w : K}, (∀ γ : G, Omega.pmoebius K₀ (ρ γ) a ≠ w) → a ∈ Omega.upperHalfPlane K₀ K →
      ∀ γ : G, Omega.pmoebius K₀ (ρ γ) (Omega.pmoebius K₀ (ρ α) a) ≠ w := by
    intro a w h ha γ
    rw [← Omega.pmoebius_mul K₀ ha, ← map_mul]
    exact h (γ * α)
  have step1 : Omega.period ρ x y α β = Omega.period ρ x z₁ α β := by
    unfold Omega.period
    exact (CerednikDrinfeld.Omega.theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint ρ hx
      (Omega.pmoebius_mem_upperHalfPlane K₀ hx _) hy hz₁ hxy (hg hxy hx) h1 (hg h1 hx)
      (fun w hw z hz => hΘ _ hx _ (Omega.pmoebius_mem_upperHalfPlane K₀ hx _) w hw z hz) β).symm
  have step2 : Omega.period ρ x z₁ α β = Omega.period ρ x' z₁ α β :=
    CerednikDrinfeld.Omega.period_eq_period_of_mem_upperHalfPlane ρ hx hx' hz₁ h1 h1'
      (fun a ha b hb z hz => hΘ a ha b hb z₁ hz₁ z hz) α β
  have step3 : Omega.period ρ x' z₁ α β = Omega.period ρ x' y' α β := by
    unfold Omega.period
    exact (CerednikDrinfeld.Omega.theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint ρ hx'
      (Omega.pmoebius_mem_upperHalfPlane K₀ hx' _) hz₁ hy' h1' (hg h1' hx') hx'y' (hg hx'y' hx')
      (fun w hw z hz => hΘ _ hx' _ (Omega.pmoebius_mem_upperHalfPlane K₀ hx' _) w hw z hz) β).symm
  rw [step1, step2, step3]

end Omega

theorem exists_mem_affinoid_zero
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) [Finite (R ⧸ Ideal.span {ϖ₀})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ₀)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ : Omega.PseudoUniformizer K₀ K) (hϖ : algebraMap R K₀ ϖ₀ = ϖ.ϖ) (hex : Omega.IsExhausted ϖ) :
    ∃ w : K, w ∈ Omega.affinoid ϖ 0 := by

  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K₀ K ϖ.ϖ) (show 0 < 2 by norm_num)
  have h2 : Valued.v y ^ 2 = Valued.v (algebraMap K₀ K ϖ.ϖ) := by rw [← Valuation.map_pow, hy]
  have hy0 : 0 < Valued.v y := by
    rw [Valuation.pos_iff]; rintro rfl
    rw [zero_pow two_ne_zero] at hy; exact ϖ.pos.ne' (by rw [← hy, Valuation.map_zero])
  have hy1 : Valued.v y < 1 := by
    by_contra h; rw [not_lt] at h
    have h' : 1 ≤ Valued.v y ^ 2 := one_le_pow₀ h
    rw [h2] at h'
    exact absurd ϖ.lt_one (not_lt.2 h')
  have hyr : Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v y := by
    rw [← h2, pow_two]
    calc Valued.v y * Valued.v y < Valued.v y * 1 := mul_lt_mul_of_pos_left hy1 hy0
      _ = Valued.v y := mul_one _
  have hyΩ : y ∈ Omega.upperHalfPlane K₀ K := by
    rw [Omega.mem_upperHalfPlane_iff]
    rintro a rfl
    rcases v_algebraMap_le_or_one_le hϖ₀ hint hv a with h | h
    · rw [hϖ] at h; exact absurd hyr (not_lt.2 h)
    · exact absurd hy1 (not_lt.2 h)
  obtain ⟨-, -, w, -, -, -, hw, -⟩ :=
    CerednikDrinfeld.Omega.exists_adj_min_le_v_apply_le_max_of_isUnit R K₀ ϖ₀ hϖ₀ K hint hv hq ϖ hrk hex 1 isUnit_one ⟨y, hyΩ⟩
  exact ⟨w, hw⟩

end ECOmega.S1
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient.ECOmega P2MW.S_AlgebraicCurve_Pic0_exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient.ECOmega.S1"
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient.ECOmega"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient.ECOmega P2MW.S_AlgebraicCurve_Pic0_exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient.ECOmega.S1"

set_option maxHeartbeats 1600000 in
open ECOmega.S1 in
theorem solution

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)

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

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))

    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [hcurve : IsCurveOver A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    (hfg : ∃ x : FC, Transcendental A.valuation.Completion x ∧ FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set FC)) FC)

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eV : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDw : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γ.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_fib : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_onto : Function.Surjective pt)

    (hpt : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (galFC : S →* SemilinearAut A.valuation.Completion FC)
    (hgalFC_base : ∀ (σ : S) (c : A.valuation.Completion), SemilinearAut.baseAut (galFC σ) c = (scalar σ) • c)
    (hgal : ∀ σ : S, ∃ (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion),
      n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) ∧ (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))))
    (πV : S →* Equiv.Perm V) (πE : S →* Equiv.Perm E) (sgn : S →* ℤˣ)
    (hπV : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ v : LT.LatticeTree.Vertex R₀ K₀, πV σ (eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (ρ n • v)))
    (hπE : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = 1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = -1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (hπ_width : ∀ σ e, D.w (πE σ e) = D.w e)
    (hsgn_pos : ∀ σ e, sgn σ = 1 → D.a (πE σ e) = πV σ (D.a e) ∧ D.b (πE σ e) = πV σ (D.b e))
    (hsgn_neg : ∀ σ e, sgn σ = -1 → D.a (πE σ e) = πV σ (D.b e) ∧ D.b (πE σ e) = πV σ (D.a e))
    (hπ_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → πV (ι τ) = 1 ∧ πE (ι τ) = 1 ∧ sgn (ι τ) = 1)
    (actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)))
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e) :
    ∃ (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ),
      (∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
        Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k))) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ),
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
          ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion)) ∧
      (∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k) ∧
      ∃ P : PeriodDatum D (↥K) A.valuation.Completion ord,
        ∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
          ∀ α β : ↥(Γ.map ρ),
            ((((Additive.toMul (P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))))) :
                (↥K)ˣ) : ↥K) : A.valuation.Completion) * Omega.period (Γ.map ρ).subtype x y α β = 1 := by
  classical

  haveI hAC : IsAlgClosed A.valuation.Completion := ValuationSubring.isAlgClosed_completion_of_liesOverPrime r Fact.out A hA
  obtain ⟨-, -, hrk⟩ := ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime r A hA
  have hint : ∀ a : R₀, Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ a)) ≤ 1 :=
    fun a => (hR₀ _).1 ⟨a, rfl⟩
  have hv : ∀ a : K₀, Valued.v (algebraMap K₀ A.valuation.Completion a) ≤ 1 → IsLocalization.IsInteger R₀ a := by
    intro a ha
    obtain ⟨b, hb⟩ := (hR₀ a).2 ha
    exact ⟨b, hb⟩
  have hq : ∀ ε : _, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ ϖ₀)) ^ N ≤ ε := by
    intro ε hε
    obtain ⟨q, hq⟩ := A.valuation_surjective ε
    have hy : Valued.v ((q : AlgebraicClosure ℚ) : A.valuation.Completion) = ε := by
      rw [← hq]; exact Valued.valuedCompletion_apply _
    have hy0 : ((q : AlgebraicClosure ℚ) : A.valuation.Completion) ≠ 0 := fun h => by
      rw [h, Valuation.map_zero] at hy; exact hε hy.symm
    have hlt : Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ ϖ₀)) < 1 := by
      rw [hϖ]; exact ϖ.lt_one
    obtain ⟨N, hN⟩ := hrk _ _ hlt hy0
    exact ⟨N, hy ▸ hN⟩
  haveI hfinq : Finite (R₀ ⧸ Ideal.span {ϖ₀}) := by
    have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mp hϖ₀
    exact Finite.of_equiv (IsLocalRing.ResidueField R₀) (Ideal.quotEquivOfEq hmax).toEquiv

  obtain ⟨K, ord, hord, hinK, hhens, hmemK⟩ := CerednikDrinfeld.Mumford.exists_periodField_completion r A hA
  refine ⟨K, ord, hord, hinK, hhens, ?_⟩

  have hActs : Mumford.ActsThrough (LT.LatticeTree.Vertex R₀ K₀) (Γ.map ρ).subtype := fun g w => rfl
  obtain ⟨hconn, hcol⟩ := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀
  obtain ⟨hadj1, -, -⟩ := CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
    ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) hconn hcol (LT.LatticeTree.stdVertex R₀ K₀)
  have hτ : ∀ (g : ↥(Γ.map ρ)) (w : LT.LatticeTree.Vertex R₀ K₀),
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g • w) =
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w := fun g w => htp g.2 w
  have hadj : ∀ u w : LT.LatticeTree.Vertex R₀ K₀, (BruhatTits.tree R₀ K₀).Adj u w →
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) u ≠
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w := by
    intro u w huw h
    have h1 := hadj1 u w huw
    rw [← h] at h1
    have h2 : (1 : ZMod 2) = 0 := add_left_cancel (h1.symm.trans (add_zero _).symm)
    exact absurd h2 (by decide)
  have hfinV : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Finite (MulAction.stabilizer (↥(Γ.map ρ)) w) :=
    fun w => UAP.finite_stabilizer_vertex_of_finite_stabilizer_dart R₀ K₀ (Γ.map ρ) hfin w
  have hdisc : Omega.IsDiscrete A.valuation.Completion (Γ.map ρ).subtype := by
    refine CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion hint hv hq
      (Γ.map ρ).subtype ?_
    haveI := hfinV (LT.LatticeTree.stdVertex R₀ K₀)
    exact Set.Finite.subset (s := (MulAction.stabilizer (↥(Γ.map ρ)) (LT.LatticeTree.stdVertex R₀ K₀) : Set _))
      (Set.toFinite _) (fun γ hγ => hγ)
  have hΘ : ∀ x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion, ∀ y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion,
      ∀ u ∈ Omega.upperHalfPlane K₀ A.valuation.Completion, ∀ z ∈ Omega.upperHalfPlane K₀ A.valuation.Completion,
      Omega.ThetaMultipliable (Γ.map ρ).subtype x y u z :=
    fun x hx y hy u hu z hz => CerednikDrinfeld.Omega.thetaMultipliable_of_isDiscrete_of_isExhausted ϖ hex _ hdisc hx hy hu hz

  have hpt : ∃ w₀ : A.valuation.Completion, w₀ ∈ Omega.affinoid ϖ 0 :=
    exists_mem_affinoid_zero R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion hint hv hq hrk ϖ hϖ hex
  obtain ⟨w₀, hw₀⟩ := hpt

  have hϖK : algebraMap R₀ K₀ ϖ₀ ≠ 0 := fun h =>
    hϖ₀.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K₀)).mp h)
  obtain ⟨n, hn⟩ : ∃ n : GL (Fin 2) K₀, n = LT.LatticeTree.diagSnd (LT.LatticeTree.unitOfNeZero (K := K₀) hϖ₀.ne_zero) := ⟨_, rfl⟩
  have hnadj : (BruhatTits.tree R₀ K₀).Adj (LT.LatticeTree.stdVertex R₀ K₀) (n • LT.LatticeTree.stdVertex R₀ K₀) := by
    rw [BruhatTits.tree_adj_iff, hn]
    refine ⟨(LT.LatticeTree.stdVertex_ne_act_diagSnd (R := R₀) (K := K₀) hϖ₀).symm,
      Or.inl ⟨LT.LatticeTree.stdLattice R₀ K₀, LT.LatticeTree.latticeMap _ (LT.LatticeTree.stdLattice R₀ K₀),
        LT.LatticeTree.isFullLattice_stdLattice, LT.LatticeTree.isFullLattice_stdLattice.map _, rfl, rfl,
        LT.LatticeTree.adjacentLattice_stdLattice_diagSnd (R := R₀) (K := K₀) hϖ₀⟩⟩
  have hsep : Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) ((1 : GL (Fin 2) K₀) • LT.LatticeTree.stdVertex R₀ K₀) ≠
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (n • LT.LatticeTree.stdVertex R₀ K₀) := by
    rw [one_smul]; exact hadj _ _ hnadj
  have hbase : ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ ((Γ.map ρ).subtype γ) (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk n) w₀) ≠
      Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk 1) w₀ := by
    intro γ hγ
    have hw₀Ω' := Omega.affinoid_subset_upperHalfPlane ϖ 0 hw₀
    obtain ⟨gγ, hgγ⟩ := Matrix.ProjGenLinGroup.mk_surjective ((Γ.map ρ).subtype γ)
    rw [← hgγ, ← Omega.pmoebius_mul K₀ hw₀Ω', ← map_mul] at hγ

    have hred := CerednikDrinfeld.Omega.smul_stdVertex_eq_of_mem_affinoid_zero R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion hint hv ϖ
      (x := Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk 1) w₀) (gγ * n) 1
      (by rw [← hγ, ← Omega.pmoebius_mul K₀ hw₀Ω', inv_mul_cancel, Omega.pmoebius_one]; exact hw₀)
      (by rw [← Omega.pmoebius_mul K₀ hw₀Ω', inv_mul_cancel, Omega.pmoebius_one]; exact hw₀)
    have hτγ := hτ γ (n • LT.LatticeTree.stdVertex R₀ K₀)
    rw [Subgroup.smul_def, show ((γ : ↥(Γ.map ρ)) : PGL(2, K₀)) = (Γ.map ρ).subtype γ from rfl, ← hgγ,
      BruhatTits.pgl_mk_smul, ← mul_smul, hred] at hτγ
    exact hsep hτγ

  have hKp : ∀ α β : ↥(Γ.map ρ),
      Omega.period (Γ.map ρ).subtype (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk n) w₀)
        (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk 1) w₀) α β ∈ K.toSubfield := by
    intro α β
    have hw₀Ω' := Omega.affinoid_subset_upperHalfPlane ϖ 0 hw₀
    have hxₐ := Omega.pmoebius_mem_upperHalfPlane K₀ hw₀Ω' (Matrix.ProjGenLinGroup.mk n)
    have hx₀ := Omega.pmoebius_mem_upperHalfPlane K₀ hw₀Ω' (Matrix.ProjGenLinGroup.mk 1)
    rw [IntermediateField.mem_toSubfield]
    refine hmemK _ (fun σ _ s hs => ?_)
    obtain ⟨t, ht⟩ := ECOmega.exists_isometricAut_apply_eq_smul (A := A) (hA := hA) (S := S) (scalar := scalar) (ι := ι)
      (hι := hι) (K₀ := K₀) (R₀ := R₀) (hR₀ := hR₀) (ϖ := ϖ) (ϖ₀ := ϖ₀) (hϖ₀ := hϖ₀) (hϖ := hϖ) (hex := hex) (hϖr := hϖr)
      (G := G) (ρ := ρ) (Γ := Γ) (htp := htp) (hfin := hfin) (FC := FC) (eFC := eFC) (hfg := hfg) (E := E) (V := V)
      (D := D) (eV := eV) (eE := eE) (hDa := hDa) (hDb := hDb) (hDw := hDw) (v₀ := v₀) (Φ := Φ) (hΦ := hΦ) (pt := pt)
      (hpt_fib := hpt_fib) (hpt_onto := hpt_onto) (hpt := hpt) (galFC := galFC) (hgalFC_base := hgalFC_base) (hgal := hgal) σ
    have hst : (s : A.valuation.Completion → A.valuation.Completion) = t.toRingEquiv := funext fun c => by rw [hs, ht]
    rw [show s _ = t.toRingEquiv _ from congrFun hst _,
      ECOmega.apply_period_eq_period_of_forall_eq_smul (Γ.map ρ).subtype t hxₐ hx₀ α β]

    refine period_eq_period ϖ hex (Γ.map ρ).subtype hdisc hΘ (t.mapsTo_upperHalfPlane hxₐ) (t.mapsTo_upperHalfPlane hx₀)
      hxₐ hx₀ (fun γ h => hbase γ ?_) hbase α β
    apply t.toRingEquiv.injective
    rw [t.comm_pmoebius _ hxₐ]
    exact h

  obtain ⟨Qh, hQsymm, hQper, hQv⟩ :=
    CerednikDrinfeld.Omega.exists_monoidHom_monoidHom_symm_mul_period_eq_one_v_eq_zpow_stabWidth R₀ K₀ ϖ₀ hϖ₀
      A.valuation.Completion hint hv hq ϖ hex (Γ.map ρ).subtype hActs hfinV
      (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτ hadj eE.symm
      1 n hw₀ hw₀ hsep K.toSubfield hKp

  have hDa' : ∀ e : E, eV.symm (D.a e) = Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eE.symm e).1.out.fst := by
    intro e
    rw [Equiv.symm_apply_eq]
    conv_lhs => rw [← eE.apply_symm_apply e]
    exact hDa (eE.symm e)
  have hDb' : ∀ e : E, eV.symm (D.b e) = Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eE.symm e).1.out.snd := by
    intro e
    rw [Equiv.symm_apply_eq]
    conv_lhs => rw [← eE.apply_symm_apply e]
    exact hDb (eE.symm e)
  have hΦ' : ∀ g : ↥(Γ.map ρ), ((Φ (Additive.ofMul (Abelianization.of g)) : ↥(ribbonKernel D)) : E → ℤ) =
      Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e => (eE.symm e).1) v₀ g := by
    intro g
    funext e
    have h := hΦ g (eE.symm e)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    unfold Mumford.pathCycle Mumford.walkCycle
    split_ifs <;> rfl
  obtain ⟨hΦsurj, hΦker⟩ :=
    CerednikDrinfeld.Mumford.surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle (BruhatTits.tree R₀ K₀)
      (CerednikDrinfeld.BruhatTits.tree_isTree R₀ K₀) (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
      hτ hadj D eE.symm eV.symm hDa' hDb' v₀ Φ hΦ'
  have hker : ∀ α : ↥(Γ.map ρ), Φ (Additive.ofMul (Abelianization.of α)) = 0 → ∀ β : ↥(Γ.map ρ), Qh α β = 1 := by

    have hW4 : ∀ (α : ↥(Γ.map ρ)) (v₁ : LT.LatticeTree.Vertex R₀ K₀), α • v₁ = v₁ → ∀ β, Qh α β = 1 := by
      intro α v₁ hα β
      have hp := CerednikDrinfeld.Omega.period_eq_one_of_smul_vertex_eq R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion hint hv hq hrk ϖ hex
        (Γ.map ρ).subtype hActs hfinV (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτ hadj
        eE.symm 1 n hw₀ hw₀ hsep α v₁ hα β
      have h1 := hQper α β
      rw [hp, mul_one] at h1
      exact Units.ext (Subtype.ext h1)
    intro α hα β
    have hmem := (hΦker (Additive.ofMul (Abelianization.of α))).1 hα
    have hS : ∀ g ∈ (⋃ w : LT.LatticeTree.Vertex R₀ K₀, (MulAction.stabilizer (↥(Γ.map ρ)) w : Set ↥(Γ.map ρ))),
        ∀ b : ↥(Γ.map ρ), Qh g b = 1 := by
      intro g hg b
      obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg
      exact hW4 g w hw b
    exact apply_apply_eq_one_of_mem_closure Qh
      (⋃ w : LT.LatticeTree.Vertex R₀ K₀, (MulAction.stabilizer (↥(Γ.map ρ)) w : Set ↥(Γ.map ρ))) hS
      (Additive.ofMul (Abelianization.of α)) hmem α rfl β
  have hordQ : ∀ α β : ↥(Γ.map ρ), ord (Additive.ofMul (Qh α β)) =
      ∑ e : E, (D.w e : ℤ) * ((Φ (Additive.ofMul (Abelianization.of α)) : E → ℤ) e *
        (Φ (Additive.ofMul (Abelianization.of β)) : E → ℤ) e) := by
    intro α β

    have h1 := hQv α β
    have h2 := hord (Qh α β)
    have hqr : Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ ϖ₀)) = Valued.v ((r : ℕ) : A.valuation.Completion) := by
      rw [hϖ, hϖr]
    rw [hqr] at h1
    have h12 : Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul (Qh α β))) =
        Valued.v ((r : ℕ) : A.valuation.Completion) ^
          (∑ e : E, ((Mumford.stabWidth ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) (eE.symm e).1 : ℕ) : ℤ) *
            Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e => (eE.symm e).1) (LT.LatticeTree.stdVertex R₀ K₀) α e *
            Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e => (eE.symm e).1) (LT.LatticeTree.stdVertex R₀ K₀) β e) :=
      h2.symm.trans h1
    have hr0 : 0 < Valued.v ((r : ℕ) : A.valuation.Completion) := by rw [← hϖr]; exact ϖ.pos
    have hr1 : Valued.v ((r : ℕ) : A.valuation.Completion) ≠ 1 := by rw [← hϖr]; exact ϖ.lt_one.ne
    rw [zpow_right_injective₀ hr0 hr1 h12]
    refine Finset.sum_congr rfl fun e _ => ?_

    have hw' : ((Mumford.stabWidth ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) (eE.symm e).1 : ℕ) : ℤ) = (D.w e : ℤ) := by
      have hc := hDw (eE.symm e)
      rw [Equiv.apply_symm_apply] at hc
      haveI := hfin (eE.symm e).1.out
      have hpos : 0 < Nat.card (MulAction.stabilizer (↥(Γ.map ρ)) (eE.symm e).1.out) := Nat.card_pos
      have : (Mumford.stabWidth ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) (eE.symm e).1 : ℕ) = (D.w e : ℕ) := by
        rw [hc, Mumford.stabWidth, Nat.toPNat'_coe, if_pos hpos]
      exact_mod_cast this

    rw [hw', Mumford.pathCycle_eq_pathCycle_of_isTree (BruhatTits.tree R₀ K₀) (CerednikDrinfeld.BruhatTits.tree_isTree R₀ K₀)
        (fun e => (eE.symm e).1) v₀ (LT.LatticeTree.stdVertex R₀ K₀) α,
      Mumford.pathCycle_eq_pathCycle_of_isTree (BruhatTits.tree R₀ K₀) (CerednikDrinfeld.BruhatTits.tree_isTree R₀ K₀)
        (fun e => (eE.symm e).1) v₀ (LT.LatticeTree.stdVertex R₀ K₀) β, ← hΦ' α, ← hΦ' β, mul_assoc]
  obtain ⟨P, hP⟩ := CerednikDrinfeld.Mumford.exists_periodDatum_apply_eq_of_surjective_of_forall_ker D Φ hΦsurj (↥K)
    A.valuation.Completion ord Qh hQsymm hker hordQ
  refine ⟨P, ?_⟩

  intro x y hx hy hxy α β
  rw [hP α β]
  have hw₀Ω := Omega.affinoid_subset_upperHalfPlane ϖ 0 hw₀
  have htrans : Omega.period (Γ.map ρ).subtype x y α β =
      Omega.period (Γ.map ρ).subtype (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk n) w₀)
        (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk 1) w₀) α β :=
    period_eq_period ϖ hex (Γ.map ρ).subtype hdisc hΘ hx hy (Omega.pmoebius_mem_upperHalfPlane K₀ hw₀Ω _)
      (Omega.pmoebius_mem_upperHalfPlane K₀ hw₀Ω _) hxy hbase α β
  have h1 := hQper α β
  rw [← htrans] at h1
  exact h1

end S_AlgebraicCurve_Pic0_exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient (solution)
