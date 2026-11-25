-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.etale_compactSupportCohomology_affineLine_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:49:51.283303+00:00
-- url     : https://prove2.me/submissions/2f78e39d-78ae-42b9-b894-a0b50a69d4d3

import Mathlib
import Definitions.Def_RPLib_FX_EtHc_10
import Definitions.Def_RPLib_FX_EtHc_11
import Definitions.Def_RPLib_FX_EtP1_25
import Definitions.Def_RPLib_FX_EtP1_34

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry CategoryTheory

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] (Λ : Type) [CommRing Λ]
    (G : Sheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology (ModuleCat.{0} Λ))
    (ι : G ⟶ (constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
      (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ))
    (hU : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
      (p : Spec (CommRingCat.of Ω) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)),
      p default ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 0) →
        IsIso ((Scheme.pointSmallEtale p).sheafFiber (A := ModuleCat.{0} Λ) |>.map ι))
    (hZ : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
      (p : Spec (CommRingCat.of Ω) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)),
      p default ∉ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 0) →
        Limits.IsZero ((Scheme.pointSmallEtale p).sheafFiber (A := ModuleCat.{0} Λ) |>.obj G)) :
    (∀ e : (Abelian.Ext ((constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
        (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) G 0 : Type), e = 0) ∧
    (∀ N : ℕ, (N : k) ≠ 0 → (N : Λ) = 0 →
      ∀ e : (Abelian.Ext ((constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
        (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) G 1 : Type), e = 0) ∧
    (∀ l n : ℕ, l.Prime → 0 < n → (l : k) ≠ 0 → ((l ^ n : ℕ) : Λ) = 0 →
      Nonempty ((Abelian.Ext ((constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
        (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) G 2 : Type) ≃+ Λ)) ∧
    (∀ l m : ℕ, l.Prime → (l : k) ≠ 0 → ((l ^ m : ℕ) : Λ) = 0 →
      ∀ (n : ℕ) (e : (Abelian.Ext ((constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
        (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) G (n + 3) : Type)), e = 0) := by
  classical
  have hO : ∀ x : RamanujanPetersson.EtCompact.P1 k, x ∈ (RamanujanPetersson.EtCompact.chartA1 k).opensRange ↔
      x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 0) := by
    intro x; rw [RamanujanPetersson.EtCompact.P1.opensRange_chartA1]
  have hU' : ∀ s : RamanujanPetersson.EtSheaves.GeomPt (RamanujanPetersson.EtCompact.P1 k),
      s.center ∈ (RamanujanPetersson.EtCompact.chartA1 k).opensRange → IsIso ((s.stalkF Λ).map ι) :=
    fun s hs => hU s.Ω s.pt ((hO _).1 hs)
  have hZ' : ∀ s : RamanujanPetersson.EtSheaves.GeomPt (RamanujanPetersson.EtCompact.P1 k),
      s.center ∉ (RamanujanPetersson.EtCompact.chartA1 k).opensRange → Limits.IsZero ((s.stalkF Λ).obj G) :=
    fun s hs => hZ s.Ω s.pt (fun h => hs ((hO _).2 h))
  -- `G ≅ openCut (A^1) Λ_{P^1}` (= `j_! Λ`), through `ι`
  have h0 : ι ≫ RamanujanPetersson.EtSheaves.quotCutπ Λ (RamanujanPetersson.EtCompact.chartA1 k).opensRange
      (RamanujanPetersson.EtSheaves.unitSh Λ (RamanujanPetersson.EtCompact.P1 k)) = 0 := by
    refine RamanujanPetersson.EtCompact.eq_zero_of_stalk _ (fun x => ?_)
    by_cases hx : x ∈ (RamanujanPetersson.EtCompact.chartA1 k).opensRange
    · exact (RamanujanPetersson.EtSheaves.isZero_stalk_quotCut _ _ _
        (RamanujanPetersson.EtCompact.mem_center_geomPtAt
          (W := ((RamanujanPetersson.EtCompact.chartA1 k).opensRange : Set (RamanujanPetersson.EtCompact.P1 k))) hx)).eq_of_tgt _ _
    · exact (hZ' _ (RamanujanPetersson.EtCompact.not_mem_center_geomPtAt
        (W := ((RamanujanPetersson.EtCompact.chartA1 k).opensRange : Set (RamanujanPetersson.EtCompact.P1 k))) hx)).eq_of_src _ _
  let φ : G ⟶ RamanujanPetersson.EtSheaves.openCut Λ (RamanujanPetersson.EtCompact.chartA1 k).opensRange
      (RamanujanPetersson.EtSheaves.unitSh Λ (RamanujanPetersson.EtCompact.P1 k)) :=
    Abelian.monoLift (RamanujanPetersson.EtSheaves.openCutι Λ (RamanujanPetersson.EtCompact.chartA1 k).opensRange
      (RamanujanPetersson.EtSheaves.unitSh Λ (RamanujanPetersson.EtCompact.P1 k))) ι h0
  have hφ : φ ≫ RamanujanPetersson.EtSheaves.openCutι Λ _ _ = ι := Abelian.monoLift_comp _ _ _
  have : IsIso φ := by
    rw [RamanujanPetersson.EtSheaves.isIso_iff_stalk]
    intro x
    by_cases hx : x ∈ (RamanujanPetersson.EtCompact.chartA1 k).opensRange
    · have hc := RamanujanPetersson.EtCompact.mem_center_geomPtAt
        (W := ((RamanujanPetersson.EtCompact.chartA1 k).opensRange : Set (RamanujanPetersson.EtCompact.P1 k))) hx
      have h1 := RamanujanPetersson.EtSheaves.isIso_stalk_openCutι (RamanujanPetersson.EtCompact.chartA1 k).opensRange
        (RamanujanPetersson.EtSheaves.unitSh Λ (RamanujanPetersson.EtCompact.P1 k))
        (RamanujanPetersson.EtSheaves.geomPtAt x) hc
      have h2 : IsIso (((RamanujanPetersson.EtSheaves.geomPtAt x).stalkF Λ).map φ ≫
          ((RamanujanPetersson.EtSheaves.geomPtAt x).stalkF Λ).map
            (RamanujanPetersson.EtSheaves.openCutι Λ (RamanujanPetersson.EtCompact.chartA1 k).opensRange
              (RamanujanPetersson.EtSheaves.unitSh Λ (RamanujanPetersson.EtCompact.P1 k)))) := by
        rw [← Functor.map_comp, hφ]; exact hU' _ hc
      exact IsIso.of_isIso_comp_right _
        (((RamanujanPetersson.EtSheaves.geomPtAt x).stalkF Λ).map (RamanujanPetersson.EtSheaves.openCutι Λ _ _))
    · have hc := RamanujanPetersson.EtCompact.not_mem_center_geomPtAt
        (W := ((RamanujanPetersson.EtCompact.chartA1 k).opensRange : Set (RamanujanPetersson.EtCompact.P1 k))) hx
      exact RamanujanPetersson.EtCompact.isIso_of_zero_zero _ (hZ' _ hc)
        (RamanujanPetersson.EtSheaves.isZero_stalk_openCut _ _ _ hc)
  -- `Ext^n(Λ, G) ≃ H^n_c(univ ∩ A^1 ⊆ P^1, Λ)` and the comparison to `H^n(P^1, Λ)`
  let E : ∀ n : ℕ, (Abelian.Ext ((constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
      (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) G n : Type) ≃+
      RamanujanPetersson.EtCompact.HcSet Λ
        (Set.univ ∩ ((RamanujanPetersson.EtCompact.chartA1 k).opensRange : Set (RamanujanPetersson.EtCompact.P1 k)))
        (RamanujanPetersson.EtSheaves.unitSh Λ (RamanujanPetersson.EtCompact.P1 k)) n := fun n =>
    RamanujanPetersson.EtCompact.Hiso Λ (asIso φ ≪≫ (RamanujanPetersson.EtCompact.cutOpenIso _ _).symm) n
  let X : ∀ n : ℕ, (Abelian.Ext ((constantSheaf (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).smallEtaleTopology
      (ModuleCat.{0} Λ)).obj (ModuleCat.of Λ Λ)) G n : Type) →+
      RamanujanPetersson.EtCompact.H Λ (RamanujanPetersson.EtSheaves.unitSh Λ (RamanujanPetersson.EtCompact.P1 k)) n :=
    fun n => (RamanujanPetersson.EtCompact.hcUnivEquiv _ n).toAddMonoidHom.comp
      ((RamanujanPetersson.EtCompact.extO _ (RamanujanPetersson.EtCompact.P1.isLocallyClosed_univ k)
        (RamanujanPetersson.EtCompact.chartA1 k).opensRange n).comp (E n).toAddMonoidHom)
  have hX : ∀ n, Function.Injective
      (RamanujanPetersson.EtCompact.extO (RamanujanPetersson.EtSheaves.unitSh Λ (RamanujanPetersson.EtCompact.P1 k))
        (RamanujanPetersson.EtCompact.P1.isLocallyClosed_univ k) (RamanujanPetersson.EtCompact.chartA1 k).opensRange n) →
      ∀ e, X n e = 0 → e = 0 := by
    intro n h e he
    have h1 : (RamanujanPetersson.EtCompact.extO _ (RamanujanPetersson.EtCompact.P1.isLocallyClosed_univ k)
        (RamanujanPetersson.EtCompact.chartA1 k).opensRange n) (E n e) = 0 := by
      simpa [X] using he
    exact (E n).injective (by rw [map_zero]; exact h (by rw [h1, map_zero]))
  refine ⟨fun e => (E 0).injective ?_, fun N hN hNΛ e => ?_, fun l n hl hn hlk hΛ => ?_,
    fun l m hl hlk hΛ n e => ?_⟩
  · rw [map_zero]; exact RamanujanPetersson.EtCompact.P1.hcA1_zero_eq_zero k Λ _
  · have hs := RamanujanPetersson.EtCompact.P1.h1_subsingleton k hN hNΛ
    exact hX 1 (RamanujanPetersson.EtCompact.P1.extO_one_injective k Λ) e (Subsingleton.elim _ _)
  · have : Fact l.Prime := ⟨hl⟩
    obtain ⟨e2⟩ := RamanujanPetersson.EtCompact.P1.nonempty_h2Equiv k hn hlk hΛ
    exact ⟨((E 2).trans ((AddEquiv.ofBijective _
      (RamanujanPetersson.EtCompact.P1.extO_bijective k Λ
        (RamanujanPetersson.EtSheaves.unitSh Λ (RamanujanPetersson.EtCompact.P1 k)) 0)).trans
      (RamanujanPetersson.EtCompact.hcUnivEquiv _ 2))).trans e2⟩
  · have : Fact l.Prime := ⟨hl⟩
    exact RamanujanPetersson.EtCompact.CurveHn.P1.H_add_three_eq_zero_all k l hlk m hΛ G n e
