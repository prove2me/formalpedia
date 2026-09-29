-- Prove2me | solution 1 for AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f42f3340-da10-58fe-a614-28ce316b1331

import Mathlib
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension_of_isAlgClosed

set_option autoImplicit false

open AlgebraicCurve

namespace TRGBody

theorem finiteAlong_of_isIntegral
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) : FiniteAlong K φ := by
  classical
  obtain ⟨x', -, hfd⟩ := hfg'
  letI : Algebra F F' := algebraAlong φ
  haveI : IsScalarTower K F F' := isScalarTower_along φ

  have hx' : IsIntegral F x' := hφ x'
  haveI h1 : FiniteDimensional F (IntermediateField.adjoin F ({x'} : Set F')) :=
    IntermediateField.adjoin.finiteDimensional hx'

  let M : IntermediateField K F' := (IntermediateField.adjoin F ({x'} : Set F')).restrictScalars K
  have hle : IntermediateField.adjoin K ({x'} : Set F') ≤ M := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    show y ∈ IntermediateField.adjoin F ({x'} : Set F')
    exact IntermediateField.subset_adjoin F _ hy
  letI : Algebra (IntermediateField.adjoin K ({x'} : Set F')) M := (IntermediateField.inclusion hle).toAlgebra
  haveI : IsScalarTower (IntermediateField.adjoin K ({x'} : Set F')) M F' :=
    IsScalarTower.of_algebraMap_eq (fun y => rfl)
  haveI h2 : Module.Finite M F' :=
    Module.Finite.of_restrictScalars_finite (IntermediateField.adjoin K ({x'} : Set F')) M F'
  haveI h2' : Module.Finite (IntermediateField.adjoin F ({x'} : Set F')) F' := h2
  show Module.Finite F F'
  exact Module.Finite.trans (IntermediateField.adjoin F ({x'} : Set F')) F'

theorem span_range_algebraMap_eq_top
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ)
    (E FE F'E : Type*) [Field E] [Field FE] [Field F'E] [Algebra K E] [Algebra E FE] [Algebra F FE]
    [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E] [IsScalarTower K E F'E] [IsScalarTower K F' F'E]
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE : FE →ₐ[E] F'E) (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f)) :
    letI := algebraAlong φE
    Submodule.span FE (Set.range (algebraMap F' F'E)) = ⊤ := by
  classical
  letI iφ : Algebra F F' := algebraAlong φ
  letI iφE : Algebra FE F'E := algebraAlong φE
  haveI : IsScalarTower E FE F'E := IsScalarTower.of_algebraMap_eq (fun e => (φE.commutes e).symm)
  haveI : Module.Finite F F' := hfin

  let A : Subalgebra FE F'E := Algebra.adjoin FE (Set.range (algebraMap F' F'E))
  have hAspan : Subalgebra.toSubmodule A = Submodule.span FE (Set.range (algebraMap F' F'E)) := by
    rw [Algebra.adjoin_eq_span]
    congr 1
    show ((Submonoid.closure (Set.range (algebraMap F' F'E)) : Submonoid F'E) : Set F'E) = _
    have : Set.range (algebraMap F' F'E) = ((MonoidHom.mrange (algebraMap F' F'E : F' →* F'E)) : Set F'E) := by
      ext; simp
    rw [this, Submonoid.closure_eq]

  have hint : ∀ u : F', IsIntegral FE (algebraMap F' F'E u) := by
    intro u
    have hu : IsIntegral F u := Algebra.IsIntegral.isIntegral u
    obtain ⟨p, hp, hp0⟩ := hu
    refine ⟨p.map (algebraMap F FE), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap FE F'E).comp (algebraMap F FE) = (algebraMap F' F'E).comp (algebraMap F F') := by
      ext f; exact hφcomm f
    rw [this, ← Polynomial.hom_eval₂, hp0, map_zero]
  have hAint : ∀ x ∈ A, IsIntegral FE x := by
    intro x hx
    refine Algebra.adjoin_induction (fun y hy => ?_) (fun r => isIntegral_algebraMap) (fun _ _ _ _ => IsIntegral.add)
      (fun _ _ _ _ => IsIntegral.mul) hx
    obtain ⟨u, rfl⟩ := hy
    exact hint u
  have hinv : ∀ x ∈ A, x⁻¹ ∈ A := by
    intro x hx
    have := Subalgebra.inv_mem_of_algebraic (A := A) (x := ⟨x, hx⟩) (hAint x hx).isAlgebraic
    simpa using this

  let T : IntermediateField E F'E := (A.restrictScalars E).toIntermediateField (fun x hx => hinv x hx)
  have hT : T = ⊤ := by
    apply top_le_iff.mp
    rw [← hgen', IntermediateField.adjoin_le_iff]
    rintro _ ⟨u, rfl⟩
    show algebraMap F' F'E u ∈ A
    exact Algebra.subset_adjoin ⟨u, rfl⟩
  apply top_le_iff.mp
  intro x _
  have hx : x ∈ T := by rw [hT]; trivial
  have hx' : x ∈ Subalgebra.toSubmodule A := hx
  rwa [hAspan] at hx'

theorem linearIndependent_algebraMap
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F']
    (hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ : F →ₐ[K] F')
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE : FE →ₐ[E] F'E) (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    {ι : Type*} (b : ι → F') (hb : letI := algebraAlong φ; LinearIndependent F b) :
    letI := algebraAlong φE
    LinearIndependent FE (fun i => algebraMap F' F'E (b i)) := by
  classical
  letI iφ : Algebra F F' := algebraAlong φ
  haveI hKFF' : IsScalarTower K F F' := isScalarTower_along φ
  letI iφE : Algebra FE F'E := algebraAlong φE
  haveI hEFE : IsScalarTower E FE F'E := IsScalarTower.of_algebraMap_eq (fun e => (φE.commutes e).symm)

  let R₀ : Subalgebra F FE := Algebra.adjoin F (Set.range (algebraMap E FE))
  have hR₀frac : ∀ z : FE, ∃ x y : R₀, z = algebraMap R₀ FE x / algebraMap R₀ FE y := by
    intro z
    have hz : z ∈ IntermediateField.adjoin E (Set.range (algebraMap F FE)) := by rw [hgen]; trivial
    obtain ⟨r, hr, s, hs, h⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    have hsw : ∀ x, x ∈ Algebra.adjoin E (Set.range (algebraMap F FE)) → x ∈ R₀ := by
      intro x hx
      rw [← Subalgebra.mem_toSubring, Algebra.adjoin_eq_ring_closure] at hx ⊢
      rwa [Set.union_comm]
    exact ⟨⟨r, hsw r hr⟩, ⟨s, hsw s hs⟩, h⟩
  haveI : IsFractionRing R₀ FE := IsFractionRing.of_field R₀ FE hR₀frac

  rw [← LinearIndependent.iff_fractionRing R₀ FE]

  let ε := Module.Free.chooseBasis K E
  have hR₀span : ∀ r : R₀, ∃ g : Module.Free.ChooseBasisIndex K E →₀ F,
      (r : FE) = g.sum (fun a c => c • algebraMap E FE (ε a)) := by
    intro r
    have hr : (r : FE) ∈ Subalgebra.toSubmodule R₀ := r.2
    rw [Algebra.adjoin_eq_span] at hr
    have hcl : ((Submonoid.closure (Set.range (algebraMap E FE)) : Submonoid FE) : Set FE) =
        Set.range (algebraMap E FE) := by
      have : Set.range (algebraMap E FE) = ((MonoidHom.mrange (algebraMap E FE : E →* FE)) : Set FE) := by
        ext; simp
      rw [this, Submonoid.closure_eq]
    rw [hcl] at hr
    have hle : Submodule.span F (Set.range (algebraMap E FE)) ≤
        Submodule.span F (Set.range (fun a => algebraMap E FE (ε a))) := by
      rw [Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      rw [← ε.linearCombination_repr e, Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.sum]
      refine Submodule.sum_mem _ fun a _ => ?_
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K E FE,
        IsScalarTower.algebraMap_apply K F FE, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨g, hg⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hle hr)
    exact ⟨g, hg.symm⟩
  choose g hg using hR₀span

  let f₀ : F' →ₐ[K] F'E := IsScalarTower.toAlgHom K F' F'E
  let A' : IntermediateField K F'E := f₀.fieldRange
  have hmemA' : ∀ x : F', f₀ x ∈ A' := fun x => f₀.mem_fieldRange.mpr ⟨x, rfl⟩
  let toA' : F' →ₗ[K] A' :=
    { toFun := fun x => ⟨f₀ x, hmemA' x⟩
      map_add' := fun x y => Subtype.ext (map_add f₀ x y)
      map_smul' := fun c x => Subtype.ext (by simp) }
  have htoA' : Function.Bijective toA' := by
    refine ⟨fun x y hxy => f₀.toRingHom.injective (congrArg Subtype.val hxy), fun y => ?_⟩
    obtain ⟨x, hx⟩ := f₀.mem_fieldRange.mp y.2
    exact ⟨x, Subtype.ext hx⟩
  let β := (Module.Free.chooseBasis K F').map (LinearEquiv.ofBijective toA' htoA')
  have h73 := AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed K F' E F'E
    hfg' hfgE' hgen' (Module.Free.chooseBasis K F').linearIndependent
  have hLD : A'.LinearDisjoint E := by
    refine IntermediateField.LinearDisjoint.of_basis_left β ?_
    convert h73 using 1
    rfl
  have hεind : LinearIndependent A' (fun a => algebraMap E F'E (ε a)) :=
    hLD.linearIndependent_right' ε.linearIndependent

  rw [linearIndependent_iff']
  intro s r hrel i hi
  let T : Finset (Module.Free.ChooseBasisIndex K E) := s.biUnion (fun j => (g (r j)).support)

  let κF : Module.Free.ChooseBasisIndex K E → F' := fun a => ∑ j ∈ s, φ (g (r j) a) * b j
  have hexp : ∀ j ∈ s, (r j : FE) = ∑ a ∈ T, g (r j) a • algebraMap E FE (ε a) := by
    intro j hj
    rw [hg (r j), Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun j => (g (r j)).support) hj) _ (fun a _ => by simp)]
  have key : ∑ j ∈ s, r j • algebraMap F' F'E (b j) =
      ∑ a ∈ T, (⟨f₀ (κF a), hmemA' (κF a)⟩ : A') • algebraMap E F'E (ε a) := by
    calc ∑ j ∈ s, r j • algebraMap F' F'E (b j)
        = ∑ j ∈ s, φE (r j : FE) * algebraMap F' F'E (b j) := by
          exact Finset.sum_congr rfl fun j _ => rfl
      _ = ∑ j ∈ s, ∑ a ∈ T, algebraMap F' F'E (φ (g (r j) a)) * algebraMap E F'E (ε a) *
            algebraMap F' F'E (b j) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hexp j hj, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Algebra.smul_def, map_mul, hφcomm, φE.commutes]
      _ = ∑ a ∈ T, ∑ j ∈ s, algebraMap F' F'E (φ (g (r j) a)) * algebraMap E F'E (ε a) *
            algebraMap F' F'E (b j) := Finset.sum_comm
      _ = ∑ a ∈ T, (⟨f₀ (κF a), hmemA' (κF a)⟩ : A') • algebraMap E F'E (ε a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Algebra.smul_def]
          show _ = f₀ (κF a) * _
          simp only [κF, map_sum, map_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          show _ = algebraMap F' F'E (φ (g (r j) a)) * algebraMap F' F'E (b j) * algebraMap E F'E (ε a)
          ring
  rw [key] at hrel
  have hκ : ∀ a ∈ T, κF a = 0 := by
    intro a ha
    have h := linearIndependent_iff'.mp hεind T _ hrel a ha
    have h' : f₀ (κF a) = 0 := congrArg Subtype.val h
    exact f₀.toRingHom.injective (h'.trans (map_zero _).symm)

  have hg0 : ∀ j ∈ s, ∀ a, g (r j) a = 0 := by
    intro j hj a
    by_cases ha : a ∈ T
    · have hsum : ∑ j ∈ s, g (r j) a • b j = 0 := by
        have := hκ a ha
        simp only [κF] at this
        simp [Algebra.smul_def] at this ⊢
        exact this
      exact linearIndependent_iff'.mp hb s (fun j => g (r j) a) hsum j hj
    · by_contra hne
      exact ha (Finset.mem_biUnion.mpr ⟨j, hj, Finsupp.mem_support_iff.mpr hne⟩)
  have hri : (r i : FE) = 0 := by
    rw [hexp i hi]
    exact Finset.sum_eq_zero fun a _ => by rw [hg0 i hi a, zero_smul]
  exact Subtype.ext hri

end TRGBody

theorem solution
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F'] [IsCurveOver K F']
    (hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hφE : φE.toRingHom.IsIntegral) :
    FiniteAlong K φ ∧ FiniteAlong E φE ∧ finrankAlong E φE = finrankAlong K φ ∧
    ∀ u : F',
      (letI := algebraAlong φE; Algebra.trace FE F'E (algebraMap F' F'E u)) =
        algebraMap F FE (letI := algebraAlong φ; Algebra.trace F F' u) := by
  classical
  have hfin : FiniteAlong K φ := TRGBody.finiteAlong_of_isIntegral K F F' hfg' φ hφ
  have hfinE : FiniteAlong E φE := TRGBody.finiteAlong_of_isIntegral E FE F'E hfgE' φE hφE
  letI iφ : Algebra F F' := algebraAlong φ
  letI iφE : Algebra FE F'E := algebraAlong φE
  haveI : Module.Finite F F' := hfin
  let bF := Module.Free.chooseBasis F F'

  have hsq : ∀ c : F, algebraMap F' F'E (algebraMap F F' c) = algebraMap FE F'E (algebraMap F FE c) :=
    fun c => (hφcomm c).symm
  have hli : LinearIndependent FE (fun i => algebraMap F' F'E (bF i)) :=
    TRGBody.linearIndependent_algebraMap K F hfg F' hfg' φ E FE hfgE hgen F'E hfgE' hgen' φE hφcomm bF
      bF.linearIndependent
  have hsp : ⊤ ≤ Submodule.span FE (Set.range fun i => algebraMap F' F'E (bF i)) := by
    have h := TRGBody.span_range_algebraMap_eq_top K F F' φ hfin E FE F'E hgen' φE hφcomm
    rw [← h, Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    rw [← bF.linearCombination_repr u, Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, map_mul, hsq, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bE : Module.Basis (Module.Free.ChooseBasisIndex F F') FE F'E := Module.Basis.mk hli hsp
  have hbE : ∀ i, bE i = algebraMap F' F'E (bF i) := fun i => Module.Basis.mk_apply hli hsp i

  have hrepr : ∀ (x : F') (j : Module.Free.ChooseBasisIndex F F'),
      bE.repr (algebraMap F' F'E x) j = algebraMap F FE (bF.repr x j) := by
    intro x j
    have key : algebraMap F' F'E x =
        Finsupp.linearCombination FE bE ((bF.repr x).mapRange (algebraMap F FE) (map_zero _)) := by
      conv_lhs => rw [← bF.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum,
        Finsupp.sum_mapRange_index (fun _ => by simp)]
      simp only [Finsupp.sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbE, Algebra.smul_def, map_mul, hsq, ← Algebra.smul_def]
    rw [key, Module.Basis.repr_linearCombination, Finsupp.mapRange_apply]
  refine ⟨hfin, hfinE, ?_, ?_⟩
  · show Module.finrank FE F'E = Module.finrank F F'
    rw [Module.finrank_eq_card_basis bE, Module.finrank_eq_card_basis bF]
  · intro u
    show Algebra.trace FE F'E (algebraMap F' F'E u) = algebraMap F FE (Algebra.trace F F' u)
    rw [Algebra.trace_eq_matrix_trace bF, Algebra.trace_eq_matrix_trace bE, Matrix.trace, Matrix.trace,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, hbE, ← map_mul, hrepr]

end S_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension_of_isAlgClosed (solution)
