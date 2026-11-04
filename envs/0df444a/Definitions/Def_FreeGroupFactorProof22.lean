-- Prove2me | Definitions.Def_FreeGroupFactorProof22
-- name    : FreeGroupFactorProof22
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T04:21:06.433203+00:00
-- url     : https://prove2.me/theorems/86d29502-e34e-45c3-9cc3-90b9b8b58852
-- title:
--   Free group factors: supporting development, part 22
-- statement:
--   Part 22 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof21

set_option linter.all false

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped ComplexConjugate

open scoped ComplexConjugate ENNReal

 theorem matrix_of_commute_left {G : Type uG} [Group G] [DecidableEq G]
    (T : GroupOperator G) (hT : ∀ g, leftRegular g * T = T * leftRegular g)
    (x y : G) :
    (T (lp.single 2 y 1)) x = (T deltaOne) (y⁻¹ * x) := by
  have hl : leftRegular y deltaOne = lp.single 2 y 1 := by
    ext b
    simp [deltaOne, lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]
  rw [← hl]
  have hc := congrArg (fun f : GroupOperator G => f deltaOne) (hT y)
  simpa only [mul_apply_eq_comp, leftRegular_apply] using
    congrArg (fun v : GroupHilbert G => v x) hc.symm

 theorem mem_groupVN_iff_commute_right {G : Type uG} [Group G]
    (T : GroupOperator G) : T ∈ groupVonNeumann G ↔
      ∀ g, rightRegular g * T = T * rightRegular g := by
  classical
  refine ⟨fun h g => groupVN_commute_right ⟨T,h⟩ g, ?_⟩
  intro hT
  have hc (U : GroupOperator G) (hU : ∀ g, leftRegular g * U = U * leftRegular g) :
      U * T = T * U := by
    apply operator_matrix_ext
    intro k
    ext x
    have hleft : ((U * T) (lp.single 2 k 1)) x =
        ∑' y : G, (U deltaOne) (y⁻¹ * x) * (T deltaOne) (y * k⁻¹) := by
      change (U (T (lp.single 2 k 1))) x = _
      rw [operator_coeff_tsum U]
      apply tsum_congr
      intro y
      rw [matrix_of_commute_left U hU x y, matrix_of_commute_right T hT y k]
    have hright : ((T * U) (lp.single 2 k 1)) x =
        ∑' y : G, (T deltaOne) (x * y⁻¹) * (U deltaOne) (k⁻¹ * y) := by
      change (T (U (lp.single 2 k 1))) x = _
      rw [operator_coeff_tsum T]
      apply tsum_congr
      intro y
      rw [matrix_of_commute_right T hT x y, matrix_of_commute_left U hU y k]
    rw [hleft, hright]
    let e : G ≃ G := ((Equiv.inv G).trans (Equiv.mulLeft x)).trans (Equiv.mulRight k)
    have hs := e.tsum_eq (fun y => (U deltaOne) (y⁻¹ * x) * (T deltaOne) (y * k⁻¹))
    change (∑' c : G, (U deltaOne) ((x * c⁻¹ * k)⁻¹ * x) *
      (T deltaOne) (x * c⁻¹ * k * k⁻¹)) = _ at hs
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel,
      mul_inv_cancel, mul_one, mul_comm] using hs.symm
  rw [groupVonNeumann, StarSubalgebra.mem_centralizer_iff]
  intro U hU
  have hu : ∀ g, leftRegular g * U = U * leftRegular g := by
    intro g
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hU _
      (leftRegular_mem_leftTranslations g)).1
  refine ⟨hc U hu, hc (star U) ?_⟩
  intro g
  have hh := congrArg star (hu g⁻¹)
  simpa only [star_mul, leftRegular_star, inv_inv] using hh.symm

open scoped ComplexConjugate

 theorem rightRegular_single {G : Type uG} [Group G] [DecidableEq G] (g y : G) :
    rightRegular g (lp.single 2 y (1 : ℂ)) = lp.single 2 (y * g⁻¹) 1 := by
  ext x
  simp only [rightRegular_apply, lp.single_apply, Pi.single_apply]
  congr 1
  exact propext (eq_mul_inv_iff_mul_eq.symm)

 theorem mem_groupVN_of_matrix_invariant {G : Type uG} [Group G] [DecidableEq G]
    (T : GroupOperator G)
    (hT : ∀ x y g : G, (T (lp.single 2 (y*g) 1)) (x*g) =
      (T (lp.single 2 y 1)) x) : T ∈ groupVonNeumann G := by
  rw [mem_groupVN_iff_commute_right]
  intro g
  apply operator_matrix_ext
  intro y
  ext x
  simp only [mul_apply_eq_comp, rightRegular_apply]
  change (T (lp.single 2 y 1)) (x*g) = (T (rightRegular g (lp.single 2 y 1))) x
  rw [rightRegular_single]
  simpa only [mul_inv_cancel_right] using (hT (x*g) y g⁻¹).symm

 theorem haar_orbit_orthonormal {G : Type uG} {H : Type uH} [Group G] [Group H] [DecidableEq G]
    (ρ : G →* groupVonNeumann H)
    (hstar : ∀ g, star (ρ g) = ρ g⁻¹)
    (htrace : ∀ g, canonicalTrace (ρ g) = if g = 1 then 1 else 0) :
    Orthonormal ℂ (fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne) := by
  classical
  rw [orthonormal_iff_ite]
  intro x y
  rw [← canonicalTrace_star_mul_inner, hstar, ← map_mul, htrace]
  simp only [inv_mul_eq_one]

 theorem spatial_of_haar_total {G : Type uG} {H : Type uH} [Group G] [Group H] [DecidableEq G]
    (ρ : G →* groupVonNeumann H)
    (hstar : ∀ g, star (ρ g) = ρ g⁻¹)
    (htrace : ∀ g, canonicalTrace (ρ g) = if g = 1 then 1 else 0)
    (htotal : ⊤ ≤ (Submodule.span ℂ (Set.range
      (fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne))).topologicalClosure) :
    ∃ e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H,
      e deltaOne = deltaOne ∧
      (∀ g, e.conjStarAlgEquiv (leftRegular g) = (ρ g : GroupOperator H)) ∧
      ∀ T : GroupOperator G, T ∈ groupVonNeumann G ↔
        e.conjStarAlgEquiv T ∈ groupVonNeumann H := by
  classical
  let v : G → GroupHilbert H := fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne
  have hon : Orthonormal ℂ v := haar_orbit_orthonormal ρ hstar htrace
  let e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H :=
    (hon.isHilbertSum htotal).linearIsometryEquiv.symm
  have he (g : G) : e (lp.single 2 g 1) = v g :=
    hon.linearIsometryEquiv_symm_apply_single_one htotal g
  have hδ : e deltaOne = deltaOne := by
    rw [deltaOne_eq, he]
    simp [v]
  have hleft (g : G) : e.conjStarAlgEquiv (leftRegular g) = (ρ g : GroupOperator H) := by
    apply e.conjStarAlgEquiv.symm.injective
    change e.conjStarAlgEquiv.symm (e.conjStarAlgEquiv (leftRegular g)) =
      e.conjStarAlgEquiv.symm (ρ g : GroupOperator H)
    rw [e.conjStarAlgEquiv.symm_apply_apply]
    apply operator_matrix_ext
    intro y
    apply e.injective
    change e (leftRegular g (lp.single 2 y 1)) =
      e (e.symm ((ρ g : GroupOperator H) (e (lp.single 2 y 1))))
    rw [e.apply_symm_apply, he]
    have hl : leftRegular g (lp.single 2 y (1 : ℂ)) = lp.single 2 (g*y) 1 := by
      ext x
      simp only [leftRegular_apply, lp.single_apply, Pi.single_apply]
      congr 1
      exact propext (inv_mul_eq_iff_eq_mul)
    rw [hl, he]
    change ((ρ (g*y) : groupVonNeumann H) : GroupOperator H) deltaOne = _
    rw [map_mul]
    rfl
  refine ⟨e, hδ, hleft, ?_⟩
  intro T
  constructor
  · intro hT
    rw [mem_groupVN_iff_commute_right]
    intro g
    apply e.conjStarAlgEquiv.symm.injective
    change e.conjStarAlgEquiv.symm (rightRegular g * e.conjStarAlgEquiv T) =
      e.conjStarAlgEquiv.symm (e.conjStarAlgEquiv T * rightRegular g)
    rw [map_mul, map_mul, e.conjStarAlgEquiv.symm_apply_apply]
    have hc : e.conjStarAlgEquiv.symm (rightRegular g) ∈
        StarSubalgebra.centralizer ℂ (leftTranslations G) := by
      rw [StarSubalgebra.mem_centralizer_iff, leftTranslations_eq_range]
      rintro _ ⟨x,rfl⟩
      constructor
      · apply e.conjStarAlgEquiv.injective
        change e.conjStarAlgEquiv (leftRegular _ * e.conjStarAlgEquiv.symm (rightRegular g)) =
          e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm (rightRegular g) * leftRegular _)
        rw [map_mul, map_mul, e.conjStarAlgEquiv.apply_symm_apply, hleft]
        exact (groupVN_commute_right (ρ x) g).symm
      · rw [leftRegular_star]
        apply e.conjStarAlgEquiv.injective
        change e.conjStarAlgEquiv (leftRegular _ * e.conjStarAlgEquiv.symm (rightRegular g)) =
          e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm (rightRegular g) * leftRegular _)
        rw [map_mul, map_mul, e.conjStarAlgEquiv.apply_symm_apply, hleft]
        exact (groupVN_commute_right (ρ x⁻¹) g).symm
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ hc).1
  · intro hT
    let U : groupVonNeumann H := ⟨e.conjStarAlgEquiv T, hT⟩
    have hm (x y : G) : (T (lp.single 2 y 1)) x =
        canonicalTrace (star (ρ x) * U * ρ y) := by
      calc
        (T (lp.single 2 y 1)) x = inner ℂ (lp.single 2 x 1) (T (lp.single 2 y 1)) := by
          simp [lp.inner_single_left]
        _ = inner ℂ (v x) ((U : GroupOperator H) (v y)) := by
          rw [← he x, ← he y, ← e.inner_map_map]
          change inner ℂ (e (lp.single 2 x 1)) (e (T (lp.single 2 y 1))) =
            inner ℂ (e (lp.single 2 x 1)) (e (T (e.symm (e (lp.single 2 y 1)))))
          rw [e.symm_apply_apply]
        _ = canonicalTrace (star (ρ x) * U * ρ y) := by
          rw [mul_assoc, canonicalTrace_star_mul_inner]
          rfl
    apply mem_groupVN_of_matrix_invariant T
    intro x y g
    rw [hm, hm, map_mul, map_mul, star_mul]
    have hc := canonicalTrace_mul (star (ρ g) * star (ρ x) * U * ρ y) (ρ g)
    simp only [← mul_assoc]
    rw [hc]
    simp only [hstar, ← mul_assoc, ← map_mul, mul_inv_cancel, one_mul]

 theorem iso_extension_of_haar_total {G : Type uG} {H : Type uH} [Group G] [Group H] [DecidableEq G]
    (ρ : G →* groupVonNeumann H)
    (hstar : ∀ g, star (ρ g) = ρ g⁻¹)
    (htrace : ∀ g, canonicalTrace (ρ g) = if g = 1 then 1 else 0)
    (htotal : ⊤ ≤ (Submodule.span ℂ (Set.range
      (fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne))).topologicalClosure) :
    ∃ Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H,
      (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology G) (groupUltraweakTopology H) Φ ∧
      ∀ g, Φ (groupUnitary g) = ρ g := by
  classical
  obtain ⟨e,hδ,hρ,hVN⟩ := spatial_of_haar_total ρ hstar htrace htotal
  refine ⟨spatialGroupIso e hVN, ?_, spatialGroupIso_normal e hVN, ?_⟩
  · intro T
    rw [canonicalTrace_eq_inner, canonicalTrace_eq_inner, ← deltaOne_eq, ← deltaOne_eq]
    change inner ℂ deltaOne (e ((T : GroupOperator G) (e.symm deltaOne))) =
      inner ℂ deltaOne ((T : GroupOperator G) deltaOne)
    rw [← hδ, e.symm_apply_apply, e.inner_map_map]
  · intro g
    apply Subtype.ext
    exact hρ g

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

section
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def reducingAlgebra (K : Submodule ℂ H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {T | (∀ x ∈ K, T x ∈ K) ∧ ∀ x ∈ K, (star T) x ∈ K}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro T U ⟨hT,hT'⟩ ⟨hU,hU'⟩
    constructor
    · intro x hx; exact K.add_mem (hT x hx) (hU x hx)
    · intro x hx; simpa using K.add_mem (hT' x hx) (hU' x hx)
  mul_mem' := by
    rintro T U ⟨hT,hT'⟩ ⟨hU,hU'⟩
    constructor
    · intro x hx; exact hT _ (hU x hx)
    · intro x hx; simpa using hU' _ (hT' x hx)
  algebraMap_mem' := by
    intro c
    constructor
    · intro x hx; simpa using K.smul_mem c hx
    · intro x hx; simpa only [← algebraMap_star_comm, ContinuousLinearMap.algebraMap_apply] using K.smul_mem (star c) hx
  star_mem' := by
    rintro T ⟨hT,hT'⟩
    exact ⟨hT', by simpa using hT⟩

theorem reducingAlgebra_isClosed (K : Submodule ℂ H) (hK : IsClosed (K : Set H)) :
    IsClosed (reducingAlgebra K : Set (H →L[ℂ] H)) := by
  change IsClosed {T : H →L[ℂ] H | _ ∧ _}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _hx
    exact hK.preimage (ContinuousLinearMap.apply ℂ H x).continuous
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _hx
    exact hK.preimage ((ContinuousLinearMap.apply ℂ H x).continuous.comp continuous_star)

omit [CompleteSpace H] in

theorem closedSpan_invariant {G : Type uG} [Group G]
    (ρ : G →* (H →L[ℂ] H)) (ξ : H) (g : G) :
    ∀ x ∈ (Submodule.span ℂ (Set.range (fun a => ρ a ξ))).topologicalClosure,
      ρ g x ∈ (Submodule.span ℂ (Set.range (fun a => ρ a ξ))).topologicalClosure := by
  let K := (Submodule.span ℂ (Set.range (fun a => ρ a ξ))).topologicalClosure
  change K ≤ K.comap (ρ g).toLinearMap
  apply Submodule.topologicalClosure_minimal
  · rw [Submodule.span_le]
    rintro _ ⟨a,rfl⟩
    change ρ g (ρ a ξ) ∈ K
    have he : ρ g (ρ a ξ) = ρ (g*a) ξ := by rw [map_mul]; rfl
    rw [he]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g*a, rfl⟩)
  · exact (Submodule.isClosed_topologicalClosure _).preimage (ρ g).continuous

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}
 theorem wordHom_mem (E : StarSubalgebra ℂ A) (U : ι → unitary A)
    (hU : ∀ i, (U i : A) ∈ E) (g : FreeGroup ι) : wordHom U g ∈ E := by
  induction g using FreeGroup.induction_on with
  | C1 => rw [map_one]; exact one_mem E
  | of i => simpa only [wordHom_of] using hU i
  | inv_of i hi => rw [wordHom_inv]; exact star_mem hi
  | mul x y hx hy => rw [map_mul]; exact mul_mem hx hy

 theorem laurentValue_mem (E : StarSubalgebra ℂ A) (C : unitary A)
    (hC : (C : A) ∈ E) (l : ℤ →₀ ℂ) : laurentValue C l ∈ E := by
  have hp (k : ℤ) : ((C ^ k : unitary A) : A) ∈ E := by
    cases k with
    | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast]
      exact pow_mem hC n
    | negSucc n =>
      rw [zpow_negSucc]
      change star ((C : A) ^ (n+1)) ∈ E
      exact star_mem (pow_mem hC (n+1))
  classical
  change (∑ k ∈ l.support, l k • ((C ^ k : unitary A) : A)) ∈ E
  exact sum_mem fun k _ => E.smul_mem (hp k) _
end UnitaryEvaluation

open UnitaryEvaluation
open scoped ENNReal

 theorem flow_word_orbit_total {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l))
    (X : ℝ → ι → groupVonNeumann (FreeGroup (Option ι)))
    (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option ι))))
    (hX₀ : X 0 = fun j => groupUnitary (FreeGroup.of (some j)))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option ι)) l) h (X t)) t) (t₀ : ℝ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (fun g : FreeGroup (Option ι) =>
      ((wordHom (extendUnitary (fun j => ⟨X t₀ j, hU t₀ j⟩)
        (generatorUnitary none)) g : groupVonNeumann (FreeGroup (Option ι))) :
          GroupOperator (FreeGroup (Option ι))) deltaOne))).topologicalClosure := by
  classical
  let U := extendUnitary (fun j => ⟨X t₀ j, hU t₀ j⟩) (generatorUnitary none)
  let ρ : FreeGroup (Option ι) →* GroupOperator (FreeGroup (Option ι)) :=
    (groupVonNeumann _).subtype.toMonoidHom.comp (wordHom U)
  let K := (Submodule.span ℂ (Set.range (fun g => ρ g deltaOne))).topologicalClosure
  let E := (reducingAlgebra K).comap (groupVonNeumann _).subtype
  have hK : IsClosed (K : Set (GroupHilbert (FreeGroup (Option ι)))) :=
    Submodule.isClosed_topologicalClosure _
  have hE : IsClosed (E : Set (groupVonNeumann (FreeGroup (Option ι)))) :=
    (reducingAlgebra_isClosed K hK).preimage continuous_subtype_val
  have hρ (g) : wordHom U g ∈ E := by
    constructor
    · exact closedSpan_invariant ρ deltaOne g
    · have he : star (ρ g) = ρ g⁻¹ := by
        change ((star (wordHom U g) : groupVonNeumann (FreeGroup (Option ι))) :
          GroupOperator (FreeGroup (Option ι))) = _
        rw [← wordHom_inv]
        rfl
      change ∀ x ∈ K, (star (ρ g)) x ∈ K
      rw [he]
      exact closedSpan_invariant ρ deltaOne g⁻¹
  have hC : (generatorUnitary (none : Option ι) : groupVonNeumann _) ∈ E := by
    simpa only [wordHom_of, U, extendUnitary, Option.elim_none] using hρ (FreeGroup.of none)
  have hXt : ∀ j, X t₀ j ∈ E := by
    intro j
    simpa only [wordHom_of, U, extendUnitary, Option.elim_some] using hρ (FreeGroup.of (some j))
  have hXS := PolynomialFlow.solution_mem_subalgebra E hE
    (laurentValue (generatorUnitary (none : Option ι)) l) hS
    (laurentValue_mem E _ hC l) h X hX hU t₀ hXt
  have hgen (i : Option ι) : (generatorUnitary i : groupVonNeumann _) ∈ E := by
    cases i with
    | none => exact hC
    | some j =>
      change groupUnitary (FreeGroup.of (some j)) ∈ E
      simpa only [hX₀] using hXS 0 j
  have hgroup (g : FreeGroup (Option ι)) : groupUnitary g ∈ E := by
    rw [← wordHom_generatorUnitary]
    exact wordHom_mem E generatorUnitary hgen g
  have hδ : deltaOne ∈ K := by
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  have hsingle (g : FreeGroup (Option ι)) : lp.single 2 g (1 : ℂ) ∈ K := by
    have hh := (hgroup g).1 deltaOne hδ
    have he : (leftRegular g) deltaOne = lp.single 2 g 1 := by
      ext x
      simp [deltaOne, lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]
    change (leftRegular g) deltaOne ∈ K at hh
    rwa [he] at hh
  change ⊤ ≤ K
  intro ξ _hξ
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ
  apply hK.mem_of_tendsto hs
  filter_upwards [] with s
  apply K.sum_mem
  intro g _hg
  have he : lp.single 2 g (ξ g) = (ξ g) • (lp.single 2 g (1 : ℂ) : GroupHilbert (FreeGroup (Option ι))) := by
    ext x
    simp [lp.single_apply, Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hsingle g)

open UnitaryEvaluation

end

end FreeGroupFactorMain

end OAI
end


