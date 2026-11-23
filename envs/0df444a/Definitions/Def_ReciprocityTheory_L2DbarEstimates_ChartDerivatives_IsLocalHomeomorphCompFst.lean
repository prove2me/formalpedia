-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst
-- name    : ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:04.145394+00:00
-- url     : https://prove2.me/theorems/acb28c84-71d1-4d56-a93e-684c85376063
-- title:
--   Is Local Homeomorph Comp Fst
-- statement:
--   Definitions and structural lemmas for Is Local Homeomorph Comp Fst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_eq_leviV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
def chartSlice {M : Type*} [TopologicalSpace M] {n : ℕ} (e : OpenPartialHomeomorph M (V n))
    {p : ℕ} (i : Fin p) : OpenPartialHomeomorph (M × Fin p) (V n) where
  toFun q := e q.1
  invFun y := (e.symm y, i)
  source := e.source ×ˢ {i}
  target := e.target
  map_source' _q hq := e.map_source hq.1
  map_target' _y hy := ⟨e.map_target hy, rfl⟩
  left_inv' _q hq := Prod.ext (e.left_inv hq.1) (Set.mem_singleton_iff.1 hq.2).symm
  right_inv' _y hy := e.right_inv hy
  open_source := e.open_source.prod (isOpen_discrete _)
  open_target := e.open_target
  continuousOn_toFun := e.continuousOn.comp continuousOn_fst (fun _q hq => hq.1)
  continuousOn_invFun := e.continuousOn_symm.prodMk continuousOn_const
theorem isChart_chartSlice {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (p : ℕ) (i : Fin p) :
    IsChart n (fun q : M × Fin p => z q.1) (chartSlice e i) := by
  intro q hq
  exact he hq.1
theorem isLocalHomeomorph_comp_fst {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) :
    IsLocalHomeomorph (fun q : M × Fin p => z q.1) := by
  intro q
  obtain ⟨e, hx, he⟩ := hz q.1
  refine ⟨chartSlice e q.2, ⟨hx, rfl⟩, ?_⟩
  funext r
  rw [he]
  rfl
theorem chart_prodFin_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    (E : OpenPartialHomeomorph (M × Fin p) (V n)) (hE : IsChart n (fun q : M × Fin p => z q.1) E)
    (y : V n) (hy : y ∈ E.target) :
    ∃ (e : OpenPartialHomeomorph M (V n)) (i : Fin p), IsChart n z e ∧ y ∈ e.target ∧
      (E.symm : V n → M × Fin p) =ᶠ[𝓝 y] fun w => (e.symm w, i) := by
  set q := E.symm y with hq
  have hqs : q ∈ E.source := E.map_target hy
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz q.1
  have hcont : ContinuousAt E.symm y := E.continuousAt_symm hy
  have hzq : z q.1 = y := by
    have h1 : z q.1 = E q := hE hqs
    rw [h1]; exact E.right_inv hy
  refine ⟨e, q.2, he, ?_, ?_⟩
  · rw [← hzq, he hxe]; exact e.map_source hxe
  · have t1 : ∀ᶠ w in 𝓝 y, (E.symm w).1 ∈ e.source :=
      (continuous_fst.continuousAt.comp hcont).preimage_mem_nhds (e.open_source.mem_nhds hxe)
    have t2 : ∀ᶠ w in 𝓝 y, (E.symm w).2 = q.2 :=
      (continuous_snd.continuousAt.comp hcont).preimage_mem_nhds ((isOpen_discrete {q.2}).mem_nhds rfl)
    have t3 : ∀ᶠ w in 𝓝 y, w ∈ E.target := E.open_target.mem_nhds hy
    filter_upwards [t1, t2, t3] with w h1 h2 h3
    have hz1 : z (E.symm w).1 = w := by
      have h4 : z (E.symm w).1 = E (E.symm w) := hE (E.map_target h3)
      rw [h4, E.right_inv h3]
    refine Prod.ext ?_ h2
    calc (E.symm w).1 = e.symm (e (E.symm w).1) := (e.left_inv h1).symm
      _ = e.symm w := by rw [← he h1, hz1]
theorem smooth_prodFin_iff {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (F : M × Fin p → ℂ) :
    Smooth n (fun q : M × Fin p => z q.1) F ↔ ∀ i, Smooth n z (fun x => F (x, i)) := by
  constructor
  · intro h i e he
    exact h (chartSlice e i) (isChart_chartSlice n z e he p i)
  · intro h E hE y hy
    obtain ⟨e, i, he, hye, hev⟩ := chart_prodFin_local n z hz p E hE y hy
    have h1 : ContDiffAt ℝ ∞ ((fun x => F (x, i)) ∘ e.symm) y :=
      (h i e he).contDiffAt (e.open_target.mem_nhds hye)
    exact (h1.congr_of_eventuallyEq (hev.fun_comp F)).contDiffWithinAt
theorem levi_prodFin {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (ph : M × Fin p → ℝ) (x : M) (i : Fin p) (ξ : Fin n → ℂ) :
    Levi n (fun q : M × Fin p => z q.1) ph (x, i) ξ = Levi n z (fun y => ph (y, i)) x ξ := by
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  rw [levi_eq_leviV n _ (chartSlice e i) (isChart_chartSlice n z e he p i) ph (x, i) ⟨hx, rfl⟩ ξ,
    levi_eq_leviV n z e he _ x hx ξ]
  rfl
def EtaleStein.prodFin {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (X : EtaleStein n M) (p : ℕ) :
    EtaleStein n (M × Fin p) where
  z q := X.z q.1
  isLocalHomeomorph := isLocalHomeomorph_comp_fst n X.z X.isLocalHomeomorph p
  e q := X.e q.1
  smooth_e := (smooth_prodFin_iff n X.z X.isLocalHomeomorph p _).2 fun _ => X.smooth_e
  levi_e := by
    rintro ⟨x, i⟩ ξ
    rw [levi_prodFin n X.z X.isLocalHomeomorph p]
    exact X.levi_e x ξ
  isCompact_le a := by
    have h : {q : M × Fin p | X.e q.1 ≤ a} = {x | X.e x ≤ a} ×ˢ (Set.univ : Set (Fin p)) := by
      ext q; simp
    rw [h]
    exact (X.isCompact_le a).prod isCompact_univ
end
end ReciprocityTheory.L2DbarEstimates


