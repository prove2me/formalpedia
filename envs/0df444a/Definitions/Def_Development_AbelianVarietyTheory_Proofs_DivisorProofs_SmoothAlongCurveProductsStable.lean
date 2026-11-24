-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlongCurveProductsStable
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlongCurveProductsStable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:58.583665+00:00
-- url     : https://prove2.me/theorems/1f92942e-5cf8-4e3d-9ab8-b47fbd6b4463
-- title:
--   Smooth Along Curve Products Stable
-- statement:
--   Definitions and structural lemmas for Smooth Along Curve Products Stable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlongCurveProductsStable.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
namespace GlobalTheory
namespace CurveProductSmooth
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G)
def JointlySmooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → K) : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (g : F → E), ContDiff ℝ ∞ g →
    ∀ l : List (P × (F → ℝ)), (∀ a ∈ l, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) →
      ContDiff ℝ ∞ fun x : F => ρ (l.map fun a => e a.1 (a.2 x)).prod (Φ (g x))
variable {ρ A e}
theorem JointlySmooth.extra {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) {p : P} (hp : p ∈ A)
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (g : F → E) (hg : ContDiff ℝ ∞ g)
    (l : List (P × (F → ℝ))) (hl : ∀ a ∈ l, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    ContDiff ℝ ∞ fun y : F × ℝ =>
      ρ (l.map fun a => e a.1 (a.2 y.1)).prod (ρ (e p y.2) (Φ (g y.1))) := by
  have h1 := h (F × ℝ) (g ∘ Prod.fst) (hg.comp contDiff_fst)
    ((l.map fun a => (a.1, a.2 ∘ Prod.fst)) ++ [(p, Prod.snd)]) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hl b hb).1, (hl b hb).2.comp contDiff_fst⟩
    · obtain rfl := List.mem_singleton.1 ha
      exact ⟨hp, contDiff_snd⟩)
  simp only [List.map_append, List.prod_append, map_mul, List.map_map, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h1
  exact h1
theorem JointlySmooth.deriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) {p : P} (hp : p ∈ A) :
    JointlySmooth ρ A e fun t => deriv (fun r : ℝ => ρ (e p r) (Φ t)) 0 := by
  intro F _ _ g hg l hl
  have h1 := h.extra hp F g hg l hl
  have h0 := h.extra hp F g hg [] (by simp)
  simp only [List.map_nil, List.prod_nil, map_one, one_apply_eq_self] at h0
  have hd : ∀ x : F, DifferentiableAt ℝ (fun r : ℝ => ρ (e p r) (Φ (g x))) 0 := fun x =>
    ((h0.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ fun r : ℝ => (x, r))).differentiable
      (by simp)) 0
  have h2 : ContDiff ℝ ∞ fun x : F => fderiv ℝ (fun r : ℝ =>
      ρ (l.map fun a => e a.1 (a.2 x)).prod (ρ (e p r) (Φ (g x)))) 0 :=
    ContDiff.fderiv (f := fun (x : F) (r : ℝ) =>
      ρ (l.map fun a => e a.1 (a.2 x)).prod (ρ (e p r) (Φ (g x)))) (g := fun _ => (0 : ℝ))
      (m := ∞) h1 contDiff_const (by simp)
  have h3 := h2.clm_apply (contDiff_const (c := (1 : ℝ)))
  convert h3 using 2 with x
  have h4 := ((ρ (l.map fun a => e a.1 (a.2 x)).prod).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hd x).hasDerivAt
  exact h4.deriv.symm
theorem JointlySmooth.foldr {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) (l : List P) (hl : ∀ p ∈ l, p ∈ A) :
    JointlySmooth ρ A e fun t =>
      l.foldr (fun p w => _root_.deriv (fun r : ℝ => ρ (e p r) w) 0) (Φ t) := by
  induction l with
  | nil => exact h
  | cons p l ih =>
    exact (ih fun q hq => hl q (List.mem_cons_of_mem _ hq)).deriv (hl p List.mem_cons_self)
end CurveProductSmooth
end GlobalTheory


