-- Prove2me | solution 1 for AronszajnRK.Inclusion.equivalent_norms_same_class
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T06:35:00.191137+00:00
-- url     : https://prove2.me/submissions/eed3c3c4-ad5f-407a-9865-54c6fdd847a8

import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Basic
import Mathlib.Tactic

open Filter Topology

namespace AronszajnRK.Inclusion

section Transfer

variable {X H H₁ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [RKHS ℂ H X ℂ] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [RKHS ℂ H₁ X ℂ]

noncomputable def transfer (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f)) :
    H₁ → H :=
  fun f₁ => Classical.choose (hsub ⟨f₁, rfl⟩)

lemma transfer_apply (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f))
    (f₁ : H₁) (x : X) : (transfer hsub f₁) x = f₁ x :=
  congrFun (Classical.choose_spec (hsub ⟨f₁, rfl⟩)) x

end Transfer

theorem normBoundAux {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f)) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f‖ ≤ M * ‖f₁‖ := by
  classical

  have key : ∀ (f₁ : H₁) (x : X), (transfer hsub f₁) x = f₁ x := transfer_apply hsub
  have addval : ∀ (f g : H₁) (x : X), ((f + g : H₁)) x = f x + g x := by
    intro f g x
    simpa using congrFun (RKHS.coe_add f g) x
  have smulval : ∀ (c : ℂ) (f : H₁) (x : X), ((c • f : H₁)) x = c * f x := by
    intro c f x
    simpa [Pi.smul_apply] using congrFun (RKHS.coe_smul f c) x

  have hadd : ∀ a b : H₁, transfer hsub (a + b) = transfer hsub a + transfer hsub b := by
    intro a b
    have e : ∀ x : X, (transfer hsub (a + b)) x = (transfer hsub a + transfer hsub b) x := by
      intro x
      calc (transfer hsub (a + b)) x = (a + b : H₁) x := key (a + b) x
        _ = a x + b x := addval a b x
        _ = (transfer hsub a) x + (transfer hsub b) x := by rw [key, key]
        _ = (transfer hsub a + transfer hsub b) x := by
            rw [show (transfer hsub a + transfer hsub b) x
                = (transfer hsub a) x + (transfer hsub b) x from by
              rw [RKHS.coe_add, Pi.add_apply]]
    exact RKHS.ext e
  have hzero : transfer hsub 0 = 0 := by
    have e : ∀ x : X, (transfer hsub 0) x = (0 : H) x := by
      intro x
      rw [key]
      simp [RKHS.coe_zero]
    exact RKHS.ext e
  have hsmul : ∀ (c : ℂ) (a : H₁), transfer hsub (c • a) = c • transfer hsub a := by
    intro c a
    have e : ∀ x : X, (transfer hsub (c • a)) x = (c • transfer hsub a) x := by
      intro x
      calc (transfer hsub (c • a)) x = (c • a : H₁) x := key (c • a) x
        _ = c * a x := smulval c a x
        _ = (c • transfer hsub a) x := by
            rw [show (c • transfer hsub a) x = c * (transfer hsub a) x from by
              rw [RKHS.coe_smul, Pi.smul_apply, smul_eq_mul]]
            rw [key]
    exact RKHS.ext e
  let L : H₁ →ₗ[ℂ] H :=
    { toFun := transfer hsub, map_add' := hadd, map_smul' := fun c a => hsmul c a }

  have hgraph : ∀ (u : ℕ → H₁) (a : H₁) (b : H),
      Filter.Tendsto u Filter.atTop (𝓝 a) → Filter.Tendsto (fun n => L (u n)) Filter.atTop (𝓝 b) → b = L a := by
    intro u a b hu hy
    apply RKHS.ext (f := b) (g := L a)
    intro x₀
    have h1 : Filter.Tendsto (fun n => (u n) x₀) Filter.atTop (𝓝 (a x₀)) :=
      ((RKHS.continuous_eval (𝕜 := ℂ) (H := H₁) x₀).tendsto a).comp hu
    have h2 : Filter.Tendsto (fun n => (L (u n)) x₀) Filter.atTop (𝓝 (b x₀)) :=
      ((RKHS.continuous_eval (𝕜 := ℂ) (H := H) x₀).tendsto b).comp hy
    have h3 : ∀ n, (L (u n)) x₀ = (u n) x₀ := fun n => key (u n) x₀
    rw [funext h3] at h2
    have h4 : (L a) x₀ = a x₀ := key a x₀
    rw [h4]
    exact tendsto_nhds_unique h2 h1
  have hcont : Continuous L := L.continuous_of_seq_closed_graph hgraph
  obtain ⟨C, hC₀, hC⟩ := SemilinearMapClass.bound_of_continuous L hcont
  refine ⟨C, hC₀, fun f₁ f hf => ?_⟩
  have hf' : f = L f₁ := RKHS.ext fun x => (congrFun hf x).trans (key f₁ x).symm
  calc ‖f‖ = ‖L f₁‖ := by rw [hf']
    _ ≤ C * ‖f₁‖ := hC f₁

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §13 (C),
Corollary IV₁, p. 383 (PDF p. 47). Let `‖ ‖` and `‖ ‖₁` be two norms corresponding to the same
(R.K.)-class `F`. There exist two positive constants `m` and `M` such that
`m‖f‖ ≤ ‖f‖₁ ≤ M‖f‖` for `f ∈ F`. The two norms are those of RKHSs `H` and `H₁` with the same
class of functions. -/
theorem equivalent_norms_same_class {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (heq : Set.range (fun f₁ : H₁ => ⇑f₁) = Set.range (fun f : H => ⇑f)) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ (f : H) (f₁ : H₁), ⇑f = ⇑f₁ → m * ‖f‖ ≤ ‖f₁‖ ∧ ‖f₁‖ ≤ M * ‖f‖ := by
  obtain ⟨M₁, hM₁, h1⟩ := normBoundAux (X := X) (H := H) (H₁ := H₁)
    (by rw [heq])
  obtain ⟨M₂, hM₂, h2⟩ := normBoundAux (X := X) (H := H₁) (H₁ := H)
    (show Set.range (fun f : H => ⇑f) ⊆ Set.range (fun f₁ : H₁ => ⇑f₁) by
      rw [← heq])
  refine ⟨1 / M₁, M₂, div_pos (by norm_num) hM₁, hM₂, ?_⟩
  intro f f₁ hf
  have e1 := h1 f₁ f hf
  have e2 := h2 f f₁ hf.symm
  constructor
  · rw [one_div, inv_mul_eq_div]
    exact (div_le_iff₀' hM₁).mpr e1
  · exact e2

end AronszajnRK.Inclusion

/-- Solution entry point. -/
theorem solution {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (heq : Set.range (fun f₁ : H₁ => ⇑f₁) = Set.range (fun f : H => ⇑f)) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ (f : H) (f₁ : H₁), ⇑f = ⇑f₁ → m * ‖f‖ ≤ ‖f₁‖ ∧ ‖f₁‖ ≤ M * ‖f‖ :=
  AronszajnRK.Inclusion.equivalent_norms_same_class heq
