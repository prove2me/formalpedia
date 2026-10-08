-- Prove2me | solution 1 for AronszajnRK.Inclusion.norm_bound_of_subclass
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T00:58:28.980986+00:00
-- url     : https://prove2.me/submissions/796abb03-4c99-471a-8df7-2f3e0bb54070

import Mathlib

open Filter Topology

namespace AronszajnRK.Inclusion

/-! ### Auxiliary: the transfer map between two RKHSs with nested function classes -/

section Transfer

variable {X H H₁ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [RKHS ℂ H X ℂ] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [RKHS ℂ H₁ X ℂ]

/-- If every function of `H₁` is a function of `H`, there is a transfer map `T : H₁ → H`
carrying each `f₁` to the element of `H` with the same function. -/
noncomputable def transfer (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f)) :
    H₁ → H :=
  fun f₁ => Classical.choose (hsub ⟨f₁, rfl⟩)

lemma transfer_apply (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f))
    (f₁ : H₁) (x : X) : (transfer hsub f₁) x = f₁ x :=
  congrFun (Classical.choose_spec (hsub ⟨f₁, rfl⟩)) x

end Transfer

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §13 (C),
Theorem IV, p. 382 (PDF p. 46). Let `F` and `F₁ ⊂ F` be (R.K.)-classes and `‖ ‖`, `‖ ‖₁` some norms
corresponding to `F` and `F₁`. Then there exists a constant `M > 0` such that `‖f‖ ≤ M‖f‖₁` for
`f ∈ F₁`. The norms are those of arbitrary RKHSs `H` and `H₁` with these classes of functions. -/
theorem norm_bound_of_subclass {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f)) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f‖ ≤ M * ‖f₁‖ := by
  classical
  -- pointwise behaviour of the transfer map
  have key : ∀ (f₁ : H₁) (x : X), (transfer hsub f₁) x = f₁ x := transfer_apply hsub
  have addval : ∀ (f g : H₁) (x : X), ((f + g : H₁)) x = f x + g x := by
    intro f g x
    simpa using congrFun (RKHS.coe_add f g) x
  have smulval : ∀ (c : ℂ) (f : H₁) (x : X), ((c • f : H₁)) x = c * f x := by
    intro c f x
    simpa [Pi.smul_apply] using congrFun (RKHS.coe_smul f c) x
  -- the transfer map is linear
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
  -- the graph of the transfer map is sequentially closed, because point evaluations are
  -- continuous on both sides
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

end AronszajnRK.Inclusion

/-- Solution entry point. -/
theorem solution {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f)) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f‖ ≤ M * ‖f₁‖ :=
  AronszajnRK.Inclusion.norm_bound_of_subclass hsub
