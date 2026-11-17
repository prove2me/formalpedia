-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_append
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:54.87372+00:00
-- url     : https://prove2.me/submissions/eea7033e-7098-422f-ae7a-589ed2e2ec68

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- Two systems of sections of isomorphic modules can be appended after transporting
the second system. Each original standard chart lies in the corresponding appended chart. -/
theorem _root_.solution {K : Type} [Field K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂)
    (e : M₁ ≅ M₂)
    (ι : Fin (N₁ + N₂ + 1 + 1) ≃ (Fin (N₁ + 1) ⊕ Fin (N₂ + 1))) :
    ∃ Q : M₁.ProjPresentation f (N₁ + N₂ + 1),
      (∀ k, Q.σ k = Sum.elim P₁.σ (fun j => e.inv.app ⊤ (P₂.σ j)) (ι k)) ∧
      (∀ i, P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) ≤
        Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (ι.symm (Sum.inl i)))) ∧
      (∀ j, P₂.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j) ≤
        Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (ι.symm (Sum.inr j)))) := by
  classical
  let σ : Fin (N₁ + N₂ + 1 + 1) → Γ(M₁, ⊤) :=
    fun k => Sum.elim P₁.σ (fun j => e.inv.app ⊤ (P₂.σ j)) (ι k)
  let U : Fin (N₁ + N₂ + 1 + 1) → X.Opens := fun k =>
    Sum.elim (fun i => P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i))
      (fun j => P₂.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (ι k)
  have hcover : iSup U = ⊤ := by
    have hc : (⨆ i : Fin (N₁ + 1),
        P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup,
        Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X K N₁)]
      rfl
    apply top_le_iff.mp
    intro x hx
    have hx' : x ∈ (⨆ i : Fin (N₁ + 1),
        P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ι.symm (Sum.inl i), by simpa [U] using hi⟩
  have hframe : ∀ k (V : X.Opens), V ≤ U k →
      Function.Bijective fun g : Γ(X, V) =>
        g • (M₁.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ k) : Γ(M₁, V)) := by
    intro k V hV
    cases hk : ι k with
    | inl i =>
        simpa only [σ, U, hk, Sum.elim_inl] using P₁.frame i V (by simpa [U, hk] using hV)
    | inr j =>
        have nat : M₁.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
            (e.inv.app ⊤ (P₂.σ j)) =
            e.inv.app V (M₂.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (P₂.σ j)) := by
          have hn := (e.inv.mapPresheaf).naturality (homOfLE (le_top : V ≤ ⊤)).op
          exact (congrFun (congrArg
            (fun t => (ConcreteCategory.hom t : Γ(M₂, ⊤) → Γ(M₁, V))) hn) (P₂.σ j)).symm
        have hb : Function.Bijective (e.inv.app V : Γ(M₂, V) → Γ(M₁, V)) := by
          refine Function.bijective_iff_has_inverse.mpr ⟨e.hom.app V, ?_, ?_⟩
          · intro x
            change (e.inv.app V ≫ e.hom.app V) x = x
            rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]
            rfl
          · intro y
            change (e.hom.app V ≫ e.inv.app V) y = y
            rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
            rfl
        have hf := hb.comp (P₂.frame j V (by simpa [U, hk] using hV))
        change Function.Bijective (fun g : Γ(X, V) => e.inv.app V
          (g • M₂.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (P₂.σ j))) at hf
        simpa only [σ, hk, Sum.elim_inr, nat, Function.comp_apply,
          Scheme.Modules.Hom.app_smul] using hf
  obtain ⟨Q, hσ, hU⟩ := Scheme.Modules.exists_projPresentation_of_iSup_eq_top
    f M₁ (N₁ + N₂ + 1) σ U hcover hframe
  refine ⟨Q, fun k => congrFun hσ k, ?_, ?_⟩
  · intro i
    simpa [U] using hU (ι.symm (Sum.inl i))
  · intro j
    simpa [U] using hU (ι.symm (Sum.inr j))

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
