-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_AffineBCSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_AffineBCSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:20.40781+00:00
-- url     : https://prove2.me/theorems/821bb926-f118-4440-9730-79791a777297
-- title:
--   Affine BCSt
-- statement:
--   Definitions and structural lemmas for Affine BCSt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/AffineBCSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
def AffineBCSt : Prop :=
  ∀ {G B G' B' : Scheme.{0}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B} {b : B' ⟶ B},
    IsPullback g q' q b → IsAffineHom q → ∀ {X : Type} [AddCommMonoid X]
    {V : B.Opens}, IsAffineOpen V → ∀ {V' : B'.Opens}, IsAffineOpen V' →
    V' ≤ b ⁻¹ᵁ V → ∀ (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V))
    (φ : Multiplicative X →* Γ(G, q ⁻¹ᵁ V)) (φ' : Multiplicative X →* Γ(G', q' ⁻¹ᵁ V')),
    (∀ x, φ' x = g.appLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG (φ x)) →
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.app V).hom φ (fun _ _ => Commute.all _ _)) →
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q'.app V').hom φ' (fun _ _ => Commute.all _ _))
def GlueSt : Prop :=
  ∀ {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
    (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V))),
    (∀ (V₁ V₂ : B.Opens) (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂) (x : Multiplicative X),
      φ V₁ h₁ x = (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (φ V₂ h₂ x)) →
    (∀ x ∈ W, ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, x ∈ V₀ ∧ ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀),
      IsAffineOpen V₁ → Function.Bijective
        (AddMonoidAlgebra.liftNCRingHom (q.app V₁).hom (φ V₁ (h₁.trans hV₀)) (fun _ _ => Commute.all _ _))) →
    ∀ (V : B.Opens), IsAffineOpen V → ∀ (h : V ≤ W),
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.app V).hom (φ V h) (fun _ _ => Commute.all _ _))
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf


