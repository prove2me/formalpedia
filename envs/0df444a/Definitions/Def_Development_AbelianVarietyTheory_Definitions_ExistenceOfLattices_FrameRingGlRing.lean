-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing
-- name    : Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:52.057664+00:00
-- url     : https://prove2.me/theorems/0df93112-73e0-41d6-97af-211e3bf72b2f
-- title:
--   Frame Ring Gl Ring
-- statement:
--   Definitions and structural lemmas for Frame Ring Gl Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/FrameRingGlRing.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Frames.Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
section Ring
variable {K : Type} [Field K] {J : Type} (m : J → ℕ) (R : Type) [CommRing R] [Algebra K R]
abbrev Var : Type := (Σ τ : J, Fin (m τ) × Fin (m τ)) ⊕ J ⊕ Bool
def genMat (τ : J) : Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Var m) R) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inl ⟨τ, i, j⟩)
def rel : Ideal (MvPolynomial (Var m) R) :=
  Ideal.span (Set.range (fun τ : J => (genMat m R τ).det * MvPolynomial.X (Sum.inr (Sum.inl τ)) - 1) ∪
    {MvPolynomial.X (Sum.inr (Sum.inr true)) * MvPolynomial.X (Sum.inr (Sum.inr false)) - 1})
abbrev GlRing : Type := MvPolynomial (Var m) R ⧸ rel m R
def glπ : R →ₐ[K] GlRing m R := (Ideal.Quotient.mkₐ K (rel m R)).comp (IsScalarTower.toAlgHom K R _)
def glX (τ : J) : Matrix (Fin (m τ)) (Fin (m τ)) (GlRing m R) := (genMat m R τ).map (Ideal.Quotient.mk (rel m R))
theorem unit_rel : Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inr true))) *
    Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inr false))) = 1 := by
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (rel m R)), Ideal.Quotient.eq]
  unfold rel
  exact Ideal.subset_span (Set.mem_union_right _ rfl)
def glS : (GlRing m R)ˣ := Units.mkOfMulEqOne _ _ (unit_rel m R)
variable {m R}
end Ring
section Geo
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
end Geo
end GlobalTheory.Frames.Model


