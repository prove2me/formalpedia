-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_L2SquaredNorms
-- name    : Development_AbelianVarietyTheory_BlockTheory_HeightDefect_L2SquaredNorms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:19.911838+00:00
-- url     : https://prove2.me/theorems/333682e1-5cc8-4346-81e6-7cb64b73f01b
-- title:
--   L2 Squared Norms
-- statement:
--   Definitions and structural lemmas for L2 Squared Norms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/L2SquaredNorms.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
section Norms
variable {K₁ : Type} [Field K₁]
def hermSq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : ℝ :=
  (z ⬝ᵥ Hm.mulVec (star z)).re
def IsL2SquareIntegralProblem (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (rig : LB.Gen (P.L.pull (eSec P.A))) (σ : K₁ →+* ℂ)
    (s : P.L.Sec) (v : ℝ) : Prop :=
  rig.IsGen ∧
  ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ : A'.left ⟶ P.A.left) (u : HolUnif A' (P.L.pull φ) P.g)
    (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (Fd : Set (Fin P.g → ℂ)),
    IsGrpPullback A' P.A (spMap σ) φ ∧ u.IsAH Hm χ ∧
    (∀ i : P.L.ι, ⊤ ≤ (P.L.pull (eSec P.A)).U (fun _ => i) →
      u.fr (fun _ => i) 0 =
        σ (valR (A := K₁) (𝟙 (Sp K₁)) ((P.L.pull (eSec P.A)).U (fun _ => i)) (rig.s (fun _ => i)).val)) ∧
    (∀ (i : P.L.ι) (z : Fin P.g → ℂ), ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ P.L.U i →
      valAt' ((u.ex z).left ≫ φ) (P.L.U i) (s.f i) = θ z * u.fr (fun _ => i) z) ∧
    IsAddFundamentalDomain u.Λ Fd volume ∧ volume Fd ≠ 0 ∧ volume Fd ≠ ⊤ ∧
    IntegrableOn (fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z)) Fd volume ∧
    v = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z)) / (volume Fd).toReal
def IsLogNormPiH (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (σ : K₁ →+* ℂ) (t : epsR K₁ ⟶ P.A) (v : ℝ) : Prop :=
  IsTangent t ∧
  ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ : A'.left ⟶ P.A.left) (u : HolUnif A' (P.L.pull φ) P.g)
    (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (t' : epsR ℂ ⟶ A') (w : Fin P.g → ℂ),
    IsGrpPullback A' P.A (spMap σ) φ ∧ u.IsAH Hm χ ∧
    t'.left ≫ φ = spMap (dualMap σ) ≫ t.left ∧ u.IsDiff w t' ∧ w ≠ 0 ∧
    v = Real.log (Real.sqrt (Real.pi * hermSq Hm w))
end Norms
section Line
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
def valLineLogNorm (n : ℤ) (mu : ArcLt Dw →₀ ℕ) (thSq : ℝ) (ℓ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log thSq - mu.sum fun x m => (m : ℝ) * ℓ x.1 x.2.2
variable {K₁ : Type} [Field K₁]
def IsLetterLogNorm (A₁ A₂ : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (σ : K₁ →+* ℂ) :
    Option ((epsR K₁ ⟶ A₁.A) ⊕ (epsR K₁ ⟶ A₂.A)) → ℝ → Prop
  | none, v => v = 0
  | some (.inl t), v => IsLogNormPiH A₁ σ t v
  | some (.inr t), v => IsLogNormPiH A₂ σ t v
def IsValLineLogNorm (B : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (rig : LB.Gen (B.L.pull (eSec B.A))) (th : B.L.Sec)
    (A₁ A₂ : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁))
    (src : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Option ((epsR K₁ ⟶ A₁.A) ⊕ (epsR K₁ ⟶ A₂.A)))
    (n : ℤ) (mu : ArcLt Dw →₀ ℕ) (σ : K₁ →+* ℂ) (a : ℝ) : Prop :=
  ∃ (thSq : ℝ) (ℓ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ), 0 < thSq ∧ IsL2SquareIntegralProblem B rig σ th thSq ∧
    (∀ τ k, IsLetterLogNorm A₁ A₂ σ (src τ k) (ℓ τ k)) ∧ a = valLineLogNorm n mu thSq ℓ
def IsValLineLogNormAt (B : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (rig : LB.Gen (B.L.pull (eSec B.A))) (th : B.L.Sec)
    (A₁ A₂ : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁))
    (src : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Option ((epsR K₁ ⟶ A₁.A) ⊕ (epsR K₁ ⟶ A₂.A)))
    (n : ℤ) (mu : ArcLt Dw →₀ ℕ) (w : InfinitePlace K₁) (a : ℝ) : Prop :=
  ∃ σ : K₁ →+* ℂ, InfinitePlace.mk σ = w ∧ IsValLineLogNorm B rig th A₁ A₂ src n mu σ a
example (ℓ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ) (c : ℝ) :
    valLineLogNorm (Dw := Dw) 2 0 (Real.exp c) ℓ = -c := by
  simp [valLineLogNorm]
example (ℓ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ) (n : ℤ) (x : ArcLt Dw) (m : ℕ) :
    valLineLogNorm n (Finsupp.single x m) 1 ℓ = -(m * ℓ x.1 x.2.2) := by
  simp [valLineLogNorm]
end Line
end GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms


