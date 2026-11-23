-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:28.616726+00:00
-- url     : https://prove2.me/theorems/13faa784-ce98-4323-8474-47f08236c81c
-- title:
--   Zn Nonneg
-- statement:
--   Definitions and structural lemmas for Zn Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/ZnNonneg.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
noncomputable section
def FjDiff (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ),
    X.IsBddSec la P → X.IsIso ξ → DifferentiableOn ℂ (X.fj la ξ ν P) X.dom
def FjBEq (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ),
    X.IsSec la P → X.IsIso ξ → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      X.fj la ξ ν P (rmul x b) = bchar la b * X.fj la ξ ν P x
def FjBdd (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ),
    X.IsBddSec la P → X.IsIso ξ → ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la (X.fj la ξ ν P) x ≤ C
def OrthoDom (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), X.IsOrtho x → x ∈ X.dom
def UnitDom (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r),
    X.IsUnitaryC n → x ∈ X.dom → X.lmulC n x ∈ X.dom
def BorFlag (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x b : Frame X.Ψ r), b ∈ Bor X.Ψ r → rmul x b ∈ X.dom →
    X.SameFlag x (rmul x b)
def ZnSmul (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (t : ℂ) (Z : X.Coord), X.zN (t • Z) = ‖t‖ * X.zN Z
def ZnNonneg (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Z : X.Coord), 0 ≤ X.zN Z
def NfacPos (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r), x ∈ X.dom → 0 < X.nfac la x
def XZZero (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), X.xZ x 0 = x
end
end PIW.FdPA


