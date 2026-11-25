-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsSt
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsSt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:11:44.738967+00:00
-- url     : https://prove2.me/theorems/f7073880-8653-4e66-ba0b-95fe87901615
-- title:
--   Max Cusps St
-- statement:
--   Definitions and structural lemmas for Max Cusps St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsSt.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.QAt
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
def hq (χ : Matrix (Fin ρ) (Fin ρ) E) (η : Fin ρ → E) : E :=
  ∑ a, ∑ b, η a * χ a b * cc (η b)
def IsExpoFD (X : Data E r) (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) : Prop :=
  IsHermE χ ∧ ∀ k, ∃ z : ℤ, phZ X cu χ k = z
def KilledFD (X : Data E r) (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) (c : ℝ) : Prop :=
  ∃ η : Fin ρ → E, η ≠ 0 ∧ (∑ a, η a • cu.e a) ∈ X.Λ ∧ ∑ τ : X.Ψ, (τ.1 (hq χ η)).re ≤ c
def MaxCuspsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r),
    (∀ ξ, X.IsIso ξ → ∃ cu : CuspFD X ρ, ξ ∈ Submodule.span E (Set.range cu.e)) →
    (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) →
    ∀ (la : Wt X.Ψ r),
    (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ,
      (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) →
    ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
      (P ∈ X.SSgt la c ↔
        ∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c →
          ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0)
end Formalism.L2.Pj.QAt


