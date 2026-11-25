-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_Places
-- name    : Development_AutomorphicArithmetic_CMTraceForms_Places
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:31:46.848673+00:00
-- url     : https://prove2.me/theorems/dcba8211-56e8-439e-87bb-d85d61a5c083
-- title:
--   Places
-- statement:
--   Definitions and structural lemmas for Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/Places.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
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
namespace UpperTheory.Depth
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def SplitAt (d p : ℕ) : Prop := p = 2 ∨ jacobiSym (-(d : ℤ)) p = 1
def SplitPlaces (p : ℕ) [Fact p.Prime] (H : Host E) (f : ℕ) (vd : ℝ) : Prop :=
  letI := H.starRing
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
    v.Integers O → ∀ [Fact (¬ IsUnit (p : O))] [Algebra ℤ_[p] O] (τO : (E →+* ℂ) → (𝓞 E →+* O)),
    Function.Injective τO → (∀ τ τ', τ (H.rt : E) = τ' (H.rt : E) ↔ τO τ H.rt = τO τ' H.rt) →
    ∃ (s : ℕ) (w : Fin s → Place p (𝓞 E)) (vdi : Fin s → ℝ),
      ∑ i, (w i).n = f ∧ ∑ i, ((w i).n : ℝ) * vdi i = (f : ℝ) * vd ∧
      (∀ i σ, σ ∈ Emb (O := O) (w i).e → ∃ τ, InPsi H τ ∧ σ = τO τ) ∧
      (∀ τ, InPsi H τ → ∃! i, τO τ ∈ Emb (O := O) (w i).e) ∧
      (∀ i σ, σ ∈ Emb (O := O) (w i).bar → ∃ τ, ¬ InPsi H τ ∧ σ = τO τ) ∧
      ∀ i, ∃ t : Fin (w i).n ≃ Emb (O := O) (w i).e, HasVd p v (w i) t (vdi i)
end UpperTheory.Depth
end


