-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularDens
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularDens
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:45.792464+00:00
-- url     : https://prove2.me/theorems/2b241dda-c3f5-49e3-a390-6c702315825b
-- title:
--   Statements Proj Regular Dens
-- statement:
--   Definitions and structural lemmas for Statements Proj Regular Dens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsProjRegularDens.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
def ProjRegularDens.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (V : Set R.X) (BV : FinHolAtlas n V),
    (∀ j, IsSmoothHerm (L j)) → HoloMap BV R.A Subtype.val → IsClosed V →
    (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ j, ∀ᵐ u, u ∈ (BV.chart j).target → (BV.chart j).symm u ∉ projRegular R Ψ BV →
      locDens BV (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val) j u = 0
end GroundTheory.Heights₂.Heights.Targets


