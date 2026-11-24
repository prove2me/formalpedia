-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagConeAlg
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagConeAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:02.510357+00:00
-- url     : https://prove2.me/theorems/5d1f1603-3d35-4e20-a0f2-d12497e11bce
-- title:
--   Statements Segre Flag Cone Alg
-- statement:
--   Definitions and structural lemmas for Statements Segre Flag Cone Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsSegreFlagConeAlg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def SegreFlagConeAlg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, 1 ≤ k → ∀ hkN : k ≤ N,
    ∃ (l : Fin k → Fin M) (m' : Fin M'),
      LinearIndependent Ω (fun i : Fin k => fun j : Fin k => φ (l i) (w (Fin.castLE hkN j))) ∧
      flagClosurePt y w e φ φ' t k ⟨none, m'⟩ ≠ 0 ∧
      ∀ p : Σ o, bundleIdx (bundleIdx ι M) M' o,
        IsAlgebraic
          (Algebra.adjoin O
            (Set.range (fun q : Σ k, ι k =>
                (C (algebraMap Ω Φ (y q)) * X (some (some q.1)) : MvPolynomial (Option (Option K)) Φ)) ∪
              Set.range (Sum.elim
                (fun i : Fin k => C (flagClosurePt y w e φ φ' t k ⟨some none, l i⟩) * X (some none))
                (fun _ : Unit => C (flagClosurePt y w e φ φ' t k ⟨none, m'⟩) * X none))))
          (C (flagClosurePt y w e φ φ' t k p) * X p.1)
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


