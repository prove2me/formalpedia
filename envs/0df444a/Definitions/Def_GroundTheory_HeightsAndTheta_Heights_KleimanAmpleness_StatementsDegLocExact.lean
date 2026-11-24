-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:37.731452+00:00
-- url     : https://prove2.me/theorems/ccf745aa-4def-46ed-9c3c-81426c2cd427
-- title:
--   Statements Deg Loc Exact
-- statement:
--   Definitions and structural lemmas for Statements Deg Loc Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsDegLocExact.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v
def DegLocExact.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M' M M'' : Type v)
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M''] [Module (Poly S N) M''] [Module S M''] [IsScalarTower S (Poly S N) M'']
    (𝓜' : GradedPMod S N M') (𝓜 : GradedPMod S N M) (𝓜'' : GradedPMod S N M'')
    (f : GradedHom 𝓜' 𝓜) (g : GradedHom 𝓜 𝓜''),
    Function.Injective f.toLin → Function.Surjective g.toLin → Function.Exact f.toLin g.toLin →
    ∀ (c : ℤ) (I : StdCell N),
      (∀ z ∈ degLoc 𝓜 c I, locMap g.toLin I.1 z = 0 →
        ∃ z' ∈ degLoc 𝓜' c I, locMap f.toLin I.1 z' = z) ∧
      (∀ z'' ∈ degLoc 𝓜'' c I, ∃ z ∈ degLoc 𝓜 c I, locMap g.toLin I.1 z = z'')
end
end GroundTheory.Heights₂.Heights.Kleiman


