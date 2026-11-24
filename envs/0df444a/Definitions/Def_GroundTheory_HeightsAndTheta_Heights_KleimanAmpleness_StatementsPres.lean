-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:17.488215+00:00
-- url     : https://prove2.me/theorems/3e0806fd-ab18-4382-a354-a165228b0f37
-- title:
--   Statements Pres
-- statement:
--   Definitions and structural lemmas for Statements Pres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsPres.lean

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
universe u v w
def GradedPres.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type (max u v))
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module (Poly S N) F) (_ : Module S F)
      (_ : IsScalarTower S (Poly S N) F) (K : Type (max u v)) (_ : AddCommGroup K)
      (_ : Module (Poly S N) K) (_ : Module S K) (_ : IsScalarTower S (Poly S N) K)
      (𝓕 : GradedPMod S N F) (𝓚 : GradedPMod S N K) (r : ℕ) (b : Module.Basis (Fin r) (Poly S N) F)
      (d : Fin r → ℤ) (f : GradedHom 𝓚 𝓕) (g : GradedHom 𝓕 𝓜),
      (∀ j, b j ∈ 𝓕.piece (d j)) ∧ Module.Finite (Poly S N) K ∧ Function.Injective f.toLin ∧
        Function.Surjective g.toLin ∧ Function.Exact f.toLin g.toLin
def GradedULift.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M),
    ∃ (M' : Type (max u v)) (_ : AddCommGroup M') (_ : Module (Poly S N) M') (_ : Module S M')
      (_ : IsScalarTower S (Poly S N) M') (𝓜' : GradedPMod S N M') (f : GradedHom 𝓜 𝓜')
      (g : GradedHom 𝓜' 𝓜), Function.LeftInverse g.toLin f.toLin ∧ Function.RightInverse g.toLin f.toLin
def CohomRetract.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M : Type v) (M' : Type w)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S N M') (f : GradedHom 𝓜 𝓜') (g : GradedHom 𝓜' 𝓜),
    Function.LeftInverse g.toLin f.toLin → ∀ (i : ℕ) (c : ℤ), Function.Injective (cohomMap f i c)
section Hypotheses
variable (k : Type u) [Field k] (N : ℕ)
end Hypotheses
end
end GroundTheory.Heights₂.Heights.Kleiman


