-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GenericGradient
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GenericGradient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:48.36844+00:00
-- url     : https://prove2.me/theorems/4e2f0648-ad65-47ac-8b57-f5033ceaa42e
-- title:
--   Generic Gradient
-- statement:
--   Definitions and structural lemmas for Generic Gradient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/GenericGradient.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qf34.genericGradient :
    {n : ℕ} →
      (J : Ideal (MvPolynomial (Fin n) ℂ)) → MvPolynomial (Fin n) ℂ → Fin n → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J) :=
    fun {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) (l : Fin n) ↦
      (Algebra.algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) :
          MvPolynomial (Fin n) ℂ ⧸ J → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
        ((Ideal.Quotient.mk J : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ ⧸ J)
          ((MvPolynomial.pderiv l : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ) f))
noncomputable def UpperTheory.Reformulated.B.Qf34.Statement :
    Prop :=
    ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] (ι : Type) [Fintype ι] (f : ι → MvPolynomial (Fin n) ℂ),
      (∀ (i : ι), f i ∈ J) →
        Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (Set.range (UpperTheory.Reformulated.B.Qf34.genericGradient J ∘ f)) =
            Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
              (UpperTheory.Reformulated.B.Qf34.genericGradient J '' (↑J : Set (MvPolynomial (Fin n) ℂ))) →
          ∃ s ∉ J, ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)


