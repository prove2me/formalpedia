-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TotalDegreeLinear
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TotalDegreeLinear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:10.156418+00:00
-- url     : https://prove2.me/theorems/a03d7803-9207-44cc-8508-bb3e37ca6269
-- title:
--   Total Degree Linear
-- statement:
--   Definitions and structural lemmas for Total Degree Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TotalDegreeLinear.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.TotalDegreeLinear.PV :
    Type → Type → Type → Type :=
    fun (ι A B : Type) ↦ MvPolynomial (ι × A ⊕ ι × B) ℂ
noncomputable def UpperTheory.Reformulated.B.TotalDegreeLinear.sub :
    {ι A B : Type} → [Fintype ι] → Matrix ι ι ℂ → Matrix ι ι ℂ → UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B →ₐ[ℂ] UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B :=
    fun {ι A B : Type} [Fintype ι] (g h : Matrix ι ι ℂ) ↦
      MvPolynomial.aeval
        (Sum.elim
          (fun (x : ι × A) ↦
            ∑ j : ι, (MvPolynomial.C : ℂ → MvPolynomial (ι × A ⊕ ι × B) ℂ) (g x.1 j) * MvPolynomial.X (Sum.inl (j, x.2)))
          fun (y : ι × B) ↦
          ∑ j : ι, (MvPolynomial.C : ℂ → MvPolynomial (ι × A ⊕ ι × B) ℂ) (h y.1 j) * MvPolynomial.X (Sum.inr (j, y.2)))


