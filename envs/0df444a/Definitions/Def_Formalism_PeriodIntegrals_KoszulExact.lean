-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_KoszulExact
-- name    : Formalism_PeriodIntegrals_KoszulExact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:25.6656+00:00
-- url     : https://prove2.me/theorems/37d55c55-e39a-4188-ba5c-c971f09e64a9
-- title:
--   Koszul Exact
-- statement:
--   Definitions and structural lemmas for Koszul Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/KoszulExact.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.KoszulExact
def form {R : Type*} [CommRing R] {D : ℕ} (s : Fin D → R) : Module.Dual R (Fin D → R) :=
  ∑ i, s i • (LinearMap.proj i : (Fin D → R) →ₗ[R] R)
def dK {R : Type*} [CommRing R] {D : ℕ} (s : Fin D → R) :
    ExteriorAlgebra R (Fin D → R) →ₗ[R] ExteriorAlgebra R (Fin D → R) :=
  CliffordAlgebra.contractLeft (form s)
end PI.KoszulExact
namespace PI
def KoszulExact.{u} : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
      (∀ (j : ℕ) (x : ExteriorAlgebra R (Fin D → R)), x ∈ ⋀[R]^(j + 1) (Fin D → R) →
          KoszulExact.dK s x = 0 → ∃ y ∈ ⋀[R]^(j + 2) (Fin D → R), KoszulExact.dK s y = x) ∧
      (∀ r : R, (∃ y ∈ ⋀[R]^1 (Fin D → R), KoszulExact.dK s y = algebraMap R _ r) ↔
          r ∈ Ideal.span (Set.range s))
end PI


