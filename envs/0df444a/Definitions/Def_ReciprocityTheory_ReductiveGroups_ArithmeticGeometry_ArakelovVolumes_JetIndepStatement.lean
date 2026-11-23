-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetIndepStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetIndepStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:13.747366+00:00
-- url     : https://prove2.me/theorems/8086fb34-2d3c-4d8d-b633-50dfdcf72746
-- title:
--   Jet Indep Statement
-- statement:
--   Definitions and structural lemmas for Jet Indep Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/JetIndepStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR
def multiLt (D a : ℕ) : Finset (Fin D → ℕ) :=
  (Finset.range a).biUnion (fun d => Finset.Nat.antidiagonalTuple D d)
def JetIndepStatement.{u, v, w} : Prop :=
  ∀ (K : Type u) (A : Type v) (H : Type w) [Field K] [CommRing A] [Algebra K A]
    [AddCommGroup H] [Module A H] [Module K H] [IsScalarTower K A H]
    (J : Ideal A) (D a0 T δ : ℕ) (s : Fin D → A) (w0 : A) (t : Fin δ → H),
    (∀ k, s k ∈ J) →
    (∀ a < a0, ∀ h : (Fin D → ℕ) → H,
      (∑ α ∈ Finset.Nat.antidiagonalTuple D a, (∏ k, s k ^ α k) • h α) ∈ (J ^ (a + 1)) • (⊤ : Submodule A H) →
      ∀ α ∈ Finset.Nat.antidiagonalTuple D a, h α ∈ J • (⊤ : Submodule A H)) →
    (∃ u : A, u * w0 - 1 ∈ J) →
    (∀ c : Fin δ → K, (∑ i, c i • t i) ∈ J • (⊤ : Submodule A H) → c = 0) →
    ∀ c : (Fin D → ℕ) → Fin δ → K,
      (∑ α ∈ multiLt D a0, ∑ i, c α i • (((∏ k, s k ^ α k) * w0 ^ (T - ∑ k, α k)) • t i)) ∈
          (J ^ a0) • (⊤ : Submodule A H) →
      ∀ α ∈ multiLt D a0, ∀ i, c α i = 0
end ReciprocityTheory.ChartRestriction.G.AR


