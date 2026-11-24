-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
-- name    : Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:12.44399+00:00
-- url     : https://prove2.me/theorems/c4ebc6e4-ca94-428b-b44a-af4382c6b755
-- title:
--   Qi Core Defs
-- statement:
--   Definitions and structural lemmas for Qi Core Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiCoreDefs.lean

import Mathlib
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
open TensorProduct
namespace PositivityTheory.PrwZar.Qi
variable {K H : Type} [Field K] [CommRing H] [Algebra K H]
def pw (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : ℕ → (H →ₐ[K] H)
  | 0 => (Algebra.ofId K H).comp ε
  | n + 1 => (Algebra.TensorProduct.lmul' K).comp ((Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H)).comp Δ)
def CounitL (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : Prop :=
  (Algebra.TensorProduct.lmul' K).comp
    ((Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H)).comp Δ) = AlgHom.id K H
def CounitR (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : Prop :=
  (Algebra.TensorProduct.lmul' K).comp
    ((Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε)).comp Δ) = AlgHom.id K H
def KilledCore : Prop :=
  ∀ (K H : Type) [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K), CounitL Δ ε → CounitR Δ ε →
    (∀ a b : ℕ, pw Δ ε (a * b) = (pw Δ ε a).comp (pw Δ ε b)) →
    (∃ m : ℕ, 0 < m ∧ ∀ x : H →ₐ[K] K, x.comp (pw Δ ε m) = ε) →
    ∃ N : ℕ, 0 < N ∧ pw Δ ε N = pw Δ ε 0
end PositivityTheory.PrwZar.Qi


