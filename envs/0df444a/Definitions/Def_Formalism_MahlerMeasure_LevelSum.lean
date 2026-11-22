-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_LevelSum
-- name    : Formalism_MahlerMeasure_LevelSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:24:23.037207+00:00
-- url     : https://prove2.me/theorems/bb9a751b-f258-4b98-b90c-13036701ecc2
-- title:
--   Level Sum
-- statement:
--   Definitions and structural lemmas for Level Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/LevelSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open MvPolynomial Finset
def qch (a j : ℕ) : ℚ := (a.choose j : ℚ)
def LevelSum : Prop :=
  ∀ (A z l : ℕ), z + l ≤ A →
    ∑ j ∈ range (l + 1), (-1 : ℚ) ^ j * qch l j * qch (A - z - l) j / qch A j = qch (z + l) l / qch A l
noncomputable def tieE {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  LinearMap.mulLeft k (∑ c, X (w c) * X (e c))
noncomputable def tieF {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ c, (pderiv (w c)).toLinearMap ∘ₗ (pderiv (e c)).toLinearMap
noncomputable def tiePhi {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (o n z : ℕ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ j ∈ range (o + 1),
    (((-1 : k) ^ j) / (((j.factorial : k) ^ 2) * ((o + n + r + z - 1).choose j : k))) •
      (((tieE w e) ^ j).comp ((tieF w e) ^ j))
def BiHom {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (a b : ℕ) (u : MvPolynomial σ k) : Prop :=
  ∀ m ∈ u.support, (∑ c, m (w c)) = a ∧ (∑ c, m (e c)) = b
def LevelAct : Prop :=
  ∀ (k σ : Type) [Field k] [CharZero k] (r : ℕ) (w e : Fin r → σ), Function.Injective w →
    Function.Injective e → (∀ c d, w c ≠ e d) → 1 ≤ r →
    ∀ (o n z l : ℕ) (u : MvPolynomial σ k), l ≤ o → l ≤ n → tieF w e u = 0 → BiHom w e (o - l) (n - l) u →
      tiePhi w e o n z ((tieE w e ^ l) u) =
        (((z + l).choose l : k) / ((o + n + r + z - 1).choose l : k)) • ((tieE w e ^ l) u)
end Formalism.GM


