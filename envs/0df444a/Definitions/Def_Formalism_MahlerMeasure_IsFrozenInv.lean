-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
-- name    : Formalism_MahlerMeasure_IsFrozenInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:11:36.393255+00:00
-- url     : https://prove2.me/theorems/a26e3d95-f53d-41da-80d7-7d86e75183a9
-- title:
--   Is Frozen Inv
-- statement:
--   Definitions and structural lemmas for Is Frozen Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/IsFrozenInv.lean

import Definitions.Def_Formalism_MahlerMeasure_GoodCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.M
open MvPolynomial Finset
def Letters.snoc {N : ℕ} (LL : Letters N) (n : ℕ) : Letters (N + 1) where
  vec := Fin.lastCases false LL.vec
  deg := Fin.lastCases n LL.deg
def Letters.total {N : ℕ} (LL : Letters N) : ℕ := ∑ i, LL.deg i
noncomputable def freezeSub (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) :
    Fin N × Fin r → MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] :=
  fun ⟨i, c⟩ =>
    if LL.vec i then
      (if c = ρ then ∑ c', X (Fin.castSucc i, c') * X (Fin.last N, c')
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c))
    else
      (if c = ρ then X (Fin.last N, ρ) * X (Fin.castSucc i, ρ)
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c) - X (Fin.castSucc i, ρ) * X (Fin.last N, c))
noncomputable def freeze (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] :=
  X (Fin.last N, ρ) ^ (n - LL.total) * aeval (freezeSub p LL ρ) f
def IsFrozenInv (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (n : ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) : Prop :=
  ∀ c, c ≠ ρ → glAct p (LL.snoc n) (N + 1) c ρ F = 0
def FreezeInto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (n : ℕ), LL.total ≤ n →
    ∀ f ∈ Pol p r LL,
      freeze p LL ρ n f ∈ Pol p r (LL.snoc n) ∧ IsFrozenInv p LL ρ n (freeze p LL ρ n f) ∧
      (f ∈ IntPol p (Fin N × Fin r) → freeze p LL ρ n f ∈ IntPol p (Fin (N + 1) × Fin r))
def FreezeBij : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (n : ℕ), LL.total ≤ n →
    (∀ f ∈ Pol p r LL, ∀ g ∈ Pol p r LL, freeze p LL ρ n f = freeze p LL ρ n g → f = g) ∧
    (∀ F ∈ PolZ p r (LL.snoc n), IsFrozenInv p LL ρ n F → ∃ f ∈ PolZ p r LL, freeze p LL ρ n f = F)
def FreezeY : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Letters N) (ρ : Fin r) (n : ℕ) {q : ℕ}
    (J : Fin q → ℕ) (Mt : Fin q → WithTop ℤ), LL.total ≤ n → (∀ k, J k ≤ N) →
    ∀ f ∈ Pol p r LL, (f ∈ Y p LL J Mt ↔ freeze p LL ρ n f ∈ Y p (LL.snoc n) J Mt)
def FreezeStep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (n : ℕ), LL.total ≤ n →
    ∀ f : MvPolynomial (Fin N × Fin r) ℚ_[p],
      X (Fin.last N, ρ) * freeze p LL ρ n f = freeze p LL ρ (n + 1) f
end Formalism.GM.M


