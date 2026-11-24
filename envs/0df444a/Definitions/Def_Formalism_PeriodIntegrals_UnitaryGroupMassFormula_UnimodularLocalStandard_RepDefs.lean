-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:32:35.475385+00:00
-- url     : https://prove2.me/theorems/16d6886f-7153-4c54-8014-88ba267f52b1
-- title:
--   Rep Defs
-- statement:
--   Definitions and structural lemmas for Rep Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
def fvec {m : Type} [DecidableEq m] (a : ℕ) (b : ℤ) (d : ℕ) (lam : ℂ) (x y : ℤ) (i₀ : m) : m → ℂ :=
  Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d))
def KeyHyps (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) : Prop :=
  CmOK a b c d ∧ IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ ∧ (∀ z ∈ Λ, cmTheta b d • z ∈ Λ) ∧
  relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0 ∧ relIdx Λ (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 ∧
  l.Prime ∧ ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 ∧ i₀ ∉ T ∧
  (∀ j ∈ T, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d))))
def ApproxAt (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (k : ℕ) (w : m → ℂ) : Prop :=
  SatMem l Λ w ∧ (∀ j ∈ T, w j = 0) ∧ ∃ p q : ℤ, ¬ (l : ℤ) ∣ q ∧
    stdH (cmL a b d ha hd lam hlam) m w w =
      stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀) * (1 + (l : ℂ) ^ k * p / q)
def KeyStart : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → ∃ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ 1 w
def KeyNewton : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → ∀ k, 1 ≤ k → ∀ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ k w → ∃ w', ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ (2 * k) w'
def KeyExact : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → ∃ K₀ : ℕ, ∀ k, K₀ ≤ k → ∀ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ k w →
    ∃ v : m → ℂ, SatMem l Λ v ∧ (∀ j ∈ T, v j = 0) ∧
      stdH (cmL a b d ha hd lam hlam) m v v =
        stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀)
end PI.UnitaryGroupMassFormula.UnimodLocStd


