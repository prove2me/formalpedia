-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
-- name    : Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:54.309886+00:00
-- url     : https://prove2.me/theorems/0c3173a9-5083-4eab-8834-8e9e5282ca54
-- title:
--   Characteristic From Ranks
-- statement:
--   Definitions and structural lemmas for Characteristic From Ranks, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
namespace CharacteristicFromRanks
variable {C : Type} [Field C]
def pT {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    (G : ∀ g, Cart V d (I g) (J g)) (g : Fin 2) (b : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => (G g).ty (Sum.inl c) = b).card
def CHProp {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (G : ∀ g, Cart V d (I g) (J g)) (n j j' : ℕ) (big : Fin 2 → ZMod d → Prop) : Prop :=
  ∀ g a, big g a → ∀ u : Fin n → I g → C, IsSat V u →
    (∀ c x, (G g).ty (Sum.inl x) ≠ a → u c x = 0) →
    ∃ y : Fin n → I g → C, (∀ ρ x, V.Ge 0 (y ρ x)) ∧
      (∀ (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
        ∀ ρ, upG g (mvExp (∑ x : I g, y ρ x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
          IntGerm V t) ∧
      ((Even d ∧ ∀ a : ZMod d, (big 0 a ↔ Even a.val)) →
        V.v (Matrix.of fun ρ c : Fin n => ∑ x, y ρ x * u c x).det ≤
          (((n : ℝ) * gam V.l + ((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ a, big g a) →
        V.v (Matrix.of fun ρ c : Fin n => ∑ x, y ρ x * u c x).det ≤
          ((((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ))
example {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) : CHProp X.G X.n X.j X.j' X.big := X.CH
def intR (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' {_ _} ha hb := VF.Ge.mul_int (V := V) ha hb
  one_mem' := VF.Ge.one (V := V)
  add_mem' {_ _} ha hb := VF.Ge.add (V := V) ha hb
  zero_mem' := VF.Ge.zero (V := V) 0
  neg_mem' {_} ha := VF.Ge.neg (V := V) ha
def vR (V : VF C) : AddValuation (intR V) (WithTop ℝ) := V.v.comap (intR V).subtype
def upB (l rp rm : ℕ) (w : ℝ) : ℝ := ((rp : ℝ) - rm) * w + (rm : ℝ) / ((l : ℝ) - 1)
end CharacteristicFromRanks
end Formalism.L2.FormalSeriesBounds


