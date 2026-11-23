-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FunctionalEquationSeries_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FunctionalEquationSeries_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:00.12272+00:00
-- url     : https://prove2.me/theorems/642950b1-039f-41a5-913f-d86a41215376
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FunctionalEquationSeries/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FunEqAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical MvPowerSeries
namespace PI.FunEqAllProof
open PI.FunEqAll
abbrev Var (d : ℕ) := Fin 3 × ZMod d
def phi (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* ℂ_[l] :=
  (algebraMap ℚ_[l] ℂ_[l]).comp PadicInt.Coe.ringHom
def Sr (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] := (phi l).range
def zv (l d : ℕ) [Fact l.Prime] (A : ZMod d → MvPowerSeries (Var d) ℂ_[l]) (s : ZMod d) :
    MvPowerSeries (Var d) ℂ_[l] :=
  fun n => ∑ e ∈ Finset.range (JetTdeg n + 1),
    ((l : ℂ_[l]) ^ e)⁻¹ * coeff n (A (s - 2 * (e : ZMod d)) ^ ((l ^ 2) ^ e))
def Xv (l d : ℕ) [Fact l.Prime] (c : Fin 3) : ZMod d → MvPowerSeries (Var d) ℂ_[l] :=
  fun k => X (c, k)
def StepSubst : Prop := ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (A : ZMod d → MvPowerSeries (Var d) ℂ_[l]),
  (∀ k, constantCoeff (A k) = 0) →
    ∀ s, MvPowerSeries.subst (fun k : ZMod d × Unit => A k.1) (zL l d s) = zv l d A s
def StepW : Prop := ∀ (l : ℕ) [Fact l.Prime] (a : ℤ_[l]), InW (phi l a)
def StepExist : Prop := ∀ (l d : ℕ) [Fact l.Prime] [NeZero d],
  ∃ Fg : ZMod d → MvPowerSeries (Var d) ℂ_[l], (∀ s, constantCoeff (Fg s) = 0) ∧
    ∀ s, zv l d Fg s = zv l d (Xv l d 0) s + zv l d (Xv l d 1) s
def StepKey : Prop := ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (G : ZMod d → MvPowerSeries (Var d) ℤ_[l]),
  (∀ k, constantCoeff (G k) = 0) → ∀ s n,
    coeff n (zv l d (fun k => map (phi l) (G k)) s) - (l : ℂ_[l])⁻¹ *
      coeff n (expand (l ^ 2) (pow_ne_zero 2 (Fact.out : l.Prime).ne_zero)
        (zv l d (fun k => map (phi l) (G k)) (s - 2))) ∈ Sr l
def StepInt : Prop := ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (Fg : ZMod d → MvPowerSeries (Var d) ℂ_[l]),
  (∀ s, constantCoeff (Fg s) = 0) →
    (∀ s, zv l d Fg s = zv l d (Xv l d 0) s + zv l d (Xv l d 1) s) →
      ∀ s n, coeff n (Fg s) ∈ Sr l
end PI.FunEqAllProof


