-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:17.182929+00:00
-- url     : https://prove2.me/theorems/5e10fa3d-da1e-48d4-ab1b-7aa2f79cd726
-- title:
--   Fintype Col Choice
-- statement:
--   Definitions and structural lemmas for Fintype Col Choice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/FintypeColChoice.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
namespace PI.WwMainW
open PI.WwMain PI.WwMain.KM
instance finiteOE (p n : ℕ) : Finite (Fin p ↪o Fin n) :=
  Finite.of_injective (fun e : Fin p ↪o Fin n => (e : Fin p → Fin n))
    (fun _ _ h => DFunLike.coe_injective h)
instance fintypeOE (p n : ℕ) : Fintype (Fin p ↪o Fin n) := Fintype.ofFinite _
instance fintypeColChoice {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram) :
    Fintype (ColChoice N nu) :=
  inferInstanceAs (Fintype (∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N))
def CBSorted : Prop :=
  ∀ (R : Type) [CommRing R] (p n : ℕ) (A : Matrix (Fin p) (Fin n) R) (B : Matrix (Fin n) (Fin p) R),
    (A * B).det = ∑ J : Fin p ↪o Fin n, (A.submatrix id J).det * (B.submatrix J id).det
def chi {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (z : Lt × Fin N0 × Fin N1 → ℂ_[l]) :
    MvPolynomial (XZ Lt N0 N1) ℤ →+* MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  eval₂Hom ((C : ℂ_[l] →+* MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]).comp (Int.castRingHom ℂ_[l]))
    (Sum.elim X (fun w => C (z w)))
def Hpol {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))
    (G : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l] :=
  ∑ μ ∈ G.support, monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).2
    (((coeff μ G : ℤ) : ℂ_[l]) * ph (monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1 1))
def wt {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (α : (Lt × Fin N0 × Fin N1) →₀ ℕ) : ℂ_[l] :=
  (α.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff α Th
def Lfun {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l]) : ℂ_[l] :=
  ∑ α ∈ P.support, coeff α P * wt l N0 N1 Th α
def EvalH : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))
    (G : MvPolynomial (XZ Lt N0 N1) ℤ) (z : Lt × Fin N0 × Fin N1 → ℂ_[l]),
    eval z (Hpol l N0 N1 ph G) = ph (chi l N0 N1 z G)
def LH : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))
    (G : MvPolynomial (XZ Lt N0 N1) ℤ),
    Lfun l N0 N1 Th (Hpol l N0 N1 ph G) = ph (applyAt0 N0 N1 l Th G)
def LLin : Prop :=
  ∀ (Lt : Type) (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]),
    (∀ p q, Lfun l N0 N1 Th (p + q) = Lfun l N0 N1 Th p + Lfun l N0 N1 Th q) ∧
    Lfun l N0 N1 Th 0 = 0 ∧
    (∀ c p, Lfun l N0 N1 Th (C c * p) = c * Lfun l N0 N1 Th p)
def DeXCB : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (nu : Lt → YoungDiagram)
    (z : Lt × Fin N0 × Fin N1 → ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]),
    DeX N0 nu (fun s a j => ∑ b : Fin N1, z (s, a, b) * y' s b j) =
      ∑ I : ColChoice N1 nu, C (minY N1 nu I y') * chi l N0 N1 z (Gxz N0 N1 nu I)
end PI.WwMainW


