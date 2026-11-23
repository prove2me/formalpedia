-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:59:58.519276+00:00
-- url     : https://prove2.me/theorems/8fdc6cc1-f8ea-4d02-95f3-80180abd3250
-- title:
--   Lift Tuple A
-- statement:
--   Definitions and structural lemmas for Lift Tuple A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleA.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGL.LTA
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
def upd {m r : ℕ} (ρ : Fin m → Fin r) (S : Finset (Fin m)) (a : Fin r) : Fin m → Fin r :=
  fun p => if p ∈ S then a else ρ p
def gmin {r c m : ℕ} (ρ : Fin m → Fin r) (κ : Fin m → Fin c) : MvPolynomial (Fin r × Fin c) ℤ :=
  (Matrix.of fun p q : Fin m => (X (ρ p, κ q) : MvPolynomial (Fin r × Fin c) ℤ)).det
def Exp {r c n m : ℕ} (e : Fin n → Fin r) (G : (Fin m → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) : Prop :=
  ∀ (a b : Fin n) (ρ : Fin m → Fin n), rowGen ℤ (e a) (e b) (G ρ) =
    ∑ S : Finset (Fin m), if (∀ p ∈ S, ρ p = b) then
      Polynomial.X ^ S.card * Polynomial.C (G (upd ρ S a)) else 0
def liftR {r n m : ℕ} (e : Fin n → Fin r) (z : Fin r) (ρ : Fin m → Fin n) : Fin (m + 1) → Fin r :=
  fun p => if hp : p.1 < m then e (ρ ⟨p.1, hp⟩) else z
def tmat {n K : ℕ} (sz : Fin K → ℕ) (a b : Fin n) (t : ℕ) (I : ∀ k, Fin (sz k) → Fin n) :
    (∀ k, Fin (sz k) → Fin n) →₀ ℤ :=
  ∑ F : (∀ k, Finset (Fin (sz k))), if (∀ k, ∀ p ∈ F k, I k p = b) ∧ ∑ k, (F k).card = t then
    Finsupp.single (fun k => upd (I k) (F k) a) 1 else 0
def tlin {n K : ℕ} (sz : Fin K → ℕ) (a b : Fin n) (t : ℕ) :
    ((∀ k, Fin (sz k) → Fin n) →₀ ℤ) →ₗ[ℤ] ((∀ k, Fin (sz k) → Fin n) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (tmat sz a b t)
def twd {n K : ℕ} (sz : Fin K → ℕ) : List (Fin n × Fin n × ℕ) →
    (((∀ k, Fin (sz k) → Fin n) →₀ ℤ) →ₗ[ℤ] ((∀ k, Fin (sz k) → Fin n) →₀ ℤ))
  | [] => LinearMap.id
  | x :: w => (tlin sz x.1 x.2.1 x.2.2).comp (twd sz w)
end PI.WGL.LTA


