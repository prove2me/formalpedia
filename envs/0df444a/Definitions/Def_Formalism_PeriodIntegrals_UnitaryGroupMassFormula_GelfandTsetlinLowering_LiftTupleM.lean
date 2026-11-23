-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:59:46.51305+00:00
-- url     : https://prove2.me/theorems/e1c42e43-ac9b-42fe-8b87-9f0533e335e2
-- title:
--   Lift Tuple M
-- statement:
--   Definitions and structural lemmas for Lift Tuple M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleM.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGL.LTM
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
def liftRows {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) : Fin (m + 1) → Fin N :=
  fun p => if hp : p.1 < m then eRow h (ρ ⟨p.1, hp⟩) else ⟨N - 1, by omega⟩
def unl {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N) :
    MvPolynomial (Fin N × Fin N) ℤ :=
  initMinor ℤ (eRow h ∘ ρ) hm
def lif {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N) :
    MvPolynomial (Fin N × Fin N) ℤ :=
  initMinor ℤ (liftRows h ρ) hm
def C0 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : MvPolynomial (Fin N × Fin N) ℤ :=
  ∏ i : Fin n, (if i.1 + 1 = n then (lpMinor ℤ (r := N) (n := N) (i.1 + 1) (by omega) (by omega)) ^ (aa h lam sg i).toNat
      else 1) *
    (if i.1 = 0 then (initMinor ℤ (n := N) (rowsZ h i) (by omega)) ^ (bb h lam sg i).toNat else 1)
def Mlift {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n) : MvPolynomial (Fin N × Fin N) ℤ :=
  C0 h lam sg * ∏ k : Fin K,
    if k ∈ L then lif h (I k) (by have := hsz k; omega) else unl h (I k) (by have := hsz k; omega)
def GoodL {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (L : Finset (Fin K)) : Prop :=
  (∀ k ∈ L, 0 < sz k) ∧
  ∀ i : Fin n, (Finset.univ.filter fun k => k ∈ L ∧ sz k = i.1).card = if i.1 = 0 then 0 else (bb h lam sg i).toNat
def stdT {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) : ∀ k, Fin (sz k) → Fin n :=
  fun k p => ⟨p.1, lt_of_lt_of_le p.2 (hsz k)⟩
def TopPart : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n), shapeDeg sz = sg.natW →
    ∀ L : Finset (Fin K), GoodL h lam sg sz L →
      (∀ J, tupCnt J = sg.natW →
        ∃ ε : ℤ, bideterminant ℤ sz hsz J = ε • extremal ℤ n sg ∧ Mlift h lam sg sz hsz L J = ε • xi ℤ h lam sg) ∧
      tupCnt (stdT sz hsz) = sg.natW ∧ bideterminant ℤ sz hsz (stdT sz hsz) = extremal ℤ n sg ∧
        Mlift h lam sg sz hsz L (stdT sz hsz) = xi ℤ h lam sg
end PI.WGL.LTM


