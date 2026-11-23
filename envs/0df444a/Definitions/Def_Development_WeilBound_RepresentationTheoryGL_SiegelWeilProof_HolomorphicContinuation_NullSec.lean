-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:28.67528+00:00
-- url     : https://prove2.me/theorems/080abffb-b630-4f65-9954-cbcb9bca292a
-- title:
--   Null Sec
-- statement:
--   Definitions and structural lemmas for Null Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/NullSec.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_IsSingTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
namespace PositivityTheory.Rg.Sw
variable {m n : ℕ}
abbrev PX (m n : ℕ) := MvPolynomial (Fin m × Fin n × Bool) ℂ
def evX (P : PX m n) (x : Fin m → Fin n → ℂ) : ℂ :=
  MvPolynomial.eval (fun k => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1) P
def gs (c : ℝ) (x : Fin m → Fin n → ℂ) : ℂ := Complex.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ))
def sgn (ε : Fin m → Bool) (a : Fin m) : ℂ := if ε a then 1 else -1
def Qb (ε : Fin m → Bool) (b : Bool) (i j : Fin n) : PX m n :=
  ∑ a ∈ Finset.univ.filter (fun a => ε a = b), X (a, i, true) * X (a, j, false)
def Qp (ε : Fin m → Bool) (i j : Fin n) : PX m n := Qb ε true i j - Qb ε false i j
def mom (c : ℝ) (P : PX m n) : ℂ := ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x
def NullSec (ε : Fin m → Bool) (c : ℝ) (P : PX m n) : Prop :=
  ∀ R ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n)), mom c (R * P) = 0
def hOp (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (P : PX m n) : PX m n :=
  ∑ i, (X (b, i, false) * pderiv (a, i, false) P - C (sgn ε a * sgn ε b) * X (a, i, true) * pderiv (b, i, true) P -
    C ((c : ℂ) * (1 - sgn ε a * sgn ε b)) * X (b, i, false) * X (a, i, true) * P)
def FFT : Prop :=
  ∀ (ι A B : Type) [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B] (p : MvPolynomial ((ι × A) ⊕ (ι × B)) ℂ),
    (∀ u ∈ Matrix.unitaryGroup ι ℂ, MvPolynomial.aeval (Sum.elim
        (fun x : ι × A => ∑ j, C (u x.1 j) * (X (Sum.inl (j, x.2)) : MvPolynomial ((ι × A) ⊕ (ι × B)) ℂ))
        (fun y : ι × B => ∑ j, C (star (u y.1 j)) * X (Sum.inr (j, y.2)))) p = p) →
    p ∈ Algebra.adjoin ℂ (Set.range fun ab : A × B =>
      ∑ i, (X (Sum.inl (i, ab.1)) : MvPolynomial ((ι × A) ⊕ (ι × B)) ℂ) * X (Sum.inr (i, ab.2)))
def Cyc : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ P : PX m n,
    ∃ R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)), NullSec ε c (P - R)
def LC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ lam : PX m n →ₗ[ℂ] ℂ, (∀ a b P, lam (hOp ε c a b P) = 0) →
    ∀ P, NullSec ε c P → lam P = 0
def gramX (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j => evX (Qp ε i j) x
def secN (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (b : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)
def NullIff : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → t ≠ 0 → ∀ P : PX m n,
    NullSec ε c P ↔ ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian → secN ε c t P b = 0
end PositivityTheory.Rg.Sw


