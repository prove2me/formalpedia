-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
-- name    : Formalism_BranchSandwichDivisors_StatementW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:09.253114+00:00
-- url     : https://prove2.me/theorems/fc64d182-0965-4df5-aebc-b50890766b5f
-- title:
--   Statement W
-- statement:
--   Definitions and structural lemmas for Statement W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/StatementW.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
noncomputable section
namespace Formalism.BranchingDeterminantCap
def extM (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun a b => if h : a.val < n ∧ b.val < n then g ⟨a.val, h.1⟩ ⟨b.val, h.2⟩
    else if a = b then 1 else 0
def rowsA {n : ℕ} (i : Fin n) : Fin (i.val + 1) → Fin (n + 1) := fun p => ⟨p.val, by omega⟩
def rowsB {n : ℕ} (i : Fin n) : Fin (i.val + 1) → Fin (n + 1) :=
  fun p => if p.val < i.val then ⟨p.val, by omega⟩ else Fin.last n
def xiB (R : Type*) [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) :
    MvPolynomial (Fin (n + 1) × Fin n) R :=
  ∏ i : Fin n, (initMinor R (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) *
    initMinor R (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i))
def lamZ {n : ℕ} (lam : Fin n → ℕ) : Fin (n + 1) → ℤ :=
  fun a => if h : a.val < n then (lam ⟨a.val, h⟩ : ℤ) else 0
def weylProd {n : ℕ} (nu : Fin (n + 1) → ℤ) : ℝ :=
  ∏ p ∈ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun p => p.1 < p.2),
    (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
      (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ))
def BranchMap : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (lam sg : Fin n → ℕ),
    Interlace (lamZ lam) (fun i => (sg i : ℤ)) →
    ∃ io : ↥(dualWeyl R n n sg) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R,
      (∀ f, io f ∈ dualWeyl R (n + 1) n lam) ∧
      (∀ (g : Matrix (Fin n) (Fin n) R) (f f' : ↥(dualWeyl R n n sg)),
        (f' : MvPolynomial (Fin n × Fin n) R) = rowAct R g (f : MvPolynomial (Fin n × Fin n) R) →
          io f' = rowAct R (extM R g) (io f)) ∧
      (∀ h : ↥(dualWeyl R n n sg), (h : MvPolynomial (Fin n × Fin n) R) = hw R le_rfl sg →
        io h = ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • xiB R lam sg) ∧
      (∀ f, ∀ m ∈ (io f).support, rowDeg m (Fin.last n) = ∑ i, (lam i - sg i))
def BranchIsometry : Prop :=
  ∀ (n : ℕ) (sg : Fin n → ℕ), Antitone sg →
    ∀ io : ↥(dualWeyl ℂ n n sg) →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin n) ℂ,
      (∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : ↥(dualWeyl ℂ n n sg)),
        (f' : MvPolynomial (Fin n × Fin n) ℂ) = rowAct ℂ g (f : MvPolynomial (Fin n × Fin n) ℂ) →
          io f' = rowAct ℂ (extM ℂ g) (io f)) →
      ∀ f h : ↥(dualWeyl ℂ n n sg), (h : MvPolynomial (Fin n × Fin n) ℂ) = hw ℂ le_rfl sg →
        fockF (io f) (io f) * fockF (h : MvPolynomial (Fin n × Fin n) ℂ) h =
          fockF (io h) (io h) * fockF (f : MvPolynomial (Fin n × Fin n) ℂ) f
def zScale (n : ℕ) (t : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal fun a => if a = Fin.last n then (t : ℂ) else 1
def BranchScale : Prop :=
  ∀ (n k d : ℕ) (t : ℝ) (F : MvPolynomial (Fin (n + 1) × Fin k) ℂ),
    (∀ m ∈ F.support, rowDeg m (Fin.last n) = d) →
      rowAct ℂ (zScale n t) F = ((t : ℂ) ^ d) • F ∧
      fockF (rowAct ℂ (zScale n t) F) (rowAct ℂ (zScale n t) F) = ((t : ℂ) ^ (2 * d)) * fockF F F
def BranchNormT : Prop :=
  ∀ (n : ℕ) (lam sg : Fin n → ℕ) (t : ℝ), Interlace (lamZ lam) (fun i => (sg i : ℤ)) →
    ∀ io : ↥(dualWeyl ℂ n n sg) →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin n) ℂ,
      (∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : ↥(dualWeyl ℂ n n sg)),
        (f' : MvPolynomial (Fin n × Fin n) ℂ) = rowAct ℂ g (f : MvPolynomial (Fin n × Fin n) ℂ) →
          io f' = rowAct ℂ (extM ℂ g) (io f)) →
      (∀ h : ↥(dualWeyl ℂ n n sg), (h : MvPolynomial (Fin n × Fin n) ℂ) = hw ℂ le_rfl sg →
        io h = ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : ℂ) • xiB ℂ lam sg) →
      (∀ f, ∀ m ∈ (io f).support, rowDeg m (Fin.last n) = ∑ i, (lam i - sg i)) →
      rowAct ℂ (zScale n t) (hw ℂ (Nat.le_succ n) lam) = hw ℂ (Nat.le_succ n) lam ∧
      ∀ f : ↥(dualWeyl ℂ n n sg),
        fockF (rowAct ℂ (zScale n t) (io f)) (rowAct ℂ (zScale n t) (io f)) *
            fockF (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) =
          ((t : ℂ) ^ (2 * ∑ i, (lam i - sg i))) *
            (((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : ℂ) ^ 2) *
            fockF (xiB ℂ lam sg) (xiB ℂ lam sg) * fockF (f : MvPolynomial (Fin n × Fin n) ℂ) f
def XiNorm : Prop :=
  ∀ (n : ℕ) (lam sg : Fin n → ℕ), Interlace (lamZ lam) (fun i => (sg i : ℤ)) →
    (fockF (xiB ℂ lam sg) (xiB ℂ lam sg)).re ≤
      weylProd (lamZ lam) * (fockF (hw ℂ (Nat.le_succ n) lam) (hw ℂ (Nat.le_succ n) lam)).re
end Formalism.BranchingDeterminantCap


