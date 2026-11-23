-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
-- name    : Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:50.348734+00:00
-- url     : https://prove2.me/theorems/96059baa-e959-4ef4-970a-4e0aafaa153c
-- title:
--   Branching Bound Last Graded One Row
-- statement:
--   Definitions and structural lemmas for Branching Bound Last Graded One Row, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/BranchingBoundLastGradedOneRow.lean

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
def LemmaDLastGradedAt (l p q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + p) → ℤ) : Prop :=
  ∀ (i' : ℤ) (eL : ℕ),
    (∀ μ2 : Fin q → ℕ, depth2 ξ (blockWtLast p q w lam2) (blockWtLast p q w μ2) ≤ i' → ExpLe l q lam2 μ2 eL) →
    ∀ (i : ℕ) (μ : Fin (q + p) → ℕ), IsDepthLast p q w μ i → depth2 ξ (blockWtLast p q w lam2) μ ≤ i' →
      ExpLe l (q + p) (blockWtLast p q w lam2) μ
        (eL + padicValInt l (Dn p (M - w) i fun b : Fin q => M - lam2 (Fin.rev b)))
def LemmaDLastGraded : Prop :=
  ∀ (l p q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + p) → ℤ), l.Prime → Antitone lam2 →
    (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) → Antitone ξ → LemmaDLastGradedAt l p q w M lam2 ξ
def BranchingBoundLastGradedOneRow : Prop :=
  ∀ (l q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + 1) → ℤ), l.Prime → Antitone lam2 →
    (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) → Antitone ξ → LemmaDLastGradedAt l 1 q w M lam2 ξ
def LastGradedImpliesLast : Prop := LemmaDLastGraded → LemmaDLast
def OneRowBoundOfLastGraded : Prop := LemmaDLastGraded → BranchingBoundLastGradedOneRow
def Depth2Levi : Prop :=
  ∀ (p q w : ℕ) (lam2 μ2 : Fin q → ℕ) (ξ : Fin (q + p) → ℤ),
    depth2 ξ (blockWtLast p q w lam2) (blockWtLast p q w μ2) =
      ∑ b : Fin q, ξ (Fin.castAdd p b) * ((lam2 b : ℤ) - (μ2 b : ℤ))
def DepthLastIff : Prop :=
  ∀ (p q w i : ℕ) (lam2 : Fin q → ℕ) (μ : Fin (q + p) → ℕ), ∑ a, μ a = ∑ a, blockWtLast p q w lam2 a →
    (IsDepthLast p q w μ i ↔
      depth2 (fun a : Fin (q + p) => if a.val < q then 1 else 0) (blockWtLast p q w lam2) μ = (i : ℤ))
def Depth2Dual : Prop :=
  ∀ (r M : ℕ) (ξ : Fin r → ℤ) (lam μ : Fin r → ℕ), (∀ a, lam a ≤ M) → (∀ a, μ a ≤ M) →
    depth2 (fun a => -ξ (Fin.rev a)) (fun a => M - lam (Fin.rev a)) (fun a => M - μ (Fin.rev a)) = depth2 ξ lam μ ∧
      (Antitone ξ → Antitone fun a => -ξ (Fin.rev a))
def DnShift : Prop :=
  ∀ (p w i q c : ℕ) (lam2 : Fin q → ℕ), (∀ b, lam2 b ≤ w) →
    Dn p (w + c) i (fun b => lam2 b + c) = Dn p w i lam2
def DnLastIndep : Prop :=
  ∀ (p w i q M M' : ℕ) (lam2 : Fin q → ℕ), w ≤ M → (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) → M ≤ M' →
    Dn p (M' - w) i (fun b : Fin q => M' - lam2 (Fin.rev b)) = Dn p (M - w) i (fun b : Fin q => M - lam2 (Fin.rev b))
def LemmaDLastGraded_rank2 : Prop :=
  ∀ (l w y M : ℕ) (ξ : Fin (1 + 1) → ℤ), l.Prime → w ≤ y → y ≤ M → Antitone ξ →
    LemmaDLastGradedAt l 1 1 w M (fun _ : Fin 1 => y) ξ
def PeelBoundLast : Prop :=
  BranchingBoundLastGradedOneRow → ∀ (l q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + 1) → ℤ), l.Prime → Antitone lam2 →
    (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) → Antitone ξ →
    ∀ (i' : ℤ) (eL : ℕ),
      (∀ μ2 : Fin q → ℕ, depth2 ξ (blockWtLast 1 q w lam2) (blockWtLast 1 q w μ2) ≤ i' → ExpLe l q lam2 μ2 eL) →
      ∀ μ : Fin (q + 1) → ℕ, depth2 ξ (blockWtLast 1 q w lam2) μ ≤ i' →
        ExpLe l (q + 1) (blockWtLast 1 q w lam2) μ (eL + (M + q - w - 1) / (l - 1))
def res {α : Type} (r : ℕ) (f : ℕ → α) : Fin r → α := fun a => f a.val
def varpi (c : ℕ) : ℕ → ℤ := fun a => if a < c then 1 else 0
def ExpUpTo (l r : ℕ) (lam : ℕ → ℕ) (ξ : ℕ → ℤ) (I : ℤ) (e : ℕ) : Prop :=
  ∀ μ : Fin r → ℕ, depth2 (res r ξ) (res r lam) μ ≤ I → ExpLe l r (res r lam) μ e
def PeelRows : Prop :=
  BranchingBoundLastGradedOneRow → ∀ (l n s h : ℕ) (lam : ℕ → ℕ) (ξ : ℕ → ℤ), l.Prime →
    (∀ a b, a ≤ b → b < n + s → lam b ≤ lam a) → lam 0 + (n + s) ≤ h + lam (n + s - 1) + 1 → Antitone ξ →
    ∀ (I : ℤ) (e : ℕ), ExpUpTo l n lam ξ I e → ExpUpTo l (n + s) lam ξ I (e + s * ((h - 1) / (l - 1)))
def blockCost (l n t I : ℕ) (lam : ℕ → ℕ) : ℕ :=
  (Finset.range (I + 1)).sup fun i =>
    padicValInt l (Dn t (lam 0 - lam n) i fun b : Fin n => lam 0 - res n lam (Fin.rev b))
def BlockStep : Prop :=
  LemmaDLast → ∀ (l n t : ℕ) (lam : ℕ → ℕ), l.Prime → 1 ≤ t →
    (∀ a b, a ≤ b → b < n + t → lam b ≤ lam a) → (∀ a, n ≤ a → a < n + t → lam a = lam n) →
    ∀ eL : ℕ, (∀ μ2 : Fin n → ℕ, ExpLe l n (res n lam) μ2 eL) →
      ∀ I : ℕ, ExpUpTo l (n + t) lam (varpi n) (I : ℤ) (eL + blockCost l n t I lam)
def ApplicationSteps : Prop :=
  LemmaDLastGraded → ∀ (l k j t q h : ℕ) (lam : ℕ → ℕ), l.Prime → 1 ≤ t →
    (∀ a b, a ≤ b → b < k + j + t + q → lam b ≤ lam a) →
    (∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)) →
    lam 0 + (k + j + t + q) ≤ h + lam (k + j + t + q - 1) + 1 →
    ∀ ecl : ℕ, (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
      ∀ I : ℕ, ExpUpTo l (k + j + t + q) lam (varpi (k + j)) (I : ℤ)
        (q * ((h - 1) / (l - 1)) + blockCost l (k + j) t I lam + j * ((h - 1) / (l - 1)) + ecl)
end Formalism.CohomologicalDescent.LD


