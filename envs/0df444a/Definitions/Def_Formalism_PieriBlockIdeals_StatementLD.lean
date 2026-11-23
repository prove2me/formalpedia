-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
-- name    : Formalism_PieriBlockIdeals_StatementLD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:24.390829+00:00
-- url     : https://prove2.me/theorems/c1d445eb-611a-4f23-9785-c16adf625e56
-- title:
--   Statement LD
-- statement:
--   Definitions and structural lemmas for Statement LD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/StatementLD.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
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
def boxesOfContent {q : ℕ} (lam2 tau : Fin q → ℕ) (c : ℤ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).card
def colLen {q : ℕ} (lam2 tau : Fin q → ℕ) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => lam2 a ≤ j ∧ j < tau a).card
def shapes (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : Finset (Fin q → ℕ) :=
  (Fintype.piFinset fun a : Fin q => Finset.Icc (lam2 a) (lam2 a + i)).filter fun tau =>
    (∀ a b : Fin q, a ≤ b → tau b ≤ tau a) ∧ ∑ a, tau a = ∑ a, lam2 a + i ∧
      (∀ b : Fin q, ∀ j < tau b, colLen lam2 tau j ≤ p) ∧ boxesOfContent lam2 tau (w : ℤ) = 0
def mu (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) (c : ℤ) : ℕ :=
  (shapes p w i lam2).sup fun tau => boxesOfContent lam2 tau c
def Dn (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : ℤ :=
  ∏ k ∈ Finset.range (q + w + i), ((w : ℤ) - ((k : ℤ) - (q : ℤ))) ^ mu p w i lam2 ((k : ℤ) - (q : ℤ))
noncomputable def nablaWt (r : ℕ) (ν μ : Fin r → ℕ) : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ) :=
  dualWeyl ℤ r r ν ⊓ weightedHomogeneousSubmodule ℤ (rowW r r) μ
def KilledAt (l r : ℕ) (ν μ : Fin r → ℕ) (c : ℤ) : Prop :=
  ∀ x ∈ nablaWt r ν μ, ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ (m * c) • x ∈ weyl ℤ r r le_rfl ν
def ExpLe (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) : Prop := KilledAt l r ν μ ((l : ℤ) ^ e)
def blockWt (p q w : ℕ) (κ : Fin q → ℕ) : Fin (p + q) → ℕ := Fin.append (fun _ : Fin p => w) κ
def blockWtLast (p q w : ℕ) (κ : Fin q → ℕ) : Fin (q + p) → ℕ := Fin.append κ (fun _ : Fin p => w)
def IsDepth (p q w : ℕ) (μ : Fin (p + q) → ℕ) (i : ℕ) : Prop :=
  ∑ a : Fin p, μ (Fin.castAdd q a) + i = p * w
def IsDepthLast (p q w : ℕ) (μ : Fin (q + p) → ℕ) (i : ℕ) : Prop :=
  ∑ a : Fin p, μ (Fin.natAdd q a) = p * w + i
def depth2 {r : ℕ} (ξ : Fin r → ℤ) (lam μ : Fin r → ℕ) : ℤ := ∑ a, ξ a * ((lam a : ℤ) - (μ a : ℤ))
def LemmaDAt (l p q w : ℕ) (lam2 : Fin q → ℕ) : Prop :=
  ∀ eL : ℕ, (∀ μ2 : Fin q → ℕ, ExpLe l q lam2 μ2 eL) →
    ∀ (i : ℕ) (μ : Fin (p + q) → ℕ), IsDepth p q w μ i →
      ExpLe l (p + q) (blockWt p q w lam2) μ (eL + padicValInt l (Dn p w i lam2))
def LemmaDGradedAt (l p q w : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (p + q) → ℤ) : Prop :=
  ∀ (i' : ℤ) (eL : ℕ),
    (∀ μ2 : Fin q → ℕ, depth2 ξ (blockWt p q w lam2) (blockWt p q w μ2) ≤ i' → ExpLe l q lam2 μ2 eL) →
    ∀ (i : ℕ) (μ : Fin (p + q) → ℕ), IsDepth p q w μ i → depth2 ξ (blockWt p q w lam2) μ ≤ i' →
      ExpLe l (p + q) (blockWt p q w lam2) μ (eL + padicValInt l (Dn p w i lam2))
def BranchingBoundOneRow : Prop :=
  ∀ (l q w : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, lam2 b ≤ w) → LemmaDAt l 1 q w lam2
def LemmaD : Prop :=
  ∀ (l p q w : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, lam2 b ≤ w) → LemmaDAt l p q w lam2
def LemmaDGraded : Prop :=
  ∀ (l p q w : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (p + q) → ℤ), l.Prime → Antitone lam2 → (∀ b, lam2 b ≤ w) →
    Antitone ξ → LemmaDGradedAt l p q w lam2 ξ
def LemmaDLast : Prop :=
  ∀ (l p q w M : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) →
    ∀ eL : ℕ, (∀ μ2 : Fin q → ℕ, ExpLe l q lam2 μ2 eL) →
      ∀ (i : ℕ) (μ : Fin (q + p) → ℕ), IsDepthLast p q w μ i →
        ExpLe l (q + p) (blockWtLast p q w lam2) μ
          (eL + padicValInt l (Dn p (M - w) i fun b : Fin q => M - lam2 (Fin.rev b)))
def DnNeZero : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ), Dn p w i lam2 ≠ 0
def MuSupport : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), (∀ b, lam2 b ≤ w) → mu p w i lam2 c ≠ 0 →
    -(q : ℤ) ≤ c ∧ c < (w : ℤ) + (i : ℤ)
def ExpLeIffKilled : Prop :=
  ∀ (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) (D : ℤ), l.Prime → D ≠ 0 →
    (ExpLe l r ν μ (e + padicValInt l D) ↔ KilledAt l r ν μ ((l : ℤ) ^ e * D))
def ExpLeMono : Prop :=
  ∀ (l r : ℕ) (ν μ : Fin r → ℕ) (e e' : ℕ), e ≤ e' → ExpLe l r ν μ e → ExpLe l r ν μ e'
def ExpBounded : Prop :=
  ∀ (l r : ℕ) (ν : Fin r → ℕ), l.Prime → Antitone ν → ∃ e : ℕ, ∀ μ : Fin r → ℕ, ExpLe l r ν μ e
def GradedImpliesPlain : Prop := LemmaDGraded → LemmaD
def OneRowOfBound : Prop := LemmaD → BranchingBoundOneRow
def wt2 (w y : ℕ) : Fin 2 → ℕ := ![w, y]
noncomputable def vec2 (w y i : ℕ) : MvPolynomial (Fin 2 × Fin 2) ℤ :=
  X (0, 0) ^ (w - y - i) * X (1, 0) ^ i * (X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0)) ^ y
def Dn2 : Prop :=
  ∀ (p w y i : ℕ), 1 ≤ p → y + i ≤ w →
    Dn p w i (fun _ : Fin 1 => y) = ((i.factorial * (w - y).choose i : ℕ) : ℤ)
def Rank2Exact : Prop :=
  ∀ (w y i : ℕ), y + i ≤ w →
    nablaWt 2 (wt2 w y) (wt2 (w - i) (y + i)) = Submodule.span ℤ {vec2 w y i} ∧ vec2 w y i ≠ 0 ∧
      ∀ c : ℤ, c • vec2 w y i ∈ weyl ℤ 2 2 le_rfl (wt2 w y) ↔ (((w - y).choose i : ℕ) : ℤ) ∣ c
def Rank2Other : Prop :=
  ∀ (w y : ℕ) (μ : Fin 2 → ℕ), y ≤ w → (∀ i : ℕ, y + i ≤ w → μ ≠ wt2 (w - i) (y + i)) →
    nablaWt 2 (wt2 w y) μ = ⊥
def LemmaD_rank2 : Prop :=
  ∀ (l w y : ℕ), l.Prime → y ≤ w → LemmaDAt l 1 1 w (fun _ : Fin 1 => y)
def LemmaDGraded_rank2 : Prop :=
  ∀ (l w y : ℕ) (ξ : Fin (1 + 1) → ℤ), l.Prime → y ≤ w → Antitone ξ →
    LemmaDGradedAt l 1 1 w (fun _ : Fin 1 => y) ξ
def MuLe : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), mu p w i lam2 c ≤ p
def MuRange : Prop :=
  ∀ (p w i q m : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) → mu p w i lam2 c ≠ 0 →
    (m : ℤ) - (q : ℤ) < c ∧ c < (w : ℤ)
def DnPos : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ), (∀ b, lam2 b ≤ w) → 0 < Dn p w i lam2
def DnDvd : Prop :=
  ∀ (p w i q m : ℕ) (lam2 : Fin q → ℕ), (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    Dn p w i lam2 ∣ (((w + q - m - 1).factorial ^ p : ℕ) : ℤ)
def DnVal : Prop :=
  ∀ (l p w i q m : ℕ) (lam2 : Fin q → ℕ), l.Prime → (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    (l - 1) * padicValInt l (Dn p w i lam2) ≤ p * (w + q - m - 1)
def PeelBound : Prop :=
  BranchingBoundOneRow → ∀ (l q w m : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    ∀ eL : ℕ, (∀ μ2 : Fin q → ℕ, ExpLe l q lam2 μ2 eL) →
      ∀ μ : Fin (1 + q) → ℕ, ExpLe l (1 + q) (blockWt 1 q w lam2) μ (eL + (w + q - m - 1) / (l - 1))
def LemmaD_sym : Prop :=
  ∀ (l q w : ℕ), l.Prime → LemmaDAt l 1 q w (fun _ : Fin q => 0)
end Formalism.CohomologicalDescent.LD


