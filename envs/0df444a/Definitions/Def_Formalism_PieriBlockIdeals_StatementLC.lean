-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_StatementLC
-- name    : Formalism_PieriBlockIdeals_StatementLC
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:39:29.579826+00:00
-- url     : https://prove2.me/theorems/e3a6fb46-b4f2-49a3-b764-5f0dff93bcd0
-- title:
--   Statement LC
-- statement:
--   Definitions and structural lemmas for Statement LC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/StatementLC.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaDSkeletonUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.CohomologicalDescent.LC
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
def colSeq {q n : ℕ} (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q) (j : Fin n) : ℕ := κ j.val (ρ j)
def cseq {q n : ℕ} (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q) (j : Fin n) : ℤ :=
  (κ j.val (ρ j) : ℤ) - ((ρ j).val : ℤ)
def IsContentSeq {q n : ℕ} (lam2 : Fin q → ℕ) (c : Fin n → ℤ) : Prop :=
  ∃ (tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ ∧ cseq κ ρ = c
def IsWt (K : Type*) {P M : Type*} {q n : ℕ} [Field K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (lam2 : Fin q → ℕ) (c : Fin n → ℤ) (z : Tens (Fin q) P M n) : Prop :=
  Cas K EM 0 z = ((casVal lam2 : ℤ) : K) • z ∧ ∀ j : Fin n, xJM K EM j z = ((c j : ℤ) : K) • z
def meas {n : ℕ} (col : Fin n → ℕ) : ℕ := ∑ l : Fin n, (n - l.val) * col l
def ContentInj : Prop :=
  ∀ (q : ℕ) (κ : Fin q → ℕ), Antitone κ → ∀ a b : Fin q,
    ((κ a : ℤ) - (a.val : ℤ) = (κ b : ℤ) - (b.val : ℤ) → a = b) ∧
      (casVal (κ + Pi.single a 1) = casVal (κ + Pi.single b 1) → a = b)
def PathDet : Prop :=
  ∀ (q n : ℕ) (lam2 tau tau' : Fin q → ℕ) (κ κ' : ℕ → Fin q → ℕ) (ρ ρ' : Fin n → Fin q),
    IsPath n lam2 tau κ ρ → IsPath n lam2 tau' κ' ρ' →
    (∀ m ≤ n, (∀ j : Fin n, j.val < m → cseq κ ρ j = cseq κ' ρ' j) → ∀ l ≤ m, κ l = κ' l) ∧
      ((∀ j ≤ n, casVal (κ j) = casVal (κ' j)) → (∀ j ≤ n, κ j = κ' j) ∧ ρ = ρ' ∧ tau = tau')
def SwapPath : Prop :=
  ∀ (q n : ℕ) (lam2 tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ →
    ∀ (j : Fin n) (hj : j.val + 1 < n), colSeq κ ρ ⟨j.val + 1, hj⟩ < colSeq κ ρ j →
    2 ≤ cseq κ ρ j - cseq κ ρ ⟨j.val + 1, hj⟩ ∧
      ∃ κ' : ℕ → Fin q → ℕ, IsPath n lam2 tau κ' (ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩) ∧
        cseq κ' (ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩) = cseq κ ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩ ∧
        colSeq κ' (ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩) = colSeq κ ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩
def SameCol : Prop :=
  ∀ (q n : ℕ) (lam2 tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ →
    ∀ (j : Fin n) (hj : j.val + 1 < n), colSeq κ ρ ⟨j.val + 1, hj⟩ = colSeq κ ρ j →
    cseq κ ρ ⟨j.val + 1, hj⟩ = cseq κ ρ j - 1 ∧
      ¬ IsContentSeq lam2 (cseq κ ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩)
def MeasSwap : Prop :=
  ∀ (n : ℕ) (col : Fin n → ℕ) (j : Fin n) (hj : j.val + 1 < n), col ⟨j.val + 1, hj⟩ < col j →
    meas (col ∘ Equiv.swap j ⟨j.val + 1, hj⟩) < meas col
def MonoRun : Prop :=
  ∀ (q n : ℕ) (lam2 tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ →
    (∀ (j : Fin n) (hj : j.val + 1 < n), colSeq κ ρ j ≤ colSeq κ ρ ⟨j.val + 1, hj⟩) →
    ∀ p j0 : ℕ, p < LD.colLen lam2 tau j0 →
    ∃ i : ℕ, i + p < n ∧ ∀ l : Fin n, i ≤ l.val → l.val ≤ i + p → colSeq κ ρ l = j0
def WtIff : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q),
    κ 0 = lam2 → (∀ j : Fin n, κ (j.val + 1) = κ j.val + Pi.single (ρ j) 1) → ∀ z : Tens (Fin q) P M n,
    ((∀ j ≤ n, Cas K EM j z = ((casVal (κ j) : ℤ) : K) • z) ↔ IsWt K EM lam2 (cseq κ ρ) z)
def CasFromX : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ) (c : Fin n → ℤ) (z : Tens (Fin q) P M n),
    IsWt K EM lam2 c z → ∀ l ≤ n, Cas K EM l z =
      ((casVal lam2 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), (2 * c i + (q : ℤ)) : ℤ) : K) • z
def Exchange : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ) (c : Fin n → ℤ) (z : Tens (Fin q) P M n)
    (j : Fin n) (hj : j.val + 1 < n), IsWt K EM lam2 c z → c j ≠ c ⟨j.val + 1, hj⟩ →
    IsWt K EM lam2 (c ∘ Equiv.swap j ⟨j.val + 1, hj⟩)
      (permY K (Equiv.swap j ⟨j.val + 1, hj⟩) z + (((c j - c ⟨j.val + 1, hj⟩ : ℤ) : K)⁻¹) • z)
def PermXWt : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ) (c : Fin n → ℤ) (z : Tens (Fin q) P M n)
    (σ : Equiv.Perm (Fin n)), IsWt K EM lam2 c z → IsWt K EM lam2 c (permX K σ z)
def ToSymYX : Prop :=
  ∀ (K R P M : Type) [CommRing K] [AddCommGroup M] [Module K M] [DecidableEq R] [DecidableEq P] [Fintype R] [Fintype P]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (z : Tens R P M n), toSym K (permY K σ z) = toSym K (permX K σ⁻¹ z)
def NoTuple : Prop :=
  ∀ (K V J : Type) [Field K] [AddCommGroup V] [Module K V] (T : J → Module.End K V) (TT : Set (J → K)) (E : Set V),
    (∀ e ∈ E, ∃ t ∈ TT, ∀ j, T j e = t j • e) → ∀ v ∈ Submodule.span K E, ∀ t0 : J → K, t0 ∉ TT →
    (∀ j, T j v = t0 j • v) → v = 0
def NoWt : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ),
    (⨆ tau, PathSpace K (P := P) EM n lam2 tau) = ⊤ →
    ∀ (c : Fin n → ℤ) (z : Tens (Fin q) P M n), IsWt K EM lam2 c z → ¬ IsContentSeq lam2 c → z = 0
def GoodSwap : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P] [Fintype P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ) (c : Fin n → ℤ)
    (j : Fin n) (hj : j.val + 1 < n), 2 ≤ c j - c ⟨j.val + 1, hj⟩ →
    (∀ z : Tens (Fin q) P M n, IsWt K EM lam2 (c ∘ Equiv.swap j ⟨j.val + 1, hj⟩) z → toSym K z = 0) →
    ∀ z : Tens (Fin q) P M n, IsWt K EM lam2 c z → toSym K z = 0
def AntiStep : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ),
    (⨆ tau, PathSpace K (P := P) EM n lam2 tau) = ⊤ →
    ∀ (c : Fin n → ℤ) (z : Tens (Fin q) P M n) (j : Fin n) (hj : j.val + 1 < n), IsWt K EM lam2 c z →
    c ⟨j.val + 1, hj⟩ = c j - 1 → ¬ IsContentSeq lam2 (c ∘ Equiv.swap j ⟨j.val + 1, hj⟩) →
    permY K (Equiv.swap j ⟨j.val + 1, hj⟩) z = - z
def Anti : Prop :=
  ∀ (K R P M : Type) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq R] [DecidableEq P]
    [Fintype R] [Fintype P] (n i : ℕ), i + Fintype.card P < n → ∀ u : Tens R P M n,
    (∀ (j : Fin n) (hj : j.val + 1 < n), i ≤ j.val → j.val < i + Fintype.card P →
      permY K (Equiv.swap j ⟨j.val + 1, hj⟩) u = - u) →
    toSym K u = 0
def ColumnsFromPieri : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P] [Fintype P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ),
    (⨆ tau, PathSpace K (P := P) EM n lam2 tau) = ⊤ →
    ∀ tau, (∃ b : Fin q, ∃ j < tau b, Fintype.card P < LD.colLen lam2 tau j) →
      ∀ z ∈ PathSpace K (P := P) EM n lam2 tau, toSym K z = 0
def LemmaDSkeleton4 : Prop :=
  ∀ (O K V P : Type) (q : ℕ) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [DecidableEq P] [Fintype P] (S : HidaSetting K V P (Fin q))
    (B : LinearMap.BilinForm K V) (n w : ℕ) (lam2 : Fin q → ℕ) (DelL : Submodule O S.W)
    (xi : (P ⊕ Fin q → ℤ) →+ ℤ) (lam : P ⊕ Fin q → ℤ)
    (l : ℕ) (e : ℕ) (i' : ℤ), l.Prime → (∀ m : ℤ, ¬ (l : ℤ) ∣ m → IsUnit (m : O)) →
    S.w = (w : K) → (∀ b, lam2 b ≤ w) → Contra S B → Generated S → (∀ v : V, (∀ x : V, B x v = 0) → v = 0) →
    (∀ b b', ∀ u ∈ DelL, S.EW b b' u ∈ DelL) →
    (⨆ tau, PathSpace K (P := P) S.EW n lam2 tau) = ⊤ →
    (∀ (α : P) (b : Fin q), 0 ≤ xi (Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1)) →
    (∀ κ, xi (lam - κ) ≤ i' → ∀ u ∈ NablaL S B DelL, (u : V) ∈ S.wt κ → (l : O) ^ e • u ∈ DelL) →
    ∀ ν, ∑ α : P, ν (Sum.inl α) + (n : ℤ) = (Fintype.card P : ℤ) * (w : ℤ) → xi (lam - ν) ≤ i' →
      ∀ v ∈ B.dualSubmodule (DeltaAll S DelL), v ∈ S.wt ν →
      (l : O) ^ (e + padicValInt l (LD.Dn (Fintype.card P) w n lam2)) • v ∈ DeltaAll S DelL ∧
        (l : O) ^ (e + padicValInt l (LD.Dn (Fintype.card P) w n lam2)) • v ∈ S.wt ν
end Formalism.CohomologicalDescent.LC


