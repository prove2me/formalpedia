-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_HodgeTateChains_H2KilledByTateDuality
-- name    : Formalism_WachLatticeTwists_HodgeTateChains_H2KilledByTateDuality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:04.338853+00:00
-- url     : https://prove2.me/theorems/e3991fd7-76c1-4bec-8960-9faa6f7eaf6f
-- title:
--   H2 Killed By Tate Duality
-- statement:
--   Definitions and structural lemmas for H2 Killed By Tate Duality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/HodgeTateChains/H2KilledByTateDuality.lean

import Definitions.Def_Formalism_WachLatticeTwists_HodgeTateChains_AdicPerturbationFixedFreeAndCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
open Polynomial
def cB (ℓ s m t gK : ℕ) (U : Finset ℤ) : ℕ := (Finset.range t).sup (fun e => cTB ℓ s m e gK U)
def StatTBcB : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (s m t e gK : ℕ) (U : Finset ℤ) (A : Type) [AddCommGroup A]
    [Module ℤ_[ℓ] A] (Hf : Submodule ℤ_[ℓ] A) (y : A), e < t →
    ((ℓ : ℤ_[ℓ]) ^ cTB ℓ s m e gK U) • y ∈ Hf → ((ℓ : ℤ_[ℓ]) ^ cB ℓ s m t gK U) • y ∈ Hf
def H2KilledByTateDuality : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    ∀ (e : ℕ) (H2 M0 P : Type) [AddCommGroup H2] [Module ℤ_[ℓ] H2] [AddCommGroup M0]
      [Module ℤ_[ℓ] M0] [AddCommGroup P] [Module ℤ_[ℓ] P] (pair : H2 →ₗ[ℤ_[ℓ]] M0 →ₗ[ℤ_[ℓ]] P),
    Function.Injective pair →
    (∀ x : M0, ((u ^ ((e : ℤ) + 1) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • x = x) →
    ∀ x : H2, ((ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ (e + 1))) • x = 0
def FreeIn (ℓ : ℕ) [Fact ℓ.Prime] {H0 H1 : Type} [AddCommGroup H0] [Module ℤ_[ℓ] H0]
    [AddCommGroup H1] [Module ℤ_[ℓ] H1] (cup : H0 →ₗ[ℤ_[ℓ]] H1) (al : ℕ) : Prop :=
  ∀ y : H1, ∃ z : H0, ∃ t : ℕ, ((ℓ : ℤ_[ℓ]) ^ t) • (((ℓ : ℤ_[ℓ]) ^ al) • y - cup z) = 0
def StatFreeAlg : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ) (V : Type) [AddCommGroup V]
    [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V), aeval g ((X - 1) * Rpoly ℓ w U i) = 0 →
    ∀ x : V, g (aeval g (Rpoly ℓ w U i) x) = aeval g (Rpoly ℓ w U i) x ∧
      ∃ y, aeval g (Rpoly ℓ w U i) x - ((Rpoly ℓ w U i).eval 1) • x = g y - y
def StatFreePiece : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (i : ℤ) (A : Md ℓ) (P : Piece ℓ A) (H0A : Md ℓ) (cup : H0A →ₗ[ℤ_[ℓ]] A),
    P.Inputs w U i →
    (∀ a0 : P.Wm, P.gm a0 = a0 → ∃ z : H0A, ((ℓ : ℤ_[ℓ]) ^ m) • P.io (P.infm a0) = cup z) →
      FreeIn ℓ cup (rI ℓ m U i + m + 2)
def StatFreeExt : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H0' H0 H0'' H1' H1 H1'' : Type)
    [AddCommGroup H0'] [Module ℤ_[ℓ] H0'] [AddCommGroup H0] [Module ℤ_[ℓ] H0]
    [AddCommGroup H0''] [Module ℤ_[ℓ] H0''] [AddCommGroup H1'] [Module ℤ_[ℓ] H1']
    [AddCommGroup H1] [Module ℤ_[ℓ] H1] [AddCommGroup H1''] [Module ℤ_[ℓ] H1'']
    (i0 : H0' →ₗ[ℤ_[ℓ]] H0) (p0 : H0 →ₗ[ℤ_[ℓ]] H0'') (dl : H0'' →ₗ[ℤ_[ℓ]] H1')
    (i1 : H1' →ₗ[ℤ_[ℓ]] H1) (p1 : H1 →ₗ[ℤ_[ℓ]] H1'')
    (cup' : H0' →ₗ[ℤ_[ℓ]] H1') (cup : H0 →ₗ[ℤ_[ℓ]] H1) (cup'' : H0'' →ₗ[ℤ_[ℓ]] H1'')
    (c' c'' al' al'' : ℕ),
    Function.Exact p0 dl → Function.Exact i1 p1 →
    (∀ z, cup (i0 z) = i1 (cup' z)) → (∀ z, cup'' (p0 z) = p1 (cup z)) →
    (∀ z, ∃ t : ℕ, ((ℓ : ℤ_[ℓ]) ^ t) • dl z = 0) →
    TorsKilled ℓ H1' c' → TorsKilled ℓ H1'' c'' → FreeIn ℓ cup' al' → FreeIn ℓ cup'' al'' →
      FreeIn ℓ cup (al' + al'' + c' + c'')
def StatHalving : Prop :=
  ∀ (α γ : ℕ → ℕ) (P : ℕ → ℕ → ℕ → Prop),
    (∀ i j al al', al ≤ al' → P i j al → P i j al') → (∀ i, P i (i + 1) (α i)) →
    (∀ i k j al' al'', i < k → k < j → P i k al'' → P k j al' →
      P i j (al' + al'' + ∑ x ∈ Finset.Ico i j, γ x)) →
    ∀ i j, i < j →
      P i j (∑ x ∈ Finset.Ico i j, α x + (∑ x ∈ Finset.Ico i j, γ x) * Nat.clog 2 (j - i))
structure FreeData (ℓ : ℕ) [Fact ℓ.Prime] where

  H0 : ℕ → ℕ → Md ℓ

  H1 : ℕ → ℕ → Md ℓ

  cup : ∀ i j, H0 i j →ₗ[ℤ_[ℓ]] H1 i j

  i0 : ∀ i k j, H0 k j →ₗ[ℤ_[ℓ]] H0 i j
  p0 : ∀ i k j, H0 i j →ₗ[ℤ_[ℓ]] H0 i k
  dl : ∀ i k j, H0 i k →ₗ[ℤ_[ℓ]] H1 k j
  i1 : ∀ i k j, H1 k j →ₗ[ℤ_[ℓ]] H1 i j
  p1 : ∀ i k j, H1 i j →ₗ[ℤ_[ℓ]] H1 i k

  piece : ∀ i, Piece ℓ (H1 i (i + 1))
def FreeData.Inputs {ℓ : ℕ} [Fact ℓ.Prime] (D : FreeData ℓ) : Prop :=
  ∀ i k j, i < k → k < j →
    Function.Exact (D.p0 i k j) (D.dl i k j) ∧ Function.Exact (D.i1 i k j) (D.p1 i k j) ∧
    (∀ z, D.cup i j (D.i0 i k j z) = D.i1 i k j (D.cup k j z)) ∧
    (∀ z, D.cup i k (D.p0 i k j z) = D.p1 i k j (D.cup i j z)) ∧
    ∀ z, ∃ t : ℕ, ((ℓ : ℤ_[ℓ]) ^ t) • D.dl i k j z = 0
def StatFreeGm : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (a : ℤ) (D : FreeData ℓ), D.Inputs →
    (∀ i, (D.piece i).Inputs w U (a + i)) →
    (∀ i, ∀ a0 : (D.piece i).Wm, (D.piece i).gm a0 = a0 →
      ∃ z : D.H0 i (i + 1), ((ℓ : ℤ_[ℓ]) ^ m) • (D.piece i).io ((D.piece i).infm a0) = D.cup i (i + 1) z) →
    (∀ i j, i < j → TorsKilled ℓ (D.H1 i j) (∑ x ∈ Finset.Ico i j, (2 + max 1 (rI ℓ m U (a + x))))) →
    ∀ i j, i < j → FreeIn ℓ (D.cup i j)
      (∑ x ∈ Finset.Ico i j, (rI ℓ m U (a + x) + m + 2) +
        (∑ x ∈ Finset.Ico i j, (2 + max 1 (rI ℓ m U (a + x)))) * Nat.clog 2 (j - i))
end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic


