-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:34.991845+00:00
-- url     : https://prove2.me/theorems/d051d9a0-7636-53e7-a1fb-cca9f5645ca1
-- title:
--   Normal Representation Lattice
-- statement:
--   Definitions and structural lemmas for Normal Representation Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/NormalRepresentationLattice.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_mem_latOf_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
section Plain
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
def nfBasis (ϖ : kˣ) (g : GL n k) (e : Fin c → ℤ) (z : n → k) : GL (n ⊕ Fin c) k :=
  colE c 1 z * embX c g * embA n (SplitFlip.diagGL fun i => ϖ ^ e i)
variable [ValuativeRel k]
def powInt (ϖ : kˣ) (e : ℤ) : Set k := {s | valuation k s ≤ valuation k ((ϖ ^ e : kˣ) : k)}
def topCoord (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : Fin c) : Set k :=
  {s | ∃ y ∈ Λ, (∀ l, i < l → y (Sum.inr l) = 0) ∧ y (Sum.inr i) = s}
def MeetsIn (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (L : Submodule 𝒪[k] (n → k)) : Prop :=
  ∀ y : n → k, Sum.elim y 0 ∈ Λ ↔ y ∈ L
def MapsLat {ι ι' : Type*} [Fintype ι'] (x : Matrix ι ι' k) (Λ' : Submodule 𝒪[k] (ι' → k))
    (Λ : Submodule 𝒪[k] (ι → k)) : Prop := ∀ v ∈ Λ', x *ᵥ v ∈ Λ
end Plain
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def NormalFormModN : Prop :=
  ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (h : GL (n ⊕ Fin c) k),
    ∃ u ∈ N k n c 1, ∃ (g : GL n k) (e : Fin c → ℤ) (z : n → k),
      latOf (u * h) = latOf (nfBasis ϖ g e z) ∧ MeetsIn (latOf h) (latOf g)
variable [MeasurableSpace k] [BorelSpace k]
def LatticeBounds : Prop :=
  ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k →
  ∀ ψ : AddChar k Circle, HasConductor ψ 1 → ∀ ν : Measure k, ν.IsAddHaarMeasure →
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ)
    (g' : GL n' k) (e' : Fin (c + 1 + 1) → ℤ) (z' : n' → k) (h : GL (n ⊕ Fin (c + 1)) k)
    (Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ),
    (∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h)) →
    (∀ x y, MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x) →
    ∀ x₀ : Matrix n n' k, opE ψ ν 1 Ψ x₀ ≠ 0 →
      (∃ e : Fin (c + 1) → ℤ, ∀ i, topCoord (latOf h) i = powInt ϖ (e i) ∧
        e' i.succ - 1 ≤ e i ∧ e i ≤ e' i.castSucc) ∧
      ((ϖ ^ e' 0 : kˣ) : k) • (Sum.elim (x₀ *ᵥ z') (Pi.single 0 1) : n ⊕ Fin (c + 1) → k) ∈ latOf h
variable {k}
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
  (T : Chain k s X Z) (ϖ : kˣ) (ψ : AddChar k Circle) (ν : Measure k)
def IsNormalRep (j c : ℕ) (h : j + c = s) (g : GL (X j ⊕ Fin (c + 1)) k) : Prop :=
  ∃ (e : Fin (c + 1) → ℤ) (z : X j → k), (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (∀ i, z i ∈ 𝒪[k]) ∧
    latOf (g * T.bas j (c + 1) (by omega)) = latOf (normalBasis ϖ e z)
def NormalReps : Prop :=
  (∀ A, T.IsRepSystem A ψ ν → ∀ j c h, ∀ g ∈ A j c h, ∃ g₁,
    DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J g₁ =
      DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J g ∧ IsNormalRep T ϖ j c h g₁) ∧
  (∃ A, T.IsRepSystem A ψ ν ∧ T.RepsNormal A ϖ) ∧
  ∀ A, T.IsRepSystem A ψ ν → T.RepsNormal A ϖ → T.RepsMeet A ∧ ∀ j c h, ∀ g ∈ A j c h,
    ∀ κ ∈ stabLat (T.bas j (c + 1) (by omega)),
      latOf (T.bas j (c + 1) (by omega)) ≤ latOf (g * κ * T.bas j (c + 1) (by omega)) ∧
      ∀ y ∈ latOf (g * κ * T.bas j (c + 1) (by omega)), ((ϖ ^ j : kˣ) : k) • y ∈ latOf (T.bas j (c + 1) (by omega))
def DepthOne : Prop :=
  ∀ A, T.IsRepSystem A ψ ν → T.RepsNormal A ϖ → ∀ j c (h : j + 1 + c = s),
    ∀ g ∈ A j (c + 1) (by omega), ∀ g' ∈ A (j + 1) c h,
    DoubleCoset.mk (R k (X (j + 1)) (c + 1) 1) (T.lev (j + 1) (c + 1) (congrArg Nat.succ h)).J g' ∈ T.idx ψ ν j c h g →
      (∀ x₀ y, om (T.mu (j + 1)) g g' (T.Phi j (c + 1) (by omega)) (affPt 1 x₀ y) ≠ 0 →
        (∀ i : Fin (c + 1), affPt 1 x₀ y (Sum.inr i) (Sum.inr i.succ) ∈ powInt ϖ (-1)) ∧
          ch (affPt 1 x₀ y) ∈ powInt ϖ (-1)) ∧
      (∀ (e : Fin (c + 1) → ℤ) (z : X (j + 1) → k),
        latOf (g' * T.bas (j + 1) (c + 1) (by omega)) = latOf (normalBasis ϖ e z) →
          ∀ i : Fin c, e i.succ - 1 ≤ e i.castSucc) ∧
      ∀ u ∈ N k (X (j + 1)) (c + 1) 1, ∀ γ : GL (X (j + 1)) k,
        u * embX (c + 1) γ ∈ Cgrp (T.lev (j + 1) (c + 1) (by omega)).J g' →
          (∀ i : Fin c, u.val (Sum.inr i.castSucc) (Sum.inr i.succ) ∈ powInt ϖ (-1)) ∧ simpleSum u ∈ powInt ϖ (-1)
def LastSteps : Prop :=
  ∀ A, T.IsRepSystem A ψ ν → T.RepsMeet A →
    (∀ g ∈ A s 0 rfl, IsNormalRep T ϖ s 0 rfl g) ∧
    (∀ g ∈ A s 0 rfl, ∀ x₀ y, T.Psi g x₀ y ≠ 0 → ∀ i, y i ∈ 𝒪[k]) ∧
    (∀ M : ℕ, 1 ≤ M → ∀ yb ∈ T.coupIdx A (box _ (ϖ ^ M)⁻¹) (box _ (ϖ ^ M)),
      ∀ y, Submodule.Quotient.mk y = yb → ∀ i, y i ∈ 𝒪[k]) ∧
    T.Adapted A (box _ (ϖ ^ (s + 1))⁻¹) (box _ (ϖ ^ (s + 1))) ∧
    ∀ ε : k, valuation k ε = 1 → ∀ yb ∈ T.coupIdx A (box _ (ϖ ^ (s + 1))⁻¹) (box _ (ϖ ^ (s + 1))),
      ∀ η, hat ψ ν ε (cosetInd _ yb) η ≠ 0 →
        ∀ y, Submodule.Quotient.mk y = yb → ε * (η ⬝ᵥ y) ∈ powInt ϖ (-((s : ℤ) + 1))
variable (k) in

def ChainSizes : Prop :=
  ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k →
  ∀ ψ : AddChar k Circle, HasConductor ψ 1 → ∀ ν : Measure k, ν.IsAddHaarMeasure →
  ∀ (s : ℕ) (r t Z : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype Z] [DecidableEq Z]
    (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (μ₀ : ℕ → kˣ →* ℂˣ), (∀ j, IsUnram (μ₀ j)) →
  ∀ (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z),
    (∀ j c h, latOf (F j c h).bas = latOf 1) →
      NormalReps (Chain.ofTwist δ hδ μ₀ F Ftop) ϖ ψ ν ∧ DepthOne (Chain.ofTwist δ hδ μ₀ F Ftop) ϖ ψ ν ∧
        LastSteps (Chain.ofTwist δ hδ μ₀ F Ftop) ϖ ψ ν
variable (k) in

def LatticeClasses : Prop := NormalFormModN k ∧ LatticeBounds k ∧ ChainSizes k
example (H : ChainSizes k) (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
    [hν : ν.IsAddHaarMeasure] (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]
    (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (μ₀ : ℕ → kˣ →* ℂˣ) (h₀ : ∀ j, IsUnram (μ₀ j)) :
    ∃ A, (twistChain s t κ δ hδ μ₀).IsRepSystem A ψ ν ∧ (twistChain s t κ δ hδ μ₀).RepsNormal A ϖ :=
  (H ϖ hϖ ψ hψ ν hν s (κ ⊕ Fin (s + 1)) t (Ix (κ ⊕ Fin (s + 1)) t (s + 2)) (XIx κ t) δ hδ μ₀ h₀
    (fun j c h => plainFrame (stdOrd κ t j c h)) (LatFrame.refl k _) fun _ _ _ => rfl).1.2.1
example {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ} (i : Fin c) :
    topCoord (latOf (1 : GL (n ⊕ Fin c) k)) i = powInt ϖ 0 := by
  ext a
  simp only [topCoord, powInt, mem_latOf_one, Set.mem_setOf_eq, zpow_zero, Units.val_one, map_one]
  constructor
  · rintro ⟨y, hy, -, rfl⟩; exact hy _
  · intro ha
    refine ⟨Pi.single (Sum.inr i) a, fun l => ?_, fun l hl => ?_, by simp⟩
    · rw [Pi.single_apply]; split_ifs
      exacts [ha, zero_mem _]
    · rw [Pi.single_apply, if_neg]; simpa using hl.ne'
end GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice


