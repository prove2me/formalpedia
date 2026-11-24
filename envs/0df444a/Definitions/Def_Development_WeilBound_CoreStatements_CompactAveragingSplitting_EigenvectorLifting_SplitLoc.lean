-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
-- name    : Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:52.219636+00:00
-- url     : https://prove2.me/theorems/ac1c1522-bdfe-4601-a038-b4d73d882fb3
-- title:
--   Split Loc
-- statement:
--   Definitions and structural lemmas for Split Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SplitLoc.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
namespace PositivityTheory.ThK.SplitLoc
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def blkA {a a' : ℕ} (b : GL (Fin (a + a')) k) : Matrix (Fin a) (Fin a) k :=
  fun i j => (b : Matrix (Fin (a + a')) (Fin (a + a')) k) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
def blkD {a a' : ℕ} (b : GL (Fin (a + a')) k) : Matrix (Fin a') (Fin a') k :=
  fun i j => (b : Matrix (Fin (a + a')) (Fin (a + a')) k) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j))
def IsBlockUpper {a a' : ℕ} (b : GL (Fin (a + a')) k) : Prop :=
  ∀ (i : Fin a') (j : Fin a), (b : Matrix (Fin (a + a')) (Fin (a + a')) k) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0
def indFac (a a' : ℕ) (α β : kˣ →* ℂˣ) (dA dD : kˣ) : ℂ :=
  (α dA : ℂ) * β dD * apow dA ((a' : ℂ) / 2) * apow dD (-(a : ℂ) / 2)
def indSp (a a' : ℕ) (α β : kˣ →* ℂˣ) : Submodule ℂ (GL (Fin (a + a')) k → ℂ) where
  carrier := {F | (∃ U : Subgroup (GL (Fin (a + a')) k), IsOpen (U : Set (GL (Fin (a + a')) k)) ∧ ∀ u ∈ U, ∀ h, F (h * u) = F h) ∧
    ∀ b h, IsBlockUpper b → ∀ dA dD : kˣ, (dA : k) = (blkA b).det → (dD : k) = (blkD b).det →
      F (b * h) = indFac a a' α β dA dD * F h}
  add_mem' := by
    rintro F G ⟨⟨U, hU, hF⟩, lF⟩ ⟨⟨U', hU', hG⟩, lG⟩
    refine ⟨⟨U ⊓ U', hU.inter hU', fun u hu h => ?_⟩, fun b h hb dA dD h1 h2 => ?_⟩
    · simp only [Pi.add_apply, hF u hu.1 h, hG u hu.2 h]
    · simp only [Pi.add_apply, lF b h hb dA dD h1 h2, lG b h hb dA dD h1 h2, mul_add]
  zero_mem' := ⟨⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩, fun _ _ _ _ _ _ _ => by simp⟩
  smul_mem' := by
    rintro c F ⟨⟨U, hU, hF⟩, lF⟩
    refine ⟨⟨U, hU, fun u hu h => ?_⟩, fun b h hb dA dD h1 h2 => ?_⟩
    · simp only [Pi.smul_apply, hF u hu h]
    · simp only [Pi.smul_apply, lF b h hb dA dD h1 h2, smul_eq_mul]; ring
def rtr {n : ℕ} (h₁ : GL (Fin n) k) (F : GL (Fin n) k → ℂ) : GL (Fin n) k → ℂ := fun h => F (h * h₁)
variable [MeasurableSpace k] [BorelSpace k]
def pRam (a a' : ℕ) (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ) : GL (Fin (a + a')) k → ℂ :=
  bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β Φ
def pRam' (a a' : ℕ) (ν α : kˣ →* ℂˣ) (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ) : GL (Fin (a + a')) k → ℂ :=
  smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α Ψ
def invL (a d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range a, (1 - Polynomial.C ((ν ϖ : ℂ) * (resCard k : ℂ) ^ ((i : ℂ) - (d : ℂ) / 2)) * Polynomial.X)
def zCoeff (a d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (φ : Matrix (Fin a) (Fin a) k → ℂ) (m : ℤ) : ℂ :=
  ∑ᶠ n : {n : Fin a → ℤ // Antitone n ∧ ∑ i, n i = m}, shell (haarVol (KO k (Fin a))) ϖ ν ((d : ℂ) / 2) φ n.1
def zetaUnr (a d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (φ : Matrix (Fin a) (Fin a) k → ℂ) : ℂ :=
  ∑ᶠ m : ℤ, ∑ j ∈ Finset.range (a + 1), (invL a d ϖ ν).coeff j * zCoeff a d ϖ ν φ (m - j)
def pUnr (a a' : ℕ) (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ) : GL (Fin (a + a')) k → ℂ :=
  fun h => zetaUnr a (a + a') ϖ ν fun g => omA ν β 1 h Φ (g * X0 k finSumFinEquiv)
def pUnr' (a a' : ℕ) (ϖ : kˣ) (ν α : kˣ →* ℂˣ) (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ) : GL (Fin (a + a')) k → ℂ :=
  ((invL a' (a + a') ϖ ν).eval 1) • smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α Ψ
structure HidaSetting (a a' : ℕ) (ϖ : kˣ) (α β ν : kˣ →* ℂˣ) : Prop where
  unif : IsUnif ϖ
  unitα : ∀ x, ‖(α x : ℂ)‖ = 1
  unitβ : ∀ x, ‖(β x : ℂ)‖ = 1
  quot : ν = α / β
  lt : a' < a
  even : Even (a + a')
  cond : ∃ e : ℕ, CondLE ϖ e α ∧ CondLE ϖ e β
def RamMaps : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (a a' : ℕ) (ϖ : kˣ) (α β ν : kˣ →* ℂˣ), HidaSetting a a' ϖ α β ν → ¬ IsUnram ν →
    (∀ Φ ∈ SB _, ∀ Φ₁ ∈ SB _, ∀ c : ℂ, pRam a a' ϖ ν β (Φ + c • Φ₁) = pRam a a' ϖ ν β Φ + c • pRam a a' ϖ ν β Φ₁) ∧
    (∀ Ψ ∈ SB _, ∀ Ψ₁ ∈ SB _, ∀ c : ℂ, pRam' a a' ν α (Ψ + c • Ψ₁) = pRam' a a' ν α Ψ + c • pRam' a a' ν α Ψ₁) ∧
    (∀ Φ ∈ SB _, pRam a a' ϖ ν β Φ ∈ indSp a a' α β) ∧ (∀ Ψ ∈ SB _, pRam' a a' ν α Ψ ∈ indSp a a' α β) ∧
    (∀ Φ ∈ SB _, ∀ g, pRam a a' ϖ ν β (omA ν β g 1 Φ) = pRam a a' ϖ ν β Φ) ∧
    (∀ Ψ ∈ SB _, ∀ g, pRam' a a' ν α (omB ν α g 1 Ψ) = pRam' a a' ν α Ψ) ∧
    (∀ Φ ∈ SB _, ∀ h₁, pRam a a' ϖ ν β (omA ν β 1 h₁ Φ) = rtr h₁ (pRam a a' ϖ ν β Φ)) ∧
    (∀ Ψ ∈ SB _, ∀ h₁, pRam' a a' ν α (omB ν α 1 h₁ Ψ) = rtr h₁ (pRam' a a' ν α Ψ)) ∧
    (∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB _, pRam a a' ϖ ν β Φ = F) ∧ (∀ F ∈ indSp a a' α β, ∃ Ψ ∈ SB _, pRam' a a' ν α Ψ = F)
def UnrMaps : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (a a' : ℕ) (ϖ : kˣ) (α β ν : kˣ →* ℂˣ), HidaSetting a a' ϖ α β ν → IsUnram α → IsUnram β →
    (∀ Φ ∈ SB _, ∀ Φ₁ ∈ SB _, ∀ c : ℂ, pUnr a a' ϖ ν β (Φ + c • Φ₁) = pUnr a a' ϖ ν β Φ + c • pUnr a a' ϖ ν β Φ₁) ∧
    (∀ Ψ ∈ SB _, ∀ Ψ₁ ∈ SB _, ∀ c : ℂ, pUnr' a a' ϖ ν α (Ψ + c • Ψ₁) = pUnr' a a' ϖ ν α Ψ + c • pUnr' a a' ϖ ν α Ψ₁) ∧
    (∀ Φ ∈ SB _, pUnr a a' ϖ ν β Φ ∈ indSp a a' α β) ∧ (∀ Ψ ∈ SB _, pUnr' a a' ϖ ν α Ψ ∈ indSp a a' α β) ∧
    (∀ Φ ∈ SB _, ∀ g, pUnr a a' ϖ ν β (omA ν β g 1 Φ) = pUnr a a' ϖ ν β Φ) ∧
    (∀ Ψ ∈ SB _, ∀ g, pUnr' a a' ϖ ν α (omB ν α g 1 Ψ) = pUnr' a a' ϖ ν α Ψ) ∧
    (∀ Φ ∈ SB _, ∀ h₁, pUnr a a' ϖ ν β (omA ν β 1 h₁ Φ) = rtr h₁ (pUnr a a' ϖ ν β Φ)) ∧
    (∀ Ψ ∈ SB _, ∀ h₁, pUnr' a a' ϖ ν α (omB ν α 1 h₁ Ψ) = rtr h₁ (pUnr' a a' ϖ ν α Ψ)) ∧
    (∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB _, pUnr a a' ϖ ν β Φ = F) ∧ (∀ F ∈ indSp a a' α β, ∃ Ψ ∈ SB _, pUnr' a a' ϖ ν α Ψ = F) ∧
    (∀ h ∈ KO k (Fin (a + a')), pUnr a a' ϖ ν β (Set.indicator {X | ∀ i j, X i j ∈ 𝒪[k]} 1) h = 1) ∧
    (∀ h ∈ KO k (Fin (a + a')), pUnr' a a' ϖ ν α (Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[k]} 1) h = 1)
def IndIrred : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (α β : kˣ →* ℂˣ), (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
    ∀ N : Submodule ℂ (GL (Fin (a + a')) k → ℂ), N ≤ indSp a a' α β → (∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) →
      N = ⊥ ∨ N = indSp a a' α β
end PositivityTheory.ThK.SplitLoc


