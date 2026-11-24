-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:09:55.338794+00:00
-- url     : https://prove2.me/theorems/53497355-b24f-44ef-bdf0-0445db0e9826
-- title:
--   Pi Nonunit
-- statement:
--   Definitions and structural lemmas for Pi Nonunit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/PiNonunit.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.SqPair.LCP
section Defs
variable {R : Type} [CommRing R] [StarRing R]
def hf {ι : Type} [Fintype ι] (A : Matrix ι ι R) (x y : ι → R) : R := star x ⬝ᵥ (A *ᵥ y)
def Unimod {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) : Prop :=
  Aᴴ = A ∧ IsUnit A.det
def hyp : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]
structure Inert (R₀ : Subring R) (ϖ : R) : Prop where
  fix : ∀ x, x ∈ R₀ ↔ star x = x
  unr : ∃ θ : R, IsUnit (θ - star θ)
  pi_mem : ϖ ∈ R₀
  pi_ne : ϖ ≠ 0
  pi_nonunit : ¬ IsUnit ϖ
  dom : IsDomain R
  val : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u
def PHyp {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : R) (A A' h : Matrix ι ι R) (k : ℕ) : Prop :=
  Unimod A ∧ Unimod A' ∧ hᴴ * A * h = (ϖ ^ (2 * k)) • A'
def PConcl {ι : Type} [Fintype ι] [DecidableEq ι] (A h : Matrix ι ι R) : Prop :=
  ∃ e f : Matrix ι ι R, e * e = e ∧ eᴴ * A = A * (1 - e) ∧ e * h = h * f
def PGen (ϖ : R) (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (A A' h : Matrix ι ι R) (k : ℕ), PHyp ϖ A A' h k → PConcl A h
def IsBase {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : R) (h : Matrix ι ι R) (k : ℕ) : Prop :=
  ∃ h₁ : Matrix ι ι R, IsUnit h₁.det ∧ h = (ϖ ^ k) • h₁
def StepOut {κ : Type} [Fintype κ] [DecidableEq κ] (A A' h : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) :
    Prop :=
  ∃ (u u' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) (A₁ A₁' h₂ : Matrix κ κ R) (d : Fin 2 → R),
    IsUnit u.det ∧ IsUnit u'.det ∧ uᴴ * A * u = fromBlocks hyp 0 0 A₁ ∧
    u'ᴴ * A' * u' = fromBlocks hyp 0 0 A₁' ∧ h * u' = u * fromBlocks (diagonal d) 0 0 h₂
end Defs
def Dichotomy : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R), (∀ x, x ∈ R₀ ↔ star x = x) →
    ∀ [IsDomain R₀] [IsDiscreteValuationRing R₀] [HenselianLocalRing R₀]
      [Finite (IsLocalRing.ResidueField R₀)],
    (∃ θ : R, IsUnit (θ - star θ)) → ∀ ϖ : R₀, Irreducible ϖ →
    (∃ ε : R, ε * ε = ε ∧ star ε = 1 - ε) ∨ Inert R₀ (ϖ : R)
def BaseLag : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R) [HenselianLocalRing R₀]
    [Finite (IsLocalRing.ResidueField R₀)] (ϖ : R), Inert R₀ ϖ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Even (Fintype.card κ) →
    ∀ A : Matrix κ κ R, Unimod A → ∃ e : Matrix κ κ R, e * e = e ∧ eᴴ * A = A * (1 - e)
def Select : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R) (ϖ : R), Inert R₀ ϖ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A A' h : Matrix ι ι R) (k : ℕ),
    PHyp ϖ A A' h k → ¬ IsBase ϖ h k →
    ∃ (a : ℕ) (x y : ι → R), 0 < a ∧ a ≤ k ∧ hf A x y = 1 ∧
      (∃ c, hf A x x = ϖ ^ (2 * a) * c) ∧
      (∃ v, h *ᵥ v = ϖ ^ (k - a) • x) ∧ (∃ w, h *ᵥ w = ϖ ^ (k + a) • y)
def Plane : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R) [HenselianLocalRing R₀] (ϖ : R),
    Inert R₀ ϖ → ∀ α β : R₀, α ∈ IsLocalRing.maximalIdeal R₀ →
    ∃ w : Matrix (Fin 2) (Fin 2) R, IsUnit w.det ∧
      wᴴ * !![(α : R), 1; 1, (β : R)] * w = hyp ∧ ∃ s' : R, w 1 0 = (α : R) * s'
def SplitOff : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] [IsLocalRing R]
    (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ],
    Fintype.card κ + 2 = Fintype.card ι →
    ∀ (A : Matrix ι ι R), Aᴴ = A → ∀ x y : ι → R, hf A x x = 0 → hf A y y = 0 → hf A x y = 1 →
    ∃ (u : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ : Matrix κ κ R),
      u * v = 1 ∧ v * u = 1 ∧ (∀ i, u i (.inl 0) = x i) ∧ (∀ i, u i (.inl 1) = y i) ∧
      uᴴ * A * u = fromBlocks hyp 0 0 A₁
def Split : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R) (ϖ : R), Inert R₀ ϖ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A A' h : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R)
      (k a : ℕ), PHyp ϖ A A' h k → a ≤ k →
    ∀ x y v w : Fin 2 ⊕ κ → R, hf A x x = 0 → hf A y y = 0 → hf A x y = 1 →
      h *ᵥ v = ϖ ^ (k - a) • x → h *ᵥ w = ϖ ^ (k + a) • y → StepOut A A' h
def Step : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (R₀ : Subring R) [HenselianLocalRing R₀] (ϖ : R),
    Inert R₀ ϖ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A A' h : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) (k : ℕ),
    PHyp ϖ A A' h k → ¬ IsBase ϖ h k → StepOut A A' h
end PI.SqPair.LCP


