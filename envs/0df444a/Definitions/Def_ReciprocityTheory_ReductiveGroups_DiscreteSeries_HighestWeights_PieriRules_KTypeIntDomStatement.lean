-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T13:55:55.49005+00:00
-- url     : https://prove2.me/theorems/29689e73-33d8-4ca6-9ff3-24473e4b5346
-- title:
--   KType Int Dom Statement
-- statement:
--   Definitions and structural lemmas for KType Int Dom Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/KTypeIntDomStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
def tensAct {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Fin n → Fin n → Module.End ℂ V) (M : Fin n → Fin n → Matrix ι ι ℂ) :
    Fin n → Fin n → Module.End ℂ (PiLp 2 (fun _ : ι => V)) :=
  fun a b => (WithLp.linearEquiv 2 ℂ (ι → V)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun i => A a b ∘ₗ LinearMap.proj i + ∑ j, M a b i j • LinearMap.proj j) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (ι → V)).toLinearMap
def khwSub {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) : Submodule ℂ W :=
  (⨅ a, LinearMap.ker (E a a - ((ν a : ℝ) : ℂ) • (1 : Module.End ℂ W))) ⊓
    ⨅ a, ⨅ b, ⨅ (_ : a < b ∧ ε a = ε b), LinearMap.ker (E a b)
def CartanCompStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (A : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (w : V) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Fin n → Fin n → Matrix ι ι ℂ) (β : Fin n → ℝ) (f : ι → ℂ),
    Formalism.REAL.KHighest ε A Λ w → w ≠ 0 →
    (∀ a, M a a *ᵥ f = ((β a : ℝ) : ℂ) • f) → (∀ a b, a < b → ε a = ε b → M a b *ᵥ f = 0) → f ≠ 0 →
    (WithLp.toLp 2 (fun i => f i • w) : PiLp 2 (fun _ : ι => V)) ≠ 0 ∧
    Formalism.REAL.KHighest ε (tensAct A M) (Λ + β) (WithLp.toLp 2 (fun i => f i • w) : PiLp 2 (fun _ : ι => V))
def KDom {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) : Prop :=
  ∀ a b, a < b → ε a = ε b → μ b ≤ μ a
def weylK {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
    ((μ + rhoC ε) a - (μ + rhoC ε) b) / (rhoC ε a - rhoC ε b)
def stdM (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ := fun a b => Matrix.single a b 1
def stdWt (n : ℕ) : Fin n → Fin n → ℝ := fun i => Pi.single i 1
def dualM (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ := fun a b => -Matrix.single b a 1
def dualWt (n : ℕ) : Fin n → Fin n → ℝ := fun i => -Pi.single i 1
abbrev pIdx {n : ℕ} (ε : Fin n → Bool) (β : Bool) : Type :=
  {p : Fin n × Fin n // ε p.1 = β ∧ ε p.2 = !β}
def pAdM {n : ℕ} (ε : Fin n → Bool) (β : Bool) : Fin n → Fin n → Matrix (pIdx ε β) (pIdx ε β) ℂ :=
  fun a b p q =>
    (if p.1.1 = a ∧ q.1.1 = b ∧ p.1.2 = q.1.2 then 1 else 0) -
      (if q.1.2 = a ∧ p.1.2 = b ∧ p.1.1 = q.1.1 then 1 else 0)
def pWt {n : ℕ} (ε : Fin n → Bool) (β : Bool) : pIdx ε β → Fin n → ℝ :=
  fun p => Pi.single p.1.1 1 - Pi.single p.1.2 1
def LowCompStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (A : Fin n → Fin n → Module.End ℂ V) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Fin n → Fin n → Matrix ι ι ℂ) (γ : ι → Fin n → ℝ),
    Formalism.REAL.KRel ε M → (∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ)) →
    ∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : ι => V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct A M) ν x →
      ∃ β : Fin n → ℝ, (∃ i, γ i = β ∧ x i ≠ 0) ∧
        ∀ j, γ j = β → Formalism.REAL.KHighest ε A (ν - β) (x j)
def TensHWStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (A : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (w : V) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Fin n → Fin n → Matrix ι ι ℂ) (γ : ι → Fin n → ℝ),
    Formalism.REAL.KRel ε A → Formalism.REAL.KUnit ε A → Formalism.REAL.KHighest ε A Λ w → Formalism.REAL.kSpan ε A w = ⊤ →
    Formalism.REAL.KRel ε M → (∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ)) →
    (∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : ι => V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct A M) ν x → ∃ i, ν = Λ + γ i) ∧
    ∀ ν : Fin n → ℝ, FiniteDimensional ℂ (khwSub ε (tensAct A M) ν) ∧
      Module.finrank ℂ (khwSub ε (tensAct A M) ν) ≤ Nat.card {i : ι // ν = Λ + γ i}
def KTypeIntDomStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (_T : KType ε Λ),
    (∀ a, ∃ m : ℤ, Λ a = m) ∧ KDom ε Λ
def WeylPosStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ), KDom ε μ → 0 < weylK ε μ
def WeylSumStdStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ), (∀ a, ∃ m : ℤ, Λ a = m) → KDom ε Λ →
    (∑ s, weylK ε (Λ + stdWt n s) = (n : ℝ) * weylK ε Λ) ∧
    ∀ s, ¬ KDom ε (Λ + stdWt n s) → weylK ε (Λ + stdWt n s) = 0
def WeylSumDualStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ), (∀ a, ∃ m : ℤ, Λ a = m) → KDom ε Λ →
    (∑ s, weylK ε (Λ + dualWt n s) = (n : ℝ) * weylK ε Λ) ∧
    ∀ s, ¬ KDom ε (Λ + dualWt n s) → weylK ε (Λ + dualWt n s) = 0
def WeylSumPStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (β : Bool) (Λ : Fin n → ℝ), (∀ a, ∃ m : ℤ, Λ a = m) → KDom ε Λ →
    (∑ p : pIdx ε β, weylK ε (Λ + pWt ε β p) = (Nat.card (pIdx ε β) : ℝ) * weylK ε Λ) ∧
    ∀ p : pIdx ε β, ¬ KDom ε (Λ + pWt ε β p) → weylK ε (Λ + pWt ε β p) = 0
def TensRepStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ),
    Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)) →
    (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) →
    ∃ (τ : KG ε →* unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
      (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V))),
      Continuous τ ∧
      (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
        HasDerivAt (fun t : ℝ => ((τ (γ t) : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ]
          PiLp 2 (fun _ : ι => T.V))) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
          (D X) 0) ∧
      ∀ a b, ((D (Matrix.single a b 1) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :
        Module.End ℂ (PiLp 2 (fun _ : ι => T.V))) =
          tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) a b
def CartanKTypeStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (β : Fin n → ℝ) (f : ι → ℂ),
    Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)) →
    (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) →
    (∀ a, dρ (Matrix.single a a 1) *ᵥ f = ((β a : ℝ) : ℂ) • f) →
    (∀ a b, a < b → ε a = ε b → dρ (Matrix.single a b 1) *ᵥ f = 0) → f ≠ 0 →
    ∃ (T' : KType ε (Λ + β))
      (φ : T'.V ≃ₗᵢ[ℂ] Formalism.REAL.kSpan ε (tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)))
        (WithLp.toLp 2 (fun i => f i • T.w) : PiLp 2 (fun _ : ι => T.V))),
      (∀ a b, ε a = ε b → ∀ v : T'.V, (φ (kunits T' a b v) : PiLp 2 (fun _ : ι => T.V)) =
        tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) a b (φ v)) ∧
      (φ T'.w : PiLp 2 (fun _ : ι => T.V)) =
        ((‖(WithLp.toLp 2 (fun i => f i • T.w) : PiLp 2 (fun _ : ι => T.V))‖⁻¹ : ℝ) : ℂ) •
          (WithLp.toLp 2 (fun i => f i • T.w) : PiLp 2 (fun _ : ι => T.V))
def PieriCountStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (γ : ι → Fin n → ℝ),
    Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)) →
    (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) →
    Formalism.REAL.KRel ε (fun a b => dρ (Matrix.single a b 1)) →
    (∀ a, dρ (Matrix.single a a 1) = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ)) →
    Function.Injective γ →
    (∑ i, weylK ε (Λ + γ i) = (Fintype.card ι : ℝ) * weylK ε Λ) →
    (∀ i, ¬ KDom ε (Λ + γ i) → weylK ε (Λ + γ i) = 0) →
    (∀ i, KDom ε (Λ + γ i) → ∃ x : PiLp 2 (fun _ : ι => T.V), x ≠ 0 ∧
      Formalism.REAL.KHighest ε (tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1))) (Λ + γ i) x) ∧
    ∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : ι => T.V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1))) ν x →
      ∃ i, ν = Λ + γ i ∧ KDom ε (Λ + γ i)
def PieriStdStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ),
    (∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : Fin n => T.V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct (kunits T) (stdM n)) ν x →
      ∃ s, ν = Λ + stdWt n s ∧ KDom ε (Λ + stdWt n s)) ∧
    (∀ s, Module.finrank ℂ (khwSub ε (tensAct (kunits T) (stdM n)) (Λ + stdWt n s)) ≤ 1) ∧
    ∀ s, KDom ε (Λ + stdWt n s) → ∃ x : PiLp 2 (fun _ : Fin n => T.V), x ≠ 0 ∧
      Formalism.REAL.KHighest ε (tensAct (kunits T) (stdM n)) (Λ + stdWt n s) x
def PieriDualStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ),
    (∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : Fin n => T.V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct (kunits T) (dualM n)) ν x →
      ∃ s, ν = Λ + dualWt n s ∧ KDom ε (Λ + dualWt n s)) ∧
    (∀ s, Module.finrank ℂ (khwSub ε (tensAct (kunits T) (dualM n)) (Λ + dualWt n s)) ≤ 1) ∧
    ∀ s, KDom ε (Λ + dualWt n s) → ∃ x : PiLp 2 (fun _ : Fin n => T.V), x ≠ 0 ∧
      Formalism.REAL.KHighest ε (tensAct (kunits T) (dualM n)) (Λ + dualWt n s) x
def PPlusStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (β : Bool) (Λ : Fin n → ℝ) (T : KType ε Λ),
    (∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : pIdx ε β => T.V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct (kunits T) (pAdM ε β)) ν x →
      ∃ p, ν = Λ + pWt ε β p ∧ KDom ε (Λ + pWt ε β p)) ∧
    (∀ p, Module.finrank ℂ (khwSub ε (tensAct (kunits T) (pAdM ε β)) (Λ + pWt ε β p)) ≤ 1) ∧
    ∀ p, KDom ε (Λ + pWt ε β p) → ∃ x : PiLp 2 (fun _ : pIdx ε β => T.V), x ≠ 0 ∧
      Formalism.REAL.KHighest ε (tensAct (kunits T) (pAdM ε β)) (Λ + pWt ε β p) x
end ReciprocityTheory.ChartRestriction.DS.HW


