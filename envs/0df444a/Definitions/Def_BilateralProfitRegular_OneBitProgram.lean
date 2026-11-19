-- Prove2me | Definitions.Def_BilateralProfitRegular_OneBitProgram
-- name    : BilateralProfitRegular_OneBitProgram
-- status  : Definition
-- author  : @sim2000dg
-- created : 2026-11-18T17:09:10.023266+00:00
-- url     : https://prove2.me/theorems/cc400876-34f1-42ce-a6d6-d6bb161c9cdf
-- title:
--   Seeded one-bit programs and their finite-horizon cost
-- statement:
--   A program reads a chronological sequence of trade bits. It either returns an output or posts a price pair for the next observation. A seeded program has a probability law on its private seed and measurable next actions. The finite-horizon cost is obtained by conditioning on the next trade bit at each price, then integrating over the seed. This formulation supports physical truncation during the initialization and refinement routines.
-- source:
--   Brüstle, di Gregorio, Fusco, and Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism, Algorithms 7–8 and Theorem 6.1.

import Definitions.Def_BilateralProfitRegular_Auxiliary

noncomputable section

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

/-- The next action or final result after a chronological one-bit history. -/
abbrev Program (α : Type) := List Bool → α ⊕ (ℝ × ℝ)

namespace Program

variable {α β Ω : Type}

def after (p : Program α) (b : Bool) : Program α := fun h => p (b :: h)

def pure (a : α) : Program α := fun _ => .inl a

def bind (p : Program α) (k : α → Program β) : Program β
  | [] => (p []).elim (fun a => k a []) Sum.inr
  | b :: h => (p []).elim (fun a => k a (b :: h)) (fun _ => bind (p.after b) k h)

def value (prob : (ℝ × ℝ) → ℝ) (gap : (ℝ × ℝ) → ℝ≥0∞)
    (p : Program α) : ℕ → (ℕ → α → ℝ≥0∞) → ℝ≥0∞
  | 0, finish => (p []).elim (finish 0) (fun _ => 0)
  | n+1, finish => (p []).elim (finish (n+1)) fun x =>
      gap x + (ENNReal.ofReal (prob x) * (p.after true).value prob gap n finish +
        ENNReal.ofReal (1 - prob x) * (p.after false).value prob gap n finish)

def Legal (S : Set (ℝ × ℝ)) (p : Program α) : Prop :=
  ∀ h x, p h = .inr x → x ∈ S

def mapQuery (f : (ℝ × ℝ) → (ℝ × ℝ)) (p : Program α) : Program α :=
  fun h => (p h).map id f

variable [MeasurableSpace α] [MeasurableSpace Ω]

def MeasurableFamily (p : Ω → Program α) : Prop :=
  ∀ h, Measurable (fun ω => p ω h)

end Program

def regretGap (E : Environment) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (muStar E - mu E x)

structure RandomProgram (I A : Type) [MeasurableSpace I] [MeasurableSpace A] where
  Seed : Type
  seedSpace : MeasurableSpace Seed
  law : Measure Seed
  probability : IsProbabilityMeasure law
  run : I × Seed → Program A
  measurable_run : Program.MeasurableFamily run
  legal : ∀ s, Program.Legal triT (run s)

namespace RandomProgram

variable {I A B J : Type} [MeasurableSpace I] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace J]

instance (p : RandomProgram I A) : MeasurableSpace p.Seed := p.seedSpace

instance (p : RandomProgram I A) : IsProbabilityMeasure p.law := p.probability

def expected (p : RandomProgram I A) (E : Environment) (i : I) (n : ℕ)
    (finish : ℕ → A → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, (p.run (i, ω)).value (P E) (regretGap E) n finish ∂p.law

def expectedCost (p : RandomProgram I A) (E : Environment) (g : (ℝ × ℝ) → ℝ≥0∞)
    (i : I) (n : ℕ) (finish : ℕ → A → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, (p.run (i, ω)).value (P E) g n finish ∂p.law

end RandomProgram

namespace Program

def finalValue (E : Environment) (m : ℕ) (_ : Unit) : ℝ≥0∞ :=
  (m : ℝ≥0∞) * regretGap E (0,0)

end Program

end BilateralProfitRegular


