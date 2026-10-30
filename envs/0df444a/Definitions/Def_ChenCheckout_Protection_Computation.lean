-- Prove2me | Definitions.Def_ChenCheckout_Protection_Computation
-- name    : ChenCheckout_Protection_Computation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T06:47:52.419986+00:00
-- url     : https://prove2.me/theorems/9920c1f2-2b64-47c8-9fec-650e9e7acf38
-- title:
--   Finite randomized arithmetic computations with execution costs
-- statement:
--   An operational computation returns a value, flips a fresh Bernoulli coin, or performs a charged block of deterministic work. Sequential composition and independent repetition expand these operations without enumerating branches during execution. Coin probabilities are real; clipping to [0,1] totalizes malformed inputs. Exact expectation is the finite weighted sum over leaves; event probability is the expectation of its indicator. The measure semantics is the corresponding finite mixture of Dirac measures on any specified measurable output space (all subsets may be used for discrete outputs). Worst execution cost is the maximum branch cost plus charged work and random-draw costs. All quantifies over every branch, including probability-zero ones. Categorical sampling uses conditional probabilities from a list of nonnegative absolute masses and assigns remaining mass to no purchase. No theorem guarantee is a field of this syntax.
-- source:
--   Chen, Ma, Simchi-Levi and Xin (2024), Mathematics of Operations Research 49(1), 297–325, https://doi.org/10.1287/moor.2023.1357, §§3.1–3.4, printed pp. 307–310 / PDF 11–14; arithmetic/sampling semantics for Procedures 1–3

import Mathlib

namespace ChenCheckout.Protection

/-- Finite arithmetic/oracle computation with fresh Bernoulli draws. `work` charges
arithmetic, comparison, indexing, probability evaluation and oracle operations.
The tree is operational syntax, not an instruction to enumerate its branches. -/
inductive Computation (α : Type) where
  | ret : α → Computation α
  | flip : ℝ → Computation α → Computation α → Computation α
  | work : ℕ → Computation α → Computation α

noncomputable section

namespace Computation

def probability (p : ℝ) : ℝ := max 0 (min 1 p)

def bind {α β : Type} : Computation α → (α → Computation β) → Computation β
  | .ret a, f => f a
  | .flip p a b, f => .flip p (bind a f) (bind b f)
  | .work c a, f => .work c (bind a f)

def map {α β : Type} (f : α → β) (c : Computation α) : Computation β :=
  bind c (fun a => .ret (f a))

/-- Finite expectations: all probabilities are real, with no grid restriction. -/
def expect {α : Type} : Computation α → (α → ℝ) → ℝ
  | .ret a, f => f a
  | .flip p a b, f => probability p * expect a f + (1 - probability p) * expect b f
  | .work _ a, f => expect a f

def prob {α : Type} (c : Computation α) (E : α → Prop) : ℝ := by
  classical
  exact expect c (fun a => if E a then 1 else 0)

/-- Worst execution cost, including one operation per random draw. -/
def cost {α : Type} : Computation α → ℕ
  | .ret _ => 0
  | .flip _ a b => 1 + max (cost a) (cost b)
  | .work c a => c + cost a

/-- All operational branches, including probability-zero branches. -/
def All {α : Type} : Computation α → (α → Prop) → Prop
  | .ret a, P => P a
  | .flip _ a b, P => All a P ∧ All b P
  | .work _ a, P => All a P

/-- Measure semantics on any chosen measurable output space. There are finitely
many leaves, so all real leaf rewards are integrable on the discrete output space. -/
def law {α : Type} [MeasurableSpace α] : Computation α → MeasureTheory.Measure α
  | .ret a => MeasureTheory.Measure.dirac a
  | .flip p a b => ENNReal.ofReal (probability p) • law a +
      ENNReal.ofReal (1 - probability p) • law b
  | .work _ a => law a

/-- Independent repeats, by fresh draws at each recursive occurrence. -/
def repetitions {α : Type} (c : Computation α) : ℕ → Computation (List α)
  | 0 => .ret []
  | m + 1 => bind c (fun a => map (List.cons a) (repetitions c m))

/-- Categorical draw from absolute masses. The residual outcome is `none`.
For nonnegative masses summing to at most the remaining mass, clipping is inactive. -/
def categorical {α : Type} : List (α × ℝ) → ℝ → Computation (Option α)
  | [], _ => .ret none
  | (a,p) :: rest, remaining =>
      .work 3 (.flip (p / remaining) (.ret (some a))
        (categorical rest (remaining - p)))

end Computation
end
end ChenCheckout.Protection


