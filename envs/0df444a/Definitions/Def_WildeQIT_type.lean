-- Prove2me | Definitions.Def_WildeQIT_type
-- name    : WildeQIT_type
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:36:08.437728+00:00
-- url     : https://prove2.me/theorems/cd4536c5-d3f2-4e62-b7a0-789d480912b3
-- title:
--   Types, type classes and typical types (Definitions 14.7.1, 14.7.3, 14.7.4)
-- statement:
--   **Definition 14.7.1 (Type).** The type or empirical distribution $t_{x^n}$ of a sequence $x^n$ is the probability mass function with $t_{x^n}(x) \equiv \frac{1}{n}N(x|x^n)$, where $N(x|x^n)$ is the number of occurrences of $x$ in $x^n$.
--
--   **Definition 14.7.3 (Type class).** $T_t^{X^n} \equiv \{x^n\in\mathcal{X}^n : t_{x^n} = t\}$, the set of all sequences of length $n$ and type $t$.
--
--   **Definition 14.7.4 (Typical type).** For $\delta>0$, $\tau_\delta$ is the set of all typical types (of length-$n$ sequences) with maximum deviation $\delta$ from the true distribution: $\tau_\delta \equiv \{t : \forall x,\ |t(x)-p_X(x)|\le\delta \text{ if } p_X(x)>0 \text{ else } t(x)=0\}$.
--
--   **Formalization Note.** `typeOf x : α → ℝ` is $t_{x^n}$ (for $n=0$ it is the zero function, by $a/0 = 0$); `typeDist x : FinDist α` packages the type of a sequence of positive length as a probability distribution; `typeClass n t` is $T_t^{X^n}$; `typesOfLength α n` is the set of all types of length-$n$ sequences and `typicalTypes p n δ` is $\tau_\delta$.
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Definition 14.7.1, §Types and Strong Typicality (roster-items.csv line 25820); with Definition 14.7.3 (Type Class, line 25859) and Definition 14.7.4 (Typical Type, line 25910).

import Definitions.Def_WildeQIT_iid
import Mathlib.Algebra.BigOperators.Field

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §14.7 (Types and strong typicality):
Definition 14.7.1 (Type): the type or empirical distribution of `xⁿ` is `t_{xⁿ}(x) ≡ N(x|xⁿ)/n`;
Definition 14.7.3 (Type class): `T_t^{Xⁿ} ≡ { xⁿ ∈ 𝒳ⁿ : t_{xⁿ} = t }`;
Definition 14.7.4 (Typical type): for `δ > 0`, `τ_δ ≡ { t : ∀ x, |t(x) − p_X(x)| ≤ δ if p_X(x) > 0
else t(x) = 0 }` (over the types of length-`n` sequences).
-/

namespace WildeQIT

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Definition 14.7.1. The type (empirical distribution) `t_{xⁿ}(a) = N(a|xⁿ)/n` of a sequence. -/
noncomputable def typeOf {n : ℕ} (x : Fin n → α) : α → ℝ := fun a => (seqCount x a : ℝ) / n

/-- The type of a sequence of positive length `n + 1`, as a probability distribution. -/
noncomputable def typeDist {n : ℕ} (x : Fin (n + 1) → α) : FinDist α where
  prob := typeOf x
  nonneg a := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  sum_eq_one := by
    unfold typeOf seqCount
    rw [← Finset.sum_div, div_eq_one_iff_eq (by positivity)]
    have h : ∑ a, ((Finset.univ.filter fun i => x i = a).card : ℝ) =
        ((Finset.univ : Finset (Fin (n + 1))).card : ℝ) := by
      rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (f := x) (t := Finset.univ)
        (fun i _ => Finset.mem_univ (x i))]
    rw [h]
    simp

@[simp] theorem typeDist_prob {n : ℕ} (x : Fin (n + 1) → α) : (typeDist x).prob = typeOf x := rfl

/-- Definition 14.7.3. The type class `T_t^{Xⁿ}` of a type `t`: all length-`n` sequences of type `t`. -/
noncomputable def typeClass (n : ℕ) (t : α → ℝ) : Finset (Fin n → α) :=
  Finset.univ.filter fun x => typeOf x = t

/-- The set of all types of length-`n` sequences. -/
noncomputable def typesOfLength (α : Type) [Fintype α] [DecidableEq α] (n : ℕ) : Finset (α → ℝ) :=
  Finset.univ.image (typeOf (α := α) (n := n))

/-- Definition 14.7.4. The set `τ_δ` of typical types of length-`n` sequences for the distribution
`p`: `|t(a) − p(a)| ≤ δ` whenever `p(a) > 0`, and `t(a) = 0` otherwise. -/
noncomputable def typicalTypes (p : FinDist α) (n : ℕ) (δ : ℝ) : Finset (α → ℝ) :=
  (typesOfLength α n).filter fun t => ∀ a, if 0 < p.prob a then |t a - p.prob a| ≤ δ else t a = 0

end WildeQIT


