-- Prove2me | Definitions.Def_RelaxedIndexability_Supplement_kStepReward
-- name    : RelaxedIndexability_Supplement_kStepReward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:02:45.042657+00:00
-- url     : https://prove2.me/theorems/8ed8a347-1c05-58c8-9541-38c7f01c0e43
-- title:
--   The $k$-step reward function $h(k)=\omega\mathbf P^kB'$ and its three forms
-- statement:
--   Fix an arm with transition matrix $\mathbf P$, reward vector $B$ and a belief $\omega$. The **$k$-step reward function** is the expected immediate reward after $k$ passive slots,
--
--   $$
--   h(k)=\mathcal T^k(\omega)B'=\omega\mathbf P^kB',\qquad k\ge0.
--   $$
--
--   Lemma EC.1 shows that for a three-state chain $h$ has one of three forms:
--
--   1. $h(k)=a_1b_1^k+a_2b_2^k+c$ with $|b_1|,|b_2|<1$;
--   2. $h(k)=ab^k+ckb^{k-1}+d$ with $|b|<1$;
--   3. $h(k)=a'A^k\sin(k\theta+b')+c'$ with $a'\ge0$, $A\in(0,1)$, $\theta\in(0,2\pi)$, $b'\in[0,2\pi)$.
--
--   The forms are predicates on a sequence and its parameters. Theorem EC.1 computes the first crossing time from them.
--
--   **Formalization Note** $0^0=1$, so form 1 allows zero bases. In form 2 the middle term is $0$ at $k=0$.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (EC.45), p.ec12; Lemma EC.1, pp.ec12–ec13

import Mathlib

open Matrix

namespace RelaxedIndexability.Supplement

variable {K : ℕ}

/-- **The `k`-step reward function `h(k) = T^k(ω) B′ = ω P^k B′`, `k ≥ 0`**
(Liu, arXiv:2107.11939v4, (EC.45), p.ec12).

**Formalization Note.** `T^k(ω)` is `ω ᵥ* P ^ k`, as in `RelaxedIndexability.crossTime`. -/
noncomputable def kStepReward (P : Matrix (Fin K) (Fin K) ℝ) (B ω : Fin K → ℝ) (k : ℕ) : ℝ :=
  (ω ᵥ* P ^ k) ⬝ᵥ B

/-- **Form 1 of Lemma EC.1** (p.ec12): `h(k) = a₁ b₁^k + a₂ b₂^k + c` with `|b₁|, |b₂| < 1`.

**Formalization Note.** `0^0 = 1`. `b₁ = b₂` and zero coefficients or bases are allowed. -/
def IsDiagonalizableForm (h : ℕ → ℝ) (a₁ b₁ a₂ b₂ c : ℝ) : Prop :=
  |b₁| < 1 ∧ |b₂| < 1 ∧ ∀ k : ℕ, h k = a₁ * b₁ ^ k + a₂ * b₂ ^ k + c

/-- **Form 2 of Lemma EC.1** (p.ec12): `h(k) = a b^k + c k b^(k−1) + d` with `|b| < 1`.

**Formalization Note.** At `k = 0` the middle term is `0`, because of its factor `k`. -/
def IsJordanForm (h : ℕ → ℝ) (a b c d : ℝ) : Prop :=
  |b| < 1 ∧ ∀ k : ℕ, h k = a * b ^ k + c * (k : ℝ) * b ^ (k - 1) + d

/-- **Form 3 of Lemma EC.1** (p.ec13): `h(k) = a′ A^k sin(kθ + b′) + c′` with `a′ ≥ 0`,
`A ∈ (0, 1)`, `θ ∈ (0, 2π)`, `b′ ∈ [0, 2π)`. -/
def IsComplexForm (h : ℕ → ℝ) (a' A θ b' c' : ℝ) : Prop :=
  0 ≤ a' ∧ A ∈ Set.Ioo 0 1 ∧ θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ b' ∈ Set.Ico 0 (2 * Real.pi) ∧
    ∀ k : ℕ, h k = a' * A ^ k * Real.sin ((k : ℝ) * θ + b') + c'

end RelaxedIndexability.Supplement


