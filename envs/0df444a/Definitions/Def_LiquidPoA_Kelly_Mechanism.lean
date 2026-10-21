-- Prove2me | Definitions.Def_LiquidPoA_Kelly_Mechanism
-- name    : LiquidPoA_Kelly_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:27.385641+00:00
-- url     : https://prove2.me/theorems/8905a53f-7130-434d-9cc4-42bd103dac40
-- title:
--   Section 2, pp. 4–5 — resource allocation mechanisms and signal vectors
-- statement:
--   A single divisible resource of unit size is shared by $n$ users. Each user $i$ submits a **signal** $s_i\ge 0$; write $s=(s_1,\dots,s_n)\in\mathbb R^n_{\ge0}$, and $(y,s_{-i})$ for the vector in which user $i$'s signal is replaced by $y$. An **allocation** is a vector $d\in\mathcal Q\cup\{\mathbf 0\}$, where $\mathcal Q=\{d\in[0,1]^n:\sum_i d_i=1\}$. A **mechanism** $M$ consists of an allocation function $g^M:\mathbb R^n_{\ge0}\to\mathcal Q\cup\{\mathbf 0\}$ and a payment function $p^M:\mathbb R^n_{\ge0}\to\mathbb R^n_{\ge0}$. Let
--
--   $$
--   \mathbb X_n=\{s\in\mathbb R^n_{\ge0}:\ s_i>0\text{ and }s_j>0\text{ for some }i\ne j\}.
--   $$
--
--   A **resource allocation mechanism** is a mechanism with the properties of §2 (pp. 4–5) and footnote 5 (p. 9):
--
--   1. $g^M(s)\in\mathcal Q\cup\{\mathbf 0\}$ and $p^M(s)\ge 0$ for every signal vector $s$;
--   2. **anonymity**: permuting the input signals permutes the allocation and the payments in the same way;
--   3. a user with signal $0$ receives nothing and pays nothing;
--   4. $g^M_i(y,\mathbf 0_{-i})=1$ for every $y>0$ (a sole positive bidder receives the whole resource);
--   5. $y\mapsto g^M_i(y,s_{-i})$ is strictly increasing on $[0,\infty)$ whenever some other user has a positive signal, and $y\mapsto p^M_i(y,s_{-i})$ is strictly increasing on $[0,\infty)$ for every $s_{-i}$;
--   6. both functions of $y$ are differentiable on $[0,\infty)$ when $s_{-i}\ne\mathbf 0$, and on $(0,\infty)$ when $s_{-i}=\mathbf 0$;
--   7. (footnote 5) $\partial g^M_i(y,s_{-i})/\partial y\,|_{y=s_i}>0$ for every $s\in\mathbb X_n$ and every user $i$;
--   8. (p. 5) the payment $y\mapsto p^M_i(y,\mathbf 0_{-i})$ of a user deviating alone from the zero vector is continuous at $y=0$, where it equals $0$.
--
--   These are the mechanism axioms under which the paper's structural lemmas (Lemmas 4.1–4.3) are stated.
--
--   **Formalization Note** Users are indexed by `Fin n` (the paper's user 1 is index 0). The mechanism's functions are total on real vectors; the axioms only constrain nonnegative signal vectors. "Increasing" is read as strictly increasing: the paper uses "monotone non-decreasing" for the weak notion (valuations, p. 5), and with merely non-decreasing payments Lemma 4.2 fails (a mechanism charging nothing has ratio (6) equal to $0/0$). The p. 6 convention that pay-your-signal mechanisms charge nothing unless two signals are positive conflicts with property 5 and is not adopted. Derivatives in the own signal are taken within $[0,\infty)$, hence one-sided at $y=0$. Footnote 5 is an axiom, since $\lambda^M_i(s)$ divides by this derivative. Property 8 is the "continuity of the payment function" that p. 5 invokes to rule out the zero signal vector as an equilibrium; it is not implied by properties 1–7 (differentiability is waived at $\mathbf 0$), and without it a mechanism whose lone-bidder payment jumps at $0$ has $\mathbf 0$ as an equilibrium with zero liquid welfare, which makes Lemma 4.2 false.
-- source:
--   Caragiannis, Voudouris, The efficiency of resource allocation mechanisms for budget-constrained users, arXiv:1707.03551v3, pp. 4–5, §2 and p. 9, footnote 5

import Mathlib

namespace LiquidPoA.Kelly

open Set Finset

/-- A nonnegative signal vector for the `n` players of Section 2. -/
def IsSignal {n : ℕ} (s : Fin n → ℝ) : Prop := ∀ i, 0 ≤ s i

/-- The simplex of unit allocations, together with the zero allocation. -/
def IsAllocation {n : ℕ} (d : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ d i) ∧ ((∑ i, d i = 1) ∨ ∀ i, d i = 0)

/-- An allocation and payment rule for a single divisible resource. -/
structure Mechanism (n : ℕ) where
  alloc : (Fin n → ℝ) → Fin n → ℝ
  pay : (Fin n → ℝ) → Fin n → ℝ

/-- Own-signal allocation with the other players' signals fixed. -/
def allocIn {n : ℕ} (M : Mechanism n) (s : Fin n → ℝ) (i : Fin n) : ℝ → ℝ :=
  fun y => M.alloc (Function.update s i y) i

/-- Own-signal payment with the other players' signals fixed. -/
def payIn {n : ℕ} (M : Mechanism n) (s : Fin n → ℝ) (i : Fin n) : ℝ → ℝ :=
  fun y => M.pay (Function.update s i y) i

/-- The signal vectors in `𝕏ₙ`, having two distinct positive coordinates. -/
def InX {n : ℕ} (s : Fin n → ℝ) : Prop :=
  IsSignal s ∧ ∃ i j, i ≠ j ∧ 0 < s i ∧ 0 < s j

/-- Section 2's mechanism properties (pp. 4–5) and the strict derivative condition of footnote 5
(p. 9). "Increasing" is strict: the paper says "monotone non-decreasing" when it means the weak
notion (p. 5, valuations). The only exception the page makes is the allocation `g_i(y, 0_{-i}) = 1`
(`alone`), so payments are strictly increasing in the own signal for every `s_{-i}`.
Differentiability fails only at the all-zero vector (`diff_alone` is on `Ioi 0`); the payment of a
sole deviator from the zero vector is continuous at `0` (`pay_cont_zero`), as p. 5 uses: "due to the
continuity of the payment function and the fact that it is equal to zero on input the signal vector 0". -/
structure IsRAMechanism {n : ℕ} (M : Mechanism n) : Prop where
  alloc_mem : ∀ s, IsSignal s → IsAllocation (M.alloc s)
  pay_nonneg : ∀ s, IsSignal s → ∀ i, 0 ≤ M.pay s i
  anon_alloc : ∀ (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ),
    IsSignal s → M.alloc (s ∘ σ) = M.alloc s ∘ σ
  anon_pay : ∀ (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ),
    IsSignal s → M.pay (s ∘ σ) = M.pay s ∘ σ
  zero_sig : ∀ s, IsSignal s → ∀ i, s i = 0 →
    M.alloc s i = 0 ∧ M.pay s i = 0
  alone : ∀ i (y : ℝ), 0 < y → M.alloc (Function.update 0 i y) i = 1
  alloc_incr : ∀ s, IsSignal s → ∀ i, (∃ j, j ≠ i ∧ 0 < s j) →
    StrictMonoOn (allocIn M s i) (Ici 0)
  pay_incr : ∀ s, IsSignal s → ∀ i,
    StrictMonoOn (payIn M s i) (Ici 0)
  pay_cont_zero : ∀ i, ContinuousWithinAt (payIn M 0 i) (Ici 0) 0
  diff : ∀ s, IsSignal s → ∀ i, (∃ j, j ≠ i ∧ 0 < s j) →
    DifferentiableOn ℝ (allocIn M s i) (Ici 0) ∧
    DifferentiableOn ℝ (payIn M s i) (Ici 0)
  diff_alone : ∀ s, IsSignal s → ∀ i, (∀ j, j ≠ i → s j = 0) →
    DifferentiableOn ℝ (allocIn M s i) (Ioi 0) ∧
    DifferentiableOn ℝ (payIn M s i) (Ioi 0)
  deriv_pos : ∀ s, InX s → ∀ i,
    0 < derivWithin (allocIn M s i) (Ici 0) (s i)

end LiquidPoA.Kelly


