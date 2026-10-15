-- Prove2me | Definitions.Def_SecretaryAdvice_Binary_LP
-- name    : SecretaryAdvice_Binary_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:59.143055+00:00
-- url     : https://prove2.me/theorems/47acfe9b-f3f1-4bc4-b61e-47d19af00a57
-- title:
--   §6 and Appendix C — binary-classifier primal and dual LP and greedy vector
-- statement:
--   For rounds $i=1,\ldots,n$ and signals $s\in\{Y,N\}$, the binary-classifier factor-revealing LP uses the reward coefficients $a(i,Y)=p/n$ and $a(i,N)=(1-p)/n$. Its primal variables $z_i^s$ lie in $[0,1]$ and satisfy
--
--   $$z_i^s\leq 1-\sum_{j<i}\frac{(1-p')z_j^Y+p'z_j^N}{j}.$$
--
--   Its dual variables $u_i^s$ are nonnegative and satisfy $u_i^s+\widehat c(i,s)\sum_{j>i}(u_j^Y+u_j^N)\geq a(i,s)$, where $\widehat c(i,Y)=(1-p')/i$ and $\widehat c(i,N)=p'/i$. The dual minimizes $\sum_i(u_i^Y+u_i^N)$. Equation (10) defines a vector by backward induction: $u_i^s=\max\{0,a(i,s)-\widehat c(i,s)\sum_{j>i}(u_j^Y+u_j^N)\}$.
--
--   The LP and its greedy dual vector are the objects used to establish optimality of a threshold policy.
--
--   **Formalization Note** LP rounds are natural numbers in $[1,n]$; every theorem uses positive denominators. The backward fold begins at round $n$ and writes each earlier round after all later coordinates are available. The definitions have total values outside $[1,n]$, but the LP constraints quantify only over that range.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 20, §6 LP display; pp. 28–29, Appendix C, equation (10)

import Mathlib
import Definitions.Def_SecretaryAdvice_Binary_Setting

namespace SecretaryAdvice.Binary

/-- The binary model's objective coefficient `a(i,s)` in §6. -/
noncomputable def a (n : ℕ) (p : ℝ) (s : Bool) : ℝ :=
  (if s then p else 1 - p) / (n : ℝ)

/-- The binary model's dual coefficient `ĉ(i,s)` in Appendix C. Only `1 ≤ i ≤ n`
is used in the LP; the value at zero is Lean's total division convention. -/
noncomputable def chat (i : ℕ) (p' : ℝ) (s : Bool) : ℝ :=
  (if s then 1 - p' else p') / (i : ℝ)

/-- The primal LP on rounds `1,...,n`, with both signals at every round. -/
def PrimalFeasible (n : ℕ) (p' : ℝ) (z : ℕ → Bool → ℝ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n → ∀ s,
    0 ≤ z i s ∧ z i s ≤ 1 ∧
    z i s ≤ 1 - ∑ j ∈ Finset.Ico 1 i,
      ((1 - p') * z j true + p' * z j false) / (j : ℝ)

/-- The §6 primal objective. -/
noncomputable def primalValue (n : ℕ) (p : ℝ) (z : ℕ → Bool → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, (p * z i true + (1 - p) * z i false) / (n : ℝ)

/-- The §6 dual LP, including nonnegativity. -/
def DualFeasible (n : ℕ) (p p' : ℝ) (u : ℕ → Bool → ℝ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n → ∀ s,
    0 ≤ u i s ∧
    a n p s ≤ u i s + chat i p' s *
      ∑ j ∈ Finset.Ioc i n, (u j true + u j false)

/-- The §6 dual objective. -/
noncomputable def dualValue (n : ℕ) (u : ℕ → Bool → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, (u i true + u i false)

/-- One backward-induction update at one round. The fold processes rounds `n,n-1,...,1`;
`u` already contains the later rounds. -/
noncomputable def greedyStep (n : ℕ) (p p' : ℝ) (u : ℕ → Bool → ℝ) (idx : ℕ) :
    ℕ → Bool → ℝ :=
  let i := idx + 1
  let tail := ∑ j ∈ Finset.Ioc i n, (u j true + u j false)
  fun j s => if j = i then max 0 (a n p s - chat i p' s * tail) else u j s

/-- Equation (10), the greedy dual vector built from the last round backwards. -/
noncomputable def greedy (n : ℕ) (p p' : ℝ) : ℕ → Bool → ℝ :=
  (List.range n).reverse.foldl (greedyStep n p p') (fun _ _ => 0)

end SecretaryAdvice.Binary


