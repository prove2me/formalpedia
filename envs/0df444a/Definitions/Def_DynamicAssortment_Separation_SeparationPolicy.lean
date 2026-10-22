-- Prove2me | Definitions.Def_DynamicAssortment_Separation_SeparationPolicy
-- name    : DynamicAssortment_Separation_SeparationPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T10:23:31.98928+00:00
-- url     : https://prove2.me/theorems/7e059faf-f0dd-4461-9d56-f3fc4f5a8b68
-- title:
--   Test assortments A_j, the frequency estimator (4), the estimate μ̂_t and Algorithm 1 (the separation-based policy π₁ = π(κ₁, T, w))
-- statement:
--   1. **Test assortments.** There are $|\mathcal A|=\lceil N/C\rceil$ of them (`numTests`), and $A_j=\{(j-1)C+1,\dots,\min\{jC,N\}\}$ (`testAssortment`, 0-based: product indices in $[jC,(j+1)C)$). Each product lies in exactly one test assortment, the one with index `blockOf C i` $=\lfloor i/C\rfloor$.
--   2. **Estimator (4).** Suppose customers $u<t$ were offered $S_u$ and made purchases $h_u$. Write $T^A(t)=\sum_{u<t}\mathbf 1\{S_u=A\}$ (`visitCount`) and $Z_i^u=\mathbf 1\{h_u=i\}$ (`purchased`). The estimate is
--   $$\hat p_{i,t}(A)=\frac{\sum_{u<t} Z_i^u\,\mathbf 1\{S_u=A\}}{\sum_{u<t}\mathbf 1\{S_u=A\}}\quad (i\in A),\qquad \hat p_{i,t}(A)=0\quad(i\notin A)$$
--   (`freqEstimate`). The mean-utility estimate is $\hat\mu_{t,i}=\big(\eta(\hat p_t(A_j))\big)_i$, where $A_j$ is the test assortment containing $i$ and $\eta$ (`eta A`) is the inverse of $p(A,\cdot)$ from Assumption 1 (`muHat`).
--   3. **Algorithm 1.** Given $\kappa_1>0$ and the horizon $T$, put $n_0=\lceil\kappa_1\log T\rceil$.
--      - *Exploration:* the test assortments are offered sequentially, each to $n_0$ consecutive customers. Customer $t<|\mathcal A|\,n_0$ (0-based) is offered $A_{\lfloor t/n_0\rfloor}$.
--      - *Exploitation:* every later customer $t$ is offered $S^*(\hat\mu_t)$, where $\hat\mu_t$ is computed by (4) from all earlier customers $u<t$.
--
--      `separationAssortment` computes $S_t$ recursively along a purchase sequence, and `algorithm1 C opt eta κ₁ T` is the resulting policy for horizon $T$.
--
--   This is the separation-based policy of Sauré and Zeevi, the object of their Theorem 2.
--
--   **Formalization Note** The paper writes $\lceil n\rceil$ as "the smallest integer larger than $n$"; the ceiling is used, which is what $|\mathcal A|=\lceil N/C\rceil$ requires. $\lceil\kappa_1\log T\rceil$ is `Nat.ceil`, and $\log$ is the natural logarithm with $\log 0=\log 1=0$. Step 2 of Algorithm 1 is read per customer: $\hat\mu_t$ is recomputed for every exploitation customer $t$, from all earlier offers of each test assortment, as the per-$t$ estimator (4) prescribes. When a test assortment has not been offered yet, Lean's $x/0=0$ fills in the undefined ratio; under Algorithm 1 this happens only when $n_0=0$, i.e. $T\le1$. The policy depends on $T$, as $\pi(\kappa_1,T,w)$ does.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, p. 394, §5.1: test assortments 𝒜, estimator (4), μ̂_{t,i}, Algorithm 1

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel
import Definitions.Def_DynamicAssortment_Separation_History

namespace DynamicAssortment.Separation

/-- Number of test assortments `|𝒜| = ⌈N / C⌉` (computed in `ℕ`). -/
def numTests (N C : ℕ) : ℕ := (N + C - 1) / C

/-- Test assortment `A_j` (p. 394), 0-based: the products with (0-based) index in
`[j C, (j + 1) C)`, i.e. the paper's `A_{j+1} = {jC + 1, …, min{(j+1)C, N}}`. -/
def testAssortment (N C : ℕ) (j : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i : Fin N => j * C ≤ i.val ∧ i.val < (j + 1) * C)

/-- Index of the unique test assortment containing product `i`. -/
def blockOf {N : ℕ} (C : ℕ) (i : Fin N) : ℕ := i.val / C

/-- `T^A(t) = ∑_{u < t} 1{S_u = A}`: how many of the customers before `t` were offered `A`. -/
def visitCount {N : ℕ} (S : ℕ → Finset (Fin N)) (A : Finset (Fin N)) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun u => S u = A)).card

/-- Purchase indicator `Z_i^u`. -/
def purchased {N : ℕ} (h : ℕ → Option (Fin N)) (u : ℕ) (i : Fin N) : ℝ :=
  if h u = some i then 1 else 0

/-- Estimator (4) (p. 394): `p̂_{i,t}(A) = ∑_{u<t} Z_i^u 1{S_u = A} / ∑_{u<t} 1{S_u = A}` for
`i ∈ A`, and `0` otherwise (Lean's `x / 0 = 0` when `A` was never offered). -/
noncomputable def freqEstimate {N : ℕ} (S : ℕ → Finset (Fin N)) (h : ℕ → Option (Fin N))
    (A : Finset (Fin N)) (t : ℕ) : Fin N → ℝ :=
  fun i => if i ∈ A then
    (∑ u ∈ Finset.range t, purchased h u i * (if S u = A then (1 : ℝ) else 0)) /
      (visitCount S A t : ℝ)
  else 0

/-- Mean-utility estimate `μ̂_{t,i} = (η(p̂_t(A_j)))_i` with `A_j` the test assortment
containing `i` (p. 394); `eta A` is the inverse of `p(A, ·)` from Assumption 1. -/
noncomputable def muHat {N : ℕ} (C : ℕ) (eta : Finset (Fin N) → (Fin N → ℝ) → (Fin N → ℝ))
    (S : ℕ → Finset (Fin N)) (h : ℕ → Option (Fin N)) (t : ℕ) : Fin N → ℝ :=
  fun i => eta (testAssortment N C (blockOf C i))
    (freqEstimate S h (testAssortment N C (blockOf C i)) t) i

/-- Assortments chosen by Algorithm 1 along the purchase sequence `h`, with exploration length
`n₀` per test assortment. Customer `t < |𝒜| n₀` gets `A_{⌊t / n₀⌋}` (the test assortments are
offered sequentially, each to `n₀` consecutive customers); every later customer `t` gets
`S*(μ̂_t)`, with `μ̂_t` computed by (4) from all customers `u < t`. -/
noncomputable def separationAssortment {N : ℕ} (C : ℕ) (opt : (Fin N → ℝ) → Finset (Fin N))
    (eta : Finset (Fin N) → (Fin N → ℝ) → (Fin N → ℝ)) (n₀ : ℕ) (h : ℕ → Option (Fin N))
    (t : ℕ) : Finset (Fin N) :=
  if t < numTests N C * n₀ then testAssortment N C (t / n₀)
  else opt (muHat C eta
    (fun u => if _hu : u < t then separationAssortment C opt eta n₀ h u else ∅) h t)
termination_by t

/-- Algorithm 1, `π_1 = π(κ_1, T, w)` (p. 394): each test assortment is offered to
`⌈κ_1 log T⌉` customers, then `S*(μ̂_t)` to every remaining customer. -/
noncomputable def algorithm1 {N : ℕ} (C : ℕ) (opt : (Fin N → ℝ) → Finset (Fin N))
    (eta : Finset (Fin N) → (Fin N → ℝ) → (Fin N → ℝ)) (κ₁ : ℝ) (T : ℕ) : Policy N T :=
  fun t pre => separationAssortment C opt eta ⌈κ₁ * Real.log T⌉₊
    (fun u => if hu : u < t.val then pre ⟨u, hu⟩ else none) t.val

end DynamicAssortment.Separation


