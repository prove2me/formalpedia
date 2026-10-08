-- Prove2me | Definitions.Def_KendallQueues_GIMs_Model
-- name    : KendallQueues_GIMs_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:29:41.655756+00:00
-- url     : https://prove2.me/theorems/73f69d7b-6a04-4340-93d5-2cbf1712ad6a
-- title:
--   §6 — the GI/M/s imbedded chain: the matrix (8)–(14), F(λ) (17), ρ = b/(sa), the trial vector (15) and the laws of Q and w
-- statement:
--   These are the objects of §§6–8 of Kendall (1953) for the queueing system GI/M/s. Customers arrive with independent inter-arrival times of law $A$ on $[0,\infty)$ and mean $a$, $0<a<\infty$; there are $s\ge1$ servers, first come first served; the service times are independent of one another and of the input, negative-exponential with mean $b$, $0<b<\infty$. The state of the **imbedded chain** at an arrival epoch is the number $i\in\{0,1,2,\dots\}$ of persons found ahead (waiting or being served) by the newly arrived customer.
--
--   1. **Death-process probabilities** (9)–(10). For $0\le n\le m$,
--   $$[n\mid m;u]=\binom{m}{n}\bigl(1-e^{-u/b}\bigr)^n e^{-(m-n)u/b},\qquad [n\mid m]=\int_0^\infty [n\mid m;u]\,dA(u).$$
--   2. **The probabilities of block B** (11)–(12). For $m\ge1$,
--   $$\{n\mid s;m;u\}=\frac{1}{(m-1)!}\Bigl(\frac{s}{b}\Bigr)^m\int_0^u e^{-sU/b}U^{m-1}[n\mid s;u-U]\,dU,\qquad \{n\mid s;m\}=\int_0^\infty\{n\mid s;m;u\}\,dA(u).$$
--   3. **Poisson probabilities** (13)–(14):
--   $$(n\mid s)=\int_0^\infty e^{-su/b}\frac{(su/b)^n}{n!}\,dA(u).$$
--   4. **The transition matrix** (8) $P=[p_{ij}]$, $i,j\ge0$, partitioned into a block $\mathbf A$ (rows and columns $0,\dots,s-1$), a block $\mathbf B$ (rows $i\ge s$, columns $j<s$) and a block $\mathbf C$ (all rows, columns $j\ge s$):
--   $$p_{ij}=\begin{cases}(i+1-j\mid s) & j\ge s,\ j\le i+1,\\ [\,i+1-j\mid i+1\,] & i<s,\ j<s,\ j\le i+1,\\ \{s-j\mid s;\,i-s+1\} & i\ge s,\ j<s,\\ 0 & j>i+1.\end{cases}$$
--   5. **The function** (17) $F(x)=\int_0^\infty e^{-(1-x)su/b}\,dA(u)$ and the **relative traffic intensity** $\rho=b/(sa)$.
--   6. **The trial vector** (15) $x=[\mu_0,\mu_1,\dots,\mu_{s-2},1,\lambda,\lambda^2,\dots]$, the $\mu$-terms being absent when $s=1$.
--   7. **The laws of $Q$ and $w$.** If $\pi$ is the law of the number $i$ found ahead, the queue size $Q=\max(i-s,0)$ of (18) has $\Pr(Q=0)=\sum_{i\le s}\pi_i$ and $\Pr(Q=n)=\pi_{s+n}$ for $n\ge1$. Given $i$, the waiting time $w$ is the sum of $k=\max(i-s+1,0)$ independent variables each distributed like $\tfrac12 b\chi^2_2/s$, i.e. exponential with mean $b/s$, so
--   $$\Pr(w\le t)=\sum_{i\ge0}\pi_i\,E_{\max(i-s+1,0)}(t),$$
--   where $E_k$ is the distribution function of the Erlang law with $k$ phases of rate $s/b$ and $E_0\equiv1$ (an atom at $0$).
--
--   Every statement of the mission is written with these objects.
--
--   **Formalization Note** The queue process itself is not formalized: the chain is given by its transition matrix (8)–(14), and $w$ by the Erlang mixture of p. 349; the paper derives both by a modelling argument ("a little consideration will show", p. 345). States are $0$-based. $(n\mid s)$ is the published `serviceProb A (s/b) n` (`paren`), and $E_k$ is the published `completionsCDF (s/b) k`. Natural-number subtractions in the matrix are taken only where the page's index is nonnegative; in `waitCDF` the truncated subtraction `i + 1 - s` is exactly $\max(i-s+1,0)$. The function `deathProb` is used only with $n\le m$. A chain with this matrix is a `TransitionMatrix` `P` of the published vocabulary with `P.p = gimsMatrix s A b`; that the matrix is stochastic is a milestone of the mission, not part of the definition. The $\mu$'s of (15) are indexed by `Fin (s - 1)`.
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §2, pp. 339–340; §6, pp. 345–347, eqs. (8)–(14); §7, pp. 348–349, eqs. (15), (17), (18); p. 349 (law of w); p. 347 (ρ ≡ b/(sa))

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime

open MeasureTheory
open QueueingFundamentals.Foundations QueueingFundamentals.GM1

namespace KendallQueues.GIMs

/-- Eq. (9), Kendall (1953), p. 345: `[n | m; u]`, the probability that exactly `n` of `m`
customers in service conclude their service within time `u`, each service time being
negative-exponential with mean `b` (a simple death process with death rate `1/b` per head):
`[n | m; u] = C(m, n) (1 - e^{-u/b})^n e^{-(m-n)u/b}`.
It is used only with `n ≤ m`; for `n > m` the binomial coefficient is `0`. -/
noncomputable def deathProb (b : ℝ) (m n : ℕ) (u : ℝ) : ℝ :=
  (Nat.choose m n : ℝ) * (1 - Real.exp (-u / b)) ^ n * Real.exp (-((m - n : ℕ) : ℝ) * u / b)

/-- Eq. (10), p. 345: `[n | m] = ∫_0^∞ [n | m; u] dA(u)`. -/
noncomputable def bracket (A : Measure ℝ) (b : ℝ) (n m : ℕ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ), deathProb b m n u ∂A

/-- Eq. (11), p. 346: `{n | s; m; u} = 1/(m-1)! (s/b)^m ∫_0^u e^{-sU/b} U^{m-1} [n | s; u - U] dU`.
It is used only with `m ≥ 1`. -/
noncomputable def braceU (b : ℝ) (s n m : ℕ) (u : ℝ) : ℝ :=
  (1 / (Nat.factorial (m - 1) : ℝ)) * ((s : ℝ) / b) ^ m *
    ∫ U in (0 : ℝ)..u, Real.exp (-(s : ℝ) * U / b) * U ^ (m - 1) * deathProb b s n (u - U)

/-- Eq. (12), p. 346: `{n | s; m} = ∫_0^∞ {n | s; m; u} dA(u)`. -/
noncomputable def brace (A : Measure ℝ) (b : ℝ) (s n m : ℕ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ), braceU b s n m u ∂A

/-- Eqs. (13)–(14), pp. 346–347: `(n | s) = ∫_0^∞ e^{-su/b} (su/b)^n / n! dA(u)`, which is the
published `serviceProb A (s / b) n`. -/
noncomputable def paren (A : Measure ℝ) (b : ℝ) (s n : ℕ) : ℝ :=
  serviceProb A ((s : ℝ) / b) n

/-- The transition matrix (8) of the GI/M/s chain imbedded at arrival epochs, pp. 345–347,
on the states `0, 1, 2, …` (the number of customers found in the system by an arrival):
* block C (`j ≥ s`, all rows): `p_ij = (i + 1 - j | s)` if `j ≤ i + 1`, `0` otherwise;
* block A (`i < s`, `j < s`): `p_ij = [i + 1 - j | i + 1]` if `j ≤ i + 1`, `0` otherwise;
* block B (`i ≥ s`, `j < s`): `p_ij = {s - j | s; i - s + 1}`.
Every natural-number subtraction here is taken where the page's index is nonnegative. -/
noncomputable def gimsMatrix (s : ℕ) (A : Measure ℝ) (b : ℝ) (i j : ℕ) : ℝ :=
  if s ≤ j then
    (if j ≤ i + 1 then paren A b s (i + 1 - j) else 0)
  else if i < s then
    (if j ≤ i + 1 then bracket A b (i + 1 - j) (i + 1) else 0)
  else
    brace A b s (s - j) (i - s + 1)

/-- Eq. (17), p. 348: `F(x) = ∫_0^∞ e^{-(1-x) s u / b} dA(u)`. -/
noncomputable def F (s : ℕ) (A : Measure ℝ) (b : ℝ) (x : ℝ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ), Real.exp (-(1 - x) * s * u / b) ∂A

/-- §7, p. 347: the relative traffic intensity `ρ = b / (s a)`. -/
noncomputable def rho (s : ℕ) (a b : ℝ) : ℝ :=
  b / ((s : ℝ) * a)

/-- Eq. (15), p. 348: the trial vector `x = [μ_0, μ_1, …, μ_{s-2}, 1, λ, λ², …]`
(the `μ`-terms absent when `s = 1`); here `x` plays the role of `λ`. -/
noncomputable def trialVector (s : ℕ) (μ : Fin (s - 1) → ℝ) (x : ℝ) (k : ℕ) : ℝ :=
  if h : k < s - 1 then μ ⟨k, h⟩ else x ^ (k - (s - 1))

/-- Eq. (18), p. 349: the law of the queue size `Q = max(i - s, 0)` when the number found
ahead `i` has law `π`: `P(Q = 0) = ∑_{i ≤ s} π_i` and `P(Q = n) = π_{s+n}` for `n ≥ 1`. -/
noncomputable def queueLaw (s : ℕ) (π : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then ∑ i ∈ Finset.range (s + 1), π i else π (s + n)

/-- p. 349: the distribution function `P(w ≤ t)` of the waiting time `w` when the number found
ahead `i` has law `π`: given `i`, `w` is the sum of `k = max(i - s + 1, 0)` independent
variables each distributed like `½ b χ²₂ / s` (exponential with mean `b/s`), so
`P(w ≤ t) = ∑_i π_i E_k(t)` with `E_k` the Erlang-`k` distribution function at rate `s/b`
(`E_0 = 1`, the atom at `0`). The natural-number subtraction `i + 1 - s` is `max(i - s + 1, 0)`. -/
noncomputable def waitCDF (s : ℕ) (b : ℝ) (π : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' i : ℕ, π i * completionsCDF ((s : ℝ) / b) (i + 1 - s) t

end KendallQueues.GIMs


