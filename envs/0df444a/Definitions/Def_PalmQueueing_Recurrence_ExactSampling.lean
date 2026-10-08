-- Prove2me | Definitions.Def_PalmQueueing_Recurrence_ExactSampling
-- name    : PalmQueueing_Recurrence_ExactSampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T23:59:06.131693+00:00
-- url     : https://prove2.me/theorems/1cbb611e-a0d4-46c3-8e38-be4d90daf979
-- title:
--   Coupling from the past: the model, the chains and the coalescence times
-- statement:
--   An exact sampling algorithm for a distribution $\pi$ allows one to generate random
--   variables with *precisely* this distribution. The **coupling from the past** algorithm, due to
--   Propp and Wilson (1996), does this for the stationary law of a discrete-time, finite-state-space
--   Markov chain, and is based on the backwards coalescence of an associated stochastic recurrence.
--
--   Let $I\!P$ be an ergodic transition matrix on the **finite** state space $E = \{1, \dots, r\}$,
--   with stationary distribution $\pi$. The chain can be implemented by a stochastic recurrence
--   $X_{n+1} = h(X_n, \xi_n)$ for an i.i.d. sequence $\{\xi_n\}$ uniform on $[0,1]$ and independent of
--   the initial state. Consider an array $\{\xi_k(i)\}_{k \in \mathbb{Z},\, i \in E}$ of i.i.d.
--   uniform variables, and for all $k \in \mathbb{Z}$ and $i \in E$ let $\{X^k_n(i)\}_{n \ge k}$ be the
--   stochastic recurrence
--   $$ X^k_{n+1}(i) = h\big(X^k_n(i),\, \xi_n(X^k_n(i))\big), \qquad n \ge k , $$
--   with initial condition $X^k_k(i) = i$.
--
--   The driving variable is indexed by the chain's **current** state, not its initial one. That is
--   what makes two chains stick together once they meet — $X^k_n(i) = X^k_n(j)$ implies
--   $X^k_m(i) = X^k_m(j)$ for all $m \ge n$ — and it is the mechanism the whole method rests on.
--
--   The **forwards** and **backwards coalescence times** are
--   $$ N^+ = \inf\{n \ge 0;\ X^0_n(1) = \dots = X^0_n(r)\}, \qquad
--   N^- = \inf\{n \ge 1;\ X^{-n}_0(1) = \dots = X^{-n}_0(r)\} , $$
--   both $+\infty$ if the condition is never satisfied. In the monotone case only the two extremal
--   chains need meet, and the **monotone backwards coalescence time** is
--   $M = \inf\{n \ge 1;\ X^{-n}_0(1) = X^{-n}_0(r)\}$.
--
--   Nothing here is an algorithm. Theorems 2.5.1 and 2.5.2 say that a random variable is almost surely
--   finite and that another has a distribution exactly equal to $\pi$; defining "the Propp-Wilson
--   algorithm" as a program and asserting something about its execution would be a different kind of
--   object, and is not what the book states. Ergodicity of $I\!P$ is carried as irreducibility
--   ($I\!P^n_{ij} > 0$ for some $n$, for every $i, j$) together with the form the proof uses —
--   Kolmogorov's theorem, $I\!P^n_{ij} \to \pi(j)$.
--
--   **Formalization Note.** Two models are defined. `CFTP` carries the array
--   $\{\xi_k(i)\}_{k \in \mathbb{Z}, i \in E}$ of i.i.d. uniforms of Theorem 2.5.1. `CFTPMono`
--   carries the model of Theorem 2.5.2, "with a single updating sequence ($\xi_n(i) = \xi_n$ for all
--   $n$ and $i$)": one i.i.d. uniform sequence $\{\xi_n\}_{n\in\mathbb{Z}}$ driving every chain. The
--   two cannot share a structure, since an array independent across states cannot also be constant in
--   the state.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, §2.5.3, pp. 109-113

import Mathlib

/-!
# Exact sampling of Markov chains: coupling from the past (§2.5.3, pp.109-113)

The Propp-Wilson setting. An ergodic transition matrix `IP` on the **finite** state space
`E = {1, …, r}` with stationary distribution `π` is implemented by a stochastic recurrence
`X_{n+1} = h(X_n, ξ_n)` driven by i.i.d. uniform `[0,1]` variables. Coupling from the past runs
*one chain from every state*, all sharing an array `{ξ_k(i)}_{k ∈ ℤ, i ∈ E}` of i.i.d. uniforms
indexed by time **and current state**, and waits for them to coalesce when started far enough in
the past.

Nothing here is an algorithm. Theorems 2.5.1 and 2.5.2 say that a random variable is almost surely
finite, and that another random variable has a distribution exactly equal to `π`; a definition of
"the Propp-Wilson algorithm" as a program, with a claim about its execution, would be a different
kind of object and is not what the book states.
-/

namespace PalmQueueing.Recurrence

open MeasureTheory Filter Topology ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The coupling-from-the-past model (§2.5.3, p.109): an ergodic transition matrix on
`E = {1, …, r}` with stationary law `π`, its updating function `h`, and the array of i.i.d.
uniform `[0,1]` variables that drives all `r` chains at once. -/
structure CFTP (Ω : Type*) [MeasurableSpace Ω] (r : ℕ) where
  /-- The underlying probability. -/
  P : Measure Ω
  /-- It is a probability. -/
  isProb : IsProbabilityMeasure P
  /-- The transition matrix `IP` on `E = {1, …, r}`. -/
  IP : Matrix (Fin r) (Fin r) ℝ
  /-- Its stationary distribution `π`. -/
  pi : Fin r → ℝ
  /-- `π` is a probability vector. -/
  pi_nonneg : ∀ i, 0 ≤ pi i
  /-- `π` sums to one. -/
  pi_sum : ∑ i, pi i = 1
  /-- `π` is stationary for `IP`. -/
  pi_stationary : ∀ j, ∑ i, pi i * IP i j = pi j
  /-- `IP` is **ergodic**: irreducible, -/
  irreducible : ∀ i j, ∃ n : ℕ, 0 < (IP ^ n) i j
  /-- and aperiodic, in the form the proof of Theorem 2.5.1 uses it: Kolmogorov's theorem for
  ergodic Markov chains, `IPⁿ i j → π j`. -/
  ergodic : ∀ i j, Tendsto (fun n : ℕ => (IP ^ n) i j) atTop (𝓝 (pi j))
  /-- The updating function `h : E × [0,1] → E` of (2.5.5). -/
  h : Fin r → ℝ → Fin r
  /-- It is measurable in the driving variable. -/
  measurable_h : ∀ i, Measurable (h i)
  /-- The array `{ξ_k(i)}_{k ∈ ℤ, i ∈ E}` driving all the chains. -/
  xi : ℤ → Fin r → Ω → ℝ
  /-- Each driving variable is a random variable. -/
  measurable_xi : ∀ k i, Measurable (xi k i)
  /-- They are independent. -/
  indep_xi : iIndepFun (fun p : ℤ × Fin r => xi p.1 p.2) P
  /-- Each is uniform on `[0,1]`. -/
  unif_xi : ∀ (k : ℤ) (i : Fin r),
    Measure.map (xi k i) P = volume.restrict (Set.Icc (0 : ℝ) 1)
  /-- `h` implements `IP`: from state `i`, the next state is `j` with probability `IP i j`. -/
  implements : ∀ (i j : Fin r) (k : ℤ),
    P {ω | h i (xi k i ω) = j} = ENNReal.ofReal (IP i j)

/-- `C.X k n i ω` is the book's `X^k_{k+n}(i)`: the chain started at time `k` in state `i`,
after `n` steps of `X^k_{n+1}(i) = h(X^k_n(i), ξ_n(X^k_n(i)))` (p.109).

The driving variable is indexed by the chain's **current** state, not by its initial one. That is
what makes two chains stick together once they meet — the funnelling property the whole method
rests on. -/
noncomputable def CFTP.X {r : ℕ} (C : CFTP Ω r) (k : ℤ) : ℕ → Fin r → Ω → Fin r
  | 0 => fun i _ => i
  | (n + 1) => fun i ω =>
      C.h (C.X k n i ω) (C.xi (k + n) (C.X k n i ω) ω)

/-- The chains started at time `-n` from every state have coalesced by time `0`:
`X^{-n}_0(1) = X^{-n}_0(2) = … = X^{-n}_0(r)` (p.110). The **backwards coalescence time** `N⁻` is
the least `n ≥ 1` for which this holds. -/
def CFTP.Coalesced {r : ℕ} (C : CFTP Ω r) (n : ℕ) (ω : Ω) : Prop :=
  ∀ i j : Fin r, C.X (-(n : ℤ)) n i ω = C.X (-(n : ℤ)) n j ω

/-- The model of the **monotone** Propp-Wilson algorithm (p.112): the same ergodic transition
matrix `IP`, stationary law `π` and updating function `h` as `CFTP`, but "the model `X_n` with a
single updating sequence (i.e. `ξ_n(i) = ξ_n` for all `n` and `i`)": one i.i.d. uniform `[0,1]`
sequence `{ξ_n}_{n ∈ ℤ}` drives every chain. (This cannot be expressed inside `CFTP`, whose array
is independent across states.) -/
structure CFTPMono (Ω : Type*) [MeasurableSpace Ω] (r : ℕ) where
  /-- The underlying probability. -/
  P : Measure Ω
  /-- It is a probability. -/
  isProb : IsProbabilityMeasure P
  /-- The transition matrix `IP` on `E = {1, …, r}`. -/
  IP : Matrix (Fin r) (Fin r) ℝ
  /-- Its stationary distribution `π`. -/
  pi : Fin r → ℝ
  /-- `π` is a probability vector. -/
  pi_nonneg : ∀ i, 0 ≤ pi i
  /-- `π` sums to one. -/
  pi_sum : ∑ i, pi i = 1
  /-- `π` is stationary for `IP`. -/
  pi_stationary : ∀ j, ∑ i, pi i * IP i j = pi j
  /-- `IP` is **ergodic**: irreducible, -/
  irreducible : ∀ i j, ∃ n : ℕ, 0 < (IP ^ n) i j
  /-- and aperiodic, as Kolmogorov's convergence `IPⁿ i j → π j`. -/
  ergodic : ∀ i j, Tendsto (fun n : ℕ => (IP ^ n) i j) atTop (𝓝 (pi j))
  /-- The updating function `h : E × [0,1] → E` of (2.5.5). -/
  h : Fin r → ℝ → Fin r
  /-- It is measurable in the driving variable. -/
  measurable_h : ∀ i, Measurable (h i)
  /-- The single updating sequence `{ξ_n}_{n ∈ ℤ}`. -/
  xi : ℤ → Ω → ℝ
  /-- Each driving variable is a random variable. -/
  measurable_xi : ∀ k, Measurable (xi k)
  /-- They are independent. -/
  indep_xi : iIndepFun xi P
  /-- Each is uniform on `[0,1]`. -/
  unif_xi : ∀ k : ℤ, Measure.map (xi k) P = volume.restrict (Set.Icc (0 : ℝ) 1)
  /-- `h` implements `IP`: from state `i`, the next state is `j` with probability `IP i j`. -/
  implements : ∀ (i j : Fin r) (k : ℤ),
    P {ω | h i (xi k ω) = j} = ENNReal.ofReal (IP i j)

/-- `C.X k n i ω` is `X^k_{k+n}(i)` in the single-sequence model:
`X^k_{n+1}(i) = h(X^k_n(i), ξ_n)`. -/
noncomputable def CFTPMono.X {r : ℕ} (C : CFTPMono Ω r) (k : ℤ) : ℕ → Fin r → Ω → Fin r
  | 0 => fun i _ => i
  | (n + 1) => fun i ω => C.h (C.X k n i ω) (C.xi (k + n) ω)

/-- The two extremal chains, started at time `-n` from the bottom and the top of the order, have
met by time `0` (p.113). The **monotone backwards coalescence time** `M` is the least `n ≥ 1` for
which this holds; the point of Theorem 2.5.2 is that this suffices. -/
def CFTPMono.CoalescedExtremal {r : ℕ} (C : CFTPMono Ω r) (bot top : Fin r) (n : ℕ) (ω : Ω) :
    Prop :=
  C.X (-(n : ℤ)) n bot ω = C.X (-(n : ℤ)) n top ω

end PalmQueueing.Recurrence


