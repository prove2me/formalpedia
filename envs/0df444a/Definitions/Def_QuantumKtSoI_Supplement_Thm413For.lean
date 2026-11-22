-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_Thm413For
-- name    : QuantumKtSoI_Supplement_Thm413For
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:38:59.968823+00:00
-- url     : https://prove2.me/theorems/da78f60a-7f52-43d0-8eef-9f7a355a619c
-- title:
--   Theorem 4.13 and Corollaries 4.14, 4.15 for a measure $\mu$; first-halt time
-- statement:
--   For a machine $A$ and an input $x$, the **first-halt time** $T_x$ has $\Pr[T_x\le t]=\sum_wP_A(x;t,w)$ and $T_x=\infty$ on the remaining mass; its expectation is $\mathbb E[T_x]=\sum_{t\ge0}\Pr[T_x>t]$, and $A$ halts with output $w$ with probability $\lim_{t\to\infty}P_A(x;t,w)$.
--
--   For a measure $\mu$ of strings this module states, with $\mu$ in place of $\mathrm{qKt}$ and the lower threshold written $s_0$:
--
--   1. **Theorem 4.13**: for every integer $a\ge1$, $\gamma\in(0,1)$ and $s_0$ with $\lfloor N^\gamma\rfloor\le s_0(N)\le N-2$ for all large $N$, no machine decides $\mathrm{Gap\text{-}M}\mu\mathrm P[s_0,N-2]$ in time $H_a(N)$, and hence none in time $2^{(\log N)^b}$ for any real $b\ge1$;
--   2. **Corollary 4.14**: for the same $a,\gamma,s_0$ there is no machine $A$ such that for all large $N$ and every $x\in\{0,1\}^N$, $\mathbb E[T_x]\le H_a(N)$ and $A$ halts with output $1$ with probability at least $2/3$ if $\mu(x)\le s_0(N)$ and at most $1/3$ if $\mu(x)>N-2$;
--   3. **Corollary 4.15**: for a thresholded measure $\mu_\varrho$, every $1/2<\alpha\le\beta<1$ and every $s$ with $n^\gamma\le s(n)\le n/2$ for some $\gamma>0$ and all large $n$, the problem with $\mathrm{YES}_n=\{w:\mu_\beta(w)\le s(n)\}$ and $\mathrm{NO}_n=\{w:\mu_\alpha(w)>s(n)\}$ (Definition 4.11) is not in $\mathrm{Promise\text{-}BQTIME}[n^{\mathrm{polylog}(n)}]$.
--
--   Theorem F.3(a) asserts these for $\mathrm{qKt}^{(c)}$; at $\mu=\mathrm{qKt}$ each is the paper's statement.
--
--   **Formalization Note** $\Pr[T_x\le t]$ is the weight of the branches halted by step $t$; the expectation is a sum in $[0,\infty]$; the limit is a supremum. $\mathrm{Promise\text{-}BQTIME}[n^{\mathrm{polylog}(n)}]$ is the union over integers $a_0\ge1$ of the problems decided in time $O(n^{(\log(n+2))^{a_0}})$ (p.22), so the statement excludes every $a_0$ and every constant.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 4.13 and Corollary 4.14, p.50; Corollary 4.15, p.51; Definition 4.11, p.49; BQTIME, p.22

import Mathlib
import Definitions.Def_QuantumKtSoI_CodedMachine
import Definitions.Def_QuantumKtSoI_Supplement_Ha
import Definitions.Def_QuantumKtSoI_Supplement_DecidesPromise
import Definitions.Def_QuantumKtSoI_Supplement_GapMqKtP

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-! The results of §4.6 for a measure `µ` of strings (Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…). With `µ = qKt` each is the paper's
statement; Theorem F.3(a) asserts them with `qKt^{(c)}` in place of `qKt`. -/

/-- `Pr[T_x ≤ t] = Σ_w P_M(x; t, w)` (p.50): the weight of the branches of `M` on `x` that have
halted within `t` steps; at `t = 0` it is `1` if the initial state is final and `0` otherwise.

**Formalization Note** Written as the total squared norm on final configurations of the branch
vectors of length `t`, which is the sum over all outputs `w` of the published `outputProb`. -/
def haltProb (M : Machine) (x : List Bool) (t : ℕ) : ℝ :=
  if t = 0 then (if M.isFinal M.init = true then 1 else 0)
  else ∑ ρ ∈ M.recSeqs x t, ∑ C ∈ (M.branch x ρ).support with M.isFinal C.state = true,
    ‖M.branch x ρ C‖ ^ 2

/-- The expectation `E[T_x] = Σ_{t ≥ 0} Pr[T_x > t]` of the first-halt time of `M` on `x` (p.50), in
`[0, ∞]` (`T_x = ∞` on the mass that never halts). -/
def expHaltTime (M : Machine) (x : List Bool) : ENNReal :=
  ∑' t : ℕ, ENNReal.ofReal (1 - haltProb M x t)

/-- The probability `lim_{t→∞} P_M(x; t, w)` that `M` halts with output `w` (p.50); the limit of
a nondecreasing sequence bounded by `1`, written as its supremum. -/
def limitOutProb (M : Machine) (x w : List Bool) : ℝ := ⨆ t : ℕ, M.outputProb x t w

/-- **Theorem 4.13** for `µ` (p.50), with the lower threshold written `s₀`: for every integer
`a ≥ 1`, every `γ ∈ (0,1)` and every `s₀ : ℕ → ℕ` with `⌊N^γ⌋ ≤ s₀(N) ≤ N − 2` for all large `N`,
no machine decides `Gap-MµP[s₀, N − 2]` (clipped thresholds, p.49) in time `H_a(N)`; consequently,
for every real `b ≥ 1`, none decides it in time `2^{(log N)^b}`. -/
def Thm413For (μ : List Bool → ℝ) : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ s₀ : ℕ → ℕ,
    (∃ N₀ : ℕ, ∀ N ≥ N₀, ⌊(N : ℝ) ^ γ⌋₊ ≤ s₀ N ∧ s₀ N ≤ N - 2) →
    (¬∃ B : CodedMachine, B.Valid ∧
      DecidesPromise B (GapMqKtPClip μ s₀).1 (GapMqKtPClip μ s₀).2 (fun N => (Ha a N : ℝ))) ∧
    ∀ b : ℝ, 1 ≤ b → ¬∃ B : CodedMachine, B.Valid ∧
      DecidesPromise B (GapMqKtPClip μ s₀).1 (GapMqKtPClip μ s₀).2
        (fun N => (2 : ℝ) ^ (Real.logb 2 (N : ℝ)) ^ b)

/-- **Corollary 4.14** (Expected running time, p.50) for `µ`: for `a`, `γ`, `s₀` as in Theorem 4.13,
there is no machine `A` such that, for all sufficiently large `N` and every `x ∈ {0,1}^N`, the
first-halt time of `A` on `x` has expectation at most `H_a(N)`, and `A` halts with output `1` with
probability at least `2/3` if `µ(x) ≤ s₀(N)` and at most `1/3` if `µ(x) > N − 2`. -/
def Cor414For (μ : List Bool → ℝ) : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ s₀ : ℕ → ℕ,
    (∃ N₀ : ℕ, ∀ N ≥ N₀, ⌊(N : ℝ) ^ γ⌋₊ ≤ s₀ N ∧ s₀ N ≤ N - 2) →
    ¬∃ A : CodedMachine, A.Valid ∧ ∃ N₀ : ℕ, ∀ x : List Bool, N₀ ≤ x.length →
      expHaltTime A.toMachine x ≤ (Ha a x.length : ENNReal) ∧
        (μ x ≤ s₀ x.length → (2 / 3 : ℝ) ≤ limitOutProb A.toMachine x [true]) ∧
        ((x.length : ℝ) - 2 < μ x → limitOutProb A.toMachine x [true] ≤ 1 / 3)

/-- **Corollary 4.15** (Unconditional minimization lower bound, p.51) for a thresholded measure
`µ_ϱ` (`μρ ϱ w` is `µ_ϱ(w)`): for every `1/2 < α ≤ β < 1` and every `s : ℕ → ℕ` with
`n^γ ≤ s(n) ≤ n/2` for some fixed `γ > 0` and all large `n`,
`MµP[β, α, s] ∉ Promise-BQTIME[n^{polylog(n)}]`, where `MµP[β, α, s]` (Definition 4.11, p.49) has
`YES_n = {w ∈ {0,1}ⁿ : µ_β(w) ≤ s(n)}` and `NO_n = {w ∈ {0,1}ⁿ : µ_α(w) > s(n)}`.

**Formalization Note** `Promise-BQTIME[n^{polylog(n)}]` is the union over integers `a₀ ≥ 1` of the
promise problems decided within time `O(n^{(log(n+2))^{a₀}})` (p.22), that is, in time
`C·n^{(log(n+2))^{a₀}}` for a constant `C` in the sense of `DecidesPromise`; the statement excludes
every `a₀` and every `C`. -/
def Cor415For (μρ : ℝ → List Bool → ℝ) : Prop :=
  ∀ α β : ℝ, 1 / 2 < α → α ≤ β → β < 1 → ∀ s : ℕ → ℕ,
    (∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, (n : ℝ) ^ γ ≤ s n ∧ (s n : ℝ) ≤ (n : ℝ) / 2) →
    ∀ a₀ : ℕ, 1 ≤ a₀ → ∀ C : ℝ, ¬∃ B : CodedMachine, B.Valid ∧
      DecidesPromise B {w | μρ β w ≤ s w.length} {w | (s w.length : ℝ) < μρ α w}
        (fun n => C * (n : ℝ) ^ (Real.logb 2 ((n : ℝ) + 2)) ^ a₀)

end QuantumKtSoI.Supplement


