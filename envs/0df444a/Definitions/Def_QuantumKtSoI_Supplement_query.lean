-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_query
-- name    : QuantumKtSoI_Supplement_query
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:28:58.275664+00:00
-- url     : https://prove2.me/theorems/c37100d8-def4-4616-8405-687d3425bd98
-- title:
--   Encoded queries $q(x,s)$, consistency with a gap, $L_{\mathrm{thr}}$, and deciding infinitely often (§6.6, §7)
-- statement:
--   For $\lambda\ge1$ let $\mathrm{wd}(\lambda)=\lceil\log(4\lambda+40)\rceil$. For $x\in\{0,1\}^\lambda$ and an integer $0\le s<2^{\mathrm{wd}(\lambda)}$ the **encoded query** is
--   $$q(x,s)=\langle x,\mathrm{bin}_{\mathrm{wd}(\lambda)}(s)\rangle ,$$
--   where $\mathrm{bin}_k(s)$ is the binary expansion of $s$ padded with leading zeros to length $k$; its length $\nu(\lambda)$ depends only on $\lambda$.
--
--   For a measure $\mu$ of strings and $g:\mathbb N\to\mathbb N$:
--
--   1. a language $L$ is **consistent with the gap $g$** if for all $\lambda\ge1$, $x\in\{0,1\}^\lambda$ and $0\le s<2^{\mathrm{wd}(\lambda)}$, $q(x,s)\in L$ whenever $\mu(x)\le s$ and $q(x,s)\notin L$ whenever $\mu(x)>s+g(\lambda)$;
--   2. $L_{\mathrm{thr}}=\{q(x,s):\mu(x)\le s\}$;
--   3. a machine $A$ **decides $L$ infinitely often in time $2^{\varepsilon\nu}$** if there are infinitely many $\lambda$ such that on every input $q(x,s)$ with $x\in\{0,1\}^\lambda$ it halts within $2^{\varepsilon\nu(\lambda)}$ steps and outputs $1$ with probability at least $2/3$ if $q(x,s)\in L$ and at most $1/3$ otherwise;
--   4. $A$ **solves the gap-$g$ promise problem at length $\lambda$ in time $T$** if on every such input it halts within $T$ steps and outputs $1$ with probability at least $2/3$ when $\mu(x)\le s$ and at most $1/3$ when $\mu(x)>s+g(\lambda)$.
--
--   With $\mu=\mathrm{qKt}$ these are the paper's definitions; Appendix F uses them with $\mathrm{qKt}^{(c)}$.
--
--   **Formalization Note** $\nu(\lambda)$ is computed at $x=0^\lambda$, $s=0$. Halting is on every branch and real deadlines are floors (p.22). "Infinitely many $\lambda$" is: for every $N$ some $\lambda\ge N$.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), §6.6, p.96; §7, p.98; p.229 (for qKt^{(c)})

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_CodedMachine

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- The threshold width `wd(λ) = ⌈log(4λ + 40)⌉` (§6.6, p.96 of Myrisiotis, STOC 2027 submission,
held version sha256 6616571c…). -/
def wd (lam : ℕ) : ℕ := Nat.clog 2 (4 * lam + 40)

/-- `bin_k(s)`: the binary expansion of `s`, padded with leading zeros to length `k` (p.96). -/
def binPad (k s : ℕ) : List Bool := List.replicate (k - (bin s).length) false ++ bin s

/-- The **encoded query** `q(x, s) = ⟨x, bin_{wd(λ)}(s)⟩` for `x ∈ {0,1}^λ` (p.96). -/
def query (x : List Bool) (s : ℕ) : List Bool := pair x (binPad (wd x.length) s)

/-- The query length `ν(λ) = |q(x, s)|`, which depends only on `λ` (p.96); computed at
`x = 0^λ`, `s = 0`. -/
def nu (lam : ℕ) : ℕ := (query (List.replicate lam false) 0).length

/-- A language `L` is **consistent with the gap** `g` for a measure `µ` of strings (p.96; p.229 for
`qKt^{(c)}`): for all `λ ≥ 1`, `x ∈ {0,1}^λ` and `0 ≤ s < 2^{wd(λ)}`, `q(x, s) ∈ L` whenever
`µ(x) ≤ s`, and `q(x, s) ∉ L` whenever `µ(x) > s + g(λ)`. -/
def ConsistentGap (μ : List Bool → ℝ) (g : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  ∀ x : List Bool, 1 ≤ x.length → ∀ s : ℕ, s < 2 ^ wd x.length →
    (μ x ≤ s → query x s ∈ L) ∧ ((s : ℝ) + g x.length < μ x → query x s ∉ L)

/-- `L_thr = {q(x, s) : µ(x) ≤ s}` (p.98), over valid queries (`|x| ≥ 1`, `s < 2^{wd(|x|)}`). -/
def Lthr (μ : List Bool → ℝ) : Set (List Bool) :=
  {q | ∃ x : List Bool, ∃ s : ℕ, 1 ≤ x.length ∧ s < 2 ^ wd x.length ∧ q = query x s ∧ μ x ≤ s}

/-- A machine `A` **decides `L` infinitely often in time `2^{εν}`** (p.98): there are infinitely many
`λ` such that, on every input `q(x, s)` with `x ∈ {0,1}^λ` (and `0 ≤ s < 2^{wd(λ)}`), `A` halts within
`2^{εν(λ)}` steps on every branch and outputs `1` with probability at least `2/3` if `q(x, s) ∈ L`
and at most `1/3` otherwise.

**Formalization Note** The real deadline is `⌊2^{εν(λ)}⌋` (p.22); "infinitely many `λ`" is
`∀ N, ∃ λ ≥ N` with `λ ≥ 1`. -/
def DecidesIO (A : CodedMachine) (L : Set (List Bool)) (ε : ℝ) : Prop :=
  ∀ N : ℕ, ∃ lam : ℕ, N ≤ lam ∧ 1 ≤ lam ∧ ∀ x : List Bool, x.length = lam → ∀ s : ℕ,
    s < 2 ^ wd lam →
      A.toMachine.HaltsWithin (query x s) ⌊(2 : ℝ) ^ (ε * nu lam)⌋₊ ∧
        (query x s ∈ L → (2 / 3 : ℝ) ≤ A.toMachine.outputProb (query x s) ⌊(2 : ℝ) ^ (ε * nu lam)⌋₊ [true]) ∧
        (query x s ∉ L → A.toMachine.outputProb (query x s) ⌊(2 : ℝ) ^ (ε * nu lam)⌋₊ [true] ≤ 1 / 3)

/-- `A` **solves the gap-`g` promise problem at length `λ` in time `T`** (p.96): on every input
`q(x, s)` with `x ∈ {0,1}^λ` and `0 ≤ s < 2^{wd(λ)}` it halts within `T` steps on every branch,
outputs `1` with probability at least `2/3` when `µ(x) ≤ s` and at most `1/3` when
`µ(x) > s + g(λ)`. No condition is imposed when `s < µ(x) ≤ s + g(λ)`. The real deadline is
`⌊T⌋`. -/
def SolvesGapAt (μ : List Bool → ℝ) (A : CodedMachine) (g : ℕ → ℕ) (lam : ℕ) (T : ℝ) : Prop :=
  ∀ x : List Bool, x.length = lam → ∀ s : ℕ, s < 2 ^ wd lam →
    A.toMachine.HaltsWithin (query x s) ⌊T⌋₊ ∧
      (μ x ≤ s → (2 / 3 : ℝ) ≤ A.toMachine.outputProb (query x s) ⌊T⌋₊ [true]) ∧
      ((s : ℝ) + g lam < μ x → A.toMachine.outputProb (query x s) ⌊T⌋₊ [true] ≤ 1 / 3)

end QuantumKtSoI.Supplement


