-- Prove2me | Definitions.Def_MonoReset_IntervalBFS_Model
-- name    : MonoReset_IntervalBFS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:47.243142+00:00
-- url     : https://prove2.me/theorems/3d08448d-013f-4c6e-94ce-f12d9fc2f88a
-- title:
--   pp. 1–3 — automaton on Fin n, words, reset sequences, cyclic monotonicity, intervals, ≺, the interval automaton δ′ with ∞
-- statement:
--   This item fixes the model of Eppstein's paper.
--
--   1. **Automaton and words** (p. 1). The states are $S = \{s_1, \dots, s_n\}$ and the alphabet is $\Sigma = \{\sigma_1, \dots, \sigma_k\}$; the automaton is a transition function $\delta(\sigma, s)$, with no start or accepting states. For a word $\tau \in \Sigma^*$, $\delta(\tau, s)$ is the state reached from $s$ by reading $\tau$ from left to right: $\delta(\tau_1\tau_2, s) = \delta(\tau_2, \delta(\tau_1, s))$ and $\delta(\varepsilon, s) = s$.
--   2. **Reset sequence** (p. 1). For $X \subseteq S$, a word $\tau$ is a reset sequence for $X$ when
--   $$|\delta(\tau, X)| = 1, \qquad \delta(\tau, X) = \{\delta(\tau, x) : x \in X\}.$$
--   3. **Monotonicity** (p. 2). A map $f : S \to S$ is monotonic when it preserves the cyclic order $s_1, s_2, \dots, s_n$: going once around the cycle from a suitable starting state $s_m$, the images $f(s_m), f(s_{m+1}), \dots$ advance weakly in the cyclic order and never pass $f(s_m)$ again. The automaton is monotonic when every letter is.
--   4. **Intervals** (p. 2). The interval $[s_i, s_j]$ is the set of states met going forward in the cyclic order from $s_i$ to $s_j$, both included; e.g. $[s_1, s_3] = \{s_1, s_2, s_3\}$. The full set $S$ has the $n$ representations $[s_i, s_{i-1}]$.
--   5. **Interval containment** (p. 2). $J = [s_h, s_i] \prec I = [s_g, s_j]$ when the endpoints appear in the cyclic order $s_g, s_h, s_i, s_j$ (weakly). This implies $J \subseteq I$ as sets, but not conversely when $I$ represents $S$.
--   6. **The interval automaton** (p. 3). Its states are the intervals together with a symbol $\infty$. For a letter $\sigma$ and $I = [s_i, s_j]$, with $d_x = \delta(\sigma, s_x)$: (1) if $d_i \ne d_j$, $\delta'(\sigma, I) = [d_i, d_j]$; (2) if $d_i = d_{i+1} = \cdots = d_j$, $\delta'(\sigma, I) = [d_i, d_i]$; (3) otherwise, and on $\infty$, $\delta'(\sigma, I) = \infty$. On words, $\delta'(\tau, \cdot)$ is the composition of the letter maps in reading order, with $\infty$ absorbing and $\delta'(\varepsilon, I) = I$.
--
--   These are the objects in which Lemmas 1–5 and Theorem 1 are stated.
--
--   **Formalization Note** States are `Fin n`, with $s_i$ the element $i-1$; letters are `Fin k`; words are lists, and `run δ τ s` is the left fold. `IsMonotonic f` says that $n = 0$ or, for some $m$, the offsets $(f(m+i) - f(m)) \bmod n$ are nondecreasing in $i \in \{0, \dots, n-1\}$ (the source's "adjacent duplicates" is read cyclically; this equals the cyclic de-duplication reading for every map with $n \le 6$, and admits e.g. $s_1 \mapsto s_1, s_2 \mapsto s_2, s_3 \mapsto s_1$). An interval is its endpoint pair `(i, j) : Fin n × Fin n`; `ivSet (i, j)` is its set of states, the states $s$ with $(s - i) \bmod n \le (j - i) \bmod n$. `Prec J I` compares cyclic offsets from the left endpoint of $I$. ∞ is `none`, so $S'$ is `Option (Fin n × Fin n)`; `dPrime1` is $\delta'$ on a letter and `dPrime` its left fold over a word.
-- source:
--   Eppstein, Reset Sequences for Monotonic Automata, author manuscript of 7 Feb 1990 (SIAM J. Comput. 19, doi:10.1137/0219033; PDF sha256 6d8caa76…), pp. 1–3 (PDF 2–4): automaton and reset sequence p. 1; monotonicity, intervals and ≺ p. 2; S′ and δ′ p. 3

import Mathlib

namespace MonoReset.IntervalBFS

variable {n k : ℕ}

/-- δ(τ, s), p. 1: the state reached from `s` after reading the word `τ` left to right,
    so that δ(τ₁τ₂, s) = δ(τ₂, δ(τ₁, s)) and δ(ε, s) = s. -/
def run (δ : Fin k → Fin n → Fin n) (τ : List (Fin k)) (s : Fin n) : Fin n :=
  τ.foldl (fun s a => δ a s) s

/-- p. 1: `τ` is a reset sequence for `(S, Σ, δ)` and `X` iff `|δ(τ, X)| = 1`. -/
def IsResetSeq (δ : Fin k → Fin n → Fin n) (X : Finset (Fin n)) (τ : List (Fin k)) : Prop :=
  (X.image (run δ τ)).card = 1

/-- p. 2: `f` preserves the cyclic order `0 → 1 → ⋯ → n-1 → 0` of the states. Read cyclically:
    from some start `m`, going once round the cycle, the cyclic offsets of the images from `f m`
    never decrease. The empty automaton (`n = 0`) is monotonic. -/
def IsMonotonic (f : Fin n → Fin n) : Prop :=
  n = 0 ∨ ∃ m : Fin n, Monotone (fun i : Fin n => (f (m + i) - f m).val)

/-- The states of the interval `[s_i, s_j]` (p. 2), the interval being given by its pair of
    endpoints `(i, j)`: every state reached from `i` by going forward in the cyclic order up to and
    including `j`. -/
def ivSet (I : Fin n × Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun s => (s - I.1).val ≤ (I.2 - I.1).val)

/-- `J ≺ I` (p. 2): the endpoints appear in the (weak) cyclic order `I.1, J.1, J.2, I.2`. -/
def Prec (J I : Fin n × Fin n) : Prop :=
  (J.1 - I.1).val ≤ (J.2 - I.1).val ∧ (J.2 - I.1).val ≤ (I.2 - I.1).val

instance (J I : Fin n × Fin n) : Decidable (Prec J I) := by
  unfold Prec; infer_instance

/-- δ′(σ, ·) on `S′ = Option (Fin n × Fin n)`, p. 3; `none` is the symbol ∞.
    (1) if `d_i ≠ d_j` the result is `[d_i, d_j]`; (2) if `δ(σ, ·)` is constant on `[s_i, s_j]` the
    result is `[d_i, d_i]`; (3) otherwise, or on ∞, the result is ∞. -/
def dPrime1 (δ : Fin k → Fin n → Fin n) (a : Fin k) :
    Option (Fin n × Fin n) → Option (Fin n × Fin n)
  | none => none
  | some I =>
    if δ a I.1 ≠ δ a I.2 then some (δ a I.1, δ a I.2)
    else if ∀ s ∈ ivSet I, δ a s = δ a I.1 then some (δ a I.1, δ a I.1) else none

/-- δ′(τ, ·), p. 3: the composition of the letter maps along the word, read left to right;
    ∞ is absorbing and δ′(ε, I) = I. -/
def dPrime (δ : Fin k → Fin n → Fin n) (τ : List (Fin k)) (I : Option (Fin n × Fin n)) :
    Option (Fin n × Fin n) :=
  τ.foldl (fun J a => dPrime1 δ a J) I

end MonoReset.IntervalBFS


