-- Prove2me | Definitions.Def_RandomPIGame_Primitive
-- name    : RandomPIGame_Primitive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:23:51.380454+00:00
-- url     : https://prove2.me/theorems/fb151eb7-688a-4faa-95b8-97fb81d734fe
-- title:
--   Primitive distribution on $S$, $p_i(k,n)$, $G_i$, the value generating function $f$ and $d(k)$
-- statement:
--   The **primitive distribution** $p$ is a probability measure on the Borel subsets of
--   $$
--   S=\{\mathrm I,\mathrm{II}\}\times[0,\infty)\times\mathbb N,
--   $$
--   where $\{\mathrm I,\mathrm{II}\}$ and $\mathbb N$ are discrete. The coordinates are written $\iota$ (the active player), $\gamma$ (the capacity) and $\xi$ (the number of children). For $(i,k,n)\in S$ and $x\in[0,1]$ put
--   $$
--   p_i(k,n)=p(\{\iota=i\}\cap\{\gamma\ge k\}\cap\{\xi=n\}),\qquad G_i(k,x)=\sum_{n\in\mathbb N}p_i(k,n)x^n .
--   $$
--   The **value generating function** is
--   $$
--   f(k,x)=1-G_{\mathrm I}(k,0)-G_{\mathrm I}(k,1)+G_{\mathrm I}(k,x)-G_{\mathrm{II}}(k,1-x),
--   $$
--   and $f_k=f(k,\cdot)$. Finally
--   $$
--   d(k)=\mathsf E_p\big(\mathbf 1_{\{\iota=\mathrm I\}\cap\{\gamma\ge k\}}\,\xi\big)+p(\{\iota=\mathrm{II}\}\cap\{\gamma\ge k\}\cap\{\xi=1\}).
--   $$
--   These are the analytic data of the model: the law of the value of the random game is governed by the fixed points of $f_k$, and $d(k)$ is the left derivative of $f_k$ at $1$.
--
--   **Formalization Note** Capacities and thresholds live in `ℝ≥0`. Lean's `0 ^ 0 = 1` gives $G_i(k,0)=p_i(k,0)$, which is the paper's convention. `G` and `f` are functions on `ℝ` whose values are meaningful on $[0,1]$. Since no moment of $\xi$ is assumed, $d(k)$ takes values in `ℝ≥0∞` and uses the Lebesgue integral.
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, §2, pp.5, 7, (2.1)–(2.2); §4.1, pp.12–13, (4.1), (4.4)

import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

namespace RandomPIGame

noncomputable section

/-- The two players `I` (the maximizer) and `II` (the minimizer).
Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, §2, p.5. -/
inductive Player : Type
  | I : Player
  | II : Player
  deriving DecidableEq

/-- The discrete σ-algebra on `{I, II}` (the Borel σ-algebra of the discrete topology, p.5). -/
instance : MeasurableSpace Player := ⊤

instance : DiscreteMeasurableSpace Player := ⟨fun _ => trivial⟩

/-- The space `S = {I, II} × [0, ∞) × ℕ` of triples (active player, capacity, number of children).
arXiv:2104.10528v1, §2, p.5.

**Formalization Note.** Capacities live in `ℝ≥0`, so the thresholds `k` of `(2.1)` do too. The
product σ-algebra is the Borel σ-algebra of `S`, since all three factors are second countable. A
primitive distribution is a measure `p : Measure S` with `[IsProbabilityMeasure p]`. -/
abbrev S : Type := Player × ℝ≥0 × ℕ

/-- `p_i(k, n) = p({ι = i} ∩ {γ ≥ k} ∩ {ξ = n})`. arXiv:2104.10528v1, §2, p.7, (2.1). -/
def pMass (p : Measure S) (i : Player) (k : ℝ≥0) (n : ℕ) : ℝ :=
  p.real {s : S | s.1 = i ∧ k ≤ s.2.1 ∧ s.2.2 = n}

/-- `G_i(k, x) = ∑_{n ∈ ℕ} p_i(k, n) x^n`, for `x ∈ [0, 1]`. arXiv:2104.10528v1, §2, p.7, (2.2).

**Formalization Note.** Lean's `0 ^ 0 = 1` gives `G_i(k, 0) = p_i(k, 0)`, which is the paper's
convention. The series is summable on `[0, 1]`, since its coefficients sum to at most `1` when `p`
is a probability measure; the definition is used on `[0, 1]` only. -/
def G (p : Measure S) (i : Player) (k : ℝ≥0) (x : ℝ) : ℝ :=
  ∑' n : ℕ, pMass p i k n * x ^ n

/-- The value generating function
`f(k, x) = 1 - G_I(k, 0) - G_I(k, 1) + G_I(k, x) - G_II(k, 1 - x)`.
arXiv:2104.10528v1, §4.1, p.12, (4.1). The function `f_k` of the paper is `f p k`.

**Formalization Note.** `f p k` is a function on `ℝ`; only its values on `[0, 1]` are meaningful
(see `G`). Iterates are written `(f p k)^[t + 1]`. -/
def f (p : Measure S) (k : ℝ≥0) (x : ℝ) : ℝ :=
  1 - G p Player.I k 0 - G p Player.I k 1 + G p Player.I k x - G p Player.II k (1 - x)

/-- `d(k) = E_p(1_{ι = I} ∩ {γ ≥ k} ξ) + p({ι = II} ∩ {γ ≥ k} ∩ {ξ = 1})`.
arXiv:2104.10528v1, §4.1, p.13, (4.4).

**Formalization Note.** The expectation may be infinite (no moment condition is assumed on `ξ`), so
`d` takes values in `ℝ≥0∞` and uses the Lebesgue integral. -/
def d (p : Measure S) (k : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ s, (if s.1 = Player.I ∧ k ≤ s.2.1 then (s.2.2 : ℝ≥0∞) else 0) ∂p
    + p {s : S | s.1 = Player.II ∧ k ≤ s.2.1 ∧ s.2.2 = 1}

end

end RandomPIGame


