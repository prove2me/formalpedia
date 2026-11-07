-- Prove2me | Definitions.Def_QCopyMono_Influence
-- name    : QCopyMono_Influence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:05.796504+00:00
-- url     : https://prove2.me/theorems/18d0541a-a114-45b4-a0ae-d1f86e5f212f
-- title:
--   Total influence $I[f]$, Fourier coefficients $\hat g(S)$ and the edge-violation probability $p$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ and let $g:\{-1,1\}^n\to\{-1,1\}$ be its sign representation, obtained by relabeling $0$ as $1$ and $1$ as $-1$ in both input and output (so $z_i=(-1)^{x_i}$ and $g(z)=(-1)^{f(x)}$). For $i\in[n]$ let $x^{\oplus i}$ be $x$ with its $i$-th coordinate flipped. The **total influence** is
--   $$
--   I[f]=I[g]=\sum_{i=1}^n\Pr_x\big[f(x)\neq f(x^{\oplus i})\big],
--   $$
--   the **Fourier coefficients** are $\hat g(S)=\mathbb E_z\big[g(z)\prod_{i\in S}z_i\big]$ for $S\subseteq[n]$, and the **edge-violation probability** is
--   $$
--   p=\Pr_{x,i}\big[(x_i=0\wedge f(x)=1\wedge f(x+e_i)=0)\vee(x_i=1\wedge f(x)=0\wedge f(x^{\oplus i})=1)\big],
--   $$
--   for $x$ uniform on $\{0,1\}^n$ and $i$ uniform on $[n]$, independently.
--
--   These are the quantities of the Fourier tester (eqs. (2)–(6)) and of the influence filter used by both testers.
--
--   **Formalization Note** Everything stays on bit strings; `sgn b` is $(-1)^b$. For $n=0$ the definition of $p$ divides by $0$ and returns $0$; every statement using $p$ assumes $n\ge1$.
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §3.1, p.7 (Inf_i, I[g], ĝ(S), p); p.12 (I[f])

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QCopyMono

open QAlgorithms

/-! # Influence, Fourier coefficients, and the edge-violation probability

P. Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §3.1, p.7, and p.12 (`I[f]`).

**Formalization Note.** The paper passes to the sign representation `g : {−1,1}ⁿ → {−1,1}`,
"relabeling 0 as 1 and 1 as −1 in both the input and output". Here everything stays on
`Qubits n = Fin n → Bool`: the relabeling is `sgn`, with `sgn false = 1` and `sgn true = −1`, so
`z_i = sgn (x i)` and `g(z) = sgn (f x)`. Flipping a coordinate commutes with the relabeling, so
`Inf_i[g]` and `I[g]` of p.7 are the counts below, and they equal `I[f]` of p.12. Fourier
coefficients are indexed by `S : Finset (Fin n)`. -/

/-- `x^{⊕i}`: `x` with its `i`-th coordinate flipped (for `xᵢ = 0` this is `x + eᵢ`). -/
def flip {n : ℕ} (x : Qubits n) (i : Fin n) : Qubits n :=
  Function.update x i (!x i)

/-- p.7 and p.12: the total influence
`I[f] = ∑ᵢ Pr_x[f(x) ≠ f(x^{⊕i})] = I[g]`. -/
noncomputable def influence {n : ℕ} (f : Qubits n → Bool) : ℝ :=
  ∑ i : Fin n, ((Finset.univ.filter fun x => f x ≠ f (flip x i)).card : ℝ) / 2 ^ n

/-- The sign relabeling of p.7: `0 ↦ 1`, `1 ↦ −1`, i.e. `(−1)^b`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- p.7: the Fourier coefficient `ĝ(S) = E_z[g(z) ∏_{i∈S} zᵢ]` of the sign representation `g`
of `f`, with `zᵢ = (−1)^{xᵢ}` and `g(z) = (−1)^{f(x)}`. -/
noncomputable def fourierCoeff {n : ℕ} (f : Qubits n → Bool) (S : Finset (Fin n)) : ℝ :=
  (∑ x : Qubits n, sgn (f x) * ∏ i ∈ S, sgn (x i)) / 2 ^ n

/-- p.7: the probability that a uniformly random edge violates monotonicity,
`p = Pr_{x, i}[(xᵢ = 0 ∧ f(x) = 1 ∧ f(x + eᵢ) = 0) ∨ (xᵢ = 1 ∧ f(x) = 0 ∧ f(x^{⊕i}) = 1)]`,
with `x` uniform on `{0,1}ⁿ` and `i` uniform on `[n]`, independently. (For `n = 0` the
denominator is `0` and the value is `0`; every statement using it assumes `n ≥ 1`.) -/
noncomputable def edgeViolProb {n : ℕ} (f : Qubits n → Bool) : ℝ :=
  ((Finset.univ.filter fun p : Qubits n × Fin n =>
      (p.1 p.2 = false ∧ f p.1 = true ∧ f (flip p.1 p.2) = false) ∨
        (p.1 p.2 = true ∧ f p.1 = false ∧ f (flip p.1 p.2) = true)).card : ℝ) /
    (2 ^ n * n)

end QCopyMono


