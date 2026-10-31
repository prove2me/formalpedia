-- Prove2me | Definitions.Def_DistortedCondExp_Dynamic
-- name    : DistortedCondExp_Dynamic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:55.70399+00:00
-- url     : https://prove2.me/theorems/b304397d-39bd-4506-9a9f-c026f2103fd9
-- title:
--   Dynamic distortion functions, $\mathcal E_{s,t}$, time-consistency, and the conditions of Theorem 3.4
-- statement:
--   The dynamic objects of Definition 2.8 of Ma, Wong and Zhang, on the binomial tree of §3.2, and the three conditions in Theorem 3.4.
--
--   1. **Dynamic distortion function** (Definition 2.8(i)). With $\mathcal T_2:=\{(s,t): s<t\}$, a mapping $\Phi:\mathcal T_2\times\mathbb R\times[0,1]\to[0,1]$ that is jointly Lebesgue measurable in $(x,p)$ for each $(s,t)\in\mathcal T_2$ and such that, for each $(s,t,x)$, $p\mapsto\Phi(s,t,x;p)$ is a distortion function.
--   2. **Conditional nonlinear expectation** (eq. (2.11)). For $(s,t)\in\mathcal T_2$ and $\xi\ge0$ measurable with respect to $\sigma(X_t)$,
--   $$
--   \mathcal E_{s,t}[\xi]:=\int_0^\infty \Phi\bigl(s,t,X_s;\mathbb P(\xi\ge x\mid\mathcal F_s)\bigr)\,dx .
--   $$
--   3. **Time-consistency** (eq. (2.12)). $\Phi$ is time-consistent if $\mathcal E_{r,t}[g(X_t)]=\mathcal E_{r,s}\bigl[\mathcal E_{s,t}[g(X_t)]\bigr]$ for all $0\le r<s<t\le T$ and all $g\in\mathcal I$.
--   4. **Initial condition** (Theorem 3.4). $\Phi(t_0,t_n,x_{0,0};p)=\varphi_{t_n}(p)$ for $n=1,\dots,N$ and all $p\in[0,1]$.
--   5. **Equation (3.17).** For all $0\le i<n\le N$, $0\le j\le i$, $0\le k\le n$:
--   $$
--   \Phi\bigl(t_i,t_n,x_{i,j};\mathbb P\{X_{t_n}\ge x_{n,k}\mid X_{t_i}=x_{i,j}\}\bigr)=\mathbb Q\{X_{t_n}\ge x_{n,k}\mid X_{t_i}=x_{i,j}\}.
--   $$
--   6. **Equation (3.12)** for every pair of times. $\mathcal E_{t_i,t_n}[g(X_{t_n})]=\mathbb E^{\mathbb Q}[g(X_{t_n})\mid\sigma(X_{t_i})]$ for all $0\le i<n\le N$ and $g\in\mathcal I$.
--
--   **Formalization Note** Times are the indices $0,\dots,N$. "Jointly Lebesgue measurable" is null-measurability of $(x,p)\mapsto\Phi(s,t,x;p)$ for the Lebesgue measure of $\mathbb R\times[0,1]$. $\mathcal E_{s,t}[\xi]$ is evaluated path by path; $\mathbb P(\cdot\mid\mathcal F_s)$ at $\omega$ conditions on the paths agreeing with $\omega$ in the first $s$ moves, and $\mathbb E^{\mathbb Q}[\cdot\mid\sigma(X_{t_i})]$ at $\omega$ conditions on $\{X_{t_i}=X_{t_i}(\omega)\}$. Identities between random variables are stated at every path; every path has positive probability under the tree's hypotheses. The integral in (2.11) is a Bochner integral over $(0,\infty)$; every $\xi$ it is applied to is bounded, so it is finite.
-- source:
--   Ma–Wong–Zhang, Time-consistent conditional expectation under probability distortion, arXiv:1809.08262v5, https://arxiv.org/abs/1809.08262v5, Definition 2.8, eqs. (2.11)–(2.12), p.8; Theorem 3.4 and eqs. (3.12), (3.17), pp.12–13

import Mathlib
import Definitions.Def_DistortedCondExp_Distortion
import Definitions.Def_DistortedCondExp_Tree

open MeasureTheory Set

namespace DistortedCondExp

/-- **Dynamic distortion function** on the times `t_0 < ⋯ < t_N` (Ma–Wong–Zhang, *Time-consistent
conditional expectation under probability distortion*, arXiv:1809.08262v5, Definition 2.8(i),
p.8): a mapping `Φ : 𝒯₂ × ℝ × [0, 1] → [0, 1]` that is jointly Lebesgue measurable in `(x, p)`
for any `(s, t) ∈ 𝒯₂` and, for each `(s, t, x) ∈ 𝒯₂ × ℝ`, the mapping `p ∈ [0, 1] ↦ Φ(s, t, x; p)`
is a distortion function in the sense of Definition 2.1.

**Formalization Note** Times are indices: `Φ s t x u` is `Φ(t_s, t_t, x; u)` and
`𝒯₂ = {(s, t) : 0 ≤ s < t ≤ N}`; values at other indices and at `u ∉ [0, 1]` are irrelevant.
"Jointly Lebesgue measurable in `(x, p)`" is null-measurability of `(x, u) ↦ Φ s t x u` for the
Lebesgue measure of `ℝ × [0, 1]` (the restriction of `volume` on `ℝ × ℝ` to `ℝ × [0, 1]`); Borel
measurability would be a stronger requirement. The range `[0, 1]` on `p ∈ [0, 1]` follows from
`IsDistortion`. -/
def IsDynamicDistortion (N : ℕ) (Φ : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ s t : ℕ, s < t → t ≤ N →
    NullMeasurable (fun z : ℝ × ℝ => Φ s t z.1 z.2)
        ((volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ x : ℝ, IsDistortion (Φ s t x)

/-- The conditional nonlinear expectation `𝓔_{s,t}` of a dynamic distortion function on the
binomial tree (Ma–Wong–Zhang, arXiv:1809.08262v5, Definition 2.8(ii), eq. (2.11), p.8):
`𝓔_{s,t}[ξ] := ∫₀^∞ Φ(s, t, X_s; ℙ(ξ ≥ x | F_s)) dx`, `ξ ∈ 𝕃⁰₊(σ(X_t))`, evaluated at the path
`ω`.

**Formalization Note** `condE x p Φ s t ξ ω` is the value at `ω` of `𝓔_{t_s,t_t}[ξ]` on the
canonical path space of the tree `(x, p)`; `ℙ(· | F_{t_s})(ω)` is the conditional probability given
the atom `histAtom s ω` of `F_{t_s}`. The integral is the Bochner integral over `(0, ∞)` with `≥`
as in (2.11). It is applied only to bounded `ξ ≥ 0` (`g(X_{t_t})` with `g ∈ ℐ`, and
`𝓔_{t_s,t_t}[g(X_{t_t})]`); for those the integrand vanishes beyond `sup ξ`, so the integral is
finite. The argument `t` enters only through `Φ`; the requirement `ξ ∈ σ(X_{t_t})` is met by every
use. -/
noncomputable def condE (x p : ℕ → ℕ → ℝ) (Φ : ℕ → ℕ → ℝ → ℝ → ℝ) {N : ℕ} (s t : ℕ)
    (ξ : Path N → ℝ) (ω : Path N) : ℝ :=
  ∫ y in Ioi (0 : ℝ), Φ s t (X x s ω) (cprob p {ω' | y ≤ ξ ω'} (histAtom s ω))

/-- **Time-consistency** (Ma–Wong–Zhang, arXiv:1809.08262v5, Definition 2.8(iii), eq. (2.12),
p.8): the tower property `𝓔_{r,t}[g(X_t)] = 𝓔_{r,s}[𝓔_{s,t}[g(X_t)]]` for all
`0 ≤ r < s < t ≤ T` and all `g ∈ ℐ`, here on the binomial tree `(x, p)` with times
`t_0 < ⋯ < t_N`.

**Formalization Note** The equality of random variables is stated for every path `ω`; under the
standing hypothesis `0 < p⁺_{i,j} < 1` every path has positive probability, so this is the
almost-sure equality of the paper. -/
def IsTimeConsistent (N : ℕ) (x p : ℕ → ℕ → ℝ) (Φ : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ r s t : ℕ, r < s → s < t → t ≤ N → ∀ g : ℝ → ℝ, InI g → ∀ ω : Path N,
    condE x p Φ r t (fun ω' => g (X x t ω')) ω =
      condE x p Φ r s (condE x p Φ s t (fun ω' => g (X x t ω'))) ω

/-- The **initial condition** of Theorem 3.4 (Ma–Wong–Zhang, arXiv:1809.08262v5, p.13):
`Φ(t_0, t_n, x_{0,0}; p) = φ_{t_n}(p)` for `n = 1, …, N` and every `p ∈ [0, 1]`. -/
def InitialCondition (N : ℕ) (x : ℕ → ℕ → ℝ) (φ : ℕ → ℝ → ℝ) (Φ : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ u ∈ Icc (0 : ℝ) 1, Φ 0 n (x 0 0) u = φ n u

/-- **Equation (3.17)** (Ma–Wong–Zhang, arXiv:1809.08262v5, Theorem 3.4, p.13): for all
`0 ≤ i < n ≤ N`, `0 ≤ j ≤ i` and `0 ≤ k ≤ n`,
`Φ(t_i, t_n, x_{i,j}; ℙ{X_{t_n} ≥ x_{n,k} | X_{t_i} = x_{i,j}}) = ℚ{X_{t_n} ≥ x_{n,k} | X_{t_i} = x_{i,j}}`,
where `ℚ` is the path law with up-probabilities `q⁺` of (3.13)/(3.15). -/
def Satisfies317 (N : ℕ) (x p : ℕ → ℕ → ℝ) (φ : ℕ → ℝ → ℝ) (Φ : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ i n j k : ℕ, i < n → n ≤ N → j ≤ i → k ≤ n →
    Φ i n (x i j)
        (cprob p {ω : Path N | x n k ≤ X x n ω} {ω : Path N | X x i ω = x i j}) =
      cprob (qPlus N x p φ) {ω : Path N | x n k ≤ X x n ω} {ω : Path N | X x i ω = x i j}

/-- **Equation (3.12)** (Ma–Wong–Zhang, arXiv:1809.08262v5, p.12) for all pairs of times:
`𝓔_{s,t}[g(X_t)] = 𝔼^ℚ[g(X_t) | σ(X_s)]` for all `g ∈ ℐ`, for every `0 ≤ s < t ≤ N`.

**Formalization Note** `𝔼^ℚ[· | σ(X_{t_i})]` at the path `ω` is the `ℚ`-conditional expectation
given the event `{X_{t_i} = X_{t_i}(ω)}`; the identity is stated at every path. -/
def Satisfies312 (N : ℕ) (x p : ℕ → ℕ → ℝ) (φ : ℕ → ℝ → ℝ) (Φ : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ i n : ℕ, i < n → n ≤ N → ∀ g : ℝ → ℝ, InI g → ∀ ω : Path N,
    condE x p Φ i n (fun ω' => g (X x n ω')) ω =
      cexp (qPlus N x p φ) (fun ω' => g (X x n ω')) {ω' : Path N | X x i ω' = X x i ω}

end DistortedCondExp


