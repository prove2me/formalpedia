-- Prove2me | Definitions.Def_QubitFreqSensing_SignPattern
-- name    : QubitFreqSensing_SignPattern
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:01.158242+00:00
-- url     : https://prove2.me/theorems/79502a95-dedf-453e-b8e2-f6940e3aa304
-- title:
--   $\pm1$ sign patterns on $[0,T]$, constant pieces, the rounding $R_K(h)$ and the correlation $A_{\omega,\phi,T,\tau}(f)$
-- statement:
--   1. A function $f$ is a **sign pattern with $m$ sign changes** on $[0,T]$ if there are times $0=t_0<t_1<\dots<t_{m+1}=T$ and signs $\sigma_0,\dots,\sigma_m\in\{-1,1\}$ with $\sigma_{k+1}=-\sigma_k$, such that $f=\sigma_k$ on $[t_k,t_{k+1})$ and $f(T)=\sigma_m$. This is the shape of the functions $f_0,f_1$ of Protocol 1 after empty pieces are discarded and equal neighbours merged.
--   2. $f$ has **at most $n$ constant pieces** on $[0,T]$ if there are $0=t_0\le\dots\le t_n=T$ with $f$ constant on each $[t_k,t_{k+1})$.
--   3. **The rounding $R_K(h)$** (Lemma 5.12). Split $[0,T]$ into $K$ intervals $I=[a,a+\delta]$, $\delta=T/K$, put $p_I=\bigl(\delta+\int_I h\bigr)/2$ and
--   $$
--   R_K(h)(t)=\begin{cases}+1,& a\le t<a+p_I,\\ -1,& a+p_I\le t<a+\delta,\end{cases}
--   $$
--   with the left limiting sign at $T$.
--   4. **The correlation** (8):
--   $$
--   A_{\omega,\phi,T,\tau}(f)=B\int_0^T f(t)\cos\bigl(\omega(t+\tau)+\phi\bigr)\,dt .
--   $$
--   A trial with pattern $f$ and wait $\tau$ returns $1$ with probability $\sin^2 A_{\omega,\phi,T,\tau}(f)$ (eq. (9)).
--
--   **Formalization Note** Indices are $0$-based. For $t\in[0,T)$ the interval of $R_K$ is the $\lfloor t/\delta\rfloor$-th; $t=T$ belongs to the last interval and gets $-1$ if $p_I<\delta$ and $+1$ if $p_I=\delta$. Values outside $[0,T]$ play no role.
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Protocol 1, step 1, p.12; eq. (8), p.15; Lemma 5.12, p.22; Theorem 5.13, p.23

import Mathlib

open MeasureTheory

namespace QubitFreqSensing

/-- **A ±1 pulse pattern with `m` sign changes** on `[0, T]` (Chen, Coladangelo, Li, Zhang,
manuscript (STOC 2027 submission), Protocol 1, step 1, p.12; Theorem 5.13, p.23): there are times
`0 = t₀ < t₁ < ⋯ < t_{m+1} = T` and signs `σ₀, …, σ_m ∈ {−1, 1}` with `σ_{k+1} = −σ_k` such that
`f = σ_k` on `[t_k, t_{k+1})` and `f(T) = σ_m`.

**Formalization Note** Indices are 0-based (the page writes `0 = t₀ < ⋯ < t_m = T` with pieces
`k = 1, …, m`); the pattern has `m + 1` pieces and exactly `m` sign changes (empty pieces discarded
and equal neighbours merged, as on p.12). Values of `f` outside `[0, T]` are irrelevant. -/
def IsSignPattern (T : ℝ) (f : ℝ → ℝ) (m : ℕ) : Prop :=
  ∃ (t : Fin (m + 2) → ℝ) (σ : Fin (m + 1) → ℝ),
    t 0 = 0 ∧ t (Fin.last (m + 1)) = T ∧ StrictMono t ∧
    (∀ k, σ k = 1 ∨ σ k = -1) ∧
    (∀ k : Fin m, σ k.succ = -σ k.castSucc) ∧
    (∀ k : Fin (m + 1), ∀ x ∈ Set.Ico (t k.castSucc) (t k.succ), f x = σ k) ∧
    f T = σ (Fin.last m)

/-- `f` is constant on each of `n` consecutive half-open pieces `[t_k, t_{k+1})` covering `[0, T)`
(`0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_n = T`; empty pieces allowed): "at most `n` constant pieces". -/
def HasConstPieces (T : ℝ) (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ t : Fin (n + 1) → ℝ, t 0 = 0 ∧ t (Fin.last n) = T ∧ Monotone t ∧
    ∀ k : Fin n, ∃ σ : ℝ, ∀ x ∈ Set.Ico (t k.castSucc) (t k.succ), f x = σ

/-- **The rounding `R_K(h)`** (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027 submission),
Lemma 5.12, p.22). Partition `[0, T]` into `K` intervals `I = [a, a + δ]`, `δ = T/K`; with
`p_I = (δ + ∫_I h)/2`, `R_K(h)(t) = +1` for `a ≤ t < a + p_I` and `−1` for `a + p_I ≤ t < a + δ`,
"half-open intervals and the left limiting sign at T".

**Formalization Note** For `t ∈ [0, T)` the interval index is `⌊t/δ⌋`; `t = T` is assigned to the
last interval and gets its left limiting sign: `−1` if `p_I < δ`, `+1` if `p_I = δ`. Values outside
`[0, T]` are irrelevant. -/
noncomputable def roundK (T : ℝ) (K : ℕ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  let δ := T / K
  let a := (min ⌊t / δ⌋₊ (K - 1) : ℕ) * δ
  let p := (δ + ∫ s in a..a + δ, h s) / 2
  if t < a + p then 1 else if t < a + δ then -1 else if p < δ then -1 else 1

/-- **The phase-shifted correlation** `A_{ω,ϕ,T,τ}(f) = B ∫₀^T f(t) cos(ω(t + τ) + ϕ) dt`
(Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027 submission), eq. (8), p.15). A trial whose
pulse pattern is `f` and whose wait is `τ` returns `1` with probability `sin²(A_{ω,ϕ,T,τ}(f))`
(eq. (9), §6 (17)). -/
noncomputable def corrA (B ω ϕ T τ : ℝ) (f : ℝ → ℝ) : ℝ :=
  B * ∫ t in (0 : ℝ)..T, f t * Real.cos (ω * (t + τ) + ϕ)

end QubitFreqSensing


