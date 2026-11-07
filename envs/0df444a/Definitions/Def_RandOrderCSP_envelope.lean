-- Prove2me | Definitions.Def_RandOrderCSP_envelope
-- name    : RandOrderCSP_envelope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:08.583251+00:00
-- url     : https://prove2.me/theorems/88ed01f6-c0e5-4cec-8dd1-e22f56705aa6
-- title:
--   The Fourier envelope and $(\zeta,s,b)$-boundedness
-- statement:
--   For $\zeta>0$, $s,N\in\mathbb N$, $s\le(e^2q^4/\zeta^2)N$ and $0\le r\le N$,
--
--   $$U_{\zeta,s,N}(r)=\begin{cases}(\zeta\sqrt{sN}/r)^{r/2}& r\in[0,s]\\(\zeta\sqrt N/\sqrt r)^{r/2}& r\in[s,(e^2q^4/\zeta^2)N]\\(eq^2N/r)^{r/2}& r\in[(e^2q^4/\zeta^2)N,N]\end{cases}$$
--
--   with $U_{\zeta,s,N}(0)=1$. A distribution $D$ on $\mathbb Z_q^N$ is **$(\zeta,s)$-bounded** when $\sum_{\mathrm{wt}(V)=r}|\hat\mu_D(V)|\le U_{\zeta,s,N}(r)$ for every $0\le r\le N$, and **$(\zeta,s,b)$-bounded** if moreover $\log_q\|\mu_D\|_\infty\le b$. This is the invariant maintained along the rounds of the DIHP game.
--
--   **Formalization Note** The envelope's domain condition $s\le(e^2q^4/\zeta^2)N$ is a conjunct of the boundedness predicate. The density bound is written as $|\mu_D(X)|\le q^b$ for all $X$.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), (5.3), p.23

import Mathlib
import Definitions.Def_RandOrderCSP_fourierCoeff

namespace RandOrderCSP

/-- **The Fourier envelope `U_{ζ,s,N}`** (5.3), p.23.

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.23: for `r ∈ [0, N]`,
`U_{ζ,s,N}(r) := (ζ√(sN)/r)^{r/2}` on `[0, s]`, `(ζ√N/√r)^{r/2}` on `[s, (e²q⁴/ζ²)N]`, and
`(eq²N/r)^{r/2}` on `[(e²q⁴/ζ²)N, N]`, with the convention `U_{ζ,s,N}(0) = 1`.

**Formalization Note.** The argument `r` is a natural number, the only values at which the envelope
is used. At `r = 0` the exponent is `0`, so the value is `1` as printed. The branches agree at the two
break points (the sanity file checks it), so assigning a break point to the lower branch is harmless. -/
noncomputable def envelope (q : ℕ) (ζ : ℝ) (s N r : ℕ) : ℝ :=
  if (r : ℝ) ≤ s then (ζ * Real.sqrt (s * N) / r) ^ ((r : ℝ) / 2)
  else if (r : ℝ) ≤ Real.exp 2 * (q : ℝ) ^ 4 / ζ ^ 2 * N then
    (ζ * Real.sqrt N / Real.sqrt r) ^ ((r : ℝ) / 2)
  else (Real.exp 1 * (q : ℝ) ^ 2 * N / r) ^ ((r : ℝ) / 2)

variable {U : Type} [Fintype U] [DecidableEq U] {q : ℕ} [NeZero q]

/-- **`(ζ, s)`-bounded** (p.23): with `N = |U|` and `μ_D(X) = q^N D(X)`, the sum of `|μ̂_D(V)|` over
`wt(V) = r` is at most `U_{ζ,s,N}(r)` for every `0 ≤ r ≤ N`.

**Formalization Note.** The envelope is printed only under the standing assumption
`s ≤ (e²q⁴/ζ²)N`; that inequality is a conjunct here, so "not bounded" also holds when it fails. In
Theorem 5.10 the constant `σ` is chosen after `ζ″`, so `s ≤ σn` gives the inequality for `ζ″`. -/
def IsEnvBounded (ζ : ℝ) (s : ℕ) (D : (U → ZMod q) → ℝ) : Prop :=
  (s : ℝ) ≤ Real.exp 2 * (q : ℝ) ^ 4 / ζ ^ 2 * (Fintype.card U : ℝ) ∧
    ∀ r ≤ Fintype.card U,
      ∑ V ∈ Finset.univ.filter (fun V : U → ZMod q => wt V = r),
          ‖fourierCoeff (fun X => ((density D X : ℝ) : ℂ)) V‖ ≤
        envelope q ζ s (Fintype.card U) r

/-- **`(ζ, s, b)`-bounded** (p.23): `(ζ, s)`-bounded and `log_q ‖μ_D‖_∞ ≤ b`.

**Formalization Note.** The second clause is written `|μ_D(X)| ≤ q^b` for every `X`. For `q ≥ 2` and a
distribution `D` the two are equivalent, since `‖μ_D‖_∞ ≥ 1 > 0` means the logarithm has a positive
argument. -/
def IsEnvBoundedB (ζ : ℝ) (s : ℕ) (b : ℝ) (D : (U → ZMod q) → ℝ) : Prop :=
  IsEnvBounded ζ s D ∧ ∀ X, |density D X| ≤ (q : ℝ) ^ b

end RandOrderCSP


