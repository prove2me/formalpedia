-- Prove2me | Definitions.Def_HasseHSG_Generator_QLogCurve
-- name    : HasseHSG_Generator_QLogCurve
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:35:40.617648+00:00
-- url     : https://prove2.me/theorems/bdf66fd5-008d-457b-8f11-f6dea84222df
-- title:
--   The $q$-logarithmic curve $p$, the $q$-derivative on $F(q)[[t]]$, the integers $B,R$ and the truncated curves $p_{q_0}$ (Eqs. (5), (15), (19), (20))
-- statement:
--   Let $F$ be a field, $a_1,\dots,a_n\in F$, and $q$ transcendental over $F$.
--
--   1. The **$q$-logarithmic curve** (Eq. (15)) is $p=(p_1,\dots,p_n)$ with
--   $$p_i(t)=\sum_{m\ge1}\frac{(a_it)^m}{[m]_q}\in F(q)[[t]].$$
--   For $f\in F(q)[t,x]$, the composition $f\circ p=f(t,p_1(t),\dots,p_n(t))\in F(q)[[t]]$ is well defined because each $p_i$ has zero constant term.
--   2. The **$q$-derivative** on $F(q)[[t]]$ is
--   $$\frac{d_q}{dt}h=\frac{h(qt)-h(t)}{(q-1)t}$$
--   (Eq. (5)). It sends $t^m$ to $[m]_q t^{m-1}$.
--   3. The integers of Eq. (19) are
--   $$B=(nd-1)\binom r2+r,\qquad R=(nd-1)\binom r3+(d-1)\binom r2.$$
--   4. For $q_0\in F$, the **truncated $q_0$-logarithm** (Eq. (20)) is
--   $$p_{q_0,i}(t)=\sum_{m=1}^{B-1}\frac{(a_it)^m}{[m]_{q_0}}\in F[t].$$
--
--   The curve $p$ is the $q$-analogue of the logarithmic curve of the characteristic-zero construction. Its truncations at specialised values $q_0$ are the pieces that the final generator interpolates.
--
--   **Formalization Note.**
--   - "$h\equiv0\bmod t^B$" is stated as $t^B\mid h$.
--   - `qDerivT` divides the series $h(qt)-h(t)$ by $t$ by shifting its coefficients down.
--   - `Bnum` and `Rnum` take values in $\mathbb Z$, because $nd-1$ can be $-1$.
--   - `truncCurve a q₀ B` takes the truncation length as a natural number; the sum runs over $1\le m<B$.
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 19, Eq. (5); p. 23, Eq. (15); p. 35, Eq. (19); p. 37, Eq. (20)

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference

open MvPolynomial

namespace HasseHSG.Generator

/-!
Bal, Ghosh, *Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary
Characteristic Fields*: the `q`-logarithmic curve `p` (Eq. (15), p. 23), the `q`-derivative
`d_q/dt` on `F(q)[[t]]` (Eq. (5), p. 19; used on power series in Lemma 5.4 and Corollary 5.5),
the integers `B`, `R` of Eq. (19) (p. 35) and the truncated curves `p_{q₀}` of Eq. (20) (p. 37).
-/

/-- The `q`-logarithmic curve `pᵢ(t) = Σ_{m ≥ 1} (aᵢ t)^m / [m]_q ∈ F(q)[[t]]` (Eq. (15)). -/
noncomputable def qLogCurve {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (i : Fin n) :
    PowerSeries (Fq F) :=
  PowerSeries.mk fun m => if m = 0 then 0 else cF (a i) ^ m / qInt (qVar F) m

/-- The composition `f ∘ p = f(t, p₁(t), …, pₙ(t)) ∈ F(q)[[t]]` of `f ∈ F(q)[t, x]` with the curve
`p` (p. 23). -/
noncomputable def compP {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (f : PolyQT F n) :
    PowerSeries (Fq F) :=
  MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom (qLogCurve a) f

/-- The `q`-derivative on `F(q)[[t]]`: `(d_q/dt) h = (h(qt) − h(t)) / ((q − 1) t)` (Eq. (5)); the
numerator has zero constant term, and division by `t` shifts coefficients down by one. -/
noncomputable def qDerivT {F : Type*} [Field F] (h : PowerSeries (Fq F)) : PowerSeries (Fq F) :=
  PowerSeries.mk fun m =>
    PowerSeries.coeff (m + 1) (PowerSeries.rescale (qVar F) h - h) / (qVar F - 1)

/-- `B = (nd − 1)·binom(r, 2) + r ∈ ℤ` (Eq. (19)). -/
def Bnum (n d r : ℕ) : ℤ := ((n * d : ℕ) - 1 : ℤ) * (r.choose 2 : ℤ) + r

/-- `R = (nd − 1)·binom(r, 3) + (d − 1)·binom(r, 2) ∈ ℤ` (Eq. (19)). -/
def Rnum (n d r : ℕ) : ℤ := ((n * d : ℕ) - 1 : ℤ) * (r.choose 3 : ℤ) + ((d : ℤ) - 1) * (r.choose 2 : ℤ)

/-- The truncated `q₀`-logarithm `p_{q₀,i}(t) = Σ_{m=1}^{B−1} (aᵢ t)^m / [m]_{q₀} ∈ F[t]`
(Eq. (20)), for `q₀ ∈ F` and a truncation length `B` (the sum runs over `1 ≤ m < B`). -/
noncomputable def truncCurve {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (q₀ : F) (B : ℕ)
    (i : Fin n) : Polynomial F :=
  ∑ m ∈ Finset.Ico 1 B, Polynomial.C (a i ^ m / qInt q₀ m) * Polynomial.X ^ m

end HasseHSG.Generator


