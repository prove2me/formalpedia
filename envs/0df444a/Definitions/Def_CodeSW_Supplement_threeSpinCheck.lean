-- Prove2me | Definitions.Def_CodeSW_Supplement_threeSpinCheck
-- name    : CodeSW_Supplement_threeSpinCheck
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:49:38.741842+00:00
-- url     : https://prove2.me/theorems/cf8ae2b7-b375-4506-8d67-81bb8cc5b3cc
-- title:
--   The 3-spin Curie-Weiss parity check matrix $h_n$ and the critical constant $c^*$
-- statement:
--   1. The **ferromagnetic 3-spin Curie-Weiss model** on $n$ bits has one check for each 3-element subset $\{i,j,k\}\subseteq[n]$, with ones exactly at $i,j,k$. Its parity check matrix $h_n\in\{0,1\}^{\binom n3\times n}$ has all strings of Hamming weight $3$ as rows, so the energy is
--   $$H(x)=2|h_nx|=2\binom{|x|}{3}+2|x|\binom{n-|x|}{2}.$$
--   2. With the entropy function $S(a)=-a\ln a-(1-a)\ln(1-a)$, let
--   $$J(u)=3\Big(\ln 2-S\big(\tfrac{1-u}{2}\big)\Big)-\frac u2\ln\frac{1+u}{1-u},\qquad 0<u<1,$$
--   let $u^*$ be its unique zero in $(0,1)$, and set
--   $$c^*=\frac{\ln\big((1+u^*)/(1-u^*)\big)}{(u^*)^2}.$$
--   Numerically $u^*\approx0.948059$ and $c^*\approx4.03251$, inside the page's $4.0324<c^*<4.0326$.
--
--   At $c=c^*$ the function $f(a)=S(a)-c(a^3/3+a(1-a)^2)$ has two equal global maxima, at $a_0=(1-u^*)/2$ and $a_1=1/2$, the phase coexistence behind Theorem 25.
--
--   **Formalization Note** Rows of $h_n$ are indexed by `Fin (n.choose 3)` through an enumeration of the 3-element subsets of `Fin n`, which is a parameter. Since $J>0$ on $(0,u^*)$ and $J<0$ on $(u^*,1)$, $u^*$ is defined as $\sup\{u\in(0,1):J(u)>0\}$; the module also defines `entropyS`, `Jfun`, `uStar` and `cStar`. $c^*$ is defined by this formula, not by the property of Lemma 23.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), §3.4, eq. (11), p.25; Lemma 23 and its proof, p.26

import Mathlib
import Definitions.Def_CodeSW_kerA

set_option autoImplicit false

open Matrix

noncomputable section

namespace CodeSW.Supplement

/-- The parity check matrix `h_n` of the **ferromagnetic 3-spin Curie-Weiss model**: its rows are
all strings of Hamming weight 3 in `{0,1}^n`, one per 3-element subset `{i,j,k} ⊆ [n]`, so the
checks form the complete 3-uniform hypergraph and `H(x) = 2|h_n x| = 2C(|x|,3) + 2|x|C(n−|x|,2)`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, §3.4, eq. (11), p.25).

**Formalization Note** Rows are indexed by `Fin (n.choose 3)` through an enumeration `e` of the
3-element subsets of `Fin n`; row `r` has ones exactly at the three elements of `e r`. -/
def threeSpinCheck (n : ℕ) (e : Fin (n.choose 3) ≃ {s : Finset (Fin n) // s.card = 3}) :
    Matrix (Fin (n.choose 3)) (Fin n) (ZMod 2) :=
  Matrix.of fun r i => if i ∈ (e r).1 then 1 else 0

/-- The entropy function `S(a) = −a ln a − (1 − a) ln(1 − a)`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §3.4, p.25). Used on `0 < a < 1`. -/
def entropyS (a : ℝ) : ℝ := -a * Real.log a - (1 - a) * Real.log (1 - a)

/-- `J(u) = 3(ln 2 − S((1−u)/2)) − (u/2) ln((1+u)/(1−u))` on `0 < u < 1`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, proof of Lemma 23, p.26). -/
def Jfun (u : ℝ) : ℝ :=
  3 * (Real.log 2 - entropyS ((1 - u) / 2)) - u / 2 * Real.log ((1 + u) / (1 - u))

/-- `u*`, the unique zero of `J` in `(0,1)` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, proof
of Lemma 23, p.26: "J has exactly one zero u* in (0,1)").

**Formalization Note** `J > 0` on `(0, u*)` and `J < 0` on `(u*, 1)` (Lemma 23's proof), so `u*` is
the supremum of `{u ∈ (0,1) : J(u) > 0}`, a nonempty set bounded by `1`. Numerically
`u* ≈ 0.948059`. -/
def uStar : ℝ := sSup {u : ℝ | 0 < u ∧ u < 1 ∧ 0 < Jfun u}

/-- The **critical constant** `c* = ln((1+u*)/(1−u*)) / (u*)²`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, Lemma 23 and its proof, p.26; `4.0324 < c* < 4.0326`).
At `c = c*` the function `f(a) = S(a) − c(a³/3 + a(1−a)²)` has two global maxima on `(0,1)`, at
`a₀ = (1 − u*)/2` and `a₁ = 1/2`.

**Formalization Note** `c*` is defined by this explicit formula, not by Lemma 23's property;
numerically `c* ≈ 4.03251`. -/
def cStar : ℝ := Real.log ((1 + uStar) / (1 - uStar)) / uStar ^ 2

end CodeSW.Supplement


