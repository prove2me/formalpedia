-- Prove2me | Definitions.Def_RevisitXor_corr
-- name    : RevisitXor_corr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:30.075549+00:00
-- url     : https://prove2.me/theorems/72c6d33f-3311-4120-a267-37af228516e4
-- title:
--   Correlation $\mathbb E_x(-1)^{f(x)+g(x)}$ of two Boolean functions
-- statement:
--   Write $[2]=\{0,1\}$, viewed as the field $\mathbb F_2$, and $[2]^n$ for the $n$-bit cube. For $b\in[2]$ let $(-1)^b$ be $1$ if $b=0$ and $-1$ if $b=1$.
--
--   The **correlation** of two functions $f,g:A\to[2]$ on a finite set $A$ is the signed average
--
--   $$\operatorname{corr}(f,g)=\mathbb E_{x\in A}\,(-1)^{f(x)+g(x)}=\frac1{|A|}\sum_{x\in A}(-1)^{f(x)+g(x)}.$$
--
--   It lies in $[-1,1]$, equals $1$ when $f=g$ and $-1$ when $f=g\oplus1$. A function $f$ "has correlation $\le\epsilon$" with a class of functions when $\operatorname{corr}(f,g)\le\epsilon$ for every $g$ in the class. Every correlation bound of the mission is stated with this quantity.
--
--   **Formalization Note** The correlation is signed, as defined on p.1; no absolute value is taken. The domain is any finite type, so the same definition serves $[2]^n$, $[2]^{kn}$ and the split $[2]^{2m}=[2]^m\times[2]^m$. The cube is `Cube n := Fin n → ZMod 2` and $(-1)^b$ is `sgn b`. On an empty domain the value is $0$; every domain used here is nonempty.
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), p.1

import Mathlib

namespace RevisitXor

/-- The Boolean cube `[2]^n`, with `[2] = {0, 1}` read as the field `ZMod 2`. Viola, *Revisiting
the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), p.1:
"Here [2] = {0, 1}".

**Formalization Note.** Addition in `ZMod 2` is the paper's `⊕` (and `+` modulo 2). -/
abbrev Cube (n : ℕ) : Type := Fin n → ZMod 2

/-- The sign `(-1)^b ∈ {1, -1}` of a bit `b ∈ ZMod 2`: `1` at `0` and `-1` at `1`. -/
noncomputable def sgn (b : ZMod 2) : ℝ := (-1 : ℝ) ^ b.val

/-- **Correlation.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of
August 25, 2026, sha256 3b49e10d…716), p.1: `f` "has correlation ≤ ϵ with circuits of size s,
meaning E_{x∈[2]^n}(−1)^{g(x)+f(x)} ≤ ϵ for every such circuit g".

`corr f g` is the uniform average of `(-1)^{f(x)+g(x)}` over a finite domain `α`.

**Formalization Note.** The correlation is the **signed** average, as defined on p.1; no absolute
value is taken. It is symmetric in `f` and `g`. The domain is any finite type, so the same
definition serves `[2]^n`, `[2]^{kn}` (curried as `Fin k → [2]^n`) and the split
`[2]^{2m} = [2]^m × [2]^m`. On an empty domain the value is `0`; every domain used in this
mission is nonempty. -/
noncomputable def corr {α : Type*} [Fintype α] (f g : α → ZMod 2) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, sgn (f x + g x)

end RevisitXor


