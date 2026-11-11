-- Prove2me | Definitions.Def_MarginMaxima_Critical_ReedSolomon
-- name    : MarginMaxima_Critical_ReedSolomon
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:01:47.854778+00:00
-- url     : https://prove2.me/theorems/5cf98854-116a-4e42-9c3e-bb074527d118
-- title:
--   The Reed–Solomon gadget of §5: $\theta,\pi,g^w,g^0,R(q,k)$; the exponent sets $I,R_0,W_p,R,T$; the spaces $V,E,G$, $\tau=\dim_{\mathbb F_q}G$; spanning tuples, lines $x_0+Gh$ and the agreement $A(y)$
-- statement:
--   Let $q\ge3$ be a prime power and $k\ge4$ an integer. Put
--   $$\theta=\frac1q+3q^{-k},\quad \pi=\frac{1+\theta}{2\sqrt q},\quad g^w=\frac{1-\theta}{2\sqrt q},\quad g^0=\frac{1-\theta}{2\sqrt q+1+\theta},\quad R(q,k)=\exp\big(9(k+2)(2k+5)q^{2k+10}\ln q\big).$$
--   **§5.1.** Fix an integer $u\ge 2k+5$, $K=\mathbb F_{q^u}$, $N=|K|=q^u$, $a=q^{u-k}$, $I=\{0,\dots,a-1\}$, $w_p=2q^{p-k-1}$, $R_0=\{0,\dots,a+w_{u-k}\}$, $W_p=\{q^p,\dots,q^p+w_p\}$ ($u-k<p\le u-1$), $R=R_0\cup\bigcup_pW_p$, $D=\max R=q^{u-1}+2q^{u-k-2}$, $T_0=R_0+I$, $T_p=W_p+I$, $T=R+I$ (sumsets). Polynomials have degree less than $N$ and are identified with their functions on $K$. $V$ and $E$ are the $K$-spans of $x^j$ ($j\in I$) and of $x^b$ ($b\in T$). $G$ is the set of functions $K\to\mathbb F_q$ of the form $\phi(x)=\sum_{s\in R}c_sx^s$, $c_s\in K$; it is an $\mathbb F_q$-space, $\tau=\dim_{\mathbb F_q}G$ and $M=|G|=q^\tau$.
--
--   **§5.2.** Let $e\ge1$ and $C=E^e$; the letter of $y\in C$ at $x\in K$ is $y(x)\in K^e$. A tuple $h\in V^e$ is **spanning** if its components span $V$ over $K$. For $x_0\in C$ and spanning $h$ the **line** is $B(x_0,h)=x_0+Gh=\{x_0+\phi h:\phi\in G\}$, and $A(y)=\#\{x\in K:(y-x_0)(x)\in\mathbb F_q h(x)\}$.
--
--   These are the objects of the Reed–Solomon construction behind Theorems 5.1, 5.2 and 5.8.
--
--   **Formalization Note.** $\mathbb F_q$ and $K$ are finite fields `F`, `K` with an `Algebra F K`; the lemmas assume `Fintype.card F = q` and `Fintype.card K = q ^ u`, and $\mathbb F_q\subseteq K$ is `Fq F K`, the image of `F`. Polynomials of degree $<N$ are elements of `K[X]`: `Vsp`, `Esp` are `Submodule.span K` of the monomials `X ^ j`, and `Gsp` is the `F`-submodule of `K[X]` of the elements of the `K`-span of `X ^ s`, `s ∈ R`, whose value at every `x : K` lies in `Fq F K`; `tauRS` is its `Module.finrank F`. $D$ is `Dval` $=q^{u-1}+2q^{u-k-2}$. The components of $T$ are `Tcomp q k u p` for $p\in[u-k,u-1]$, with $p=u-k$ standing for $T_0$. Elements of $C$ are tuples `Fin e → K[X]` with components in `Esp`; `IsSpanning` requires the components in $V$ and their span equal to $V$; `rsLine` is $\{x_0+(\phi h_i)_i:\phi\in G\}$ and `rsAgree` counts the `x : K` with $(y-x_0)(x)=c\,h(x)$ for some $c\in\mathbb F_q$.
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 9 (§5 parameters, Theorem 5.1's R(q,k)), pp. 9–10 (§5.1), p. 11 (§5.2)

import Mathlib

open Polynomial

namespace MarginMaxima.Critical

/-! ### Parameters of §5 (functions of the prime power `q ≥ 3` and the integer `k ≥ 4`) -/

/-- `θ = 1/q + 3 q^{−k}`. -/
noncomputable def thetaRS (q k : ℕ) : ℝ := 1 / (q : ℝ) + 3 * (q : ℝ) ^ (-(k : ℤ))

/-- `π = (1 + θ)/(2√q)`. -/
noncomputable def piRS (q k : ℕ) : ℝ := (1 + thetaRS q k) / (2 * Real.sqrt q)

/-- `g^w = (1 − θ)/(2√q)` (margin with witnesses; a function of `q, k`). -/
noncomputable def gwRS (q k : ℕ) : ℝ := (1 - thetaRS q k) / (2 * Real.sqrt q)

/-- `g^0 = (1 − θ)/(2√q + 1 + θ)` (margin at zero witnesses; a function of `q, k`). -/
noncomputable def g0RS (q k : ℕ) : ℝ := (1 - thetaRS q k) / (2 * Real.sqrt q + 1 + thetaRS q k)

/-- `R(q, k) = exp(9 (k + 2)(2k + 5) q^{2k+10} ln q)`. -/
noncomputable def RqK (q k : ℕ) : ℝ :=
  Real.exp (9 * (k + 2) * (2 * k + 5) * (q : ℝ) ^ (2 * k + 10) * Real.log q)

/-! ### §5.1 The exponent sets (with `u ≥ 2k + 5`) -/

/-- `a = q^{u−k}`. -/
def aRS (q k u : ℕ) : ℕ := q ^ (u - k)

/-- `I = {0, …, a − 1}`. -/
def Iset (q k u : ℕ) : Finset ℕ := Finset.range (aRS q k u)

/-- `w_p = 2 q^{p−k−1}`. -/
def wRS (q k p : ℕ) : ℕ := 2 * q ^ (p - k - 1)

/-- `R₀ = {0, …, a + w_{u−k}}`. -/
def R0set (q k u : ℕ) : Finset ℕ := Finset.range (aRS q k u + wRS q k (u - k) + 1)

/-- `W_p = {q^p, …, q^p + w_p}`. -/
def Wset (q k p : ℕ) : Finset ℕ := Finset.Icc (q ^ p) (q ^ p + wRS q k p)

/-- The indices `u − k < p ≤ u − 1` of the short intervals `W_p`. -/
def Pidx (k u : ℕ) : Finset ℕ := Finset.Ioc (u - k) (u - 1)

/-- `R = R₀ ∪ ⋃_{u−k<p≤u−1} W_p`. -/
def Rset (q k u : ℕ) : Finset ℕ := R0set q k u ∪ (Pidx k u).biUnion (Wset q k)

/-- `D = q^{u−1} + 2 q^{u−k−2}` (the paper's `max R`). -/
def Dval (q k u : ℕ) : ℕ := q ^ (u - 1) + 2 * q ^ (u - k - 2)

/-- The sumset `A + B = {x + y : x ∈ A, y ∈ B}`. -/
def sumset (A B : Finset ℕ) : Finset ℕ := (A ×ˢ B).image fun p => p.1 + p.2

/-- The components of `T`, indexed by `p ∈ [u − k, u − 1]`: `T_{u−k} := T₀ = R₀ + I` and
`T_p = W_p + I` for `u − k < p ≤ u − 1`. -/
def Tcomp (q k u p : ℕ) : Finset ℕ :=
  if p = u - k then sumset (R0set q k u) (Iset q k u) else sumset (Wset q k p) (Iset q k u)

/-- `T = R + I`. -/
def Tset (q k u : ℕ) : Finset ℕ := sumset (Rset q k u) (Iset q k u)

/-- The `K`-span of the monomials `X^j`, `j ∈ A`, in `K[X]`. -/
noncomputable def monoSpan (K : Type) [Field K] (A : Finset ℕ) : Submodule K K[X] :=
  Submodule.span K ((fun j : ℕ => (X : K[X]) ^ j) '' (A : Set ℕ))

/-- `V = span_K {x^j : j ∈ I}`. Polynomials of degree `< N = |K|` stand for functions on `K`. -/
noncomputable def Vsp (K : Type) [Field K] (q k u : ℕ) : Submodule K K[X] :=
  monoSpan K (Iset q k u)

/-- `E = span_K {x^b : b ∈ T}`. -/
noncomputable def Esp (K : Type) [Field K] (q k u : ℕ) : Submodule K K[X] :=
  monoSpan K (Tset q k u)

/-- The subfield `F_q ⊆ K`, the image of `F`. -/
def Fq (F K : Type) [Field F] [Field K] [Algebra F K] : Set K := Set.range (algebraMap F K)

/-- `G`: the polynomials `Σ_{s ∈ R} c_s x^s`, `c_s ∈ K`, that are `F_q`-valued at every point of
`K`, as an `F_q`-subspace of `K[X]`. -/
noncomputable def Gsp (F K : Type) [Field F] [Field K] [Algebra F K] (q k u : ℕ) :
    Submodule F K[X] :=
  (monoSpan K (Rset q k u)).restrictScalars F ⊓
    ⨅ x : K, Submodule.comap ((Polynomial.leval x).restrictScalars F)
      (LinearMap.range (Algebra.linearMap F K))

/-- `τ = dim_{F_q} G`. -/
noncomputable def tauRS (F K : Type) [Field F] [Field K] [Algebra F K] (q k u : ℕ) : ℕ :=
  Module.finrank F (Gsp F K q k u)

/-! ### §5.2 Lines and agreement (with `e ≥ 1`, `C = E^e`) -/

/-- `h ∈ V^e` is spanning: its components lie in `V` and span `V` over `K`. -/
def IsSpanning (K : Type) [Field K] (q k u : ℕ) {e : ℕ} (h : Fin e → K[X]) : Prop :=
  (∀ i, h i ∈ Vsp K q k u) ∧ Submodule.span K (Set.range h) = Vsp K q k u

/-- The line `B(x₀, h) = x₀ + G h = {x₀ + ϕ h : ϕ ∈ G}`. -/
def rsLine (F K : Type) [Field F] [Field K] [Algebra F K] (q k u : ℕ) {e : ℕ}
    (x0 h : Fin e → K[X]) : Set (Fin e → K[X]) :=
  {y | ∃ ϕ ∈ Gsp F K q k u, y = x0 + fun i => ϕ * h i}

open Classical in
/-- `A(y) = #{x ∈ K : (y − x₀)(x) ∈ F_q h(x)}`, where `y(x) ∈ K^e` is the letter of `y` at `x`. -/
noncomputable def rsAgree (F K : Type) [Field F] [Field K] [Fintype K] [Algebra F K] {e : ℕ}
    (x0 h y : Fin e → K[X]) : ℕ :=
  (Finset.univ.filter fun x : K =>
    ∃ c ∈ Fq F K, ∀ i, (y i - x0 i).eval x = c * (h i).eval x).card

end MarginMaxima.Critical


