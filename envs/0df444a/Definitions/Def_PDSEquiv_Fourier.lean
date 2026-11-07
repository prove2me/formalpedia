-- Prove2me | Definitions.Def_PDSEquiv_Fourier
-- name    : PDSEquiv_Fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:40.674982+00:00
-- url     : https://prove2.me/theorems/f83e7b44-c767-4ce5-ac21-2fab94112e00
-- title:
--   The $q$-biased Fourier basis, $\Pi_D$, $f^{>D}$, the likelihood ratio $L$, and $R=c_q^{D^2}N^{D+1}$
-- statement:
--   On $L^2(\mathrm{ER}(N,q))$ with $\langle f,g\rangle=\mathbb E_{G\sim\mathrm{ER}(N,q)}[f(G)g(G)]$ and norms $\|f\|_{r}=(\mathbb E|f|^r)^{1/r}$:
--
--   1. For $S\subseteq\binom{[N]}2$, $\psi_S(G)=\prod_{e\in S}\frac{G_e-q}{\sqrt{q(1-q)}}$, and $v(S)$ is the number of vertices incident to some pair of $S$.
--   2. For an integer $D\ge2$, $\Pi_D f=\sum_{S:\,v(S)\le D}\langle f,\psi_S\rangle\,\psi_S$ is the orthogonal projection onto the span of $\{\psi_S: v(S)\le D\}$ (the $\psi_S$ are orthonormal for $0<q<1$), and $f^{>D}=f-\Pi_Df$.
--   3. $L=d\mathrm{PDS}(N,k,p,q)/d\mathrm{ER}(N,q)$, the ratio of the two masses.
--   4. $c_q=\max\bigl(\tfrac q{1-q},\tfrac{1-q}q\bigr)$ and $R=c_q^{D^2}N^{D+1}$, display (5).
--   5. For Proposition 6.6: the least integer $D\ge2$ with $(1-r)(D+1)\ge2d+11$.
--
--   These are the objects of the low vertex-degree analysis of §5.
--
--   **Formalization Note** $\psi_S$ and the coefficients $\langle f,\psi_S\rangle$ are the published $q$-biased characters and coefficients `OAI.Problem313.BiasedFourier.char`, `coeff` on $\{0,1\}^{\binom{[N]}2}$. For $0<q<1$ the law $\mathrm{ER}(N,q)$ has full support, so functions need no quotient and $L$ divides by a positive number.
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), §4.3, pp.13–14 (L², ψ_S, v(S), Π_D, f^{>D}); §5, p.14 (L); (5), p.16; Proposition 6.6, p.23 (the least D)

import Mathlib
import Definitions.Def_PDSEquiv_Laws

set_option autoImplicit false

namespace PDSEquiv

noncomputable section

/-!
# The `q`-biased Fourier vocabulary, `Π_D`, `f^{>D}`, the likelihood ratio, and `R`

S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), §4.3, p.14, and (5), p.16.

**Formalization Note.** `ψ_S` and the coefficients `⟨f, ψ_S⟩` are the published `q`-biased
characters and coefficients `OAI.Problem313.BiasedFourier.char`, `coeff` on `{0,1}^Pair N`. `Π_D` is written as its Fourier expansion over the sets `S` with `v(S) ≤ D`;
the functions `ψ_S` are orthonormal in `L²(ER(N, q))` for `0 < q < 1`, so this is the orthogonal
projection onto their span. For `0 < q < 1` the law `ER(N, q)` has full support, so functions on
graphs need no quotient, and the division in `likelihood` is by a positive number.
-/

/-- `L²(ER(N, q))` inner product, `⟨f, g⟩ = E_{G∼ER(N,q)}[f(G) g(G)]`, §4.3, p.13. -/
def erInner {N : ℕ} (q : ℝ) (f g : Graph N → ℝ) : ℝ := ∑ G, erMass N q G * f G * g G

/-- `‖f‖_{2,ER(N,q)}`, §4.3, p.13. -/
def erL2 {N : ℕ} (q : ℝ) (f : Graph N → ℝ) : ℝ := Real.sqrt (∑ G, erMass N q G * f G ^ 2)

/-- `‖f‖_{1,ER(N,q)}`, §4.3, p.13. -/
def erL1 {N : ℕ} (q : ℝ) (f : Graph N → ℝ) : ℝ := ∑ G, erMass N q G * |f G|

/-- `ψ_S(G) = ∏_{e∈S} (G_e − q)/√(q(1 − q))`, §4.3, p.14: the published `q`-biased character
`OAI.Problem313.BiasedFourier.char` on the cube `{0,1}^Pair N`. -/
def psi {N : ℕ} (q : ℝ) (S : Finset (Pair N)) (G : Graph N) : ℝ :=
  OAI.Problem313.BiasedFourier.char q S G

/-- `v(S)`, the number of vertices incident to some pair in `S`, §4.3, p.14. -/
def vDeg {N : ℕ} (S : Finset (Pair N)) : ℕ :=
  (S.biUnion fun e => ({e.1.1, e.1.2} : Finset (Fin N))).card

/-- `Π_D f`, the low vertex-degree part of `f`, §4.3, p.14. -/
def piD {N : ℕ} (q : ℝ) (D : ℕ) (f : Graph N → ℝ) (G : Graph N) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Pair N) => vDeg S ≤ D), OAI.Problem313.BiasedFourier.coeff q f S * psi q S G

/-- `f^{>D} = (I − Π_D) f`, the high vertex-degree part of `f`, §4.3, p.14. -/
def highPart {N : ℕ} (q : ℝ) (D : ℕ) (f : Graph N → ℝ) (G : Graph N) : ℝ := f G - piD q D f G

/-- `L = dPDS/dER`, the likelihood ratio, §5, p.14. -/
def likelihood (N k : ℕ) (p q : ℝ) (G : Graph N) : ℝ := pdsMass N k p q G / erMass N q G

/-- `c_q = max(q/(1 − q), (1 − q)/q)`, display (5), p.16. -/
def cq (q : ℝ) : ℝ := max (q / (1 - q)) ((1 - q) / q)

/-- `R = c_q^{D²} N^{D+1}`, display (5), p.16. -/
def bigR (q : ℝ) (D N : ℕ) : ℝ := cq q ^ (D ^ 2) * (N : ℝ) ^ (D + 1)

/-- The least integer `D ≥ 2` with `(1 − r)(D + 1) ≥ 2d + 11`, Proposition 6.6, p.23. The set is
nonempty for `r < 1`. -/
def leastD (r : ℝ) (d : ℕ) : ℕ :=
  sInf {D : ℕ | 2 ≤ D ∧ 2 * (d : ℝ) + 11 ≤ (1 - r) * ((D : ℝ) + 1)}

end

end PDSEquiv


