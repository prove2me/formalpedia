-- Prove2me | Definitions.Def_SYKLearn_Hermite
-- name    : SYKLearn_Hermite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:39.096197+00:00
-- url     : https://prove2.me/theorems/cae77d34-ec96-49eb-ba93-0d8112b27958
-- title:
--   Hermite projections $\Pi_d$ in the SYK couplings and the thermal response $z_O=\mathrm{Tr}[Oe^{-\beta H}]/\mathbb E Z_H$
-- statement:
--   Let $h_j=\mathrm{He}_j/\sqrt{j!}$ be the normalized probabilists' Hermite polynomials and, for a multi-index $r$, $h_r(x)=\prod_I h_{r_I}(x_I)$. For a function $f$ of the couplings $g$ (scalar-, complex- or vector-valued) the **Hermite-degree-$d$ projection** is
--
--   $$\Pi_df(g)=\sum_{|r|=d}h_r(g/\sigma_n)\ \mathbb E_{g'}\big[h_r(g'/\sigma_n)\,f(g')\big],$$
--
--   the orthogonal projection of $f$ in $L^2$ of the Gaussian coupling law onto the polynomials of Hermite degree exactly $d$ in the standardized couplings $g/\sigma_n$. For a matrix $O$ the **normalized thermal response** is
--
--   $$z_O=\frac{\mathrm{Tr}[Oe^{-\beta H_g}]}{\mathbb E_g Z_{H_g}},\qquad Z_H=\mathrm{Tr}[e^{-\beta H}],$$
--
--   and $z_0=z_{I}$.
--
--   These objects describe how thermal expectations depend on the random couplings: the paper expands $\bar\rho_4,\bar\rho_8$ in Hermite degree and controls the tail of the expansion.
--
--   **Formalization Note** The published `SYKEdge.hermN` gives $h_j$. Multi-indices of total degree $d$ are enumerated as maps into $\{0,\dots,d\}$ with sum $d$. The integral is a Bochner integral in the codomain (coordinatewise for vectors); every function projected in the mission is integrable against every Hermite polynomial under the Gaussian law. The paper's monic Hermite polynomials in variance $\sigma_n^2$ span the same degree spaces. All uses take the model's coupling law with $J=1$ and $\sigma=\sigma_n$.
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), §1.2.1, p.6; (29) and Table 1, pp.19–20; Lemma 3.9, p.30

import Mathlib
import Definitions.Def_SYKLearn_Direction
import Definitions.Def_SYKEdge_Hermite

noncomputable section
open MeasureTheory

namespace SYKLearn

/-!
# Hermite projections `Π_d` in the SYK couplings, and the normalized thermal response `z_O`

A. Anshu, S. Arunachalam, S. Chen, Y. Hwang, *Efficiently Learning SYK Hamiltonians*, STOC 2027
submission (held file sha256 5d7d199a…), §1.2.1, p.6; Table 1 and (29), pp.19–20; Lemma 3.9, p.30.

**Formalization Note.**
* `hermMulti r x = Π_I h_{r_I}(x_I)` with the published normalized Hermite polynomial
  `SYKEdge.hermN j = He_j/√(j!)`; under the standard Gaussian these are orthonormal.
* `hermProj σ μ d f` is `Π_d f`, the part of Hermite degree `d` of a function `f` of the couplings:
  `Π_d f (x) = Σ_{|r|=d} h_r(x/σ) · E_μ[h_r(y/σ) f(y)]`, the orthogonal projection of `f` onto the
  span of the degree-`d` Hermite polynomials in the standardized couplings `y/σ`. The multi-indices
  of total degree `d` have entries `≤ d`, so they are enumerated as `r : ι → Fin (d+1)` with
  `Σ r = d`. The paper's monic Hermite polynomials in variance `σ²` (p.6) span the same spaces.
  Every use takes `μ = disorderLaw Q`, `σ = sigma N` and `Q.J = 1`, so that `μ` is the product of
  `N(0, σ²)`. The integral is the Bochner integral in the codomain (`ℝ`, `ℂ`, or `Ext N`,
  coordinatewise); every function projected in the mission is integrable against every Hermite
  polynomial under the Gaussian law.
* `zO β Q O w = Tr[O e^{−βH_g}] / E_g Z_H` (Lemma 3.9, p.30), complex-valued, normalized trace,
  `Z_H = Tr[e^{−βH}]`. With `O = 1` it is `z_0` of (29).
-/

open SYKFastMix.FastMixing

/-- The multivariate normalized Hermite polynomial `h_r(x) = Π_i h_{r_i}(x_i)`. -/
def hermMulti {ι : Type*} [Fintype ι] (r : ι → ℕ) (x : ι → ℝ) : ℝ :=
  ∏ i, SYKEdge.hermN (r i) (x i)

/-- The Hermite-degree-`d` projection `Π_d f` with respect to the product Gaussian `μ` of
standard deviation `σ` in each coordinate (p.6, p.19). -/
def hermProj {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (σ : ℝ) (μ : Measure (ι → ℝ)) (d : ℕ) (f : (ι → ℝ) → E) (x : ι → ℝ) : E :=
  ∑ r ∈ (Finset.univ : Finset (ι → Fin (d + 1))).filter (fun r => ∑ i, (r i : ℕ) = d),
    hermMulti (fun i => (r i : ℕ)) (σ⁻¹ • x) •
      ∫ y, hermMulti (fun i => (r i : ℕ)) (σ⁻¹ • y) • f y ∂μ

/-- `z_O = Tr[O e^{−βH_g}] / E_g Tr[e^{−βH_g}]` (Lemma 3.9, p.30). -/
def zO {N : ℕ} (β : ℝ) (Q : Model N) (O : Mat (SiteHilbert N)) (w : Disorder N) : ℂ :=
  SYKEdge.ntr (O * mexp ((-β : ℂ) • hamiltonian Q w)) / (annealedZ β Q : ℂ)

end SYKLearn


