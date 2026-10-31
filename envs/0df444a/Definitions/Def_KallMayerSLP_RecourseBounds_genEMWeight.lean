-- Prove2me | Definitions.Def_KallMayerSLP_RecourseBounds_genEMWeight
-- name    : KallMayerSLP_RecourseBounds_genEMWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:45.922667+00:00
-- url     : https://prove2.me/theorems/ff21f53e-277e-4b93-96b2-4efa35eb00ae
-- title:
--   Generalized Edmundson–Madansky distribution $\mathbb Q(v^\nu)$, (2.30)
-- statement:
--   Let $\mathbb P_\xi$ be the distribution of a random vector $\xi$ with $\operatorname{supp}\mathbb P_\xi\subset\Xi=\times_{i=1}^r[a_i,b_i]$. The **generalized Edmundson–Madansky (E–M) distribution** is the probability measure $\mathbb Q$ on the vertices $v^\nu$ of $\Xi$ given by
--   $$
--   \mathbb Q(v^\nu)=\int_\Xi \mathbb P_{\eta(\xi)}(v^\nu)\,\mathbb P_\xi(d\xi)=\int_\Xi\prod_{i\in I_\nu}\frac{b_i-\xi_i}{b_i-a_i}\cdot\prod_{i\in J_\nu}\frac{\xi_i-a_i}{b_i-a_i}\,\mathbb P_\xi(d\xi),
--   $$
--   with $I_\nu=\{i\mid v^\nu_i=a_i\}$ and $J_\nu$ its complement. Unlike the product E–M distribution of the independent case, it needs no independence of the components of $\xi$.
--
--   **Formalization Note** The definition takes any measure $\mu$ on $\mathbb R^r$ (`Fin r → ℝ`). For $\mu=\mathbb P_\xi$ it is $\mathbb Q(v)$; for the restriction of $\mathbb P_\xi$ to a cell $\Xi_k$ of a partition it is $\pi_k\,\mathbb Q_k(v)$, the cell's E–M distribution times the cell's probability $\pi_k=\mathbb P_\xi(\Xi_k)$. The integral is the Bochner integral of `vertexProb`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Lemma 2.7, (2.30), p.216 (PDF 225)

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_vertexProb

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **The generalized Edmundson–Madansky distribution `Q` on the vertices of a box, (2.30).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.7, (2.30), printed p.216
(PDF 225): `Q(v^ν) = ∫_Ξ IP_{η(ξ)}(v^ν) IP_ξ(dξ)
= ∫_Ξ ∏_{i∈I_ν} (βᵢ − ξᵢ)/(βᵢ − αᵢ) · ∏_{i∈J_ν} (ξᵢ − αᵢ)/(βᵢ − αᵢ) IP_ξ(dξ)`.

**Formalization Note.** `μ` is the distribution `IP_ξ` (a measure on `Fin r → ℝ`); for a finite
measure that is not a probability measure (a restriction `μ.restrict Ξₖ`, used for the cells of a
partition) this is `IP_ξ(Ξₖ) · Q_k(v)`, the cell's E–M distribution multiplied by the cell's
probability. The integral is the Bochner integral; the integrand is a polynomial in `ξ`, integrable
whenever `μ` is a finite measure carried by a bounded set. -/
noncomputable def genEMWeight {r : ℕ} (μ : Measure (Fin r → ℝ)) (a b : Fin r → ℝ)
    (v : Fin r → Bool) : ℝ :=
  ∫ x, vertexProb a b x v ∂μ

end KallMayerSLP.RecourseBounds


