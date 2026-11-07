-- Prove2me | Definitions.Def_F3SubsetSum_RootMultiplicity
-- name    : F3SubsetSum_RootMultiplicity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:09.938201+00:00
-- url     : https://prove2.me/theorems/0f4f4e4b-992d-455c-99d6-2411e8086d15
-- title:
--   Multiplicity $\mathrm{mult}_a(p)$ of a root of a multivariate polynomial
-- statement:
--   For a polynomial $p(z)\in K[z_1,\dots,z_n]$ and a point $a\in K^n$, the **multiplicity** of the root $z=a$ is
--
--   $$
--   \mathrm{mult}_a(p)=\min\bigl\{|s| : z^s \text{ has a nonzero coefficient in } p(z+a)\bigr\},
--   $$
--
--   the least total degree of a monomial of $p$ after translating $a$ to the origin. It is positive exactly when $p(a)=0$, and it is the quantity bounded on average by the multiplicity Schwartz–Zippel lemma.
--
--   **Formalization Note** The paper uses it for $p\neq0$; for $p=0$ the value is $0$.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, proof of Lemma 4.15, p.25

import Mathlib

namespace F3SubsetSum

open MvPolynomial

/-- **Multiplicity of a root** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1,
proof of Lemma 4.15, p.25): "mult_a(p(z)) is the least total degree of a nonzero monomial in
p(z + a)". Here `p(z + a)` is `p` with `z_i ↦ z_i + a_i`, and the total degree of the monomial
`z^s` is `Σ_i s_i`.

**Formalization Note** The paper uses it for nonzero `p`; for `p = 0` the set of degrees is empty
and the value is `0`. -/
noncomputable def rootMult {K : Type*} [CommRing K] {n : ℕ} (a : Fin n → K)
    (p : MvPolynomial (Fin n) K) : ℕ :=
  sInf ((fun s : Fin n →₀ ℕ => ∑ i, s i) ''
    ↑(aeval (fun i => X i + C (a i)) p).support)

end F3SubsetSum


