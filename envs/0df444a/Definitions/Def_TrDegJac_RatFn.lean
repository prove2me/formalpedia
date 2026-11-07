-- Prove2me | Definitions.Def_TrDegJac_RatFn
-- name    : TrDegJac_RatFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:28.054086+00:00
-- url     : https://prove2.me/theorems/4fe7eaaf-c8da-43fc-aeb5-0a52d45d2504
-- title:
--   The rational function field $\mathbb F(x_1,\dots,x_n)$
-- statement:
--   Let $\mathbb F$ be a field and $n\in\mathbb N$. The **rational function field** $\mathbb F(x)=\mathbb F(x_1,\dots,x_n)$ is the fraction field of the polynomial ring $\mathbb F[x]=\mathbb F[x_1,\dots,x_n]$. Every polynomial $q\in\mathbb F[x]$ is regarded as an element of $\mathbb F(x)$ through the canonical inclusion $\mathbb F[x]\hookrightarrow\mathbb F(x)$.
--
--   All field degrees and all Jacobian ranks of the mission are computed inside this one ambient field.
--
--   **Formalization Note** $\mathbb F[x_1,\dots,x_n]$ is `MvPolynomial (Fin n) F`, with variables indexed from $0$; $\mathbb F(x)$ is its `FractionRing`, and `toRatFn` is the inclusion.
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), §2.1, p.7

import Mathlib

set_option autoImplicit false

namespace TrDegJac

/-- **The rational function field `F(x₁, …, x_n)`** — Forbes and Staicu, *Approximating
Transcendence Degree in Medium Characteristic*, STOC 2027 submission (manuscript sha256
3ab72a42…), §2.1, p.7: "We will use F(x) to denote the fraction field of the polynomial ring F[x]."

**Formalization Note.** The polynomial ring `F[x₁, …, x_n]` is `MvPolynomial (Fin n) F` (variables
indexed from `0`), and `F(x)` is its `FractionRing`. -/
abbrev RatFn (F : Type*) [Field F] (n : ℕ) : Type _ := FractionRing (MvPolynomial (Fin n) F)

/-- The inclusion `F[x] → F(x)` of a polynomial into the rational function field (§2.1, p.7). -/
noncomputable abbrev toRatFn {F : Type*} [Field F] {n : ℕ} (q : MvPolynomial (Fin n) F) :
    RatFn F n :=
  algebraMap (MvPolynomial (Fin n) F) (RatFn F n) q

end TrDegJac


