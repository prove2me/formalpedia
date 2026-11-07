-- Prove2me | Definitions.Def_TrDegJac_trDeg
-- name    : TrDegJac_trDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:42.904334+00:00
-- url     : https://prove2.me/theorems/2fef0a3d-8d1d-4ad5-a89f-9783da45a48e
-- title:
--   Transcendence degree $\operatorname{tr-deg}_{\mathbb F}(f)$ of a family of polynomials
-- statement:
--   Let $f_1,\dots,f_m\in\mathbb F[x_1,\dots,x_n]$. The **transcendence degree** of the family is
--   $$
--   \operatorname{tr-deg}_{\mathbb F}(f)=\max\{\,|S| : S\subseteq\{1,\dots,m\},\ (f_i)_{i\in S}\text{ algebraically independent over }\mathbb F\,\}.
--   $$
--
--   The paper defines it as the size of a maximally algebraically independent subset of $f$; by Lemma 2.7 every such subset has this maximum size.
--
--   **Formalization Note** Written as `sSup` of a set of natural numbers that contains $0$ (the empty subfamily) and is bounded by $m$, so the supremum is attained and is never a junk value.
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Definition 2.5, p.8

import Mathlib

set_option autoImplicit false

namespace TrDegJac

/-- **Transcendence degree of a family of polynomials** — Forbes and Staicu, *Approximating
Transcendence Degree in Medium Characteristic*, STOC 2027 submission (manuscript sha256
3ab72a42…), Definition 2.5, p.8: "the transcendence degree of f₁, …, f_m is size of the maximally
algebraically independent subset of the polynomials, denoted by tr-deg_F(f)."

`trDeg f` is the largest `k` such that some `k` of the polynomials `f₁, …, f_m` are algebraically
independent over `F`.

**Formalization Note.** The supremum is over a set of natural numbers that contains `0` (the empty
subfamily is independent) and is bounded by `m`, so it is a genuine maximum, never the junk value of
an empty or unbounded `sSup`. Definition 2.5 speaks of "the" maximal subset; Lemma 2.7 (p.8) says all
maximal subsets have the same size, which is this maximum. -/
noncomputable def trDeg {F : Type*} [Field F] {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) F) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset (Fin m), S.card = k ∧ AlgebraicIndependent F (fun i : S => f i)}

end TrDegJac


