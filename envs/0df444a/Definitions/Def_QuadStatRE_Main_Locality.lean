-- Prove2me | Definitions.Def_QuadStatRE_Main_Locality
-- name    : QuadStatRE_Main_Locality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:44:31.420104+00:00
-- url     : https://prove2.me/theorems/9fe633e4-97e5-4342-a54e-04b4d79e173c
-- title:
--   Output locality of an $\mathbb F_2$-polynomial description (§2.2, Complexity measures)
-- statement:
--   Let $D$ be a description of a polynomial map $\mathbb F_2^N\times\mathbb F_2^\rho\to\mathbb F_2^\ell$ (the published `QuadraticRE.Desc`: each output coordinate is a list of monomials in the $N$ input variables $v$ and the $\rho$ random variables $r$). Following §2.2 of the paper, the **output locality** of the encoding is at most $k$ if every output bit of $\mathrm{Enc}(v;r)$ depends on at most $k$ bits of $(v,r)$. Formally, $D$ has locality at most $k$ when for every output coordinate $i$ there is a set $S$ of at most $k$ of the $N+\rho$ variables such that
--   $$(v,r)\big|_S=(v',r')\big|_S\ \Longrightarrow\ D(v;r)_i=D(v';r')_i .$$
--
--   Together with degree (the published `Desc.DegLE`), locality is one of the two complexity measures of the main theorem: a degree-2, locality-3 encoder computes every output bit by a quadratic polynomial in at most three bits.
--
--   **Formalization Note.** Locality is semantic: it is about what each coordinate of the evaluated map depends on, not about how many distinct variables are written in its monomial list (which can only be larger).
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 13, §2.2, Complexity measures

import Mathlib
import Definitions.Def_QuadraticRE_Desc

namespace QuadStatRE.Main

open QuadraticRE

/-- Output locality of an encoder given by an `F₂`-polynomial description
(Applebaum, *Quadratic Statistical Randomized Encoding for All Functions*, STOC 2027 submission,
§2.2 "Complexity measures", p. 13): "The output locality is at most `ℓ` if every output bit of
`Enc(v; r)` depends on at most `ℓ` bits of `(v, r)`".

`LocalLE D k` says: for every output coordinate `i` there is a set `S` of at most `k` of the
`N + ρ` variables (input variables `Sum.inl`, tape variables `Sum.inr`) such that any two assignments
agreeing on `S` give the same value of coordinate `i`.

**Formalization Note.** Locality is semantic (dependence of the evaluated map), not a count of the
variables written in the monomial lists, which could be larger than the semantic count. -/
def LocalLE {N ρ ℓ : ℕ} (D : Desc N ρ ℓ) (k : ℕ) : Prop :=
  ∀ i : Fin ℓ, ∃ S : Finset (Fin N ⊕ Fin ρ), S.card ≤ k ∧
    ∀ (x x' : Fin N → F2) (r r' : Fin ρ → F2),
      (∀ v ∈ S, Sum.elim x r v = Sum.elim x' r' v) → D.eval x r i = D.eval x' r' i

end QuadStatRE.Main


