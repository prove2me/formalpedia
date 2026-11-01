-- Prove2me | Definitions.Def_GibbsCongestion_polarWeight
-- name    : GibbsCongestion_polarWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:20.085514+00:00
-- url     : https://prove2.me/theorems/c7a6e29b-132e-4194-aa7b-7efe764b845f
-- title:
--   Weights $w_\Pi$ of the polarized generating polynomial $\Pi(g)$
-- statement:
--   Let $g(x)=\sum_{\alpha\in\mathcal L}\frac{n!}{\alpha!}e^{-T\Phi(\alpha)}x^\alpha$ be the generating polynomial (11), with one variable per path. Its polarization $\Pi(g)$ (with $\kappa=(n,\dots,n)$) is a multi-affine polynomial in the variables $x_{pj}$, $p\in\mathcal P$, $1\le j\le n$, supported on the $n$-element subsets $B$ of $\mathcal P\times[n]$, the bases of the $n$-uniform matroid. For such $B$ let $\alpha(B)_p=|\{j:(p,j)\in B\}|$. The coefficient of $x^B$ is
--   $$w_\Pi(B)=\binom{n}{\alpha(B)}^{-1}\frac{n!}{\alpha(B)!}e^{-T\Phi(\alpha(B))},\qquad\binom{n}{\alpha}=\prod_p\binom{n}{\alpha_p},\ \ \alpha!=\prod_p\alpha_p!.$$
--   The base-exchange chain with these weights is the chain whose modified log-Sobolev constant $\rho(\Pi(\mathcal L))$ appears in (14).
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, display (10), §3.1, p.14; display (11), p.15; App. B.3, p.28

import Mathlib
import Definitions.Def_GibbsCongestion_loadPotential

namespace GibbsCongestion

/-- The weights of the polarized generating polynomial `Π(g)` of (11), displays (10)–(11)
(Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §3.1, p.14; §4, p.15; App. B.3, p.28): for a set `B` of `n` elements of `P × [n]` with
`α(B)_p = |{j : (p, j) ∈ B}|`,
`w_Π(B) = (n choose α(B))⁻¹ · (n! / α(B)!) · e^{−TΦ(α(B))}`,
where `(n choose α) = ∏_p (n choose α_p)` and `α! = ∏_p α_p!`.

**Formalization Note** `Φ(α)` is `loadPotential`. The ground set `{(p, j) : p ∈ P, 1 ≤ j ≤ n}` is
`P × Fin n`; its `n`-element subsets are the bases of the `n`-uniform matroid of App. B.3. -/
noncomputable def polarWeight {E : Type*} [Fintype E] [DecidableEq E] (P : Finset (Finset E))
    (n : ℕ) (c : E → ℕ → ℝ) (T : ℝ) (B : Finset (P × Fin n)) : ℝ :=
  (∏ p : P, ((n.choose (B.filter (fun x => x.1 = p)).card : ℕ) : ℝ))⁻¹ *
    ((n.factorial : ℝ) / ∏ p : P, (((B.filter (fun x => x.1 = p)).card.factorial : ℕ) : ℝ)) *
    Real.exp (-T * loadPotential c (fun p => (B.filter (fun x => x.1 = p)).card))

end GibbsCongestion


