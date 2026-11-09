-- Prove2me | Definitions.Def_HDXHitting_BipSingLE
-- name    : HDXHitting_BipSingLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:35.631203+00:00
-- url     : https://prove2.me/theorems/f9922d18-174b-46b4-bddc-1f92e7fc22b6
-- title:
--   Second singular value of a weighted bipartite graph at most $\lambda$ (Rayleigh form)
-- statement:
--   Let $B(u,w)\ge0$ be edge weights of a bipartite graph between finite sets $U$ and $W$, with left degrees $d_L(u)=\sum_w B(u,w)$ and right degrees $d_R(w)=\sum_u B(u,w)$. The graph has **second singular value at most $\lambda$** if for every $g$ on $U$ with $\sum_u d_L(u)g(u)=0$ and every $h$ on $W$ with $\sum_w d_R(w)h(w)=0$,
--   $$
--   \Big(\sum_{u,w}B(u,w)\,g(u)\,h(w)\Big)^2\le \lambda^2\Big(\sum_u d_L(u)\,g(u)^2\Big)\Big(\sum_w d_R(w)\,h(w)^2\Big).
--   $$
--   This is the condition that the random-walk operator from $L^2(\pi_W)$ to $L^2(\pi_U)$ has second largest singular value at most $\lambda\ge0$ (Section 2.1).
--
--   **Formalization Note** The walk maps constants to constants and mean-zero functions to mean-zero functions, so its second singular value is its norm on mean-zero functions, which is the displayed condition. It is invariant under positive scaling of $B$.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Section 2.1, p.11 (bipartite random-walk operator)

import Mathlib

namespace HDXHitting

/-- "The bipartite graph `(U, W, E)` with nonnegative edge weights `B` has second singular
value at most `λ`" (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), §2.1, p.11: the random-walk operator from `L²(π_W)` to
`L²(π_U)`), in Rayleigh form: with left degrees `d_L(u) = ∑_w B(u, w)` and right degrees
`d_R(w) = ∑_u B(u, w)`, every `g` with `∑_u d_L(u) g(u) = 0` and every `h` with
`∑_w d_R(w) h(w) = 0` satisfy
`(∑_{u,w} B(u, w) g(u) h(w))² ≤ λ² (∑_u d_L(u) g(u)²)(∑_w d_R(w) h(w)²)`.

**Formalization Note** The walk maps the constants to the constants and their orthogonal
complements to each other, so the second singular value is the norm of the walk on mean-zero
functions, i.e. the condition above for `λ ≥ 0`. It is invariant under positive scaling of `B`. -/
def BipSingLE {U W : Type*} [Fintype U] [Fintype W] (B : U → W → ℝ) (lam : ℝ) : Prop :=
  ∀ (g : U → ℝ) (h : W → ℝ), ∑ u, (∑ w, B u w) * g u = 0 → ∑ w, (∑ u, B u w) * h w = 0 →
    (∑ u, ∑ w, B u w * g u * h w) ^ 2 ≤
      lam ^ 2 * (∑ u, (∑ w, B u w) * g u ^ 2) * (∑ w, (∑ u, B u w) * h w ^ 2)

end HDXHitting


