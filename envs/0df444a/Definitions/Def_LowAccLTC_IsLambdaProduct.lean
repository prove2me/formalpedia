-- Prove2me | Definitions.Def_LowAccLTC_IsLambdaProduct
-- name    : LowAccLTC_IsLambdaProduct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:23.055006+00:00
-- url     : https://prove2.me/theorems/2f991264-7833-4fab-bfb5-f10809ccd82e
-- title:
--   $\lambda$-products: colored swap walks on links are spectral expanders
-- statement:
--   A weighted $r$-partite complex $X$ is a **$\lambda$-product** if for every face $s$ of co-rank at least $2$ and every two distinct colours $i,j\notin\mathrm{col}(s)$, the $i,j$-swap walk on the link $X_s$ — the bipartite graph between $X_s[i]$ and $X_s[j]$ whose edges are the $2$-faces of the link, sampled from the induced measure — is a $\lambda$-one-sided spectral expander, i.e. $\|A_L|_{\mathbf 1^\perp}\|\le\lambda$.
--
--   This is the expansion hypothesis of the trickling-down Proposition 5.11.
--
--   **Formalization Note** $\|A_L|_{\mathbf 1^\perp}\|\le\lambda$ is written variationally: $\big(\mathbb E_{(u,w)}[g(u)h(w)]\big)^2\le\lambda^2\,\mathbb E[g^2]\,\mathbb E[h^2]$ for all $g$ of mean $0$ on the left side and all $h$ on the right side.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definition 2.7 p.15 (PDF p.18), Lemma 2.26 p.20 (PDF p.23)

import Definitions.Def_LowAccLTC_PartiteComplex

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

namespace PartiteComplex

variable {r : ℕ} {V T : Type*} [Fintype T] (X : PartiteComplex r V T)

/-- `X` is a `λ`-product (Lemma 2.26, p.20, after [GLL22]): for every face `s` of co-rank at
least `2` and all colours `i ≠ j` not in `col(s)`, the `i,j`-swap walk on the link `X_s` (the
bipartite graph between `X_s[i]` and `X_s[j]` whose edges are the `2`-faces of the link, sampled
by sampling `t ∼ μ` conditioned on `s ⊆ t` and taking its vertices of colours `i, j`) is a
`λ`-one-sided spectral expander.

**Formalization Note.** For a bipartite graph `G = (L, R, E)` the paper's spectral bound is
`λ(G) = ‖A_L|_{f ⊥ 1}‖` (Definition 2.7). `λ(G) ≤ λ` is written variationally: for every `g` on
`L` with mean `0` and every `h` on `R`, `(E_{(u,w)} g(u) h(w))² ≤ λ² · E g² · E h²`
(equivalent for `λ ≥ 0`). -/
def IsLambdaProduct (lam : ℝ) : Prop :=
  ∀ s, X.IsFace s → s.card + 2 ≤ r → ∀ i j : Fin r, i ≠ j →
    (∀ v ∈ s, X.col v ≠ i) → (∀ v ∈ s, X.col v ≠ j) → ∀ g h : V → ℝ,
    X.Estar s (fun t => g (X.vert t i)) = 0 →
    (X.Estar s (fun t => g (X.vert t i) * h (X.vert t j))) ^ 2
      ≤ lam ^ 2 * X.Estar s (fun t => g (X.vert t i) ^ 2) * X.Estar s (fun t => h (X.vert t j) ^ 2)

end PartiteComplex

end LowAccLTC


