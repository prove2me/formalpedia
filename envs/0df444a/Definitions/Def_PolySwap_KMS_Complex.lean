-- Prove2me | Definitions.Def_PolySwap_KMS_Complex
-- name    : PolySwap_KMS_Complex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:38:32.831199+00:00
-- url     : https://prove2.me/theorems/d791fc8f-53ac-434b-9b5f-274b76f7f186
-- title:
--   Weighted pure simplicial complexes: Garland weights, links, skeleta, the faces complexes $F^rX$ and $F^{\mathcal I}X$, local spectral expansion
-- statement:
--   A finite **pure** simplicial complex $X$ is given by its maximal faces $X(d)$ (sets of $d+1$ vertices) and a positive **top-level distribution** $w_d$ on them; its faces are all subsets of maximal faces, the empty face included, and $X(k)$ is the set of faces with $k+1$ vertices. The **Garland weights** are the marginals of "sample $\sigma_d\sim w_d$, order its vertices uniformly, output the initial segments":
--   $$w_i(\sigma)=\frac{\sum_{\tau\in X(d),\,\tau\supseteq\sigma}w_d(\tau)}{\binom{d+1}{i+1}}\qquad(\sigma\in X(i)).$$
--   The **degree** of a face is the number of maximal faces containing it.
--
--   * The **link** $X_\sigma=\{\tau\in X:\tau\cap\sigma=\emptyset,\ \tau\cup\sigma\in X\}$ carries the conditional distribution $w(\tau)\propto w_d(\tau\cup\sigma)$.
--   * The **$n$-skeleton** $X^{\le n}$ has maximal faces $X(n)$ with top-level distribution the marginal $w_n$ of $X$ (not the uniform one), so $w^{\le n}_i=w_i$ for $i\le n$.
--   * The **$r$-faces complex** $F^rX$ has vertex set $X(r)$ (faces with $r+1$ vertices); $\{\sigma_0,\dots,\sigma_k\}$ is a face iff the $\sigma_i$ are pairwise disjoint and $\bigcup\sigma_i\in X$. Its maximal faces are the families of $t+1=\lfloor\frac{d+1}{r+1}\rfloor$ disjoint $(r+1)$-subsets of a maximal face of $X$, weighted by $\frac{(t+1)!((r+1)!)^{t+1}}{((t+1)(r+1))!}w_{(t+1)(r+1)-1}(\bigcup\sigma_i)$ (sample a face and partition it uniformly); lower faces carry the induced weights.
--   * For a $(d+1)$-partite $X$ with colour map $\mathrm{col}$ and a collection $\mathcal I=\{I_1,\dots,I_T\}$ of pairwise disjoint colour sets, the **colored faces complex** $F^{\mathcal I}X$ has vertices the faces whose colour set is some $I_j$; a set of them is a face iff their colours are distinct members of $\mathcal I$ and their union is a face of $X$. Its weight is that of $F^rX$ conditioned on the colours $\mathcal I$, i.e. proportional to $w_{T(r+1)-1}$ of the union.
--   * $\binom{[d]}{r+1}^{[T]}$ is the set of collections of $T$ pairwise disjoint $(r+1)$-subsets of $[d]=\{0,\dots,d\}$.
--   * $X$ is an **$\varepsilon$-(one-sided) local spectral expander** if for every face $\tau$ with $-1\le\dim\tau\le d-2$ (the empty face included) the second largest eigenvalue of the random walk on the weighted 1-skeleton of $X_\tau$ is at most $\varepsilon$.
--
--   **Formalization Note.** `WComplex V` stores `tops : Finset (Finset V)` and an unnormalised weight `wt`; `gw` divides by the total top weight, so only the ratios of `wt` on `tops` matter. Faces, vertices and links are derived from `tops`. Colours are natural numbers and `coloredFaces col I` takes the colour map and `I : Finset (Finset ℕ)`; for a partite complex and disjoint colour sets it is the paper's $F^{\mathcal I}X$. `IsLocalSpectralExpander ε` states $\lambda_2\le\varepsilon$ in variational form: with $\pi=w_0$ and $w_1$ the vertex and edge weights of the link, the walk $M(u,v)=w_1(\{u,v\})/(2\pi(u))$ is self-adjoint on $\ell^2(\pi)$ and $\lambda_2(M)\le\varepsilon$ iff $\sum_{u\ne v}\tfrac12w_1(\{u,v\})g(u)g(v)\le\varepsilon\sum_v\pi(v)g(v)^2$ for every $g$ with $\sum_v\pi(v)g(v)=0$. The condition $\varepsilon\in[0,1)$ of Definition 2.7 is not bundled. Uses `open Classical` for the decidability of finite set operations.
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), §2.1 (pp. 9–11, Definitions 2.1–2.3, Garland weights, skeleta, links), §2.2.1 (p. 11, Definition 2.7), §2.2.3 (pp. 14–15, Definitions 2.11, 2.14, 2.16)

import Mathlib

open Classical

noncomputable section

namespace PolySwap.KMS

/-!
# Weighted pure simplicial complexes, Garland weights, links, skeleta, faces complexes

Dikstein, Oppenheim, Valentiner-Branth, *Polynomial Swap Coboundary Expansion with Applications
to LTCs and PCPs*, STOC 2027 submission (manuscript sha256 b9cb2095…), §2.1 (pp. 9–11,
Definitions 2.1–2.3, Garland weights), §2.2.1 (p. 11, Definition 2.7), §2.2.3 (pp. 14–15,
Definitions 2.11, 2.14, 2.16).

A finite pure complex is given by its maximal faces `tops` (all of the same size `d + 1` in every
use) and a positive top-level weight `wt` on them; the faces are the subsets of the maximal faces
(the empty face included). The weight need not be normalised: every Garland weight divides by the
total top weight, so `wt` and any positive multiple of it give the same complex.
-/

/-- A finite pure weighted simplicial complex on the vertex type `V`, given by its maximal faces
`tops` and the (unnormalised, positive on `tops`) top-level distribution `wt`. -/
structure WComplex (V : Type*) where
  /-- the maximal faces `X(d)` -/
  tops : Finset (Finset V)
  /-- the top-level weight `w_d` (up to normalisation); only its values on `tops` matter -/
  wt : Finset V → ℝ

namespace WComplex

variable {V : Type*} (X : WComplex V)

/-- `σ` is a face of `X` (Definition 2.1): it is contained in a maximal face. -/
def IsFace (σ : Finset V) : Prop := ∃ τ ∈ X.tops, σ ⊆ τ

/-- The vertex set `X(0)` (vertices are the elements of the maximal faces). -/
def vertices : Finset V := X.tops.biUnion id

/-- All faces of `X`, the empty face included. -/
def faces : Finset (Finset V) := X.tops.biUnion Finset.powerset

/-- The faces with exactly `k` vertices, i.e. `X(k - 1)`. -/
def facesCard (k : ℕ) : Finset (Finset V) := X.faces.filter (fun σ => σ.card = k)

/-- The Garland weight of a face (§2.1, p. 11):
`w_i(σ) = Σ_{τ ∈ X(d), τ ⊇ σ} w_d(τ) / binom(d+1, i+1)` with `|σ| = i + 1`, `|τ| = d + 1`, and
`w_d` normalised to a probability distribution on `X(d)`. -/
def gw (σ : Finset V) : ℝ :=
  (∑ τ ∈ X.tops.filter (fun τ => σ ⊆ τ), X.wt τ / ((τ.card.choose σ.card : ℕ) : ℝ)) /
    ∑ τ ∈ X.tops, X.wt τ

/-- The link `X_σ = {τ ∈ X | τ ∩ σ = ∅, τ ∪ σ ∈ X}` (Definition 2.2), with the conditional
distribution `w(τ) ∝ w_d(τ ∪ σ)` on its maximal faces (p. 11). -/
def link (σ : Finset V) : WComplex V where
  tops := (X.tops.filter (fun τ => σ ⊆ τ)).image (fun τ => τ \ σ)
  wt τ := X.wt (τ ∪ σ)

/-- The `n`-skeleton `X^{≤n}` (§2.1, p. 10), with the top-level distribution inherited from `X`:
its maximal faces are the faces of `X` with `n + 1` vertices, weighted by the Garland weight
`w_n` of `X` (p. 11), not uniformly. -/
def skeleton (n : ℕ) : WComplex V where
  tops := X.facesCard (n + 1)
  wt σ := X.gw σ

/-- The `r`-faces complex `F^r X` (Definition 2.11): its vertices are the faces of `X` with
`r + 1` vertices, and `{σ₀, …, σ_k}` is a face iff the `σ_i` are pairwise disjoint and their union
is a face of `X`. Its maximal faces are the sets of `t + 1 = ⌊(d+1)/(r+1)⌋` pairwise disjoint
`(r+1)`-subsets of a maximal face of `X`; the top-level weight of `{σ₀, …, σ_t}` is
`(t+1)! ((r+1)!)^{t+1} / ((t+1)(r+1))! · w_{(t+1)(r+1)-1}(∪ σ_i)` (sample a `t'`-face of `X` and
partition it uniformly at random); lower faces carry the induced (Garland) weights. -/
def facesComplex (r : ℕ) : WComplex (Finset V) where
  tops := X.tops.biUnion (fun τ => ((τ.powersetCard (r + 1)).powerset).filter
    (fun P => P.card = τ.card / (r + 1) ∧ (P : Set (Finset V)).PairwiseDisjoint id))
  wt P := ((P.card.factorial : ℝ) * ((r + 1).factorial : ℝ) ^ P.card /
      ((P.card * (r + 1)).factorial : ℝ)) * X.gw (P.sup id)

/-- The colored faces complex `F^I X` (Definition 2.14) of a partite complex with colour function
`col` with respect to a collection `I` of pairwise disjoint colour sets: its vertices are the faces
`σ` with `col(σ) ∈ I`, and a set of such faces is a face iff their colours are distinct members of
`I` and their union is a face of `X`. Its maximal faces are, for every maximal face `τ` of `X`
containing all colours of `⋃ I`, the family `{τ_J : J ∈ I}` with `τ_J` the vertices of `τ` with
colour in `J`; the weight is that of `F^r X` conditioned on the colours `I`, i.e. proportional to
`w_{T(r+1)-1}(∪_J τ_J)` (p. 14). -/
def coloredFaces (col : V → ℕ) (I : Finset (Finset ℕ)) : WComplex (Finset V) where
  tops := (X.tops.filter (fun τ => ∀ J ∈ I, (τ.filter (fun v => col v ∈ J)).image col = J)).image
    (fun τ => I.image (fun J => τ.filter (fun v => col v ∈ J)))
  wt P := X.gw (P.sup id)

/-- `X` is an `ε`-(one-sided) local spectral expander (Definition 2.7): for every face `τ` with
`-1 ≤ dim τ ≤ d - 2` (the empty face included), the second largest eigenvalue of the random walk
on the weighted 1-skeleton of the link `X_τ` is at most `ε`. Written in its variational form:
with `π = w_0` the vertex weights of the link and `w_1` its edge weights, the walk is
`M(u,v) = w_1({u,v}) / (2π(u))`, self-adjoint on `ℓ²(π)`, and `λ₂(M) ≤ ε` iff
`Σ_{u ≠ v} w_1({u,v})/2 · g(u)g(v) ≤ ε Σ_v π(v) g(v)²` for every `g` with `Σ_v π(v) g(v) = 0`. -/
def IsLocalSpectralExpander (ε : ℝ) : Prop :=
  ∀ τ ∈ X.faces, (∃ ρ ∈ X.tops, τ ⊆ ρ ∧ τ.card + 2 ≤ ρ.card) →
    ∀ g : V → ℝ, ∑ v ∈ (X.link τ).vertices, (X.link τ).gw {v} * g v = 0 →
      ∑ u ∈ (X.link τ).vertices, ∑ v ∈ (X.link τ).vertices,
          (if u = v then 0 else (X.link τ).gw {u, v} / 2 * (g u * g v))
        ≤ ε * ∑ v ∈ (X.link τ).vertices, (X.link τ).gw {v} * g v ^ 2

/-- The degree of a face `σ` (§2.1, p. 10): the number of maximal faces containing it. -/
def degree (σ : Finset V) : ℕ := (X.tops.filter (fun τ => σ ⊆ τ)).card

end WComplex

/-- `([d] choose r+1)^[T]` (Definition 2.16): the collections of `T` pairwise disjoint
`(r+1)`-subsets of the colour set `[d] = {0, …, d}`. -/
def disjointColorSets (d r T : ℕ) : Finset (Finset (Finset ℕ)) :=
  (((Finset.range (d + 1)).powersetCard (r + 1)).powersetCard T).filter
    (fun I => (I : Set (Finset ℕ)).PairwiseDisjoint id)

end PolySwap.KMS


