-- Prove2me | Definitions.Def_PottsRapidMixing_Supplement_Lattice
-- name    : PottsRapidMixing_Supplement_Lattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:28:06.348199+00:00
-- url     : https://prove2.me/theorems/631996ae-5013-489c-8df1-5d01ff812e9e
-- title:
--   The box $\{1,\dots,m\}^d$, wired box crossings, and the critical point $\beta_c(q,\mathbb Z^d)$
-- statement:
--   **The box.** For integers $d,m\ge1$, the box $\{1,\dots,m\}^d\subset\mathbb Z^d$ with free boundary is the graph on $[m]^d$ in which $x\sim y$ when $x$ and $y$ agree in all coordinates but one, where they differ by exactly $1$. It has $n=m^d$ vertices, no wrap-around and no boundary spins; it is the $d$-fold box product of the path on $m$ vertices.
--
--   **Wired crossing probabilities.** Let $\Lambda_N=\{-N,\dots,N\}^d$ with its nearest-neighbour edges, $0$ its centre and $\partial\Lambda_N$ the vertices with some coordinate equal to $\pm N$. For $p\in(0,1)$ and $q>0$, the wired random-cluster law $\phi^1_{\Lambda_N,p,q}$ is the random-cluster law on the edges of $\Lambda_N$,
--   $$\phi^1_{\Lambda_N,p,q}(\omega)\propto\Bigl(\frac{p}{1-p}\Bigr)^{|\omega|}q^{c^1(\omega)},$$
--   where $c^1(\omega)$ counts the components after all of $\partial\Lambda_N$ is identified into one vertex. Set
--   $$\theta_N(p)=\phi^1_{\Lambda_N,p,q}(0\leftrightarrow\partial\Lambda_N).$$
--
--   **The critical point.** For an integer $q\ge2$ and $d\ge2$,
--   $$\beta_c(q,\mathbb Z^d)=\sup\bigl\{\beta>0:\ \theta_N(1-e^{-\beta})\to0\text{ as }N\to\infty\bigr\}.$$
--   Equivalently $\beta_c=-\log(1-p_c)$ with $p_c(q,d)=\sup\{p:\phi^1_{\mathbb Z^d,p,q}(0\leftrightarrow\infty)=0\}$, since $\phi^1_{\mathbb Z^d,p,q}(0\leftrightarrow\infty)=\lim_N\theta_N(p)$; through the Edwards–Sokal coupling it is the critical inverse temperature of the $q$-state Potts model on $\mathbb Z^d$. This is the threshold of Theorem 1.2.
--
--   **Formalization Note** The box is encoded on `Fin d → Fin m` (coordinate $k$ standing for $k+1$), and $\Lambda_N$ on `Fin d → Fin (2N+1)` (coordinate $k$ standing for $k-N$). The wired law is the mission's published `rcBoundary` on $\Lambda_N$ with the boundary partition given by the graph joining all pairs of boundary vertices. The supremum is taken in `EReal`, so an empty or unbounded set has no junk value, and `β < β_c` holds exactly when some $\beta'>\beta$ has $\theta_N(1-e^{-\beta'})\to0$ (proved in `Solutions/verification/PottsRapidMixing_Supplement_Sanity`). The paper does not define $\beta_c$; this is the standard definition. The torus $(\mathbb Z/m\mathbb Z)^d$ is not defined here: it is the published `MarkovMixing.torusGraph`.
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, §1, p.3 (cube in ℤ^d, β_c(q, ℤ^d)); §7, p.45 ((7.1), wired box law); Remark 7.3, p.48 (free boundary box)

import Mathlib
import Definitions.Def_PottsRapidMixing_RandomCluster
import Definitions.Def_PottsRapidMixing_Threshold

open scoped Classical
open Filter Topology

namespace PottsRapidMixing.Supplement

/-- The box `{1, …, m}^d ⊂ ℤ^d` with free boundary, as a graph (Blanca, Gheissari, Park, Zhang,
arXiv:2610.42059, p.3, "a cube in ℤ^d on n vertices", and Remark 7.3, p.48): vertices are
`x : Fin d → Fin m` (coordinate `k ∈ Fin m` standing for `k + 1`), and `x ∼ y` when they agree in all
coordinates but one, where they differ by exactly `1`. There is no wrap-around and there are no
boundary spins, so it has `n = m^d` vertices. This is the `d`-fold box product of the path on `m`
vertices. -/
def boxGraph (d m : ℕ) : SimpleGraph (Fin d → Fin m) where
  Adj x y := ∃ j : Fin d, (∀ i : Fin d, i ≠ j → x i = y i) ∧
    ((x j : ℕ) + 1 = (y j : ℕ) ∨ (y j : ℕ) + 1 = (x j : ℕ))
  symm := by
    constructor
    rintro x y ⟨j, hoff, hj⟩
    exact ⟨j, fun i hi => (hoff i hi).symm, hj.symm⟩
  loopless := ⟨fun x ⟨j, _, hj⟩ => by omega⟩

/-- The centre `0` of the box `Λ_N = {−N, …, N}^d`, encoded on `Fin d → Fin (2N+1)` (coordinate `k`
standing for `k − N`): the vertex with every coordinate `N`. -/
def boxCentre (d N : ℕ) : Fin d → Fin (2 * N + 1) := fun _ => ⟨N, by omega⟩

/-- The vertex boundary `∂Λ_N` of `Λ_N = {−N, …, N}^d`: the vertices with some coordinate `±N`,
i.e. `0` or `2N` in the encoding on `Fin (2N+1)`. -/
def IsBoxBoundary (d N : ℕ) (x : Fin d → Fin (2 * N + 1)) : Prop :=
  ∃ i : Fin d, (x i : ℕ) = 0 ∨ (x i : ℕ) = 2 * N

/-- The graph joining every two distinct boundary vertices of `Λ_N`: as the boundary partition `ζ` of
the published `rcBoundary`, it identifies all of `∂Λ_N` into one block (the *wired* boundary
condition). -/
def wiredBoundary (d N : ℕ) : SimpleGraph (Fin d → Fin (2 * N + 1)) :=
  SimpleGraph.fromRel (fun x y => IsBoxBoundary d N x ∧ IsBoxBoundary d N y)

/-- `θ_N(p) = φ¹_{Λ_N, p, q}(0 ↔ ∂Λ_N)`: the probability, under the wired random-cluster law on the
box `Λ_N` at parameters `p` and `q`, that the centre is joined to the boundary by open edges. The law
is the published `rcBoundary` on `boxGraph d (2N+1)` with boundary partition `wiredBoundary d N`. -/
noncomputable def wiredCrossing (d N : ℕ) (p q : ℝ) : ℝ :=
  ∑ ω : (boxGraph d (2 * N + 1)).edgeSet → Bool,
    rcBoundary (boxGraph d (2 * N + 1)) p q (wiredBoundary d N) ω *
      (if ∃ b, IsBoxBoundary d N b ∧ (edgeGraph (boxGraph d (2 * N + 1)) ω).Reachable (boxCentre d N) b
        then 1 else 0)

/-- The critical point `β_c(q, ℤ^d)` of the `q`-state Potts model on `ℤ^d` (arXiv:2610.42059, pp.3,
45), through the random-cluster model with `p = 1 − e^{−β}` (published `pOf`):
`β_c = sup {β > 0 : θ_N(1 − e^{−β}) → 0 as N → ∞}`, i.e. `p_c(q, d) = sup {p : φ¹_{ℤ^d,p,q}(0 ↔ ∞) = 0}`
and `β_c = −log(1 − p_c)`.

**Formalization Note.** The paper does not define `β_c`; this is the standard definition. Since
`φ¹_{ℤ^d}(0 ↔ ∞) = lim_N θ_N(p)` for the wired box laws, it is the usual infinite-volume critical point,
and for integer `q ≥ 2` the Edwards–Sokal coupling makes it the Potts critical point. The supremum is in
`EReal`, so neither an empty set nor an unbounded one has a junk value: `β < β_c` holds exactly when
some `β' > β` has `θ_N(1 − e^{−β'}) → 0`. -/
noncomputable def betaC (q d : ℕ) : EReal :=
  sSup ((fun β : ℝ => (β : EReal)) ''
    {β : ℝ | 0 < β ∧ Tendsto (fun N : ℕ => wiredCrossing d N (pOf β) (q : ℝ)) atTop (𝓝 0)})

end PottsRapidMixing.Supplement


