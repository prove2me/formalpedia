-- Prove2me | Definitions.Def_WeakMFG_Existence_UHC
-- name    : WeakMFG_Existence_UHC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:45.974689+00:00
-- url     : https://prove2.me/theorems/21420fcb-e6e1-45e7-adf6-d7056d792b1e
-- title:
--   Upper hemicontinuity of a set-valued map (§7.1)
-- statement:
--   Let $K$ be a topological space and $(E,d)$ a metric space. For $F\subset E$ and $\varepsilon>0$ write $B(F,\varepsilon)=\{y\in E:\inf_{b\in F}d(y,b)<\varepsilon\}$. A set-valued map $\Gamma:K\to 2^E$ is *upper hemicontinuous at* $x\in K$ if for every $\varepsilon>0$ there is a neighbourhood $U$ of $x$ with
--   $$\Gamma(U)\subset B(\Gamma(x),\varepsilon).$$
--   This is the notion used in the set-valued fixed point theorem and in Berge's maximum theorem of §7.1.
--
--   **Formalization Note** The page defines the notion for a metric space $K$ with a ball $B(x,\delta)$; a neighbourhood of $x$ is equivalent there and needs only a topology on $K$. The condition $y\in B(\Gamma(x),\varepsilon)$ is unfolded as "some $b\in\Gamma(x)$ has $d(y,b)<\varepsilon$", so that $B(\emptyset,\varepsilon)=\emptyset$ as on the page.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §7.1, p. 23

import Mathlib

open Filter Topology

namespace WeakMFG.Existence

/-- Upper hemicontinuity (Carmona–Lacker, arXiv:1307.1152v2, §7.1, p. 23): `Γ : K → 2^E` is upper
hemicontinuous at `x` if for every `ε > 0` there is a neighbourhood `U` of `x` with
`Γ(U) ⊂ B(Γ(x), ε) = {a : inf_{b ∈ Γ(x)} d(a, b) < ε}`.
Formalization Note: the page uses a ball `B(x, δ)` in a metric space `K`; a neighbourhood filter
is equivalent there and needs only a topology on `K`. `B(Γ(x), ε)` is unfolded as "some
`b ∈ Γ(x)` with `dist a b < ε`", so that `B(∅, ε) = ∅` as on the page. -/
def UHCAt {K E : Type*} [TopologicalSpace K] [PseudoMetricSpace E] (Γ : K → Set E) (x : K) :
    Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ y in 𝓝 x, ∀ a ∈ Γ y, ∃ b ∈ Γ x, dist a b < ε

end WeakMFG.Existence


