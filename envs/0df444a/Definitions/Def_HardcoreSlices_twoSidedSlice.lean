-- Prove2me | Definitions.Def_HardcoreSlices_twoSidedSlice
-- name    : HardcoreSlices_twoSidedSlice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:43.730218+00:00
-- url     : https://prove2.me/theorems/316115bd-d868-4cd1-8cc8-b6e617962bd8
-- title:
--   The two-sided independent set slice
-- statement:
--   Let $G=(X,Y,E)$ be bipartite, with $k_X,k_Y$ given. Then $\mathcal I_{k_X,k_Y}(G)$ is the set of independent sets $I$ with $|I\cap X|=k_X$ and $|I\cap Y|=k_Y$; $\mu^{(k_X,k_Y)}$ is the uniform distribution on it; and the two-sided slice is its downward closure, a pure $(k_X+k_Y)$-dimensional complex on the ground set $X\cup Y$.
--
--   The set `freeSide G b τ` is $X\setminus(\tau_X\cup N(\tau_Y))$, and $Y\setminus(\tau_Y\cup N(\tau_X))$ for the other side: the vertices of a side compatible with $\tau$. It is the denominator data of Lemma 4.1.
--
--   **Formalization Note** A side is named by a Boolean: `false` is $X$ and `true` is $Y$.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Definition 1.6, p.3; Lemma 4.1, p.19

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting
import Definitions.Def_HardcoreSlices_downUp

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- The side named by a Boolean: `false` is `X` and `true` is `Y`. -/
noncomputable def sideOf (m : ℕ) (b : Bool) : Finset (Vertex m) := if b then evenSide m else oddSide m

/-- `I_{kX,kY}(G)`, the independent sets with `kX` vertices in `X` and `kY` in `Y`. Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), Definition 1.6, p.3:
"`IkX,kY(G) = { I ∈ Ik(G) | k = kX + kY, |I ∩ X| = kX, |I ∩ Y| = kY }`". -/
noncomputable def twoSidedFacets {m : ℕ} (G : SimpleGraph (Vertex m)) (kX kY : ℕ) :
    Finset (Finset (Vertex m)) :=
  Finset.univ.filter (fun I => IsIndependent G I ∧ (I ∩ oddSide m).card = kX ∧
    (I ∩ evenSide m).card = kY)

/-- The two-sided slice complex (Definition 1.6, p.3): "the closure of `IkX,kY(G)` over ground set
`X ∪ Y`". -/
noncomputable def twoSidedComplex {m : ℕ} (G : SimpleGraph (Vertex m)) (kX kY : ℕ) :
    Finset (Finset (Vertex m)) :=
  downClosure (twoSidedFacets G kX kY)

/-- `µ^{(kX,kY)}`, "the uniform distribution over `IkX,kY(G)`" (Definition 1.6, p.3). -/
noncomputable def twoSidedLaw {m : ℕ} (G : SimpleGraph (Vertex m)) (kX kY : ℕ)
    (I : Finset (Vertex m)) : ℝ :=
  if I ∈ twoSidedFacets G kX kY then 1 / ((twoSidedFacets G kX kY).card : ℝ) else 0

/-- `X \ (τX ∪ N(τY))` (and `Y \ (τY ∪ N(τX))` for `b = true`), the free vertices of a side in Lemma 4.1, p.19. -/
noncomputable def freeSide {m : ℕ} (G : SimpleGraph (Vertex m)) (b : Bool) (τ : Finset (Vertex m)) :
    Finset (Vertex m) :=
  sideOf m b \ ((τ ∩ sideOf m b) ∪ vertexBoundary G (τ ∩ sideOf m (!b)))

end HardcoreSlices


