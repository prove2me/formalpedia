-- Prove2me | Definitions.Def_SteinerCutDominants_IsSupportRep
-- name    : SteinerCutDominants_IsSupportRep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:18.397229+00:00
-- url     : https://prove2.me/theorems/dc45558e-bef3-4b6d-93ce-dfb440684357
-- title:
--   The support graph $(G_a,T)$ of a vector, up to scale
-- statement:
--   For $a\in\mathbb R^{E(G)}$, the graph $G_a=(V_a,E_a)$ is the subgraph of $G$ on the edges $E_a$ with $a_e\neq 0$ and their end nodes. A weighted Steiner graph $H$ with embedding $\varphi$ and scale $r$ **represents** $(G_a,T)$ if $\varphi$ maps the terminals of $H$ onto $T$, the edges of $G$ with $a_e\neq0$ are exactly the images of the edges of $H$, and $a=r\,c_H$ on them.
--
--   **Formalization Note** This is how a real inequality not yet scaled to minimum integer form is compared with a Steiner subgraph of $(G,T)$. Since $H$ is connected with at least two terminals, $\varphi$ has range exactly $V_a$.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §2, p.4

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG_wt

namespace SteinerCutDominants

/-- `H` represents the support graph `(G_a, T)` of the real vector `a` on `G`, up to the scale `r`
(Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, §2, p.4): the embedding `φ` maps the
terminals of `H` onto `T`, the edges of `G` with `a e ≠ 0` are exactly the images of the edges of
`H`, and `a` equals `r` times the weights of `H` on them.

**Formalization Note** `G_a = (V_a, E_a)` is the subgraph of the edges with `a e ≠ 0`. Being a
`WSG`, `H` is connected with at least two terminals, so `φ` has range exactly `V_a`. -/
def IsSupportRep {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V)
    (a : G.edgeSet → ℝ) (H : WSG) (φ : H.V ↪ V) (r : ℝ) : Prop :=
  H.T.map φ = T ∧
    (∀ x y, H.G.Adj x y ↔ edgeVal G a (φ x) (φ y) ≠ 0) ∧
    (∀ x y, edgeVal G a x y ≠ 0 → x ∈ Set.range φ ∧ y ∈ Set.range φ) ∧
    (∀ x y, H.G.Adj x y → edgeVal G a (φ x) (φ y) = r * (H.wt x y : ℝ))

end SteinerCutDominants


