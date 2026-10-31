-- Prove2me | Definitions.Def_SteinerCutDominants_IsGluingAt
-- name    : SteinerCutDominants_IsGluingAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:29.88002+00:00
-- url     : https://prove2.me/theorems/97dc7b6b-b306-4576-96ec-719aa647d7cb
-- title:
--   Gluing at a common terminal $w$
-- statement:
--   $(G,T)$ arises by **gluing** $(G_1,T_1)$ and $(G_2,T_2)$ at the common terminal $w$ if $V(G_1)\cap V(G_2)=\{w\}$, $w\in T_1\cap T_2$, $V(G)=V(G_1)\cup V(G_2)$, $E(G)=E(G_1)\cup E(G_2)$, and $T=T_1\cup T_2$ or $T=(T_1\cup T_2)\setminus\{w\}$. The glued weight vector $c$ is the minimum integer form of
--   $$
--   (\gamma_{c_2}(G_2,T_2)\cdot c_1,\ \gamma_{c_1}(G_1,T_1)\cdot c_2).
--   $$
--
--   **Formalization Note** $V(G_1)$, $V(G_2)$ are identified with subsets of $V(G)$ by embeddings. Minimum integer form is expressed as $\gcd c=1$ together with $k\,c=(\gamma_{c_2}c_1,\gamma_{c_1}c_2)$ for some $k>0$.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §5, p.10

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG_wt
import Definitions.Def_SteinerCutDominants_gamma

namespace SteinerCutDominants

/-- `H` is obtained by gluing `H₁` and `H₂` at the common terminal node `w` (Conforti, Kaibel,
*Steiner Cut Dominants*, arXiv:2209.14802v2, §5, p.10): `V(G₁) ∩ V(G₂) = {w}`, `w ∈ T₁ ∩ T₂`,
`V(G) = V(G₁) ∪ V(G₂)`, `E(G) = E(G₁) ∪ E(G₂)`, `T = T₁ ∪ T₂` or `T = (T₁ ∪ T₂) \ {w}`, and `c` is the
minimum integer form of `(γ_{c₂}(G₂, T₂) · c₁, γ_{c₁}(G₁, T₁) · c₂)`.

**Formalization Note** `V(G₁)` and `V(G₂)` are identified with subsets of `V(G)` by the embeddings
`φ₁`, `φ₂`, so that the relation holds up to isomorphism by construction. "Minimum integer form"
is the conjunction `gcd c = 1` and `k • c = (γ₂ c₁, γ₁ c₂)` for some `k > 0`. Each `γ` is the graph's
own value, and the two are crossed. -/
def IsGluingAt (H₁ H₂ H : WSG) (φ₁ : H₁.V ↪ H.V) (φ₂ : H₂.V ↪ H.V) (w : H.V) : Prop :=
  w ∈ H₁.T.map φ₁ ∧ w ∈ H₂.T.map φ₂ ∧
    (∀ x₁ x₂, φ₁ x₁ = φ₂ x₂ → φ₁ x₁ = w) ∧
    (∀ x, x ∈ Set.range φ₁ ∨ x ∈ Set.range φ₂) ∧
    (∀ x y, H.G.Adj x y ↔
      (∃ a b, H₁.G.Adj a b ∧ x = φ₁ a ∧ y = φ₁ b) ∨
        (∃ a b, H₂.G.Adj a b ∧ x = φ₂ a ∧ y = φ₂ b)) ∧
    (H.T = H₁.T.map φ₁ ∪ H₂.T.map φ₂ ∨ H.T = (H₁.T.map φ₁ ∪ H₂.T.map φ₂).erase w) ∧
    (Finset.univ : Finset H.G.edgeSet).gcd H.c = 1 ∧
    ∃ k : ℝ, 0 < k ∧
      (∀ a b, k * (H.wt (φ₁ a) (φ₁ b) : ℝ) = gamma H₂ * (H₁.wt a b : ℝ)) ∧
      (∀ a b, k * (H.wt (φ₂ a) (φ₂ b) : ℝ) = gamma H₁ * (H₂.wt a b : ℝ))

end SteinerCutDominants


