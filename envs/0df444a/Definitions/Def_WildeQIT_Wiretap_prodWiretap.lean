-- Prove2me | Definitions.Def_WildeQIT_Wiretap_prodWiretap
-- name    : WildeQIT_Wiretap_prodWiretap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:37.77441+00:00
-- url     : https://prove2.me/theorems/299acfbb-63d7-476e-8cff-c8557b540e3d
-- title:
--   Classical joint wiretap channel $N_1\otimes N_2$
-- statement:
--   Let $N_i\equiv p_{Y_i,Z_i|X_i}$, $i\in\{1,2\}$, be classical wiretap channels. The **joint wiretap channel** $N_1\otimes N_2$ has input pairs $(x_1,x_2)$, gives Bob the pair $Y_1Y_2$ and Eve the pair $Z_1Z_2$, and has distribution
--
--   $$
--   p_{Y_1,Z_1|X_1}(y_1,z_1|x_1)\,p_{Y_2,Z_2|X_2}(y_2,z_2|x_2).
--   $$
--
--   The two channels act independently, while the joint input distribution (together with Alice's auxiliary variable) may be correlated. Its private information is the left-hand side of the additivity theorem.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second). Bob's alphabet is $\mathcal Y_1\times\mathcal Y_2$ and Eve's is $\mathcal Z_1\times\mathcal Z_2$; the product distribution of the two channel outputs is reindexed from $((y_1,z_1),(y_2,z_2))$ to $((y_1,y_2),(z_1,z_2))$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.2.1 and eq. (13.60), p. 397

import Definitions.Def_WildeQIT_Wiretap_WiretapChannel

namespace WildeQIT.Wiretap

open WildeQIT

/-- **The classical joint wiretap channel `N₁ ⊗ N₂`.**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.2.1 and (13.60),
p. 397: for wiretap channels `Nᵢ ≡ p_{Yᵢ,Zᵢ|Xᵢ}` (`i ∈ {1, 2}`) the joint channel has distribution
`p_{Y₁,Z₁|X₁}(y₁, z₁|x₁) p_{Y₂,Z₂|X₂}(y₂, z₂|x₂)`; Bob receives `Y₁Y₂` and Eve receives `Z₁Z₂`.

`prodWiretap N₁ N₂` is the wiretap channel with input alphabet `α₁ × α₂`, Bob's alphabet
`β₁ × β₂` and Eve's alphabet `γ₁ × γ₂`, and
`(prodWiretap N₁ N₂ (x₁, x₂)).prob ((y₁, y₂), (z₁, z₂)) = N₁(y₁, z₁|x₁) · N₂(y₂, z₂|x₂)`. -/
noncomputable def prodWiretap {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type} [Fintype β₁] [Fintype β₂]
    [Fintype γ₁] [Fintype γ₂]
    (N₁ : WiretapChannel α₁ β₁ γ₁) (N₂ : WiretapChannel α₂ β₂ γ₂) :
    WiretapChannel (α₁ × α₂) (β₁ × β₂) (γ₁ × γ₂) :=
  fun x => ((N₁ x.1).prod (N₂ x.2)).comap (Equiv.prodProdProdComm β₁ β₂ γ₁ γ₂)

end WildeQIT.Wiretap


