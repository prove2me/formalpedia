-- Prove2me | Definitions.Def_WildeQIT_Wiretap_prodChannel
-- name    : WildeQIT_Wiretap_prodChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:58.281486+00:00
-- url     : https://prove2.me/theorems/da30f7a6-4c20-4722-b939-12f7f53a26c6
-- title:
--   Classical joint channel $N_1\otimes N_2$
-- statement:
--   Let $N_1\equiv p_{Y_1|X_1}$ and $N_2\equiv p_{Y_2|X_2}$ be classical channels. The **joint channel** $N_1\otimes N_2$ has input pairs $(x_1,x_2)$, output pairs $(y_1,y_2)$, and transition probabilities
--
--   $$
--   p_{Y_1,Y_2|X_1,X_2}(y_1,y_2|x_1,x_2)=p_{Y_1|X_1}(y_1|x_1)\,p_{Y_2|X_2}(y_2|x_2).
--   $$
--
--   The two channels act independently, but an input distribution of the joint channel is an arbitrary distribution $p_{X_1,X_2}$ on pairs, so the inputs may be correlated. This is the channel whose mutual information is compared with $I(N_1)+I(N_2)$ in the additivity theorem.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second).
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Section 13.1.2, eq. (13.15), p. 391

import Definitions.Def_WildeQIT_Channel

namespace WildeQIT.Wiretap

open WildeQIT

/-- **The classical joint channel `N₁ ⊗ N₂`.**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.1.2, (13.15), p. 391:
`N₁ ⊗ N₂` is the channel with
`p_{Y₁,Y₂|X₁,X₂}(y₁, y₂|x₁, x₂) = p_{Y₁|X₁}(y₁|x₁) p_{Y₂|X₂}(y₂|x₂)`.

`prodChannel N₁ N₂` maps the input pair `(x₁, x₂)` to the product distribution
`N₁(·|x₁) ⊗ N₂(·|x₂)` on output pairs `(y₁, y₂)`. Its input distributions are arbitrary
distributions on pairs, so correlated inputs are allowed. -/
noncomputable def prodChannel {α₁ α₂ β₁ β₂ : Type} [Fintype β₁] [Fintype β₂]
    (N₁ : Channel α₁ β₁) (N₂ : Channel α₂ β₂) : Channel (α₁ × α₂) (β₁ × β₂) :=
  fun x => (N₁ x.1).prod (N₂ x.2)

end WildeQIT.Wiretap


