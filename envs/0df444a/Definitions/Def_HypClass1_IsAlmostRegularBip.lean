-- Prove2me | Definitions.Def_HypClass1_IsAlmostRegularBip
-- name    : HypClass1_IsAlmostRegularBip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:25:33.694268+00:00
-- url     : https://prove2.me/theorems/96cd23cf-2078-4b66-920c-cd5b4ce6b80a
-- title:
--   $(\gamma\pm\varepsilon)pn$-regular bipartite graph
-- statement:
--   A bipartite graph $R$ with parts $X, Y$, $|X| = |Y| = n$, is **$(\gamma \pm \varepsilon)pn$-regular** if every vertex $z \in X \cup Y$ has
--   $$
--   (\gamma - \varepsilon)pn \le \deg_R(z) \le (\gamma + \varepsilon)pn.
--   $$
--   It is the hypothesis on the graph $R$ to be covered in Lemmas 6.1 and 6.3.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), p.9 (after Definition 4.1) and Lemmas 6.1, 6.3, pp.15–16

import Mathlib
import Definitions.Def_HypClass1_IsPseudorandomBip

namespace HypClass1

/-- **`(γ ± ε)pn`-regular bipartite graph**: every vertex degree lies in `[(γ − ε)pn, (γ + ε)pn]`.
Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), p.9 (after Definition 4.1: "We will often refer to a bipartite graph B satisfying (A1) as an
(1 ± ε)pn-regular bipartite graph"), used in Lemmas 6.1 and 6.3, pp.15–16 ("R is (γ ± ε)pn-regular").

**Formalization Note.** `R ⊆ X × Y` and `n = |X|` (the statements using it have `|X| = |Y| = n`). -/
def IsAlmostRegularBip {α β : Type*} [DecidableEq α] [DecidableEq β] (γ ε p : ℝ) (X : Finset α)
    (Y : Finset β) (R : Finset (α × β)) : Prop :=
  R ⊆ X ×ˢ Y ∧
  (∀ x ∈ X, (γ - ε) * p * X.card ≤ ldeg R x ∧ (ldeg R x : ℝ) ≤ (γ + ε) * p * X.card) ∧
  (∀ y ∈ Y, (γ - ε) * p * X.card ≤ rdeg R y ∧ (rdeg R y : ℝ) ≤ (γ + ε) * p * X.card)

end HypClass1


