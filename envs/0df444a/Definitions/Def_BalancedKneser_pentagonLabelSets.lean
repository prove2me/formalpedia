-- Prove2me | Definitions.Def_BalancedKneser_pentagonLabelSets
-- name    : BalancedKneser_pentagonLabelSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:13.377491+00:00
-- url     : https://prove2.me/theorems/626690e2-896e-49ae-ab2f-d9f6731cadf3
-- title:
--   Pentagon labels $A_i$ and the pentagon configurations in $[2n]$
-- statement:
--   On a five-point set $D$ arrange a pentagon, and let $A_i$ be the two neighbors of point $i$. On $\mathrm{Fin}\,5$ with the cycle $0-1-2-3-4-0$ this is $A_i=\{i-1,i+1\}$ (mod 5).
--
--   A **pentagon configuration** in $[2n]$ chooses disjoint $I,D\subseteq[2n]$ with $|I|=n-2$ and $|D|=5$ (with a pentagon on $D$) and uses the five $n$-sets $I\cup A_i$. The **complemented configuration** uses their five complements. The set `pentagonLabelSets n` collects, over all choices, the five-element label families of both kinds. The pentagon cycle $z_{I,D}$ is the boundary of the simplex on such a label family (Proposition 3.2).
--
--   **Formalization Note** A pentagon on $D$ is transported from $\mathrm{Fin}\,5$ by an injection $e:\mathrm{Fin}\,5\hookrightarrow\mathrm{Fin}\,2n$ with image $D$; every pentagon on a five-point set arises this way. $|I|=n-2$ is written $|I|+2=n$. The module proves $|A_i|=2$.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §3.2, p.6 (PDF p.8): pentagon labels and configurations

import Mathlib
import Definitions.Def_BalancedKneser_configLabels

namespace BalancedKneser

/-- **Pentagon labels** (Alipour–Jafari, arXiv:2611.04486v1, §3.2, p.6 (PDF p.8): "On a
five-point set D, arrange a pentagon. Let Aᵢ be the two neighbors of point i"). On `Fin 5`
arranged as the cycle `0 – 1 – 2 – 3 – 4 – 0`, the label of `i` is `{i + 1, i − 1}`
(arithmetic mod 5). Every pentagon on a five-point set is the image of this one under a
bijection. -/
def pentA (i : Fin 5) : Finset (Fin 5) := {i + 1, i - 1}

theorem pentA_card (i : Fin 5) : (pentA i).card = 2 := by
  revert i; decide

/-- **The pentagon configurations in `[2n]`** (arXiv:2611.04486v1, §3.2, p.6 (PDF p.8): "choose
disjoint I, D ⊆ [2n] with |I| = n − 2 and |D| = 5, and use the labels I ∪ Aᵢ. … We also use
the cycles obtained by complementing all five n-sets."). Each member is the set of five
`n`-subsets of `[2n]` of one pentagon configuration `(I, D)` (with `D` the image of an injection
`e : Fin 5 ↪ Fin (2n)` and the pentagon transported by `e`), or of its complemented
configuration. -/
def pentagonLabelSets (n : ℕ) : Set (Finset (KSet (2 * n) n)) :=
  {L | ∃ (I : Finset (Fin (2 * n))) (e : Fin 5 ↪ Fin (2 * n)),
    I.card + 2 = n ∧ Disjoint I (Finset.univ.map e) ∧
    (L = configLabels n pentA I e ∨ L = configLabelsCompl n pentA I e)}

end BalancedKneser


