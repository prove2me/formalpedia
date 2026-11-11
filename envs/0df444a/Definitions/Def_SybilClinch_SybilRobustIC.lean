-- Prove2me | Definitions.Def_SybilClinch_SybilRobustIC
-- name    : SybilClinch_SybilRobustIC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:58.950128+00:00
-- url     : https://prove2.me/theorems/19fc88fa-d59f-45c1-bbc4-1aa7d767e511
-- title:
--   Sybil-robust incentive compatibility
-- statement:
--   A mechanism is **Sybil-robust incentive compatible** if, for every physical trader, every true type (of either direction, eligible or not), every fixed strategy profile of the other traders, and every admissible strategy (Definition 2.4), the true utility from the truthful merged strategy, the single identity reporting the true type, is at least the true utility from the deviation.
--
--   **Formalization Note** The mechanism is given as a relation `Out ids rep f` (outcome `f` possible on the profile). Identities are natural-number labels; the truthful identity is any label $i_0$ outside the others' identity set $O$, and the deviation any finite label set $D$ disjoint from $O$ ($D=\emptyset$ allowed). The two profiles' report functions agree on $O$ and are otherwise independent, so a mechanism cannot exploit labels. For a function mechanism, `Out` is its graph.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.3, Definition 2.6, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SybilClinch_trueUtil
import Definitions.Def_SybilClinch_StratAdmissible

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.3, Definition 2.6 (Sybil-robust incentive compatibility), printed p.7 (PDF p.9).

`Out ids rep f` says that `f` is an outcome the mechanism may produce on the profile `(ids, rep)`.
The mechanism is Sybil-robust IC if for every true type `t` (either direction, eligible or not),
every fixed profile `O` of the other traders' identities, every admissible strategy `D`
(Definition 2.4), the true utility of the truthful merged strategy (the single identity `i₀`
reporting `t`) is at least the true utility of the deviation.

**Formalization Note.** Identities are labels in `ℕ`; `i₀` is any label outside `O`, and `D` any
finite label set disjoint from `O` (`D = ∅` is allowed). The two profiles use report functions
`rep₁`, `rep₂` that agree on `O` and are otherwise unrelated, so a mechanism cannot exploit
labels or reports outside the profile. For a relational mechanism the inequality is required for
every pair of possible outcomes. -/
def SybilRobustIC (Out : Finset ℕ → (ℕ → Report) → (ℕ → Fill) → Prop) : Prop :=
  ∀ (t : Report), t.Valid →
    ∀ (O D : Finset ℕ) (i₀ : ℕ) (rep₁ rep₂ : ℕ → Report),
      i₀ ∉ O → Disjoint O D → (∀ j ∈ O, (rep₁ j).Valid) → (∀ j ∈ O, rep₂ j = rep₁ j) →
      rep₁ i₀ = t → StratAdmissible t D rep₂ →
      ∀ f₁ f₂ : ℕ → Fill, Out (insert i₀ O) rep₁ f₁ → Out (O ∪ D) rep₂ f₂ →
        trueUtil t D rep₂ f₂ ≤ trueUtil t {i₀} rep₁ f₁

end SybilClinch


