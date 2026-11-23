-- Prove2me | Definitions.Def_ExtensionComplexity_TSP_Supplement_OneWayProtocol
-- name    : ExtensionComplexity_TSP_Supplement_OneWayProtocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:35:39.17764+00:00
-- url     : https://prove2.me/theorems/20e3ba25-0f5d-41eb-93cd-d74c7b8a267d
-- title:
--   One-way quantum protocols computing matrices in expectation (§4.2)
-- statement:
--   Let $I$ and $J$ be Alice's and Bob's input sets and let $r$ be the message dimension. Alice assigns a real $r$-dimensional state $\rho_i$ to each $i\in I$. Bob assigns a finite labelled POVM $(E^j_o,\theta^j_o)$ to each $j\in J$, with every label nonnegative. The protocol computes a real matrix $M$ in expectation exactly when
--
--   $$
--   \forall i\in I\ \forall j\in J,\qquad
--   \sum_o\theta^j_o\operatorname{Tr}(E^j_o\rho_i)=M_{ij}.
--   $$
--
--   The protocol has pure-state messages exactly when every $\rho_i$ is pure. These definitions impose the actual state and measurement conditions before defining computation in expectation. Alice's state depends only on her input and Bob's measurement only on his input; the finite number of outcomes may vary with Bob's input.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, DOI 10.1145/2716307, p. 17:17, §4.2, opening paragraph

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Supplement_LabelledPOVM

namespace ExtensionComplexity.TSP.Supplement

/-- Section 4.2, p. 17:17: Alice sends a state depending on her row input;
Bob chooses a POVM depending on his column input and returns its nonnegative label. -/
structure OneWayProtocol (ι κ : Type*) (r : ℕ) where
  alice : ι → QuantumState r
  bob : κ → LabelledPOVM r
  label_nonnegative : ∀ j o, 0 ≤ (bob j).label o

/-- Every entry is computed in expectation, not merely with a success probability. -/
def OneWayProtocol.Computes {ι κ : Type*} {r : ℕ}
    (P : OneWayProtocol ι κ r) (M : Matrix ι κ ℝ) : Prop :=
  ∀ i j, (P.bob j).expectation (P.alice i) = M i j

/-- Every message, for every Alice input, is pure. -/
def OneWayProtocol.PureMessages {ι κ : Type*} {r : ℕ}
    (P : OneWayProtocol ι κ r) : Prop :=
  ∀ i, (P.alice i).IsPure

end ExtensionComplexity.TSP.Supplement


