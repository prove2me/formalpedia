-- Prove2me | Definitions.Def_SetMultCost_Circuit_IsHomogeneous
-- name    : SetMultCost_Circuit_IsHomogeneous
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:45.761612+00:00
-- url     : https://prove2.me/theorems/b7153ddc-c23a-4333-961c-aa6576f95c41
-- title:
--   Homogeneous circuit
-- statement:
--   A circuit is **homogeneous** when the polynomial computed at every node is homogeneous; the zero polynomial counts.
--
--   **Formalization Note** This differs from the printed sentence, "A circuit is said to be a homogeneous circuit if the polynomial computed at every node has degree at most $d$". The proof of Lemma 4.2 relies on "degrees do not decrease at any sum gate in a homogeneous circuit", and under the printed wording Lemma 4.2 fails for $x_1\cdots x_d+x_1$. The paper applies Lemma 4.2 only to set-multilinear circuits, whose nodes are all homogeneous.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), §2, p.8; proof of Lemma 4.2, p.14

import Mathlib
import Definitions.Def_SetMultCost_Circuit

namespace SetMultCost

/-- **Homogeneous circuit**: the polynomial computed at every node is homogeneous (the zero
polynomial counts).

Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), §2, p.8 prints "A circuit is said to be a homogeneous circuit if the polynomial computed at
every node has degree at most d". Lemma 4.2's proof (p.14) relies on "degrees do not decrease at
any sum gate in a homogeneous circuit", which the printed sentence does not give: in the circuit
`x₁ ⋯ x_d + x₁` every node has degree at most `d`, yet the sum gate has a child of degree `1`.

**Formalization Note.** This is the standard meaning of the term, which the paper's proof uses, not
the printed sentence. The paper applies Lemma 4.2 only to set-multilinear circuits, whose nodes are
all homogeneous. -/
def Circuit.IsHomogeneous {σ F : Type*} [CommRing F] (Φ : Circuit σ F) : Prop :=
  ∀ v, ∃ k : ℕ, (Φ.nodeValue v).IsHomogeneous k

end SetMultCost


