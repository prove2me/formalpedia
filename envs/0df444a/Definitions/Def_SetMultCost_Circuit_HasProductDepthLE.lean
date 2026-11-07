-- Prove2me | Definitions.Def_SetMultCost_Circuit_HasProductDepthLE
-- name    : SetMultCost_Circuit_HasProductDepthLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:49.943137+00:00
-- url     : https://prove2.me/theorems/9295f761-f2f2-4652-888c-eba1acf9fc83
-- title:
--   Product-depth at most $\Delta$, by a height function
-- statement:
--   A **product-height function** on a circuit assigns a natural number $h(v)$ to each node so that $h(c)\le h(v)$ when $v$ is an addition gate with child $c$, while $h(c)+1\le h(v)$ when $v$ is a multiplication gate with child $c$, and $h(v)\ge1$ at every multiplication gate.
--
--   A circuit has **product-depth at most $\Delta$** when it has such a function with $h\le\Delta$ at every node. Equivalently, every directed path contains at most $\Delta$ multiplication gates.
--
--   **Formalization Note** The paper assumes alternately layered circuits, at a small blowup in size. The height of a layer in such a circuit is a height function, so the class here contains the paper's: $\Sigma\Pi\Sigma$ has product-depth $1$, and $\Sigma\Pi\Sigma\Pi$ and $\Sigma\Pi\Sigma\Pi\Sigma$ have product-depth $2$.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), §2, p.7

import Mathlib
import Definitions.Def_SetMultCost_Circuit

namespace SetMultCost

namespace Circuit

variable {σ F : Type*}

/-- A **product-height function**: heights do not decrease from a child to a parent addition gate,
and strictly increase from a child to a parent multiplication gate, and a multiplication gate has
height at least `1`. -/
def IsHeightFn (Φ : Circuit σ F) (h : Fin Φ.numNodes → ℕ) : Prop :=
  ∀ v, match Φ.gate v with
    | .var _ => True
    | .const _ => True
    | .add cs => ∀ c ∈ cs, h c ≤ h v
    | .mul cs => 1 ≤ h v ∧ ∀ c ∈ cs, h c + 1 ≤ h v

/-- **Product-depth at most `Δ`.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), §2, p.7: "the product-depth is the number of layers with
product gates".

**Formalization Note.** The paper assumes alternately layered circuits "With a small blowup in
size"; here there is no layering. A circuit has product-depth at most `Δ` when it has a height
function bounded by `Δ` at every node, equivalently when every directed path contains at most `Δ`
multiplication gates. The height of a layer of an alternately layered circuit is such a function,
so the class contains the paper's. -/
def HasProductDepthLE (Φ : Circuit σ F) (Δ : ℕ) : Prop :=
  ∃ h : Fin Φ.numNodes → ℕ, Φ.IsHeightFn h ∧ ∀ v, h v ≤ Δ

end Circuit

end SetMultCost


