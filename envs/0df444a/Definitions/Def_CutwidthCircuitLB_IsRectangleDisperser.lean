-- Prove2me | Definitions.Def_CutwidthCircuitLB_IsRectangleDisperser
-- name    : CutwidthCircuitLB_IsRectangleDisperser
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:24.322685+00:00
-- url     : https://prove2.me/theorems/56269e04-0b49-4537-a22d-c192bdf3afed
-- title:
--   $K$-rectangle disperser
-- statement:
--   For $K > 1$, a function $f : \{0,1\}^n \to \{0,1\}$ is a **$K$-rectangle disperser** if for every partition $[n] = U \sqcup V$ and every rectangle $P \times Q$ with $|P|, |Q| \ge K$, the function $f$ is nonconstant on $P \times Q$ (it takes both values there).
--
--   Lemma 4.1 turns this property into a lower bound on the number of edges of read-once programs computing $f$.
--
--   **Formalization Note** The predicate is written for every real $K$; each theorem that uses it assumes $K > 1$ where the paper does.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 4.1, p.11

import Mathlib
import Definitions.Def_CutwidthCircuitLB_rect

namespace CutwidthCircuitLB

/-- `f : {0,1}ⁿ → {0,1}` is a **`K`-rectangle disperser** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 4.1, p.11): for every
partition `[n] = U ⊔ V` and every rectangle `P × Q` with `|P|, |Q| ≥ K`, `f` is nonconstant on
`P × Q`.

**Formalization Note** The paper defines the notion for `K > 1`; the predicate is written for
every real `K`, and each statement using it assumes what the paper assumes about `K`. The
partition is `U` and its complement; "nonconstant" is: `f` takes both values on the rectangle. -/
def IsRectangleDisperser {n : ℕ} (K : ℝ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ (U : Finset (Fin n)) (P : Set ({j // j ∈ U} → Bool)) (Q : Set ({j // j ∈ Uᶜ} → Bool)),
    K ≤ (P.ncard : ℝ) → K ≤ (Q.ncard : ℝ) →
      (∃ x ∈ rect U P Q, f x = true) ∧ (∃ x ∈ rect U P Q, f x = false)

end CutwidthCircuitLB


