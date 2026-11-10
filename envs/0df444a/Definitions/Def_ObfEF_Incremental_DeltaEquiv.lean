-- Prove2me | Definitions.Def_ObfEF_Incremental_DeltaEquiv
-- name    : ObfEF_Incremental_DeltaEquiv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:55:56.356194+00:00
-- url     : https://prove2.me/theorems/2171824b-2be2-4b9b-a3ce-6ad2d6bc99ea
-- title:
--   δ-equivalence of two circuits via a subcircuit (Definition 2.3)
-- statement:
--   Let two circuits $C^1,C^2$ have the same topology in the gate-list view, with gate functions $f^1_j$ and $f^2_j$, and let $S$ be a subcircuit. Following Definition 2.3 (after Jain–Jin), $C^1$ and $C^2$ are **δ-equivalent via $S$** if
--
--   1. their topologies are identical,
--   2. the corresponding gates outside $S$ are identical: $f^1_j=f^2_j$ for every $j\notin S$, and
--   3. every $\xi\in\{0,1\}^{\mathrm{inp}(S)}$ satisfies
--   $$C^1_S(\xi)=C^2_S(\xi),$$
--   that is, the two versions of $S$ produce the same values on every wire of $\mathrm{out}(S)$.
--
--   This is the local equivalence condition used in gate-by-gate security proofs: a replacement of $S$ that preserves the output boundary for every boundary input preserves the surrounding computation. (The "δ" is historical and unrelated to an advantage.)
--
--   **Formalization Note.** Condition 1 is built in: both circuits are gate-function maps `f₁ f₂` over one `Wiring`.
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), pp. 25-26, Definition 2.3

import Mathlib
import Definitions.Def_ObfEF_Incremental_GateList

/-!
# δ-equivalence via a subcircuit (Definition 2.3)

Abram, Datta, Dutta, Roy, *Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to
Falsifiable Assumptions*, STOC 2027 submission (manuscript sha256 f9518747…), pp. 25–26,
Definition 2.3 (after [JJ22]).

Two circuits with identical topology are given as two gate-function maps `f₁ f₂` over one
`Wiring`, so the first condition of the definition holds by construction.
-/

namespace ObfEF.Incremental

/-- `C¹` and `C²` (gate functions `f₁`, `f₂` over the wiring `W`) are δ-equivalent via the
subcircuit `S`: the gates outside `S` are identical, and every assignment `ξ` to `inp(S)` gives
the same values on `out(S)`. -/
def DeltaEquiv (W : Wiring) (f₁ f₂ : Fin W.n → Bool → Bool → Bool) (S : Finset (Fin W.n)) :
    Prop :=
  (∀ j : Fin W.n, j ∉ S → f₁ j = f₂ j) ∧
  ∀ ξ : ℕ → Bool, ∀ o : ℕ, W.IsOutBoundary S o → W.subVal f₁ S ξ o = W.subVal f₂ S ξ o

end ObfEF.Incremental


