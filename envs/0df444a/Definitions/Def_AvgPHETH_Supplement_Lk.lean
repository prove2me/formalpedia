-- Prove2me | Definitions.Def_AvgPHETH_Supplement_Lk
-- name    : AvgPHETH_Supplement_Lk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:59:13.061814+00:00
-- url     : https://prove2.me/theorems/6bec35ff-d8ee-4812-8c8d-a048eb76a789
-- title:
--   The language $L_k^O$
-- statement:
--   For the oracle $O=A+V$ and $k\ge1$,
--
--   $$x\in L_k^O\iff(k,|x|)\text{ is active and }\forall y_1\in Y_1(|x|)\ \exists y_2\in Y_2(|x|)\cdots Q_ky_k\in Y_k(|x|):\ V_k(x,y_1,\dots,y_k)=1 .$$
--
--   $L_k^O\in\Pi_k^{p,O}$, and it is the language shown to be hard for $\Sigma_k$ machines. Since the quantified expression evaluates the selector tree $T^k_x$, $x\in L_k^O$ iff the root bit $B^k_x$ is $1$.
--
--   **Formalization Note** $V_k(x,y_1,\dots,y_k)$ is the induced leaf value $T^k_x(y_1,\dots,y_k)$ under the assignment that determines $V$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.39 (PDF 41)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_treeVal
import Definitions.Def_AvgPHETH_Supplement_IsActive
import Definitions.Def_AvgPHETH_Supplement_aPar
import Definitions.Def_AvgPHETH_AltLen

namespace AvgPHETH.Supplement

open AvgPHETH

/-- The language `L_k^O` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.39 (PDF 41)):
`x ∈ L_k^O ⟺ (k, |x|)` is active and
`∀y₁ ∈ Y₁(|x|) ∃y₂ ∈ Y₂(|x|) ⋯ Q_k y_k ∈ Y_k(|x|) : V_k(x, y₁, …, y_k) = 1`.

**Formalization Note** `β` is the assignment to the construction variables that determines `V`, and
`V_k(x, y₁, …, y_k) = T^k_x(y₁, …, y_k)` is `treeVal β k x [y₁, …, y_k]`; `Y_j(n) = {0,1}^{a_j(n)}`. The
quantifiers are the published `AvgPHETH.AltLen` with first quantifier `∀`. -/
def Lk (ε : ℕ → ℝ) (β : CVar → List Bool) (k : ℕ) : Set (List Bool) :=
  {x | IsActive ε k x.length ∧
      AltLen ((List.range k).map (fun j => aPar ε (j + 1) x.length)) false
        (fun ys => treeVal β k x ys = true)}

end AvgPHETH.Supplement


