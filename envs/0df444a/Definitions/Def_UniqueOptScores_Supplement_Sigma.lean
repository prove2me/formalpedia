-- Prove2me | Definitions.Def_UniqueOptScores_Supplement_Sigma
-- name    : UniqueOptScores_Supplement_Sigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:51:25.43586+00:00
-- url     : https://prove2.me/theorems/a4559656-4457-4442-afe3-8a3630e5dbb3
-- title:
--   The level $\Sigma^{\mathrm P}_k$ of the polynomial hierarchy
-- statement:
--   For $k\ge 0$, a language $L\subseteq\{0,1\}^*$ belongs to $\Sigma^{\mathrm P}_k$ if there are a deterministic polynomial-time machine $V$ and a polynomial $p$ such that for every input $x$
--   $$x\in L\iff \exists y_1\,\forall y_2\,\exists y_3\cdots Q_k y_k:\; V \text{ accepts } \langle x,\,y_1y_2\cdots y_k\rangle,$$
--   where every $y_i$ ranges over $\{0,1\}^{p(|x|)}$ and the $k$ blocks alternate, beginning with an existential block. For $k=0$ there are no quantifiers and $\Sigma^{\mathrm P}_0=\mathrm P$; for $k=1$ this is NP in verifier form.
--
--   These are the levels whose union is the polynomial hierarchy $\mathrm{PH}$.
--
--   **Formalization Note** The quantifier prefix is the published alternating-quantifier helper `KarpLiptonOM.Alt` (blocks of exact length $p(|x|)$, the usual padding equivalence with "at most $p(|x|)$"); the blocks are given to $V$ concatenated, which determines each block since all have the same length. Machines are the base mission's oracle machines with a polynomial clock valid for every oracle, run with the empty oracle (the unrelativized setting); acceptance is output $1$; $\langle\cdot,\cdot\rangle$ is the base pairing.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), §3.2, p.14 (PDF p.15), "The polynomial hierarchy"

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_UniqueOptScores_IsClocked
import Definitions.Def_UniqueOptScores_output
import Definitions.Def_UniqueOptScores_pair
import Definitions.Def_KarpLiptonOM_Alt

namespace UniqueOptScores

namespace Supplement

/-- **The level Σ^P_k of the polynomial hierarchy** (unrelativized).
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.14 (PDF p.15): "For k ≥ 1, the classes Σ^P_k and Π^P_k are defined by k alternating
blocks of polynomially bounded quantifiers over a polynomial-time predicate, beginning with an
existential and a universal block, respectively. With Σ^P_0 = Π^P_0 = P, …"; p.15: "We omit
oracle superscripts in the unrelativized setting."

`L ∈ Sigma k` if there are a clocked deterministic machine `V` (the polynomial-time predicate) and
a polynomial `p` such that `x ∈ L` exactly when
`∃ y₁ ∀ y₂ ∃ y₃ ⋯ (k blocks, |yᵢ| = p(|x|))`, `V` accepts `⟨x, y₁ ++ ⋯ ++ y_k⟩`.

**Formalization Note.** The quantifier prefix is the published `KarpLiptonOM.Alt` (blocks of exact
length `p(|x|)`, the usual padding equivalence); the blocks are passed to `V` concatenated,
`y₁ ++ ⋯ ++ y_k`, which determines every block because all have the same length.
Machines are the base mission's `HMBinPacking.OracleMachine` with a clock valid for every oracle (`IsClocked`), run with the empty oracle `∅` (unrelativized); acceptance is
output `[true]`; pairing is the base `pair`. For `k = 0` the condition is
`output V ∅ (pair x []) = [true]`, i.e. `Sigma 0 = P`, as on the page; `Sigma 1` is the base
mission's `NP ∅` in the same verifier form. -/
def Sigma (k : ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (V : HMBinPacking.OracleMachine) (t p : Polynomial ℕ), IsClocked V t ∧
    ∀ x : List Bool, x ∈ L ↔
      KarpLiptonOM.Alt (p.eval x.length) k true
        (fun ys => output V ∅ (pair x ys.flatten) = [true])}

end Supplement

end UniqueOptScores


