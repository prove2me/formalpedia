-- Prove2me | Definitions.Def_AvgPHETH_Supplement_aAnswer
-- name    : AvgPHETH_Supplement_aAnswer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:43:36.787058+00:00
-- url     : https://prove2.me/theorems/9c4bdc9a-a9b8-4da8-b5c1-fcff67af513a
-- title:
--   The answer $A(q)\in\{1,0,\bot\}$ to an $A$-query
-- statement:
--   Let $q=(\langle M,d\rangle,u,1^{T^{16}})$ be a valid query, $\Phi=(M,d,\exists)$, and let $f_q$ be the function in the unset construction variables that outputs $\Phi^O_{T,|u|}(u)$, i.e. whether
--
--   $$\exists w_1\in\{0,1\}^{|u|}\ \forall w_2\in\{0,1\}^{|u|}\cdots Q_dw_d\in\{0,1\}^{|u|}:\ M^O(u,w_1,\dots,w_d)\text{ accepts within }T\text{ steps}.$$
--
--   Then $A(q)=1$ if $f_q\equiv1$, $A(q)=0$ if $f_q\equiv0$, and $A(q)=\bot$ otherwise. So $A$ answers only when the answer no longer depends on the part of $V$ that is still undetermined.
--
--   **Formalization Note** $f_q$ is evaluated at every total assignment extending the current partial assignment, with the $A$-answers assigned so far; $A$-queries not yet assigned are answered $0$ there, and Proposition 8.3 shows that $M$ cannot reach them within $T$ steps.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, steps 2(a)–(b), p.41 (PDF 43); Definition 4.3, p.15 (PDF 17)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_Completions
import Definitions.Def_AvgPHETH_Supplement_oracleOf
import Definitions.Def_KarpLiptonOM_OracleTM
import Definitions.Def_KarpLiptonOM_Alt
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_acceptsAt

namespace AvgPHETH.Supplement

open KarpLiptonOM AvgPHETH

/-- The answer `A(q)` given to a valid query `q = (⟨M, d⟩, u, 1^{T^16})`, `M = mach i`, in step 2 of a
stage (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, steps 2(a)–(b), p.41 (PDF 43)): "Let `Φ = (M, d, ∃)`. Let `f_q` be
the function in the unset construction variables that outputs `Φ^O_{T,|u|}(u)`. Set `A(q)` to `1` if
`f_q ≡ 1`, `0` if `f_q ≡ 0`, and `⊥` otherwise." Here `Φ^O_{T,|u|}(u) = 1` iff
`∃w₁ ∈ {0,1}^{|u|} ∀w₂ ∈ {0,1}^{|u|} ⋯ Q_d w_d ∈ {0,1}^{|u|} : M^O(u, w₁, …, w_d)` accepts within `T` steps
(Definition 4.3, p.15 (PDF 17)).

**Formalization Note** `ρ` is the partial assignment `ρ_i` after the restriction round, `tab` holds the
`A`-answers assigned so far (the queries with a smaller time parameter), and `f_q` is evaluated at every
total assignment `τ` extending `ρ` with the oracle `oracleOf ε tab τ`, in which `A`-queries not yet
assigned are answered `0`. Proposition 8.3 (p.42, PDF 44) shows that `M` cannot reach such a query
within `T` steps, so the default is never read. The answers are `some true` (`1`), `some false` (`0`)
and `none` (`⊥`). -/
noncomputable def aAnswer (ε : ℕ → ℝ) (mach : ℕ → OracleTM)
    (tab : ℕ → ℕ → List Bool → ℕ → Option Bool) (ρ : CVar → Option (List Bool))
    (i d : ℕ) (u : List Bool) (T : ℕ) : Option Bool := by
  classical
  exact
    if ∀ τ ∈ Completions ε ρ,
        Alt u.length d true (fun ws => acceptsAt (mach i) (oracleOf ε tab τ) T (tupleEnc (u :: ws))) then
      some true
    else if ∀ τ ∈ Completions ε ρ,
        ¬ Alt u.length d true
          (fun ws => acceptsAt (mach i) (oracleOf ε tab τ) T (tupleEnc (u :: ws))) then
      some false
    else none

end AvgPHETH.Supplement


