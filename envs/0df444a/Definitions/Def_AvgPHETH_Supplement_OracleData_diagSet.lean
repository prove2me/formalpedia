-- Prove2me | Definitions.Def_AvgPHETH_Supplement_OracleData_diagSet
-- name    : AvgPHETH_Supplement_OracleData_diagSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:48:12.638333+00:00
-- url     : https://prove2.me/theorems/ef5161df-b1ec-4d80-9958-95b354713a23
-- title:
--   The disagreeing pairs $(\alpha,x)$ of step 3(b)
-- statement:
--   When the reserved group $(k_s,n_s)$ is due, let $\mathcal C_s$ be the set of assignments to its variables consistent with the current partial assignment, and for $\alpha\in\mathcal C_s$ let $O_\alpha$ be the oracle obtained by extending the current construction with $\alpha$. With $\Psi=(M_s,k_s,\exists)$, this definition is the set of pairs $(\alpha,x)$, $\alpha\in\mathcal C_s$, $x\in\{0,1\}^{n_s}$, such that
--
--   $$\alpha(B^{k_s}_x)\ne\Psi^{O_\alpha}_{t_s(n_s),t_s(n_s)}(x).$$
--
--   Completing the group by such an $\alpha$ makes $M_s$, clocked to $t_s(n_s)$, err on $x$.
--
--   **Formalization Note** In $O_\alpha$, variables of other groups that are still unassigned get the empty string and unassigned $A$-queries are answered $0$; Proposition 8.3 shows that $M_s$ cannot reach either within $t_s(n_s)$ steps. An element $\alpha$ of $\mathcal C_s$ is stored as an assignment that is the empty string on every name outside the group, so the set of disagreeing pairs is a subset of the finite set $\mathcal C_s\times\{0,1\}^{n_s}$, as on the page.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, step 3(b) i–iii, p.41 (PDF 43)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_OracleData
import Definitions.Def_AvgPHETH_Supplement_OracleData_tPar
import Definitions.Def_AvgPHETH_Supplement_CVar_IsValid
import Definitions.Def_AvgPHETH_Supplement_CVar_valLen
import Definitions.Def_AvgPHETH_Supplement_oracleOf
import Definitions.Def_KarpLiptonOM_Alt
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_acceptsAt

namespace AvgPHETH.Supplement

open KarpLiptonOM AvgPHETH

/-- The disagreeing pairs of step 3(b) for the reserved group `(k_s, n_s)`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, step 3(b) i–iii, p.41 (PDF 43)): the pairs `(α, x)` of an assignment `α`
consistent with the current partial assignment `ρ` and an input `x ∈ {0,1}^{n_s}` such that
`α(B^{k_s}_x) ≠ Ψ^{O_α}_{t_s(n_s), t_s(n_s)}(x)`, where `Ψ = (M_s, k_s, ∃)` and `O_α` is "the oracle
obtained by extending the current construction with the assignment `α`".

**Formalization Note** `C_s` is, as on the page, the finite set of the assignments to the variables of
the group `(k_s, n_s)` that are consistent with `ρ`: `α` gives every variable of the group a value of
its alphabet, agreeing with `ρ` where `ρ` is assigned, and is the empty string on every name outside
the group. So the set of disagreeing pairs is a subset of the finite set `C_s × {0,1}^{n_s}`, and the
selection rule of step 3(b)iii sees nothing but these pairs. `O_α` takes the variables of the group
from `α`, the other variables from `ρ`, and the `A`-answers from the current table `tab`. Variables of
other groups that are still unassigned get the empty string and `A`-queries not yet assigned are
answered `0`; Proposition 8.3 (p.42, PDF 44–45) shows that `M_s` cannot reach either within
`t_s(n_s)` steps, so these defaults are never read.
`Ψ^{O}_{t,t}(x) = 1` iff `∃w₁ ∀w₂ ⋯ Q_{k_s} w_{k_s}`, all in `{0,1}^t`, such that `M_s^O(x, w₁, …)` accepts
within `t` steps (Definition 4.3). -/
def OracleData.diagSet (D : OracleData) (s : ℕ) (ρ : CVar → Option (List Bool))
    (tab : ℕ → ℕ → List Bool → ℕ → Option Bool) : Set ((CVar → List Bool) × List Bool) :=
  {p | (∀ v : CVar,
        (v.IsValid D.eps ∧ v.k = (D.enum s).1 ∧ v.x.length = D.ns s →
          (∀ b, ρ v = some b → p.1 v = b) ∧ (p.1 v).length = v.valLen D.eps) ∧
        (¬ (v.IsValid D.eps ∧ v.k = (D.enum s).1 ∧ v.x.length = D.ns s) → p.1 v = [])) ∧
      p.2.length = D.ns s ∧
      ¬ (p.1 ⟨(D.enum s).1, p.2, true, []⟩ = [true] ↔
        Alt (D.tPar s (D.ns s)) (D.enum s).1 true
          (fun ws => acceptsAt (D.mach (D.enum s).2.1)
            (oracleOf D.eps tab
              (fun v => if v.k = (D.enum s).1 ∧ v.x.length = D.ns s then p.1 v else (ρ v).getD []))
            (D.tPar s (D.ns s)) (tupleEnc (p.2 :: ws))))}

end AvgPHETH.Supplement


