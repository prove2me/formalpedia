-- Prove2me | Definitions.Def_AvgPHETH_Supplement_Formula_IsCritical
-- name    : AvgPHETH_Supplement_Formula_IsCritical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:30:10.682544+00:00
-- url     : https://prove2.me/theorems/bd9dfc0c-c1c1-42e5-8882-0c6ca6e3dee1
-- title:
--   Critical assignments of a formula
-- statement:
--   The **neutral value** of an AND gate is $1$ and that of an OR gate is $0$. An assignment $\alpha$ to the variables of a formula $F$ is **critical** for $F$ if, under $\alpha$, every gate of $F$ has at most one child that does not evaluate to the gate's neutral value: at most one child of each AND gate evaluates to $0$, and at most one child of each OR gate evaluates to $1$.
--
--   Theorem 7.1 is a lower bound against circuits that only have to agree with the hard formula on its critical assignments.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3 'Critical assignments', p.16 (PDF 18)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_Formula
import Definitions.Def_AvgPHETH_Supplement_Formula_eval

namespace AvgPHETH.Supplement

/-- An assignment `α` is **critical** for the formula `F` if every gate of `F` has at most one child
that does not evaluate to the gate's neutral value (`1` for AND, `0` for OR)
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)).

**Formalization Note** The neutral value of `gate a m ch` is `a` itself (`true` for AND). -/
def Formula.IsCritical {V : Type} (α : V → Bool) : Formula V → Prop
  | .leaf _ => True
  | .gate a _ ch => {i | (ch i).eval α ≠ a}.Subsingleton ∧ ∀ i, (ch i).IsCritical α

end AvgPHETH.Supplement


