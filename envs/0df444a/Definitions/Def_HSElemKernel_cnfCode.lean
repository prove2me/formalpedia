-- Prove2me | Definitions.Def_HSElemKernel_cnfCode
-- name    : HSElemKernel_cnfCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:02.129956+00:00
-- url     : https://prove2.me/theorems/bb2623ce-55f0-4b72-9dab-9394aa1440f9
-- title:
--   Code of a CNF formula
-- statement:
--   The **code** of a CNF formula $\Psi$ with variables $x_0, \dots, x_{N-1}$ and clauses $C_1, \dots, C_M$ (the published type `MainResults.CNF N`) is the list
--   $$[\,N,\ M\,] \mathbin{+\!\!+} \mathrm{block}(C_1) \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \mathrm{block}(C_M),$$
--   where $\mathrm{block}(C)$ is the width $|C|$ followed by the codes of the literals of $C$, and the literal $x_v$ has code $2v + 1$, the literal $\neg x_v$ code $2v$.
--
--   A literal of a clause is satisfied by an assignment $a$ when $a(v) = b$ for the literal $(v, b)$.
--
--   It is the input format of the variable-pair reduction (Lemma 2.4) and the output format of the cardinality encoding (Lemma 3.2).
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 2.3, p.5 ("the encoding length of Ψ") and Section 3.3, p.7

import Mathlib
import Definitions.Def_MainResults

namespace HSElemKernel

/-- The code of a CNF formula `Ψ` with `N` variables and `M` clauses (Sheng–Xiao,
arXiv:2609.06512, held version sha256 aca9c70e…, Section 2.3, p.5, "the encoding length of Ψ"):
`[N, M] ++ block(C₁) ++ ⋯ ++ block(C_M)`, where `block(C) = |C| :: (codes of the literals of C)`
and the literal `(v, b)` has code `2v + b` (`v` for `b = 1`, `¬v` for `b = 0`).

**Formalization Note** The formula is the published `MainResults.CNF N` (variables `Fin N`,
clauses and literals listed in order); its strict inverse is `decodeCNF`. -/
def cnfCode {N : ℕ} (Ψ : MainResults.CNF N) : List ℕ :=
  [N, Ψ.length] ++ Ψ.flatMap (fun C => C.length :: C.map (fun l => 2 * l.1.val + l.2.toNat))

end HSElemKernel


