-- Prove2me | Definitions.Def_Random2SATWindow_CriticalLaw_PureLiteral
-- name    : Random2SATWindow_CriticalLaw_PureLiteral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:40:52.097233+00:00
-- url     : https://prove2.me/theorems/1659729a-50f7-4170-8a30-5ad1f347f726
-- title:
--   The pure literal core $F_C$, its counts $b_C,m_C$, the core excess $X(F)$ and the reduced-kernel clause count $m_K$
-- statement:
--   §5.1.9 (printed pp. 49–51).
--
--   * `IsPolarClosed G`: every literal occurring in $G$ has its complement occurring in $G$ (every occurring variable appears in both polarities).
--   * The pure literal core $F_C$ (`pureCore F`) is the unique largest subformula of $F$ with this property: the union of all such subformulas. The paper proves it is what the pure literal algorithm leaves, in any deletion order.
--   * `occVars G`, the variables occurring in $G$; `occDegree G i`, the number of occurrences of variable $i$ (a legal clause has at most one literal per variable).
--   * $b_C$ = `coreVars F`, $m_C$ = `coreClauses F`, and (128) $X(F)=m_C-b_C$ (`coreExcess F`, in $\mathbb Z$).
--   * $m_K$ (`kernelClauses F`), the number of clauses of the reduced kernel. Suppressing a core variable of type $(1,1)$ (degree $2$ in the core) by resolution removes that variable and one net clause, and leaves every other occurrence degree unchanged (clauses keep both literal positions, with multiplicity). Components made only of such variables are cycles of zero excess and are discarded. So the kernel consists of the core variables of degree $\ge3$, and $m_K=m_C-\#\{\text{core variables of degree }2\}$; then $X=m_K-b_K\le m_K$, as on p. 51.
--
--   **Formalization Note.** $m_K$ is given by this closed form rather than by simulating the suppression on a multigraph. The paper's counting argument (each suppression removes one variable and one clause; discarded components have as many clauses as variables) determines it uniquely, and it reproduces the paper's identity $2m_K=M(1,2)+M(2,1)-M(2,2)$ (total occurrences of degree-$\ge3$ core variables).
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), §5.1.9, (127)–(128), printed pp. 49–51 (PDF 51–53)

import Mathlib
import Definitions.Def_Random2SATWindow_CriticalLaw_Formulas

set_option autoImplicit false

open scoped BigOperators

namespace Random2SATWindow.CriticalLaw

/-! # The pure literal core, its excess and the reduced kernel

Ravelomanana, *Inside the Critical Window of Random 2-SAT*, STOC 2027 submission (manuscript
sha256 eef2fa67…), §5.1.9, (127)–(128), printed pp. 49–50 (PDF 51–52) and printed p. 51
(PDF 53). -/

/-- A subformula in which every occurring variable appears in both polarities: every literal
occurring in a clause of `G` has its complement occurring in some clause of `G`. -/
def IsPolarClosed {n : ℕ} (G : Formula n) : Prop :=
  ∀ c ∈ G, ∀ u ∈ c.val, ∃ c' ∈ G, u.compl ∈ c'.val

open Classical in
/-- The pure literal core `F_C`: the unique largest subformula of `F` in which every occurring
variable appears in both polarities (the union of all such subformulas; equivalently what the
pure literal algorithm leaves, in any deletion order). -/
noncomputable def pureCore {n : ℕ} (F : Formula n) : Formula n :=
  (F.powerset.filter IsPolarClosed).sup id

open Classical in
/-- The variables occurring in a formula. -/
noncomputable def occVars {n : ℕ} (G : Formula n) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ c ∈ G, ∃ u ∈ c.val, u.1 = i

open Classical in
/-- The occurrence degree of the variable `i` in `G` (number of clauses containing a literal on
`i`; a legal clause has at most one literal on each variable). -/
noncomputable def occDegree {n : ℕ} (G : Formula n) (i : Fin n) : ℕ :=
  (G.filter fun c => ∃ u ∈ c.val, u.1 = i).card

/-- `b_C`, the number of variables of the pure literal core. -/
noncomputable def coreVars {n : ℕ} (F : Formula n) : ℕ := (occVars (pureCore F)).card

/-- `m_C`, the number of clauses of the pure literal core. -/
noncomputable def coreClauses {n : ℕ} (F : Formula n) : ℕ := (pureCore F).card

/-- The core excess (128): `X(F) = m_C - b_C`. -/
noncomputable def coreExcess {n : ℕ} (F : Formula n) : ℤ :=
  (coreClauses F : ℤ) - (coreVars F : ℤ)

open Classical in
/-- `m_K`, the number of clauses of the reduced kernel (printed pp. 50–51): suppressing a core
variable of type `(1, 1)` (one positive and one negative occurrence, i.e. degree `2` in the
core) by resolution removes that variable and one net clause and leaves every other degree
unchanged, and components made only of such variables are cycles of zero excess that are
discarded; so the kernel has the core variables of degree `≥ 3` and
`m_K = m_C - #{core variables of degree 2}` clauses, counted with multiplicity. -/
noncomputable def kernelClauses {n : ℕ} (F : Formula n) : ℕ :=
  coreClauses F - ((occVars (pureCore F)).filter fun i => occDegree (pureCore F) i = 2).card

end Random2SATWindow.CriticalLaw


