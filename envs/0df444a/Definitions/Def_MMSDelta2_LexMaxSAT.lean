-- Prove2me | Definitions.Def_MMSDelta2_LexMaxSAT
-- name    : MMSDelta2_LexMaxSAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:23.876726+00:00
-- url     : https://prove2.me/theorems/0df735a4-dc33-40b1-988a-de49e721ed7c
-- title:
--   LexMaxSAT, LexMaxSAT-Promise and LexMax3SAT-Promise
-- statement:
--   An instance of **LexMaxSAT** is a CNF formula $\varphi(x_1,\dots,x_n)$, $n\ge1$, with the variables ordered $x_1\succ x_2\succ\cdots\succ x_n$. Truth assignments are compared lexicographically in this order, with $1>0$. The question is whether $x_n=1$ in the lexicographically largest satisfying assignment of $\varphi$; an unsatisfiable formula is a no-instance.
--
--   1. $\mathrm{LexMaxSAT}$ is the language of codes of yes-instances.
--   2. **LexMaxSAT-Promise** is the promise problem with the same question under the promise that $\varphi$ is satisfiable: its yes-instances are the codes of satisfiable formulas whose lexicographically largest satisfying assignment has $x_n=1$, and its no-instances are the codes of the other satisfiable formulas.
--   3. **LexMax3SAT-Promise** is defined in the same way for 3-CNF formulas, i.e. formulas in which every clause has at most three literals.
--
--   These are the first three problems of the reduction chain LexMaxSAT → LexMaxSAT-Promise → LexMax3SAT-Promise → LexMax4Partition-Promise.
--
--   **Formalization Note** A formula is the published `CookPvsNP.CNF` with variables $0,\dots,n-1$ (variable $k$ is $x_{k+1}$); assignments are `Fin n → Bool` compared as lists. The code is the code of $n$ followed by `CookPvsNP.encodeCNF` with two bits per symbol. "3-CNF" is read as "at most three literals per clause", the form the reduction of Lemma A.2 produces.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Appendix A.1, p.53 (PDF p.55); §4, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_MMSDelta2_Delta2P
import Definitions.Def_MMSDelta2_instCode

namespace MMSDelta2

/-!
# LexMaxSAT, LexMaxSAT-Promise and LexMax3SAT-Promise

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), Appendix A.1, p.53 (PDF p.55): "An instance
consists of a CNF formula `φ(x_1, …, x_n)`, with the variables ordered as `x_1 ≻ x_2 ≻ ⋯ ≻ x_n`. The
question is whether `x_n = 1` in the lexicographically largest satisfying assignment of `φ`. If `φ`
is unsatisfiable, the instance is treated as a no-instance." LexMaxSAT-Promise adds the promise
that `φ` is satisfiable; LexMax3SAT-Promise asks in addition that `φ` be a 3-CNF; §4, p.12.

**Formalization Note.**
* An instance is `n ≥ 1` and a published `CookPvsNP.CNF` all of whose variables are `< n`;
  variable index `k` is `x_{k+1}`, so index `0` is the most significant variable `x_1` and index
  `n − 1` is the last variable `x_n`.
* An assignment is `x : Fin n → Bool`; assignments are compared by the lexicographic order of the
  lists `x_1 … x_n` with `false < true` (`1 > 0`). The lexicographically largest satisfying
  assignment is unique when it exists.
* "3-CNF" is read as: every clause has at most three literals (the reduction of Lemma A.2 leaves
  "Clauses containing at most three literals … unchanged").
* Code: `natCode n`, then the published `CookPvsNP.encodeCNF φ` with its four symbols written as
  two bits each. A string that encodes no instance is not in `LexMaxSATLang` and is outside both
  promises.
-/

/-- An instance of LexMaxSAT: `n ≥ 1` variables and a CNF formula over the variables `0, …, n−1`. -/
structure SatInstance where
  /-- the number of variables -/
  n : ℕ
  /-- the formula -/
  phi : CookPvsNP.CNF
  hn : 1 ≤ n
  hvars : ∀ C ∈ phi, ∀ l ∈ C, l.2 < n

namespace SatInstance

/-- The assignment `x` satisfies the formula: every clause has a literal made true by `x`. -/
def Sat (I : SatInstance) (x : Fin I.n → Bool) : Prop :=
  ∀ C ∈ I.phi, ∃ l ∈ C, ∃ h : l.2 < I.n, x ⟨l.2, h⟩ = l.1

/-- `x` is the lexicographically largest satisfying assignment (`x_1` first, `true > false`). -/
def IsLexMax (I : SatInstance) (x : Fin I.n → Bool) : Prop :=
  I.Sat x ∧ ∀ y, I.Sat y → ¬ (List.ofFn x < List.ofFn y)

/-- The formula is satisfiable. -/
def Satisfiable (I : SatInstance) : Prop := ∃ x, I.Sat x

/-- The last variable `x_n` is `1` in the lexicographically largest satisfying assignment (false
when the formula is unsatisfiable). -/
def LastTrue (I : SatInstance) : Prop :=
  ∃ x, I.IsLexMax x ∧ (List.ofFn x).getLast? = some true

/-- Every clause has at most three literals. -/
def Is3CNF (I : SatInstance) : Prop := ∀ C ∈ I.phi, C.length ≤ 3

end SatInstance

/-- Two bits for each symbol of `CookPvsNP.encodeCNF`. -/
def satSymBits : CookPvsNP.SatSym → List Bool
  | .pos => [false, false]
  | .neg => [false, true]
  | .one => [true, false]
  | .endClause => [true, true]

/-- The binary code of a LexMaxSAT instance. -/
def cnfCode (I : SatInstance) : List Bool :=
  natCode I.n ++ (CookPvsNP.encodeCNF I.phi).flatMap satSymBits

/-- LexMaxSAT ([Kre88]; p.12, p.53): codes of instances whose lexicographically largest satisfying
assignment sets the last variable to `1`. -/
def LexMaxSATLang : Set (List Bool) :=
  {w | ∃ I : SatInstance, I.LastTrue ∧ w = cnfCode I}

/-- LexMaxSAT-Promise (p.53): the promise is that the formula is satisfiable. -/
def LexMaxSATPromise : KarpLiptonOM.PromiseProblem :=
  promiseOn {w | ∃ I : SatInstance, I.Satisfiable ∧ w = cnfCode I} LexMaxSATLang

/-- LexMax3SAT-Promise (p.53): as LexMaxSAT-Promise, for 3-CNF formulas. -/
def LexMax3SATPromise : KarpLiptonOM.PromiseProblem :=
  promiseOn {w | ∃ I : SatInstance, I.Satisfiable ∧ I.Is3CNF ∧ w = cnfCode I} LexMaxSATLang

end MMSDelta2


