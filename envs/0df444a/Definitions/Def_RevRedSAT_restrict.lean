-- Prove2me | Definitions.Def_RevRedSAT_restrict
-- name    : RevRedSAT_restrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:47:02.888529+00:00
-- url     : https://prove2.me/theorems/58a90279-c1a8-4294-bf10-8eb733b44388
-- title:
--   Substituting constants into a formula, and adaptive query strategies
-- statement:
--   For a CNF formula $\varphi$ over $n$ variables and a partial assignment $\rho$ (each variable fixed to a constant or left free), the **restricted formula** discards every clause containing a literal made true by $\rho$ and removes the literals on fixed variables from the remaining clauses (proof of Lemma 4.8, p.34: "substitute the chosen value, discard satisfied clauses, and remove false literals from the remaining clauses"). The number of satisfying **extensions** of $\rho$ counts the assignments that agree with $\rho$ and satisfy $\varphi$; it is the number of satisfying assignments of the restricted formula over its unfixed variables.
--
--   An **adaptive query strategy** consists of a rule giving, after the answers received so far, the next query (a partial assignment substituted into the formula), and a rule giving the final partial assignment after all answers. Running it for $t$ rounds against an oracle produces the list of $t$ answers.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 4.8 and its proof, p.34

import Mathlib
import Definitions.Def_MainResults
import Definitions.Def_RevRedSAT_encCNF

set_option autoImplicit false

namespace RevRedSAT

/-- **Substituting constants for some variables of a formula.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 4.8, p.34 and its
proof: "Every query is obtained by substituting constants for some variables of F"; "substitute the
chosen value, discard satisfied clauses, and remove false literals from the remaining clauses".

`ρ i = some b` fixes variable `i` to `b`; `ρ i = none` leaves it free. Clauses containing a literal
made true are discarded; literals on fixed variables are removed from the remaining clauses. -/
def restrict {n : ℕ} (φ : MainResults.CNF n) (ρ : Fin n → Option Bool) : MainResults.CNF n :=
  (φ.filter fun C => !(C.any fun l => decide (ρ l.1 = some l.2))).map
    fun C => C.filter fun l => decide (ρ l.1 = none)

/-- The number of assignments extending the partial assignment `ρ` that satisfy `φ`; this is the
number of satisfying assignments of `restrict φ ρ` over its unfixed variables (proof of Lemma 4.8,
p.34: "retain every unfixed variable in the list of counted variables"). -/
noncomputable def numExt {n : ℕ} (φ : MainResults.CNF n) (ρ : Fin n → Option Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun a : Fin n → Bool =>
    (∀ i b, ρ i = some b → a i = b) ∧ SatBy a φ).card

/-- **An adaptive query strategy.** After the answers `h` received so far, the next query is the
formula restricted by `query h`; after the last answer, `final h` is the chosen partial assignment. -/
structure QueryStrategy (n : ℕ) where
  /-- the partial assignment substituted into the formula for the next query -/
  query : List Bool → (Fin n → Option Bool)
  /-- the partial assignment chosen after all answers -/
  final : List Bool → (Fin n → Option Bool)

/-- The answers received in the first `t` rounds when every query `ρ` is answered by `oracle ρ`. -/
def runAnswers {n : ℕ} (σ : QueryStrategy n) (oracle : (Fin n → Option Bool) → Bool) :
    ℕ → List Bool
  | 0 => []
  | t + 1 => runAnswers σ oracle t ++ [oracle (σ.query (runAnswers σ oracle t))]

end RevRedSAT


