-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_TrimmedBall
-- name    : KSATSingleFlip_Connect_TrimmedBall
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T08:18:02.860559+00:00
-- url     : https://prove2.me/theorems/36431dd4-6bb3-4379-9540-e52c04444c22
-- title:
--   Marked locally tree-structured factor balls
-- statement:
--   A trimmed radius-$2r$ factor ball at a variable is retained if it is a tree and every variable in the ball has full-formula degree at most $D$; otherwise it is empty. The stored data includes the variable identities, original clause-occurrence labels, and the ordered signed clauses. When one clause is inserted by appending it to the formula list, the existing occurrence labels stay fixed.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.7, printed pp. 12–13 (PDF pp. 14–15), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

noncomputable section
open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Original list-position identifiers of clause occurrences in a factor ball. -/
def ballClauseLabels {n : ℕ} (Φ : GFormula (Fin n)) (v : Fin n) (r : ℕ) : Finset ℕ :=
  (ballIdx Φ v r).image Fin.val

/-- The marked locally tree-structured ball; otherwise `none`. Its data
records variable identities, original clause occurrence labels, and signed
clauses in order. Inserting at the end preserves every old clause label. -/
def trimmedBall {n : ℕ} (Φ : GFormula (Fin n)) (v : Fin n) (r D : ℕ) :
    Option (Finset (Fin n) × Finset ℕ × GFormula (Fin n)) :=
  if LocallyTree Φ v r D then some (ballVars Φ v r, ballClauseLabels Φ v r, ballF Φ v r) else none

end KSATSingleFlip.Connect


