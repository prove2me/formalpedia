-- Prove2me | Definitions.Def_Freiman_continuants
-- name    : Freiman_continuants
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:43:32.286725+00:00
-- url     : https://prove2.me/theorems/5344f376-94d2-4306-b38a-b3bcb35e4e16
-- title:
--   Continuants with the report’s digit-count convention
-- statement:
--   The four entries are the matrix product in (found:continuants), represented as natural numbers. The empty word has (previous numerator,current numerator,previous denominator,current denominator)=(1,0,0,1). Sequence indices count the digits already used; no existing definition is changed.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §§1.1–1.3

import Definitions.Def_Freiman_prefixEval
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Freiman

def wordContinuantData (w : List ℕ+) : (ℕ × ℕ) × (ℕ × ℕ) :=
  w.foldl (fun d a => ((d.1.2, (a : ℕ) * d.1.2 + d.1.1),
    (d.2.2, (a : ℕ) * d.2.2 + d.2.1))) ((1, 0), (0, 1))
def wordContinuantPrevP (w : List ℕ+) : ℕ := (wordContinuantData w).1.1
def wordContinuantP (w : List ℕ+) : ℕ := (wordContinuantData w).1.2
def wordContinuantPrevQ (w : List ℕ+) : ℕ := (wordContinuantData w).2.1
def wordContinuantQ (w : List ℕ+) : ℕ := (wordContinuantData w).2.2
def continuantP (b : ℕ → ℕ+) (n : ℕ) : ℕ := wordContinuantP ((List.range n).map b)
def continuantQ (b : ℕ → ℕ+) (n : ℕ) : ℕ := wordContinuantQ ((List.range n).map b)
def continuantPrevP (b : ℕ → ℕ+) (n : ℕ) : ℕ := wordContinuantPrevP ((List.range n).map b)
def continuantPrevQ (b : ℕ → ℕ+) (n : ℕ) : ℕ := wordContinuantPrevQ ((List.range n).map b)

end Freiman


