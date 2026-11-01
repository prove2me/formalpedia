-- Prove2me | Definitions.Def_BudgetCoreExchange_CoreWelfare
-- name    : BudgetCoreExchange_CoreWelfare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:08.126596+00:00
-- url     : https://prove2.me/theorems/3a2f77fc-90f4-4bc5-9a89-b84f7d7cdb1d
-- title:
--   The decision problem CoreWelfare: does some core outcome have welfare at least $D$?
-- statement:
--   **CoreWelfare** is the language of codes of pairs $(E,D)$ where $E$ is a valid combinatorial exchange with budget-constrained buyers whose valuations (in the "XOR of additive groups" language), budgets and endowments are rational data, $D$ is a rational threshold, and
--   $$
--   \exists\ \text{a core outcome } o \text{ of } E \text{ with } \sum_{i}v_i(S_i)-\sum_j v_j(Z_j)\ \ge\ D .
--   $$
--   Buyers, sellers and items are numbered $0,\dots,n_B-1$, $0,\dots,n_S-1$, $0,\dots,n_K-1$. The code lists $n_B,n_S,n_K$, then for each seller its endowment and its ask, for each buyer its budget and its bid, and finally $D$; natural numbers are written in binary, rationals as sign, numerator and denominator in lowest terms, sets of items in increasing order.
--
--   This is the decision form of "computing a welfare-maximizing core outcome" used in Appendix A of the paper.
--
--   **Formalization Note** Payments in outcomes are real numbers; only the instance data are rational. The code is self-delimiting.
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Theorem 2, p.9; Appendix A.1, p.27 ('the problem of finding a core outcome of welfare D'); A.4, p.31

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_BudgetCoreExchange_Exchange
import Definitions.Def_BudgetCoreExchange_InCore

namespace BudgetCoreExchange

/-- The alphabet in which exchanges are written: binary digits `zero`/`one`, `endNum` (ends a
natural number), `plus`/`minus` (sign of an integer), `item` (starts a list element) and
`endList` (ends a list). -/
inductive ExSym where
  | zero
  | one
  | endNum
  | plus
  | minus
  | item
  | endList
  deriving DecidableEq

instance : Fintype ExSym where
  elems := {ExSym.zero, ExSym.one, ExSym.endNum, ExSym.plus, ExSym.minus, ExSym.item, ExSym.endList}
  complete := by intro x; cases x <;> simp

/-- Code of a natural number: its binary digits, least significant first, then `endNum`. -/
def encNat (k : ℕ) : List ExSym :=
  (Nat.digits 2 k).map (fun d => if d = 0 then ExSym.zero else ExSym.one) ++ [ExSym.endNum]

/-- Code of an integer: its sign, then its absolute value. -/
def encInt (z : ℤ) : List ExSym :=
  (if 0 ≤ z then ExSym.plus else ExSym.minus) :: encNat z.natAbs

/-- Code of a rational number in lowest terms: numerator, then denominator, in binary. -/
def encRat (r : ℚ) : List ExSym :=
  encInt r.num ++ encNat r.den

/-- Code of a list: every element's code preceded by `item`, then `endList`. -/
def encList {α : Type} (f : α → List ExSym) (xs : List α) : List ExSym :=
  xs.flatMap (fun a => ExSym.item :: f a) ++ [ExSym.endList]

/-- Code of a set of items `Fin nK`: the list of its elements in increasing order. -/
def encFinset {nK : ℕ} (s : Finset (Fin nK)) : List ExSym :=
  encList (fun k => encNat k.val) (s.sort (· ≤ ·))

/-- Code of a rational bid: the list of its groups, each its required bundle followed by the list
of its weighted parts. -/
def encBid {nK : ℕ} (b : Bid (Fin nK) ℚ) : List ExSym :=
  encList (fun g => encFinset g.req ++ encList (fun p => encFinset p.1 ++ encRat p.2) g.parts) b

/-- Code of a rational exchange instance with `nB` buyers, `nS` sellers, `nK` items, together with
the welfare threshold `D`: the numbers `nB, nS, nK`; per seller its endowment and its ask; per buyer
its budget and its bid; then `D`. Numbers are written in binary. -/
def encodeInstance {nB nS nK : ℕ} (E : Exchange (Fin nB) (Fin nS) (Fin nK) ℚ) (D : ℚ) :
    List ExSym :=
  encNat nB ++ encNat nS ++ encNat nK ++
    encList (fun j => encFinset (E.endow j) ++ encBid (E.ask j)) (List.finRange nS) ++
    encList (fun i => encRat (E.budget i) ++ encBid (E.bid i)) (List.finRange nB) ++
    encRat D

/-- The decision version of computing a welfare-maximizing core outcome (Bichler–Waldherr,
arXiv:1807.08253v1, Theorem 2, p.9, in the form of Appendix A, A.1 p.27 and A.4 p.31): the codes
of the pairs `(E, D)` of a valid combinatorial exchange with budget-constrained buyers `E` with
rational data and a rational threshold `D` such that **some core outcome of `E` has welfare at
least `D`**.

**Formalization Note.** Instance data (valuations in the "XOR of additive groups" language,
budgets, `D`) are rational and written in binary; payments in outcomes are real. Buyers, sellers and
items are `Fin nB`, `Fin nS`, `Fin nK`. -/
def CoreWelfare : CookPvsNP.Lang ExSym :=
  { s | ∃ (nB nS nK : ℕ) (E : Exchange (Fin nB) (Fin nS) (Fin nK) ℚ) (D : ℚ),
      (E.map (fun r : ℚ => (r : ℝ))).Valid ∧
      (∃ o, InCore (E.map (fun r : ℚ => (r : ℝ))) o ∧
        (D : ℝ) ≤ welfare (E.map (fun r : ℚ => (r : ℝ))) o) ∧
      s = encodeInstance E D }

end BudgetCoreExchange


