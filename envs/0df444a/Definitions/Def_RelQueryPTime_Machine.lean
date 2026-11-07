-- Prove2me | Definitions.Def_RelQueryPTime_Machine
-- name    : RelQueryPTime_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:28.932781+00:00
-- url     : https://prove2.me/theorems/62aafbc3-c3e7-47ba-96d2-822923968161
-- title:
--   Tableau of a Turing-machine run: cell contents, absolute head position, symbol coding, one move $\langle a_{-1}a_0a_1\rangle \to a$
-- statement:
--   Let $M$ be a one-tape Turing machine in Cook's model, with tape symbols $\Gamma$ plus a blank, states $Q$, accepting state $q_{\mathrm{accept}}$ and rejecting state $q_{\mathrm{reject}}$, run on an input $w$.
--
--   1. A **cell content** is a pair (state or "no head", tape symbol or blank).
--   2. $\mathrm{headPos}(t) \in \mathbb Z$ is the absolute position of the head after $t$ steps (the input starts at cell $0$; each non-halting step moves the head by $\pm 1$).
--   3. $\mathrm{Cell}(t, j)$ is the content of cell $j \in \mathbb Z$ after $t$ steps of the run: the current state if the head is on cell $j$, and the symbol in cell $j$.
--   4. A symbol is coded by an $\ell$-tuple $\bar a$ of domain elements, $\ell = |\text{cell contents}|$: $\bar a$ stands for the bits $b_m = [a_m \neq 0]$ and codes the $i$-th cell content in a fixed enumeration, $i = \sum_m b_m 2^m$ (when $i$ is in range).
--   5. $\langle a_{-1}a_0a_1\rangle \to a$: the content $a$ of a cell after one move of $M$, computed from the contents $a_{-1}, a_0, a_1$ of the cell's left neighbour, the cell and its right neighbour. The scanned cell receives the symbol written by the transition function, the head arrives from the left on a right move and from the right on a left move, and a halting state stays and changes nothing.
--
--   These objects carry the machine simulation in the hard half of Theorem 1.
--
--   **Formalization Note** Cook's configurations store the tape relative to the head and extend it with blanks at the left end; the absolute position is recovered from the same run, so no second machine model is introduced. The tape is two-way infinite, so cells left of the input (negative numbers) are used.
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, proof of Theorem 1, p.149 (Cell(x1…xr,p1…pk,t1…tk,a); "<a-1a0a1>→a" means that the triple leads to the symbol a in one move of M) (PDF p.3)

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace RelQueryPTime

open CookPvsNP

/-- The contents of one cell of the tableau of a run of `M` (Immerman, STOC 1982, proof of
Theorem 1, p.149): the state of `M` if the head is on the cell (`none` otherwise) and the tape
symbol in the cell (`none` = blank). -/
abbrev CellSym {Γ : Type} (M : TM Γ) : Type := Option M.Q × Option Γ

/-- The number `ℓ = |CellSym M|` of domain variables used to code one cell symbol. -/
noncomputable def symWidth {Γ : Type} [Fintype Γ] (M : TM Γ) : ℕ := Fintype.card (CellSym M)

/-- Decoding of an `ℓ`-tuple of domain elements (`ℓ = symWidth M`) as a cell symbol: the tuple
`a` stands for the bits `b_m = [a_m ≠ 0]`, i.e. the number `i = Σ_m b_m 2^m`, and codes the
`i`-th cell symbol in a fixed enumeration of `CellSym M` when `i < |CellSym M|` (otherwise it codes
nothing).

**Formalization Note** The page lets one variable `a` range over the symbols; a symbol set larger
than the domain needs a tuple, and bits need two distinct elements (`n ≥ 2`). -/
noncomputable def decodeSym {Γ : Type} [Fintype Γ] (M : TM Γ) {n : ℕ}
    (a : Fin (symWidth M) → Fin n) : Option (CellSym M) :=
  let i := ∑ m : Fin (symWidth M), (if (a m : ℕ) = 0 then 0 else 2 ^ (m : ℕ))
  if h : i < Fintype.card (CellSym M) then some ((Fintype.equivFin (CellSym M)).symm ⟨i, h⟩)
  else none

/-- The absolute head position (in `ℤ`, starting at `0` on the first input symbol) after `t`
steps of `M` on input `w`. It moves by `±1` with each non-halting step of `TM.step`.

**Formalization Note** `CookPvsNP.Cfg` stores the tape relative to the head; this function
recovers the absolute position from the same run `TM.run`. -/
def headPos {Γ : Type} (M : TM Γ) (w : List Γ) : ℕ → ℤ
  | 0 => 0
  | t + 1 =>
      let c := M.run t (M.init w)
      if M.IsHalting c then headPos M w t
      else headPos M w t + (match (M.δ c.state c.head).2.2 with
        | Move.right => 1
        | Move.left => -1)

/-- The tape symbol of a configuration at offset `o` from the head (`none` = blank). -/
def tapeAt {Γ Q : Type} (c : Cfg Γ Q) (o : ℤ) : Option Γ :=
  if o = 0 then c.head
  else if o < 0 then c.left.getD ((-o).toNat - 1) none
  else c.right.getD (o.toNat - 1) none

/-- `Cell(p, t)`: the contents of tape cell `j` (absolute position in `ℤ`, the input starting at
`0`) at time `t` in the run of `M` on `w` (Immerman, STOC 1982, proof of Theorem 1, p.149): the
state, if the head is on cell `j`, and the tape symbol. -/
def cell {Γ : Type} (M : TM Γ) (w : List Γ) (t : ℕ) (j : ℤ) : CellSym M :=
  let c := M.run t (M.init w)
  (if j = headPos M w t then some c.state else none, tapeAt c (j - headPos M w t))

/-- `⟨a₋₁ a₀ a₁⟩ → a` (Immerman, STOC 1982, proof of Theorem 1, p.149): the contents `a` of a
cell after one move of `M`, given the contents `a₋₁, a₀, a₁` of the cell's left neighbour, the cell
and its right neighbour before the move. The scanned cell receives the symbol written by `δ`; the
head arrives from the left neighbour on a right move and from the right neighbour on a left move;
a halting state stays where it is and changes nothing. -/
def leads {Γ : Type} (M : TM Γ) (l m r : CellSym M) : CellSym M :=
  let halt : M.Q → Bool := fun q => decide (q = M.qaccept) || decide (q = M.qreject)
  let sym : Option Γ := match m.1 with
    | some q => if halt q then m.2 else (M.δ q m.2).2.1
    | none => m.2
  let st : Option M.Q := match m.1 with
    | some q => if halt q then some q else none
    | none =>
      (match l.1 with
        | some q => if !halt q && decide ((M.δ q l.2).2.2 = Move.right)
            then some (M.δ q l.2).1 else none
        | none => none) <|>
      (match r.1 with
        | some q => if !halt q && decide ((M.δ q r.2).2.2 = Move.left)
            then some (M.δ q r.2).1 else none
        | none => none)
  (st, sym)

end RelQueryPTime


