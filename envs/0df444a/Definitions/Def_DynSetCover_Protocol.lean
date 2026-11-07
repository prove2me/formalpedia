-- Prove2me | Definitions.Def_DynSetCover_Protocol
-- name    : DynSetCover_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:34.372973+00:00
-- url     : https://prove2.me/theorems/2ced8e95-5007-4fc0-b6dd-69a024f29e60
-- title:
--   §1, §7 — encoding of the instance and updates, reports, recourse and maintained covers
-- statement:
--   A word-RAM solves fully dynamic set cover online as follows. Its input is the list of words
--   $$\mathrm{enc}(\text{instance})\ \|\ (\text{one word per update}),$$
--   where the instance encoding lists $u$, $m$, and for each set $S_s$ in order: $|S_s|$, its elements in increasing order, and the binary representations (bit count, then bits) of a numerator and a denominator of $c_0(S_s)$. The costs are therefore positive rationals $c_0(S_s)=\mathrm{num}(s)/\mathrm{den}(s)$.
--
--   The program reports a change of its cover by writing one word: $2s$ adds $S_s$, $2s+1$ removes it. For the update read by read number $k$, its **report** is the list of words written from that read up to the next read (its length is the update's **recourse**), and its **maintained cover** is the effect of all words written before the next read, applied to the empty cover. A report is **well formed** if every word names a set ($w<2m$). Theorem 7.5 additionally places a capacity bound $N$ in one word between the instance and the updates.
--
--   **Formalization Note** `RatCosts inst num den` states $0<\mathrm{num}(s)$, $0<\mathrm{den}(s)$ and $c_0(S_s)=\mathrm{num}(s)/\mathrm{den}(s)$. The number of cost-bit words is $\sum_s(\text{bits of num}(s)+\text{bits of den}(s))$.
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), §1, p.1 (PDF 3); §7, p.56 (PDF 58) and Theorem 7.5, p.65 (PDF 67), 'the original cost encodings'

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_DynSetCover_Updates
import Definitions.Def_DynSetCover_DRAM

namespace DynSetCover

/-! # Encodings, reports and maintained covers of an online word-RAM

Paul, Solomon, STOC 2027 submission (sha256 a671756b…), §1, p.1 (PDF 3) and §7, pp.56, 65
(PDF 58, 67): the algorithm receives the fixed set system once, then the updates one at a time,
and after each update returns its maintained cover; the recourse is the number of sets added to
or removed from the cover per update.

**Formalization Note.** A RAM receives the costs encoded: positive rationals given by numerators
`num` and denominators `den` with `c0(S s) = num s / den s` (`RatCosts`; any representation, not
necessarily reduced). The instance is the word list `enc inst num den`:
`[u, m]`, then for each set `s` in index order: `|S s|`, its elements in increasing order, the
bit length of `num s`, its bits (least significant first, one word each, `0` or `1`), the bit
length of `den s`, and its bits. Updates follow, one word each (`Upd.word`). A program reports
a cover change by writing one word: `2s` adds set `s`, `2s + 1` removes it. The maintained cover
after some step is obtained by applying all words written so far to the empty cover. Words
`≥ 2m` are malformed; the theorems require none. -/

/-- The costs of `inst` are the positive rationals `num s / den s`. -/
def RatCosts (inst : Instance) (num den : Fin inst.m → ℕ) : Prop :=
  ∀ s, 0 < num s ∧ 0 < den s ∧ inst.c0 s = (num s : ℝ) / (den s : ℝ)

/-- The bits of `n` as `0/1` words, least significant first. -/
def bitWords (n : ℕ) : List ℕ := (Nat.bits n).map (fun b => if b then 1 else 0)

/-- The words describing input set `s`. -/
def setWords (inst : Instance) (num den : Fin inst.m → ℕ) (s : Fin inst.m) : List ℕ :=
  [(inst.S s).card] ++ ((inst.S s).image (fun e : Fin inst.u => (e : ℕ))).sort (· ≤ ·) ++
    [(Nat.bits (num s)).length] ++ bitWords (num s) ++
    [(Nat.bits (den s)).length] ++ bitWords (den s)

/-- The encoding of the fixed set system. Its length is `K` in the theorems. -/
def enc (inst : Instance) (num den : Fin inst.m → ℕ) : List ℕ :=
  [inst.u, inst.m] ++ (List.finRange inst.m).flatMap (setWords inst num den)

/-- The number of cost-bit words in the encoding ("the original cost encodings", p.65). -/
def costBits (inst : Instance) (num den : Fin inst.m → ℕ) : ℕ :=
  ∑ s, ((Nat.bits (num s)).length + (Nat.bits (den s)).length)

/-- The input of the online machine: the instance, then the updates. -/
def input (inst : Instance) (num den : Fin inst.m → ℕ) (σ : List (Upd inst.u)) : List ℕ :=
  enc inst num den ++ σ.map Upd.word

/-- The input with a capacity bound `N` in one word after the instance (Theorem 7.5). -/
def inputCap (inst : Instance) (num den : Fin inst.m → ℕ) (N : ℕ) (σ : List (Upd inst.u)) :
    List ℕ :=
  enc inst num den ++ [N] ++ σ.map Upd.word

/-- The effect of one reported word on a cover. -/
def applyReport (m : ℕ) (C : Finset (Fin m)) (w : ℕ) : Finset (Fin m) :=
  if h : w / 2 < m then
    (if w % 2 = 0 then insert ⟨w / 2, h⟩ C else C.erase ⟨w / 2, h⟩)
  else C

/-- The cover obtained by applying a list of reported words to the empty cover. -/
def coverOf (m : ℕ) (ws : List ℕ) : Finset (Fin m) := ws.foldl (applyReport m) ∅

/-- Every reported word names a set. -/
def WellFormed (m : ℕ) (ws : List ℕ) : Prop := ∀ w ∈ ws, w < 2 * m

/-- The report of the update read by read number `k`: the words written from that read up to
the next read (`τ k` is the step of read `k`). Its length is the update's recourse. -/
def report (W : ℕ) (P : Program) (inp : List ℕ) (τ : ℕ → ℕ) (k : ℕ) : List ℕ :=
  outputBetween W P inp (τ k) (τ (k + 1))

/-- The maintained cover returned for the update read by read number `k`: all words written
before read `k + 1`, applied to the empty cover. -/
def coverAfter (m W : ℕ) (P : Program) (inp : List ℕ) (τ : ℕ → ℕ) (k : ℕ) : Finset (Fin m) :=
  coverOf m (conf W P inp (τ (k + 1))).output

end DynSetCover


