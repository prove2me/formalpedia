-- Prove2me | Definitions.Def_DynApproxIdx_Main_Oracle
-- name    : DynApproxIdx_Main_Oracle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:52:01.474945+00:00
-- url     : https://prove2.me/theorems/dbe1ec35-8ad8-49c6-aa72-2de38e5139a3
-- title:
--   Balanced Monotone Range Decomposition and its oracle model (Lemma 6.1)
-- statement:
--   **The problem.** The input consists of positive integers $k,m,\lambda$ with $0<k<m$, and a function $f$ from the nonempty subintervals $[l..r)$ of $[0..m)$ to $[0..\lambda]$ that is **monotone** ($[l..r)\subseteq[l'..r')$ implies $f([l..r))\le f([l'..r'))$) and vanishes on singletons ($f(\{i\})=0$ for every $i\in[0..m)$). A valid output is a list $I_1,\dots,I_t$ of nonempty intervals partitioning $[0..m)$ (every position in exactly one $I_i$; the list need not be left to right) with
--   $$t>k,\qquad f(I_1)=f(I_2)=\dots=f(I_{k+1})\ge f(I_{k+2})\ge\dots\ge f(I_t),$$
--   together with the value $v=f(I_1)$.
--
--   **The oracle model.** The function $f$ is available only through an oracle. A program of the word RAM `DynBrooks_Machine` starts with the words $k,m,\lambda$ pending. To evaluate $f([l..r))$ it writes the words $1,l,r$ and then executes a `read`: whenever the machine is blocked at a `read`, the oracle delivers $f([l..r))$ for the last three words $1,l,r$ written ($0$ if the last three words do not have this form or do not describe a nonempty subinterval of $[0..m)$), and the `read` executes in the same step. Each delivery is one **oracle call**. The program answers by writing $0,t,l_1,r_1,\dots,l_t,r_t,v$ after its queries and executing `halt`.
--
--   This is the setting of Lemma 6.1, which computes the split points of a pattern in the paper's index.
--
--   **Formalization Note.** The value of $f$ at the empty interval is never used (blocks of a partition are nonempty). The cost $\mathrm{eval}_f$ of one evaluation is accounted for by counting oracle calls separately from machine steps.
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), §6.1, problem box and Lemma 6.1, p. 22 (PDF 24)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynApproxIdx_Main_Run

namespace DynApproxIdx.Main

open DynBrooks

/-! # Balanced Monotone Range Decomposition and its oracle model (Lemma 6.1)

Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC 2027 submission
(manuscript sha256 7f902057…): §6.1, the problem box and Lemma 6.1, p. 22 (PDF 24).

**Formalization Note.**
* An interval is a nonempty half-open `[l..r) ⊆ [0..m)`, `l < r ≤ m`, and `f l r` stands for
  `f([l..r))`; the values of `f` at other pairs are never used.
* `f` is an oracle. The program runs on the published word RAM `DynBrooks` with the words
  `k, m, λ` pending. To query `f([l..r))` it writes the three words `1, l, r` and then executes a
  `read`: whenever the machine is blocked at a `read` with no input pending, the oracle delivers
  one word, `f(l, r)` for the last three words `1, l, r` written (`0` if the last three words
  written do not have this form or do not name an interval of `[0..m)`), and that `read` is executed
  in the same step. Each such delivery is one **oracle call**; every executed instruction is one
  step.
* The program answers by writing `0, t, l_1, r_1, …, l_t, r_t, v` after its queries and halting
  (the instruction `halt`). The output is a partition of `[0..m)` into `I_1, …, I_t` in the
  written order (not necessarily left to right).
* "`O(kλ · eval_f · log m)` time" is read as: at most `C·k·λ·log₂ m` steps and at most
  `C·k·λ·log₂ m` oracle calls, with a universal `C`, on every coin tape. -/

/-- `f` is monotone on the nonempty subintervals of `[0..m)`: `[l..r) ⊆ [l'..r')` implies
`f(l, r) ≤ f(l', r')`. -/
def MonotoneOnIntervals (m : ℕ) (f : ℕ → ℕ → ℕ) : Prop :=
  ∀ l r l' r' : ℕ, l' ≤ l → l < r → r ≤ r' → r' ≤ m → f l r ≤ f l' r'

/-- A valid input of Balanced Monotone Range Decomposition: positive integers `k, m, λ` with
`0 < k < m`, and a monotone `f` from the subintervals of `[0..m)` to `[0..λ]` with `f({i}) = 0`
for every `i ∈ [0..m)`. -/
def IsBMRDInput (k m lam : ℕ) (f : ℕ → ℕ → ℕ) : Prop :=
  0 < k ∧ k < m ∧ 0 < lam ∧ MonotoneOnIntervals m f ∧
  (∀ l r : ℕ, l < r → r ≤ m → f l r ≤ lam) ∧ ∀ i : ℕ, i < m → f i (i + 1) = 0

/-- The list `I_1, …, I_t` of intervals `[l..r)` partitions `[0..m)`: every entry is a nonempty
subinterval of `[0..m)`, and every `x ∈ [0..m)` lies in exactly one entry (counted with
multiplicity). -/
def IsIntervalPartition (m : ℕ) (I : List (ℕ × ℕ)) : Prop :=
  (∀ J ∈ I, J.1 < J.2 ∧ J.2 ≤ m) ∧
  (I.flatMap fun J => List.range' J.1 (J.2 - J.1)).Perm (List.range m)

/-- A valid output: a partition `I_1, …, I_t` of `[0..m)` with `t > k` and
`f(I_1) = ⋯ = f(I_{k+1}) ≥ f(I_{k+2}) ≥ ⋯ ≥ f(I_t)`, together with `v = f(I_1)`. -/
def IsBMRDOutput (k m : ℕ) (f : ℕ → ℕ → ℕ) (I : List (ℕ × ℕ)) (v : ℕ) : Prop :=
  IsIntervalPartition m I ∧ k < I.length ∧
  (∀ i : ℕ, i < k + 1 → f (I.getD i (0, 0)).1 (I.getD i (0, 0)).2 = v) ∧
  List.IsChain (fun J J' => f J'.1 J'.2 ≤ f J.1 J.2) I

/-- The oracle's reply when the machine has written `out`: `f(l, r)` if `out` ends with the words
`1, l, r` and `[l..r)` is a nonempty subinterval of `[0..m)`, and `0` otherwise. -/
def oracleReply (m : ℕ) (f : ℕ → ℕ → ℕ) (out : List ℕ) : ℕ :=
  match out.reverse with
  | r :: l :: 1 :: _ => if l < r ∧ r ≤ m then f l r else 0
  | _ => 0

open Classical in
/-- One step of the oracle machine, with the number of oracle calls so far: when the machine is
blocked at a `read`, the oracle delivers its reply and the `read` executes. -/
noncomputable def oStep (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (m : ℕ) (f : ℕ → ℕ → ℕ)
    (s : Config w × ℕ) : Config w × ℕ :=
  if IsCompleted P s.1 then (step P ω (feed s.1 [oracleReply m f s.1.output]), s.2 + 1)
  else (step P ω s.1, s.2)

/-- The oracle machine after `t` steps, started on the words `k, m, λ` with no call made. -/
noncomputable def oRun (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (k m lam : ℕ)
    (f : ℕ → ℕ → ℕ) (t : ℕ) : Config w × ℕ :=
  (oStep P ω m f)^[t] (initConfig w [k, m, lam], 0)

/-- The machine has halted: its program counter is at a `halt` instruction. -/
def Halted (P : Program) {w : ℕ} (c : Config w) : Prop :=
  P[c.pc]? = some Instr.halt

/-- The written words are a sequence of queries `1, l, r` followed by the answer
`0, t, l_1, r_1, …, l_t, r_t, v` of a valid output with `t ≤ 5kλ`. -/
def BMRDAnswer (k m lam : ℕ) (f : ℕ → ℕ → ℕ) (out : List ℕ) : Prop :=
  ∃ (Qs I : List (ℕ × ℕ)) (v : ℕ),
    out = (Qs.flatMap fun q => [1, q.1, q.2]) ++ [0, I.length] ++
      (I.flatMap fun J => [J.1, J.2]) ++ [v] ∧
    IsBMRDOutput k m f I v ∧ I.length ≤ 5 * k * lam

end DynApproxIdx.Main


