-- Prove2me | Definitions.Def_MatroidSensOracle_AlgRAM
-- name    : MatroidSensOracle_AlgRAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:59.412217+00:00
-- url     : https://prove2.me/theorems/12928831-82e7-449c-a99f-a8d0e6b853d3
-- title:
--   The algebraic RAM over a field $\mathbb F$ and its oracle semantics; coefficient encoding of polynomial matrices
-- statement:
--   The **algebraic RAM over a field $\mathbb F$** has two banks of cells indexed by the integers: word cells holding $w$-bit words and field cells holding elements of $\mathbb F$. Word instructions are those of the randomized word RAM without its coin. Field instructions are the constants $0$ and $1$, addition, subtraction, multiplication and inversion (with $0^{-1}=0$), indirect load and store with addresses in word cells, the branch "if $F[i]=0$ go to $l$", and a coin $F[i]:=$ a uniform element of $\mathbb F$. Every instruction costs one step, so the running time counts field operations together with word operations.
--
--   An oracle is a pair of programs. When the preprocessing halts, word cells $0$ and $1$ hold $L_w$ and $L_F$, and the stored structure is word cells $2,\dots,L_w+1$ and field cells $0,\dots,L_F-1$; the **space** is $L_w+L_F$ cells. The query starts from a memory holding exactly this structure and the query (its words from word cell $L_w+2$, its field elements from field cell $L_F$), with fresh coins. For a finite field, a run of at most $T$ steps reads at most $T$ coins, and probabilities are counted uniformly over $\mathbb F^{T}$.
--
--   A polynomial matrix $M\in\mathbb F_d[Y]^{N\times N}$ is input as the coefficients $0,\dots,d$ of its entries, row by row.
--
--   This is the model of Lemma 2.2 ("field operations") and of the oracles of Theorems 3.5 and 3.7, whose matroids are "represented over $\mathbb F$".
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), §2, pp.12–13 (PDF pp.15–16); §3.2–3.3, pp.17–21 (PDF pp.20–24)

import Mathlib

set_option autoImplicit false

namespace MatroidSensOracle

/-!
# The algebraic RAM over a field `F` and its oracle semantics

Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), §2, pp.12–13
(PDF pp.15–16): Lemma 2.2 counts "field operations"; Theorems 3.5 and 3.7 (pp.19–21) state
preprocessing time, space and query time of oracles for matroids "represented over F", correct with
probability `1 − O(N/|F|)`.

**Formalization Note.**
* **Machine.** Two banks of cells indexed by `ℤ`: word cells holding `BitVec w`, and field cells
  holding elements of `F`. The word instructions are those of `MatroidSensOracle.Instr` without its
  coin (`one add sub mul udiv umod load store bltz`). The field instructions are `fzero`, `fone`
  (constants `0`, `1`), `fadd`, `fsub`, `fmul`, `finv` (with `0⁻¹ = 0`), `fload i j : F[i] := F[[j]]`,
  `fstore i j : F[[i]] := F[j]` (field addresses taken from word cells, read signed), the zero test
  `fbz i l` (jump to `l` if `F[i] = 0`), and the coin `fcoin i : F[i] := a uniform element of F`.
  `halt` stops; fetching past the end halts. Every instruction costs one step, so time counts field
  operations and word operations together.
* **Coins.** The `c`-th executed `fcoin` returns `ω c`. A run of at most `T` steps reads at most `T`
  coins, so probabilities are counted over `ω ∈ F^T` (extended by `0`), uniformly.
* **Oracle.** When the preprocessing halts, word cell `0` holds `Lw` and word cell `1` holds `LF`; the
  stored structure is the word cells `2, …, Lw + 1` and the field cells `0, …, LF − 1`. The space is
  `Lw + LF` cells. The query starts from a fresh memory holding exactly these (at the same
  addresses), the query's words from word cell `Lw + 2` on and its field elements from field cell
  `LF` on. The query draws fresh coins.
-/

/-- Instructions of the algebraic RAM; `i j k` name cells, `l` a position in the program. -/
inductive AInstr where
  | one (i : ℤ)             -- W[i] := 1
  | add (i j k : ℤ)         -- W[i] := W[j] + W[k]
  | sub (i j k : ℤ)         -- W[i] := W[j] - W[k]
  | mul (i j k : ℤ)         -- W[i] := W[j] * W[k]
  | udiv (i j k : ℤ)        -- W[i] := W[j] / W[k], unsigned
  | umod (i j k : ℤ)        -- W[i] := W[j] mod W[k], unsigned
  | load (i j : ℤ)          -- W[i] := W[W[j]]
  | store (i j : ℤ)         -- W[W[i]] := W[j]
  | bltz (i : ℤ) (l : ℕ)    -- if W[i] < 0, go to position l
  | fzero (i : ℤ)           -- F[i] := 0
  | fone (i : ℤ)            -- F[i] := 1
  | fadd (i j k : ℤ)        -- F[i] := F[j] + F[k]
  | fsub (i j k : ℤ)        -- F[i] := F[j] - F[k]
  | fmul (i j k : ℤ)        -- F[i] := F[j] * F[k]
  | finv (i j : ℤ)          -- F[i] := F[j]⁻¹
  | fload (i j : ℤ)         -- F[i] := F[W[j]]
  | fstore (i j : ℤ)        -- F[W[i]] := F[j]
  | fbz (i : ℤ) (l : ℕ)     -- if F[i] = 0, go to position l
  | fcoin (i : ℤ)           -- F[i] := uniform element of F
  | halt

/-- The program draws no coins. -/
def AInstr.IsCoin : AInstr → Prop
  | .fcoin _ => True
  | _ => False

/-- The final word and field memories, if `P`, run from position `pc` with next coin index `c`,
halts within `t` steps. -/
noncomputable def aexec {F : Type} [Field F] [DecidableEq F] {w : ℕ} (P : List AInstr)
    (ω : ℕ → F) : (t pc c : ℕ) → (wm : ℤ → BitVec w) → (fm : ℤ → F) →
    Option ((ℤ → BitVec w) × (ℤ → F))
  | 0, _, _, _, _ => none
  | t + 1, pc, c, wm, fm =>
    let wwrite (i : ℤ) (v : BitVec w) :=
      aexec P ω t (pc + 1) c (fun x => if x = i then v else wm x) fm
    let fwrite (i : ℤ) (v : F) (c' : ℕ) :=
      aexec P ω t (pc + 1) c' wm (fun x => if x = i then v else fm x)
    match P.getD pc .halt with
    | .one i => wwrite i 1
    | .add i j k => wwrite i (wm j + wm k)
    | .sub i j k => wwrite i (wm j - wm k)
    | .mul i j k => wwrite i (wm j * wm k)
    | .udiv i j k => wwrite i (wm j / wm k)
    | .umod i j k => wwrite i (wm j % wm k)
    | .load i j => wwrite i (wm (wm j).toInt)
    | .store i j => wwrite (wm i).toInt (wm j)
    | .bltz i l => aexec P ω t (if (wm i).toInt < 0 then l else pc + 1) c wm fm
    | .fzero i => fwrite i 0 c
    | .fone i => fwrite i 1 c
    | .fadd i j k => fwrite i (fm j + fm k) c
    | .fsub i j k => fwrite i (fm j - fm k) c
    | .fmul i j k => fwrite i (fm j * fm k) c
    | .finv i j => fwrite i (fm j)⁻¹ c
    | .fload i j => fwrite i (fm (wm j).toInt) c
    | .fstore i j => fwrite (wm i).toInt (fm j) c
    | .fbz i l => aexec P ω t (if fm i = 0 then l else pc + 1) c wm fm
    | .fcoin i => fwrite i (ω c) (c + 1)
    | .halt => some (wm, fm)

/-- The word memory at the start: the words `ws` in cells `0, 1, …`, `0` elsewhere. -/
def aloadWords (w : ℕ) (ws : List ℤ) : ℤ → BitVec w :=
  fun a => if a < 0 then 0 else BitVec.ofInt w (ws.getD a.toNat 0)

/-- The field memory at the start: the elements `xs` in cells `0, 1, …`, `0` elsewhere. -/
def aloadFields {F : Type} [Field F] (xs : List F) : ℤ → F :=
  fun a => if a < 0 then 0 else xs.getD a.toNat 0

/-- The coin sequence given by finitely many coins `c`, extended by `0`. -/
def extendCoins {F : Type} [Field F] {T : ℕ} (c : Fin T → F) : ℕ → F :=
  fun i => if h : i < T then c ⟨i, h⟩ else 0

/-- An oracle on the algebraic RAM: a preprocessing and a query program. -/
structure AOracle where
  prep : List AInstr
  query : List AInstr

/-- The query's initial memories: the stored structure of the halted preprocessing state `st`
(word cells `0, …, Lw + 1`, field cells `0, …, LF − 1`) and the query `(qw, qf)` after it. -/
def aQueryMemory {F : Type} [Field F] {w : ℕ} (st : (ℤ → BitVec w) × (ℤ → F))
    (qw : List ℤ) (qf : List F) : (ℤ → BitVec w) × (ℤ → F) :=
  let Lw := (st.1 0).toNat
  let LF := (st.1 1).toNat
  (fun a => if a < 0 then 0 else if a ≤ Lw + 1 then st.1 a
      else BitVec.ofInt w (qw.getD (a.toNat - (Lw + 2)) 0),
   fun a => if a < 0 then 0 else if a < LF then st.2 a else qf.getD (a.toNat - LF) 0)

/-- One run: preprocessing on `(iw, iF)` for at most `TP` steps with coins `ω₁`, then the query on
the stored structure and `(qw, qf)` for at most `TQ` steps with coins `ω₂`. -/
noncomputable def AOracle.run {F : Type} [Field F] [DecidableEq F] (O : AOracle) (w : ℕ)
    (iw : List ℤ) (iF : List F) (qw : List ℤ) (qf : List F) (TP TQ : ℕ) (ω₁ ω₂ : ℕ → F) :
    Option (((ℤ → BitVec w) × (ℤ → F)) × ((ℤ → BitVec w) × (ℤ → F))) :=
  match aexec O.prep ω₁ TP 0 0 (aloadWords w iw) (aloadFields iF) with
  | none => none
  | some st =>
    let q0 := aQueryMemory st qw qf
    (aexec O.query ω₂ TQ 0 0 q0.1 q0.2).map fun r => (st, r)

/-- Preprocessing bound: on every coin sequence the preprocessing halts within `TP` steps and stores
at most `space` cells (`Lw + LF`). -/
def AOracle.PrepWithin {F : Type} [Field F] [DecidableEq F] (O : AOracle) (w : ℕ)
    (iw : List ℤ) (iF : List F) (TP : ℕ) (space : ℝ) : Prop :=
  ∀ ω : ℕ → F, ∃ st, aexec O.prep ω TP 0 0 (aloadWords w iw) (aloadFields iF) = some st ∧
    (((st.1 0).toNat + (st.1 1).toNat : ℕ) : ℝ) ≤ space

/-- Query bound: on all coins of preprocessing and query, the query halts within `TQ` steps. -/
def AOracle.QueryWithin {F : Type} [Field F] [DecidableEq F] (O : AOracle) (w : ℕ)
    (iw : List ℤ) (iF : List F) (qw : List ℤ) (qf : List F) (TP TQ : ℕ) : Prop :=
  ∀ ω₁ ω₂ : ℕ → F, (O.run w iw iF qw qf TP TQ ω₁ ω₂).isSome

/-- Error bound for one fixed query: the fraction of coin vectors `(ω₁, ω₂) ∈ F^TP × F^TQ` on which
the run does not halt with a final query word memory satisfying `ok` is at most `ε`. -/
noncomputable def AOracle.ErrorAtMost {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (O : AOracle) (w : ℕ) (iw : List ℤ) (iF : List F) (qw : List ℤ) (qf : List F) (TP TQ : ℕ)
    (ok : (ℤ → BitVec w) → Prop) (ε : ℝ) : Prop :=
  open Classical in
  ((Finset.univ.filter fun p : (Fin TP → F) × (Fin TQ → F) =>
      ¬ ∃ r, O.run w iw iF qw qf TP TQ (extendCoins p.1) (extendCoins p.2) = some r ∧
        ok r.2.1).card : ℝ) /
    (Fintype.card ((Fin TP → F) × (Fin TQ → F)) : ℝ) ≤ ε

/-- The input field elements of a polynomial matrix with entries of degree at most `d`: the
coefficients `0, …, d` of each entry, entries in row-major order. -/
noncomputable def polyMatrixFields {F : Type} [Field F] {N : ℕ} (d : ℕ) (M : Matrix (Fin N) (Fin N) (Polynomial F)) :
    List F :=
  (List.finRange N).flatMap fun i => (List.finRange N).flatMap fun j =>
    (List.range (d + 1)).map fun l => (M i j).coeff l

end MatroidSensOracle


