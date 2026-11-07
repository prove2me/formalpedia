-- Prove2me | Definitions.Def_PackingLPAccel_Machine
-- name    : PackingLPAccel_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:32.243848+00:00
-- url     : https://prove2.me/theorems/ea456438-2198-4e5b-bc85-eaf1dc4e2324
-- title:
--   The exact-arithmetic work-depth language: $\mathsf{Stmt}$, $\mathsf{Eval}$, oracle models
-- statement:
--   A program is a term of a structured language over private real and integer registers and shared real and integer memories. Its atomic instructions are the ones the paper's computational model lists: rational literals, $+,-,\times,\div$ on reals, integer roots $x^{1/k}$, comparisons (as branch and loop guards), indirect loads and stores, integer addition and subtraction, and a cast from integers to reals. A program also has sequencing, loops on comparisons, a parallel loop $\mathsf{parFor}$, and an oracle instruction.
--
--   The relation $\mathsf{Eval}\,O\,s\,\sigma\,\sigma'\,w\,d$ says that $s$ run from $\sigma$ with oracle $O$ ends in $\sigma'$ with work $w$ and depth $d$. Every atomic instruction has work and depth $1$. Sequencing adds both. A parallel loop over $c$ iterations runs each iteration from the same snapshot of the state, and has work $1+c+\sum_i w_i$ and depth $1+\max_i d_i$. If two iterations change one memory cell, or if an oracle query has no answer, there is no derivation.
--
--   This object is the meaning of "there is a deterministic algorithm" in every machine-level statement of the mission. It makes work and depth formal: work is the total number of operations, and depth is the length of the longest chain of dependent operations.
--
--   **Formalization Note** No constructor carries a function, and literals are rational by typing, so a program cannot read an instance for free. Floor, real-to-integer cast, integer multiplication and division, bit operations, $\exp$ and $\log$ are absent: the list is the literal list of p.8. The semantics is CREW, and the PRAM variants differ by polylogarithmic factors. $\mathsf{lg}(s)=\lfloor\log_2 s\rfloor+1$ is the polylogarithm base of every $\widetilde O$.
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Computational model, p.8 (pdf 9), and footnote 4, p.1 (pdf 2)

import Mathlib

namespace PackingLPAccel

/-!
# The exact-arithmetic work-depth language

Chen, Chen, Graur, Sidford, *Accelerated Parallel Algorithms for Packing Linear Programming*,
STOC 2027 submission (manuscript sha256 1dac7711…), "Computational model", p.8, and footnote 4, p.1
("parallel random-access machine (PRAM)").

**Formalization Note.** The page lists scalar addition, subtraction, multiplication, division by a
nonzero number, comparisons and nonnegative integer roots at constant work and depth, and defines
depth as the length of the longest chain of dependent operations. A flat RAM cannot express that
chain, so this is a structured language with a parallel loop.
* State: private real and integer registers `r`, `p`; shared real and integer memories `M`, `I`
  indexed by `ℤ`; an oracle-call counter.
* No constructor carries a function, and real literals are rational by typing, so a program cannot
  read an instance for free. `x / 0 = 0` is Lean's value and is harmless.
* **Not in the language:** floor, real-to-integer cast, integer multiplication or division, bit
  operations, `exp`, `log`, real powers other than `rroot`, non-rational constants, coins. The list
  is the literal list of p.8. Integer powers are programs (repeated squaring).
* `parFor` runs every iteration from the same snapshot of the state (CREW): two iterations changing
  one memory cell have no derivation. Registers are private, so the parent keeps its own.
* Work is the number of operations. A `parFor` over `c` iterations has work `1 + c + ∑ wᵢ` and depth
  `1 + max dᵢ`. Sequencing adds depths, which only charges more.
* `oracle` costs `(1, 1)` and increments `calls`; `answer = none` has no derivation, so evaluation
  itself carries "every query is in the allowed class". `noOracle` makes `oracle` underivable.
-/

/-- A machine state: private registers, shared memories, and the oracle-call counter. -/
structure State where
  /-- Real registers (private to a parallel iteration). -/
  r : ℕ → ℝ
  /-- Integer registers (private to a parallel iteration). -/
  p : ℕ → ℤ
  /-- Shared real memory. -/
  M : ℤ → ℝ
  /-- Shared integer memory. -/
  I : ℤ → ℤ
  /-- Number of oracle calls so far. -/
  calls : ℕ

/-- Set a real register. -/
def State.setR (st : State) (d : ℕ) (x : ℝ) : State := { st with r := Function.update st.r d x }

/-- Set an integer register. -/
def State.setP (st : State) (d : ℕ) (x : ℤ) : State := { st with p := Function.update st.p d x }

/-- The atomic instructions of p.8, each of work `1` and depth `1`. -/
inductive Instr where
  /-- `r[d] := c`, a rational literal. -/
  | rconst (d : ℕ) (c : ℚ)
  /-- `r[d] := r[a] + r[b]`. -/
  | radd (d a b : ℕ)
  /-- `r[d] := r[a] - r[b]`. -/
  | rsub (d a b : ℕ)
  /-- `r[d] := r[a] * r[b]`. -/
  | rmul (d a b : ℕ)
  /-- `r[d] := r[a] / r[b]`. -/
  | rdiv (d a b : ℕ)
  /-- `r[d] := r[a] ^ (1 / p[k])` when `0 ≤ r[a]` and `1 ≤ p[k]`, else `0`. -/
  | rroot (d a k : ℕ)
  /-- `r[d] := M[p[q]]`. -/
  | rload (d q : ℕ)
  /-- `M[p[q]] := r[a]`. -/
  | rstore (q a : ℕ)
  /-- `r[d] := (p[q] : ℝ)`. -/
  | rofInt (d q : ℕ)
  /-- `p[d] := c`. -/
  | pconst (d : ℕ) (c : ℤ)
  /-- `p[d] := p[a] + p[b]`. -/
  | padd (d a b : ℕ)
  /-- `p[d] := p[a] - p[b]`. -/
  | psub (d a b : ℕ)
  /-- `p[d] := I[p[q]]`. -/
  | pload (d q : ℕ)
  /-- `I[p[q]] := p[a]`. -/
  | pstore (q a : ℕ)
  /-- Do nothing. -/
  | skip

/-- The effect of an atomic instruction. -/
noncomputable def Instr.exec : Instr → State → State
  | .rconst d c, st => st.setR d (c : ℝ)
  | .radd d a b, st => st.setR d (st.r a + st.r b)
  | .rsub d a b, st => st.setR d (st.r a - st.r b)
  | .rmul d a b, st => st.setR d (st.r a * st.r b)
  | .rdiv d a b, st => st.setR d (st.r a / st.r b)
  | .rroot d a k, st =>
      st.setR d (if 0 ≤ st.r a ∧ 1 ≤ st.p k then st.r a ^ ((1 : ℝ) / (st.p k : ℝ)) else 0)
  | .rload d q, st => st.setR d (st.M (st.p q))
  | .rstore q a, st => { st with M := Function.update st.M (st.p q) (st.r a) }
  | .rofInt d q, st => st.setR d (st.p q : ℝ)
  | .pconst d c, st => st.setP d c
  | .padd d a b, st => st.setP d (st.p a + st.p b)
  | .psub d a b, st => st.setP d (st.p a - st.p b)
  | .pload d q, st => st.setP d (st.I (st.p q))
  | .pstore q a, st => { st with I := Function.update st.I (st.p q) (st.p a) }
  | .skip, st => st

/-- Programs: atomic instructions, sequencing, branches, loops on comparisons, the parallel loop
over the integer range `p[lo] ≤ p[v] < p[hi]`, and the oracle instruction. -/
inductive Stmt where
  | atom (i : Instr)
  | seq (s t : Stmt)
  | ifRLe (a b : ℕ) (s t : Stmt)
  | ifPLe (a b : ℕ) (s t : Stmt)
  | whileRLe (a b : ℕ) (s : Stmt)
  | whilePLe (a b : ℕ) (s : Stmt)
  | parFor (v lo hi : ℕ) (s : Stmt)
  | oracle

/-- An oracle: from the state at the call, the new shared memories, or `none` when the query is
outside the allowed class. -/
structure OracleModel where
  /-- The answer to the query held in the state. -/
  answer : State → Option ((ℤ → ℝ) × (ℤ → ℤ))

/-- The absence of an oracle: the `oracle` instruction has no derivation. -/
def noOracle : OracleModel := ⟨fun _ => none⟩

/-- Exclusive write: at most one iteration changes any given memory cell. Reads are concurrent. -/
def ExclusiveWrite {c : ℕ} (st : State) (t : Fin c → State) : Prop :=
  (∀ a i j, (t i).M a ≠ st.M a → (t j).M a ≠ st.M a → i = j) ∧
    (∀ a i j, (t i).I a ≠ st.I a → (t j).I a ≠ st.I a → i = j)

open Classical in
/-- The state after a parallel loop: the parent's registers, the writes of all iterations, and the
oracle calls of all iterations. -/
noncomputable def mergeFor {c : ℕ} (st : State) (t : Fin c → State) : State where
  r := st.r
  p := st.p
  M := fun a => if h : ∃ i, (t i).M a ≠ st.M a then (t h.choose).M a else st.M a
  I := fun a => if h : ∃ i, (t i).I a ≠ st.I a then (t h.choose).I a else st.I a
  calls := st.calls + ∑ i, ((t i).calls - st.calls)

/-- Big-step semantics with cost: `Eval O s st st' w d` says that `s` run from `st` under the oracle
model `O` ends in `st'` with work `w` and depth `d`. There is no derivation for a divergent run, a
write conflict, or a query with `answer = none`. -/
inductive Eval (O : OracleModel) : Stmt → State → State → ℕ → ℕ → Prop where
  | atom (i : Instr) (st : State) : Eval O (.atom i) st (i.exec st) 1 1
  | seq {s t : Stmt} {st st' st'' : State} {w₁ d₁ w₂ d₂ : ℕ} :
      Eval O s st st' w₁ d₁ → Eval O t st' st'' w₂ d₂ →
      Eval O (.seq s t) st st'' (w₁ + w₂) (d₁ + d₂)
  | ifRLeTrue {a b : ℕ} {s t : Stmt} {st st' : State} {w d : ℕ} :
      st.r a ≤ st.r b → Eval O s st st' w d → Eval O (.ifRLe a b s t) st st' (1 + w) (1 + d)
  | ifRLeFalse {a b : ℕ} {s t : Stmt} {st st' : State} {w d : ℕ} :
      ¬ st.r a ≤ st.r b → Eval O t st st' w d → Eval O (.ifRLe a b s t) st st' (1 + w) (1 + d)
  | ifPLeTrue {a b : ℕ} {s t : Stmt} {st st' : State} {w d : ℕ} :
      st.p a ≤ st.p b → Eval O s st st' w d → Eval O (.ifPLe a b s t) st st' (1 + w) (1 + d)
  | ifPLeFalse {a b : ℕ} {s t : Stmt} {st st' : State} {w d : ℕ} :
      ¬ st.p a ≤ st.p b → Eval O t st st' w d → Eval O (.ifPLe a b s t) st st' (1 + w) (1 + d)
  | whileRLeExit {a b : ℕ} {s : Stmt} {st : State} :
      ¬ st.r a ≤ st.r b → Eval O (.whileRLe a b s) st st 1 1
  | whileRLeLoop {a b : ℕ} {s : Stmt} {st st' st'' : State} {w d w' d' : ℕ} :
      st.r a ≤ st.r b → Eval O s st st' w d → Eval O (.whileRLe a b s) st' st'' w' d' →
      Eval O (.whileRLe a b s) st st'' (1 + w + w') (1 + d + d')
  | whilePLeExit {a b : ℕ} {s : Stmt} {st : State} :
      ¬ st.p a ≤ st.p b → Eval O (.whilePLe a b s) st st 1 1
  | whilePLeLoop {a b : ℕ} {s : Stmt} {st st' st'' : State} {w d w' d' : ℕ} :
      st.p a ≤ st.p b → Eval O s st st' w d → Eval O (.whilePLe a b s) st' st'' w' d' →
      Eval O (.whilePLe a b s) st st'' (1 + w + w') (1 + d + d')
  | parFor {v lo hi : ℕ} {s : Stmt} {st : State} {c : ℕ} {t : Fin c → State} {w d : Fin c → ℕ} :
      c = (st.p hi - st.p lo).toNat →
      (∀ i : Fin c, Eval O s (st.setP v (st.p lo + (i : ℕ))) (t i) (w i) (d i)) →
      ExclusiveWrite st t →
      Eval O (.parFor v lo hi s) st (mergeFor st t) (1 + c + ∑ i, w i)
        (1 + Finset.univ.sup d)
  | oracle {st : State} {m : (ℤ → ℝ) × (ℤ → ℤ)} :
      O.answer st = some m →
      Eval O .oracle st { st with M := m.1, I := m.2, calls := st.calls + 1 } 1 1

/-- The polylogarithm base `⌊log₂ s⌋ + 1 ≥ 1`; every `Õ` is `C · (…) · lg s ^ K`. -/
def lg (s : ℕ) : ℕ := Nat.log 2 s + 1

end PackingLPAccel


