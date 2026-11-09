-- Prove2me | Definitions.Def_RecoveryStorage3SUM_Adaptive_OracleMachine
-- name    : RecoveryStorage3SUM_Adaptive_OracleMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:58.237789+00:00
-- url     : https://prove2.me/theorems/b651588e-52b3-497e-a09e-2784be7af93a
-- title:
--   The word RAM with an evaluation oracle, collision probability, and correct inverters
-- statement:
--   The machine for function inversion is the published word RAM plus one instruction $[i]:=f([j])$ of unit cost, for a function $f$ on $[N]=\{0,\dots,N-1\}$. Evaluation is the only access to $f$, and arguments outside $[N]$ return $0$.
--
--   The **collision probability** of $f$ is
--   $$q(f)=\Pr_{x,x'}[f(x)=f(x')]=\frac{|\{(x,x')\in[N]^2: f(x)=f(x')\}|}{N^2}$$
--   for independent uniform $x,x'\in[N]$.
--
--   An answer to a query $y$ is **correct** if it is some $x\in f^{-1}(y)$ when that fiber is nonempty, and $\bot$ otherwise. An inverter is correct if it answers every $y\in[N]$ correctly.
--
--   These notions carry Lemma 2.3 of the source, and they let the analysis of Recover use inverter guarantees without restating the machine.
--
--   **Formalization Note** The answer $\bot$ is a negative word in cell $0$.
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Section 1.1, p.4; Lemma 2.3, p.6

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

open MatroidSensOracle

/-!
# The word RAM with an evaluation oracle, and function inversion

Carmel, Kosoburd, Krauthgamer, STOC 2027 submission #561, §1.1, p.4: "Given a constant time oracle
for a function f over a finite domain, one can build a (randomized) data structure that, when queried
for a value y, reports a preimage of y (if it exists) within time bound T"; Lemma 2.3, p.6.

**Formalization Note.** The machine extends `MatroidSensOracle.Instr` by one instruction
`[i] := f([j])`, of unit cost, for the function under inversion. Evaluation is the only access to `f`.
An argument outside `[N]` returns `0`. The answer `⊥` is a negative word in cell `0`.
-/

/-- Instructions of the oracle machine: those of the word RAM, plus one evaluation of `f`. -/
inductive OInstr where
  | base (I : Instr)
  | eval (i j : ℤ)

/-- The final memory, if the program `P` with oracle `f` on `[N]`, run from position `pc` with next
coin index `c` on memory `m`, halts within `t` steps. The semantics of `base` instructions is that of
`MatroidSensOracle.exec`; `eval i j` sets `[i] := f([j])`, with `[j]` read as a signed word. -/
noncomputable def oexec {w : ℕ} (N : ℕ) (f : ℕ → ℕ) (P : List OInstr) (ω : Coins) :
    (t pc c : ℕ) → (m : ℤ → BitVec w) → Option (ℤ → BitVec w)
  | 0, _, _, _ => none
  | t + 1, pc, c, m =>
    let write (i : ℤ) (v : BitVec w) (c' : ℕ) :=
      oexec N f P ω t (pc + 1) c' fun x => if x = i then v else m x
    match P.getD pc (.base .halt) with
    | .eval i j =>
      let x := (m j).toInt
      write i (BitVec.ofNat w (if 0 ≤ x ∧ x < N then f x.toNat else 0)) c
    | .base (.one i) => write i 1 c
    | .base (.add i j k) => write i (m j + m k) c
    | .base (.sub i j k) => write i (m j - m k) c
    | .base (.mul i j k) => write i (m j * m k) c
    | .base (.udiv i j k) => write i (m j / m k) c
    | .base (.umod i j k) => write i (m j % m k) c
    | .base (.load i j) => write i (m (m j).toInt) c
    | .base (.store i j) => write (m i).toInt (m j) c
    | .base (.bltz i l) => oexec N f P ω t (if (m i).toInt < 0 then l else pc + 1) c m
    | .base (.coin i j) => write i (BitVec.ofNat w (draw (ω c) (m j).toNat)) (c + 1)
    | .base .halt => some m

/-- An oracle program without coin instructions. -/
def OCoinFree (P : List OInstr) : Prop := ∀ i j : ℤ, OInstr.base (.coin i j) ∉ P

/-- `f` maps `[N]` into `[N]`. -/
def IsSelfMap (N : ℕ) (f : ℕ → ℕ) : Prop := ∀ x < N, f x < N

open Classical in
/-- The collision probability `q(f) = Pr_{x,x′}[f(x) = f(x′)]` for independent uniform `x, x′ ∈ [N]`. -/
noncomputable def collisionProb (N : ℕ) (f : ℕ → ℕ) : ℝ :=
  (((Finset.range N ×ˢ Finset.range N).filter fun x => f x.1 = f x.2).card : ℝ) / ((N : ℝ) ^ 2)

/-- The answer `ans` to the query `y` is right: some `x ∈ f⁻¹(y)` if `f⁻¹(y)` is nonempty in `[N]`,
and `⊥` (`none`) otherwise. -/
def InvertsAt (N : ℕ) (f : ℕ → ℕ) (y : ℕ) (ans : Option ℕ) : Prop :=
  match ans with
  | some x => x < N ∧ f x = y
  | none => ∀ x < N, f x ≠ y

/-- `inv` answers every query `y ∈ [N]` correctly. -/
def CorrectInverter (N : ℕ) (f : ℕ → ℕ) (inv : ℕ → Option ℕ) : Prop :=
  ∀ y < N, InvertsAt N f y (inv y)

/-- The answer stored in cell `0` of a halted query: `⊥` for a negative word, else its value. -/
def decodeAnswer {w : ℕ} (m : ℤ → BitVec w) : Option ℕ :=
  if (m 0).toInt < 0 then none else some (m 0).toNat

end RecoveryStorage3SUM.Adaptive


