-- Prove2me | Definitions.Def_InteractionElim_Main_Procedure
-- name    : InteractionElim_Main_Procedure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:22:58.67846+00:00
-- url     : https://prove2.me/theorems/afaf78fd-a03d-4612-96b2-31d3bb4eeabd
-- title:
--   Agent-only sequential procedures on one block with noisy binary linear queries (Lemma C.1, Corollary C.2)
-- statement:
--   Fix $r$ and a finite **menu** of $M$ actions: binary linear functionals $\ell_k\in\mathbb F_2^r$ with noise parameters $p_k$. At an unknown truth $x\in\mathbb F_2^r$, action $k$ returns the fresh bit $\ell_k\cdot x\oplus Z$, $Z\sim\mathrm{Bernoulli}(p_k)$, independent of everything else. Coordinate queries are the menu $\ell_i=e_i$, $M=r$. A **procedure** maps its private fair-coin tape and the list of (action, response) pairs so far to the next action or to a final output (for a verifier: accept or reject a proposed root; for a stage procedure: the submitted value). The module defines the run, the probability of each output, the expected number of calls, and the **menu certificate**: $a_k\ge0$ with $\sum_{k:\,\ell_k\cdot z\ne\ell_k\cdot y}a_k\ge1$ for all $y\in D\setminus\{z\}$ (for the coordinate menu, the certificate of (2.4)).
--
--   `VerifierSpec` packages the guarantees 1–3 of Lemma C.1 for a procedure proposing root $z$ of a cell $D$ with certificate mass $t$ and parameter $H$: acceptance probability $\ge 9/10$ at truth $z$, $\le e^{-H}$ at every other truth of $D$, expected calls $\le C\{tH+\ln(2+tH)\}$ and calls on every path $\le CtH\ln(2+tH)$ at every truth of $D$. A procedure can also be computed by a program of the bit-cost machine from explicit rational data.
--
--   **Formalization Note** Noise parameters are clamped to $[0,1]$ inside the law (`coin`), which changes nothing for $p_k\in[1/8,3/8]$. Expected calls are a lower Lebesgue integral in $[0,\infty]$.
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), pp. 34-36, Appendix C, Lemma C.1 and Corollary C.2

import Mathlib
import Definitions.Def_InteractionElim_Main_Machine

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Matrix

namespace InteractionElim.Main

/-!
# Agent-only sequential procedures on one block with noisy linear queries

Source: Jin, Zang, Xu, Li, *Eliminating Ongoing Interaction in Long-Running Verification Agents*,
STOC 2027 submission (manuscript sha256 44f6d829…), Appendix C, Lemma C.1 (pp. 34–35) and
Corollary C.2 (p. 36).

A block has an unknown truth `x ∈ F_2^r`. A finite *menu* of `M` actions is given by binary
linear functionals `ℓ_k ∈ F_2^r` and noise parameters `p_k`: action `k` returns the fresh noisy
bit `ℓ_k · x ⊕ Z` with `Z ∼ Bernoulli(p_k)`, independent of everything else (the `n`-th use of
action `k` reads entry `n` of its own noise array). Coordinate queries are the menu
`ℓ_i = e_i`, `M = r`. A procedure uses its own fresh private fair-coin tape and its responses:
from the tape and the list of (action, response) pairs so far it either calls an action or
stops with an output `o : O` (for a verifier, `true` = accept the proposed root; for a stage
procedure, the submitted value). Every call is an actual paid call.
-/

/-- A procedure action: call menu action `k`, or stop with output `o`. -/
inductive PAct (M : ℕ) (O : Type) where
  | query (k : Fin M)
  | output (o : O)

/-- Procedure actions carry the discrete σ-algebra. -/
instance (M : ℕ) (O : Type) : MeasurableSpace (PAct M O) := ⊤

/-- An agent-only procedure with `M` menu actions and outputs in `O`. -/
structure Procedure (M : ℕ) (O : Type) where
  act : Tape → List (Fin M × ZMod 2) → PAct M O

/-- The procedure is a measurable function of its tape. -/
def Procedure.IsMeasurable {M : ℕ} {O : Type} (pc : Procedure M O) : Prop :=
  ∀ l, Measurable fun ρ : Tape => pc.act ρ l

/-- Randomness of a procedure run: its tape and one noise array per action. -/
inductive PSrc (M : ℕ) where
  | tape (n : ℕ)
  | noise (k : Fin M) (n : ℕ)

/-- The law of a procedure run: fair tape, `noise k n ∼ Bernoulli(p_k)`, all independent. -/
noncomputable def plaw {M : ℕ} (p : Fin M → ℝ) : Measure (PSrc M → Bool) :=
  Measure.infinitePi fun s : PSrc M =>
    match s with
    | .tape _ => coin (1 / 2)
    | .noise k _ => coin (p k)

/-- Procedure state: responses so far, call counts per action, output once stopped. -/
structure PState (M : ℕ) (O : Type) where
  log : List (Fin M × ZMod 2)
  calls : Fin M → ℕ
  out : Option O

/-- One step of the procedure `pc` with menu `ℓ` at truth `x`. -/
noncomputable def pstep {r M : ℕ} {O : Type} (ell : Fin M → Fin r → ZMod 2)
    (pc : Procedure M O) (x : Fin r → ZMod 2) (ω : PSrc M → Bool) (s : PState M O) :
    PState M O :=
  match s.out with
  | some _ => s
  | none =>
    match pc.act (fun n => ω (.tape n)) s.log with
    | .query k =>
        { log := s.log ++
            [(k, ell k ⬝ᵥ x + (if ω (.noise k (s.calls k)) then (1 : ZMod 2) else 0))]
          calls := Function.update s.calls k (s.calls k + 1)
          out := none }
    | .output o => { s with out := some o }

/-- The procedure state after `t` steps. -/
noncomputable def prun {r M : ℕ} {O : Type} (ell : Fin M → Fin r → ZMod 2) (pc : Procedure M O)
    (x : Fin r → ZMod 2) (ω : PSrc M → Bool) (t : ℕ) : PState M O :=
  (pstep ell pc x ω)^[t] { log := [], calls := fun _ => 0, out := none }

/-- The probability, at truth `x`, that the procedure stops with output `o`. -/
noncomputable def probOutput {r M : ℕ} {O : Type} (ell : Fin M → Fin r → ZMod 2)
    (p : Fin M → ℝ) (pc : Procedure M O) (x : Fin r → ZMod 2) (o : O) : ℝ≥0∞ :=
  plaw p {ω | ∃ t, (prun ell pc x ω t).out = some o}

/-- The expected total number of calls at truth `x`. -/
noncomputable def expCalls {r M : ℕ} {O : Type} (ell : Fin M → Fin r → ZMod 2)
    (p : Fin M → ℝ) (pc : Procedure M O) (x : Fin r → ZMod 2) : ℝ≥0∞ :=
  ∫⁻ ω, ⨆ t, (∑ k, ((prun ell pc x ω t).calls k : ℝ≥0∞)) ∂(plaw p)

/-- The coordinate menu `ℓ_i = e_i` on `F_2^r`. -/
def coordMenu (r : ℕ) : Fin r → Fin r → ZMod 2 := fun i => Pi.single i 1

/-- A feasible menu certificate for root `z` against `D`: `a_k ≥ 0` and
`∑_{k : ℓ_k·z ≠ ℓ_k·y} a_k ≥ 1` for every `y ∈ D \ {z}` (constraints indexed by the actions
distinguishing `z` from `y`). For the coordinate menu this is `IsCertificate`. -/
def IsMenuCertificate {r M : ℕ} (ell : Fin M → Fin r → ZMod 2) (D : Set (Fin r → ZMod 2))
    (z : Fin r → ZMod 2) (a : Fin M → ℝ) : Prop :=
  (∀ k, 0 ≤ a k) ∧
    ∀ y ∈ D, y ≠ z → 1 ≤ ∑ k ∈ Finset.univ.filter (fun k => ell k ⬝ᵥ z ≠ ell k ⬝ᵥ y), a k

/-- The verification guarantees 1–3 of Lemma C.1 for a procedure `pc` that proposes root `z`
of the cell `D` (output `true` = accept `z`), with certificate mass `t`, parameter `H` and
constant `C`: acceptance probability at least `9/10` at truth `z`; at most `e^{-H}` at every
truth `x ∈ D \ {z}`; at every truth `x ∈ D`, expected calls at most `C(tH + ln(2 + tH))` and
calls at most `C t H ln(2 + tH)` on every path. -/
def VerifierSpec {r M : ℕ} (ell : Fin M → Fin r → ZMod 2) (p : Fin M → ℝ)
    (D : Finset (Fin r → ZMod 2)) (z : Fin r → ZMod 2) (t : ℝ) (H : ℕ) (C : ℝ)
    (pc : Procedure M Bool) : Prop :=
  ENNReal.ofReal (9 / 10) ≤ probOutput ell p pc z true ∧
    (∀ x ∈ D, x ≠ z → probOutput ell p pc x true ≤ ENNReal.ofReal (Real.exp (-(H : ℝ)))) ∧
    (∀ x ∈ D, expCalls ell p pc x ≤ ENNReal.ofReal (C * (t * H + Real.log (2 + t * H)))) ∧
    ∀ x ∈ D, ∀ ω n, ((∑ k, (prun ell pc x ω n).calls k : ℕ) : ℝ) ≤
      C * t * H * Real.log (2 + t * H)

/-! ## Procedures computed by a program of the bit-cost machine -/

/-- Encoding of a procedure action, given an encoding of outputs. -/
def encPAct {M : ℕ} {O : Type} (encO : O → List Bool) : PAct M O → List Bool
  | .query k => false :: encNat k
  | .output o => true :: encO o

/-- Encoding of a response log. -/
def encPLog {M : ℕ} (l : List (Fin M × ZMod 2)) : List Bool :=
  encList (fun e : Fin M × ZMod 2 => encNat e.1 ++ encBit e.2) l

open Classical in
/-- The procedure computed by `prog` on the explicit data `data`: each action is one halting
run of `prog` on `data` followed by the encoded response log, reading the procedure's tape;
an output that is not a valid code (or no halt) stops with `dflt`. -/
noncomputable def procOfProgram {M : ℕ} {O : Type} (encO : O → List Bool) (dflt : O)
    (prog : Program) (data : List Bool) : Procedure M O where
  act := fun ρ l =>
    match progOut prog (data ++ encPLog l) ρ with
    | some c => if h : ∃ a : PAct M O, encPAct encO a = c then Classical.choose h
                else .output dflt
    | none => .output dflt

/-- The explicit rational input of Lemma C.1: `r`, `M`, the menu functionals, the rational
noise parameters, the cell `D` (listed), the proposed root `z`, the rational certificate `a`,
and `H`. -/
def encVerifierInput {r M : ℕ} (ell : Fin M → Fin r → ZMod 2) (p : Fin M → ℚ)
    (Dl : List (Fin r → ZMod 2)) (z : Fin r → ZMod 2) (a : Fin M → ℚ) (H : ℕ) : List Bool :=
  encNat r ++ encNat M ++ encList encVec (List.ofFn ell) ++ encList encRat (List.ofFn p) ++
    encList encVec Dl ++ encVec z ++ encList encRat (List.ofFn a) ++ encNat H

end InteractionElim.Main


