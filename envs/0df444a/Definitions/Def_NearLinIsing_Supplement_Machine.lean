-- Prove2me | Definitions.Def_NearLinIsing_Supplement_Machine
-- name    : NearLinIsing_Supplement_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:37:42.062627+00:00
-- url     : https://prove2.me/theorems/135660b8-e94f-4c3a-b405-42a6dea1425c
-- title:
--   The randomized real-arithmetic machine of §2.6, its work, output law and input layout, and total variation between measures
-- statement:
--   Theorems 1.2, 1.3 and A.1 assert that algorithms exist. To state this, programs are taken from a fixed, deep-embedded machine whose instruction set is the computational model of §2.6: "Work counts arithmetic operations, integer rounding, comparisons, evaluation of elementary functions, and generation of uniform and geometric random variables. For continuous spins we also permit evaluation of Bessel ratios and generation of Poisson and beta random variables."
--
--   A **program** is a finite list of instructions. Its core is the published real pointer machine (real registers, integer pointer registers, a real memory indexed by $\mathbb Z$, exact $+,-,\times,\div$, rational literals, indirect load and store, pointer moves, the comparison jumps, `accept` and `reject`). The added instructions, each at unit cost, are:
--
--   1. integer rounding $\lfloor x\rfloor$, $\lceil x\rceil$, also into a pointer register, and pointer-to-real;
--   2. the elementary functions $\exp$, $\log$, $\sqrt{\cdot}$, $\sin$, $\cos$, $\arctan$;
--   3. a uniform draw from $[0,1]$, and geometric, Poisson and beta draws;
--   4. the Bessel ratio $I_k(x)/I_0(x)$, where $I_k$ is the modified Bessel function of the first kind.
--
--   Randomness is one tape of independent uniform $[0,1]$ values. Every draw reads the next value $U$; a geometric, Poisson or beta draw returns the quantile $F^{-1}(U)=\inf\{x: U\le F(x)\}$ of its law, which has exactly that law. A program is **admissible** if all its literals are rational, and **discrete** if it uses no continuous-spin primitive (Bessel ratio, Poisson draw, beta draw).
--
--   The **work** of a run is the number of executed instructions until the first halted state (an `accept` or `reject`), and $+\infty$ if the run never halts; the **expected work** is its integral over the tape. The input graph is given by indexed incidence lists in memory cells $0,1,2,\dots$: $n$, $m$, the number of real parameters, the parameters (such as $\beta$, $\varepsilon$), the endpoints of every edge, every degree, the start address of every incidence list, and the lists. The output is read from memory cells $-1,-2,\dots$ of the halted state, and the **output law** is the law of this vector over the tape on halting runs.
--
--   Finally, for measures $\rho,\pi$ on the same measurable space,
--
--   $$d_{TV}(\rho,\pi)=\sup_{A\text{ measurable}}|\rho(A)-\pi(A)|\qquad(\S2.1).$$
--
--   **Formalization Note** The literals are restricted to rationals because an arbitrary real literal would be non-uniform advice, which the paper's model does not have; this only shrinks the set of programs, so the existence statements become stronger. A program counter outside the program is stuck and never halts. Geometric draws count failures before the first success (Mathlib's `geometricMeasure`). $I_k$ is the published series `QueueingFundamentals.Transient.besselI`, which equals the paper's integral $\frac1{2\pi}\int_0^{2\pi}e^{x\cos\theta}\cos(k\theta)\,d\theta$ for integer $k$.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, §2.6 (computational model), p. 9; §2.1 (total variation), p. 7; I_k, p. 2; Bessel ratios r_k, p. 8

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_QueueingFundamentals_Transient_besselI
import Definitions.Def_NearLinIsing_IncGraph
import Definitions.Def_NearLinIsing_Prog

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NearLinIsing

namespace Supplement

/-!
# The randomized real-arithmetic machine of §2.6

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, §2.6, p. 9: "The graph is given by indexed incidence lists. Work
counts arithmetic operations, integer rounding, comparisons, evaluation of elementary functions,
and generation of uniform and geometric random variables. For continuous spins we also permit
evaluation of Bessel ratios and generation of Poisson and beta random variables. These are
arithmetic-work guarantees in a real-arithmetic model."

Theorems 1.2, 1.3 and A.1 assert that an algorithm exists ("has an ε-approximate sampler", "there
are randomized algorithms"). They quantify over the programs of this deep-embedded machine: a
program is a finite list of instructions, no instruction carries a Lean function, and the input is
readable only through memory.

**Formalization Note.**
* The core is the published real pointer machine `SmaleNinth.RAMInstr` (real registers, integer
  pointer registers, real memory `ℤ → ℝ`, exact `+ − × ÷` with `x / 0 = 0`, literals, indirect
  load and store, pointer set/copy/increment/decrement, the comparison jumps `r ≤ 0` and `p ≤ p'`,
  `accept`, `reject`).
* Added, each at unit cost, exactly the primitives §2.6 lists: integer rounding `⌊·⌋`, `⌈·⌉` (also
  into a pointer register, `toPtr`, and back, `ofPtr`); the elementary functions `exp`, `log`
  (`Real.log`, `log 0 = 0`), `√`, `sin`, `cos`, `arctan`; a uniform `[0, 1]` draw; geometric,
  Poisson and beta draws; and the Bessel ratio `I_k(x)/I_0(x)`.
* `Admissible`: every real literal of the program is rational (an arbitrary real literal would be
  non-uniform advice, which the paper's model does not have).
* `Discrete`: the program uses none of the continuous-spin primitives (Bessel ratio, Poisson draw,
  beta draw). Theorem 1.3 (Potts) is stated for such programs; Theorems 1.2 and A.1 (XY) may use
  them.
* Randomness: one tape of i.i.d. uniform `[0, 1]` values, the base mission's `Tape` with law
  `tapeLaw`. Every draw instruction reads the next cell `U`; `unif` writes `U`, and a geometric,
  Poisson or beta draw writes the quantile `F⁻¹(U) = inf {x : U ≤ F(x)}` of its law, which has
  exactly that law. So each draw has its exact law and the draws are independent.
* Geometric draws use Mathlib's `geometricMeasure p` on `{0, 1, 2, …}` (`P(k) = (1 − p)^k p`, the
  number of failures before the first success); parameters outside `(0, 1]` give `0`. Poisson
  draws use `poissonMeasure`, with a negative mean read as `0`. Beta draws use Mathlib's
  `betaMeasure a b`; nonpositive parameters give `0`.
* Bessel ratio: `r[d] := I_k(r[x]) / I_0(r[x])` with `k = |⌊r[k]⌋|`. `I_k` is the published
  `QueueingFundamentals.Transient.besselI`, the power series `∑_j (x/2)^{k+2j}/(j!(k+j)!)`; for an
  integer order it equals the paper's integral `I_k(x) = (1/2π) ∫_0^{2π} e^{x cos θ} cos(kθ) dθ`
  (p. 2), DLMF 10.25.2 and 10.32.3.
* Every executed instruction costs one unit of work. A state whose program counter holds the core
  `accept` or `reject` is halted. A program counter outside the program is stuck and never halts,
  so its work is `⊤`.
* Input: memory cells `0, 1, 2, …` hold `graphInput G params` (below); every other cell, register
  and pointer is `0`. Output: memory cells `−1, −2, …` of the halted state.
-/

/-- The elementary functions with a unit-cost instruction. -/
inductive Elem : Type
  | exp
  | log
  | sqrt
  | sin
  | cos
  | arctan

/-- The value of an elementary function (`Real.log 0 = 0`, `Real.sqrt` of a negative is `0`). -/
noncomputable def Elem.eval : Elem → ℝ → ℝ
  | .exp => Real.exp
  | .log => Real.log
  | .sqrt => Real.sqrt
  | .sin => Real.sin
  | .cos => Real.cos
  | .arctan => Real.arctan

/-- The non-uniform draws with a unit-cost instruction. -/
inductive Draw : Type
  /-- geometric with success probability `a` (failures before the first success) -/
  | geometric
  /-- Poisson with mean `a` -/
  | poisson
  /-- beta with parameters `(a, b)` -/
  | beta

/-- The law of a draw with parameters `(a, b)`, as a measure on `ℝ`. -/
noncomputable def Draw.law : Draw → ℝ → ℝ → Measure ℝ
  | .geometric, a, _ =>
      if h : 0 < a ∧ a ≤ 1 then
        (geometricMeasure (⟨a, h.1.le, h.2⟩ : unitInterval)).map (fun k : ℕ => (k : ℝ))
      else Measure.dirac 0
  | .poisson, a, _ => (poissonMeasure (Real.toNNReal a)).map (fun k : ℕ => (k : ℝ))
  | .beta, a, b => if 0 < a ∧ 0 < b then betaMeasure a b else Measure.dirac 0

/-- The quantile `F⁻¹(u) = inf {x : u ≤ F(x)}` of a law `μ` on `ℝ` with distribution function
`F = cdf μ`. For a probability measure and `u ∈ (0, 1)`, `F⁻¹(U)` with `U` uniform has law `μ`. -/
noncomputable def quantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | u ≤ cdf μ x}

/-- The Bessel ratio `I_k(x) / I_0(x)` (§2.6; the `r_k = I_k(log β)/I_0(log β)` of p. 8). -/
noncomputable def besselRatio (k : ℕ) (x : ℝ) : ℝ :=
  QueueingFundamentals.Transient.besselI k x / QueueingFundamentals.Transient.besselI 0 x

/-- One instruction of the machine. -/
inductive Instr : Type
  /-- A core instruction of `SmaleNinth.RAMInstr`. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `r[d] := ⌊r[a]⌋`. -/
  | floor (d a : ℕ)
  /-- `r[d] := ⌈r[a]⌉`. -/
  | ceil (d a : ℕ)
  /-- `p[d] := ⌊r[a]⌋` (integer rounding into a pointer register). -/
  | toPtr (d a : ℕ)
  /-- `r[d] := p[a]`. -/
  | ofPtr (d a : ℕ)
  /-- `r[d] := f(r[a])` for an elementary function `f`. -/
  | elem (f : Elem) (d a : ℕ)
  /-- `r[d] := I_k(r[x]) / I_0(r[x])` with `k = |⌊r[k]⌋|`. -/
  | bessel (d k x : ℕ)
  /-- `r[d] :=` the next uniform `[0, 1]` tape value. -/
  | unif (d : ℕ)
  /-- `r[d] :=` a draw from `D.law r[a] r[b]`, computed from the next tape value. -/
  | draw (D : Draw) (d a b : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program : Type := List Instr

/-- Every real literal of the program is rational. -/
def Program.Admissible (P : Program) : Prop :=
  ∀ i ∈ P, ∀ (dst : ℕ) (c : ℝ), i = .core (.const dst c) → ∃ r : ℚ, c = (r : ℝ)

/-- The instruction is one of the continuous-spin primitives of §2.6 (Bessel ratio, Poisson draw,
beta draw). -/
def Instr.IsContinuousPrim : Instr → Prop
  | .bessel _ _ _ => True
  | .draw .poisson _ _ _ => True
  | .draw .beta _ _ _ => True
  | _ => False

/-- The program uses none of the continuous-spin primitives. -/
def Program.Discrete (P : Program) : Prop :=
  ∀ i ∈ P, ¬ i.IsContinuousPrim

/-- The core table of `P`; positions holding an added instruction carry a placeholder that `step`
never executes. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun i => match i with
    | .core c => c
    | _ => .const 0 0

/-- A machine state: the core configuration and the tape cursor. -/
structure State where
  /-- program counter, real registers, pointer registers, real memory -/
  cfg : SmaleNinth.RAMConfig
  /-- the number of tape cells read -/
  cursor : ℕ

/-- The state is halted: its program counter holds the core `accept` or `reject`. -/
def Halted (P : Program) (s : State) : Prop :=
  P[s.cfg.pc]? = some (.core .accept) ∨ P[s.cfg.pc]? = some (.core .reject)

/-- Advance the program counter with new real registers and pointer registers. -/
def State.next (s : State) (regs : ℕ → ℝ) (ptrs : ℕ → ℤ) : State :=
  { s with cfg := ⟨s.cfg.pc + 1, regs, ptrs, s.cfg.mem⟩ }

/-- Advance the program counter, write `v` into real register `d`, and consume one tape cell. -/
def State.nextDraw (s : State) (d : ℕ) (v : ℝ) : State :=
  { cfg := ⟨s.cfg.pc + 1, Function.update s.cfg.regs d v, s.cfg.ptrs, s.cfg.mem⟩,
    cursor := s.cursor + 1 }

open Classical in
/-- One step of `P` on the tape `ω`. A halted state stays put; an invalid program counter is
stuck (it stays put and never halts). The tape occurs only in the draw instructions. -/
noncomputable def step (P : Program) (ω : Tape) (s : State) : State :=
  if Halted P s then s else
  let r := s.cfg.regs
  let p := s.cfg.ptrs
  match P[s.cfg.pc]? with
  | none => s
  | some (.core _) => { s with cfg := SmaleNinth.RAMStep (coreProgram P) s.cfg }
  | some (.floor d a) => s.next (Function.update r d (⌊r a⌋ : ℝ)) p
  | some (.ceil d a) => s.next (Function.update r d (⌈r a⌉ : ℝ)) p
  | some (.toPtr d a) => s.next r (Function.update p d ⌊r a⌋)
  | some (.ofPtr d a) => s.next (Function.update r d (p a : ℝ)) p
  | some (.elem f d a) => s.next (Function.update r d (f.eval (r a))) p
  | some (.bessel d k x) => s.next (Function.update r d (besselRatio (⌊r k⌋).natAbs (r x))) p
  | some (.unif d) => s.nextDraw d ((ω s.cursor : unitInterval) : ℝ)
  | some (.draw D d a b) =>
      s.nextDraw d (quantile (D.law (r a) (r b)) ((ω s.cursor : unitInterval) : ℝ))

/-- The initial state on input memory `x`. -/
def initState (x : ℤ → ℝ) : State := ⟨⟨0, fun _ => 0, fun _ => 0, x⟩, 0⟩

/-- The state after `t` steps of `P` on input `x` and tape `ω`. -/
noncomputable def run (P : Program) (x : ℤ → ℝ) (ω : Tape) (t : ℕ) : State :=
  (step P ω)^[t] (initState x)

/-- The run of `P` on input `x` and tape `ω` halts. -/
def HaltsOn (P : Program) (x : ℤ → ℝ) (ω : Tape) : Prop :=
  ∃ t, Halted P (run P x ω t)

open Classical in
/-- **Work** of a run: the number of instructions executed before the first halted state, `⊤` if
the run never halts. -/
noncomputable def haltTime (P : Program) (x : ℤ → ℝ) (ω : Tape) : ℕ∞ :=
  if h : HaltsOn P x ω then (Nat.find h : ℕ∞) else ⊤

/-- **Expected work**: the lower integral of the work over the tape law (`⊤` whenever the run fails
to halt with positive probability). -/
noncomputable def expectedWork (P : Program) (x : ℤ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ((haltTime P x ω : ℕ∞) : ℝ≥0∞) ∂tapeLaw

/-- The first halted state (the initial state if the run never halts). -/
noncomputable def finalState (P : Program) (x : ℤ → ℝ) (ω : Tape) : State :=
  run P x ω (haltTime P x ω).toNat

/-- The output vector of length `len`: memory cells `−1, −2, …, −len` of the first halted
state. -/
noncomputable def outVec (P : Program) (x : ℤ → ℝ) (len : ℕ) (ω : Tape) : Fin len → ℝ :=
  fun i => (finalState P x ω).cfg.mem (-(i : ℤ) - 1)

/-- The **output law**: the law of the output vector over the tape, on the halting runs. -/
noncomputable def outLaw (P : Program) (x : ℤ → ℝ) (len : ℕ) : Measure (Fin len → ℝ) :=
  (tapeLaw.restrict {ω | HaltsOn P x ω}).map (outVec P x len)

/-- The start address of the incidence list of `v` in `graphInput G params`. -/
def listStart (G : IncGraph) (p : ℕ) (v : Fin G.n) : ℕ :=
  3 + p + 2 * G.m + 2 * G.n + ∑ u ∈ Finset.univ.filter (fun u : Fin G.n => u < v), (G.inc u).length

/-- The input as a list of reals: `n, m`, the number `p` of real parameters, the parameters, the
endpoint pair of every edge `e = 0, …, m−1`, the degree of every vertex, the start address of every
incidence list, and the incidence lists themselves, concatenated in vertex order (the indexed
incidence lists of §2.6). -/
noncomputable def inputList (G : IncGraph) (params : List ℝ) : List ℝ :=
  [(G.n : ℝ), (G.m : ℝ), (params.length : ℝ)] ++ params
    ++ (List.finRange G.m).flatMap
        (fun e => [(((G.ends e).1 : ℕ) : ℝ), (((G.ends e).2 : ℕ) : ℝ)])
    ++ (List.finRange G.n).map (fun v => ((G.inc v).length : ℝ))
    ++ (List.finRange G.n).map (fun v => (listStart G params.length v : ℝ))
    ++ (List.finRange G.n).flatMap (fun v => (G.inc v).map (fun e => ((e : ℕ) : ℝ)))

/-- The input memory: cell `a ≥ 0` holds entry `a` of `inputList G params`, every other cell `0`. -/
noncomputable def graphInput (G : IncGraph) (params : List ℝ) : ℤ → ℝ :=
  fun a => if 0 ≤ a then (inputList G params).getD a.toNat 0 else 0

/-- **Total variation distance** `d_TV(ρ, π) = sup_{A measurable} |ρ(A) − π(A)|` of two finite
measures on the same measurable space (§2.1, p. 7). -/
noncomputable def tvM {α : Type} [MeasurableSpace α] (ρ π : Measure α) : ℝ :=
  ⨆ A : {A : Set α // MeasurableSet A}, |ρ.real A.1 - π.real A.1|

end Supplement

end NearLinIsing


