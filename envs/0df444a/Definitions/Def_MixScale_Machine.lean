-- Prove2me | Definitions.Def_MixScale_Machine
-- name    : MixScale_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:10:36.100761+00:00
-- url     : https://prove2.me/theorems/c4852f97-4273-44e9-8e97-ac5d7b70f1ce
-- title:
--   The sampling real RAM with an adversarial approximate profile oracle
-- statement:
--   The model of computation in which "global polynomial-time algorithm" is read. The paper says: "Our polynomial-time guarantees use the real-arithmetic model and the efficient profile evaluation assumptions of definition A.1" (p.3) and "We use real arithmetic with elementary function evaluation and the effective profile access of definition A.1" (p.48). It gives no instruction list, so this machine is a reading.
--
--   A program is one finite list of instructions, the same for all inputs. The instructions are the published `SmaleNinth` real RAM core (exact $+,-,\times,\div$, rational literals, indirect memory access through integer pointers, comparison jumps); a pointer-to-real cast; $\sqrt{\cdot},\exp,\log,\cos,\sin$ of a register; a fair coin; a standard Gaussian draw (the algorithm draws $g,g'\sim N(0,I_d)$ in (43)); `sample`, which writes the next i.i.d. sample of $\mathbb R^d$ to memory at cost $d$; a profile query `prof`, which returns $O(j,u,\eta)$ at cost $\lceil\mathrm{evalC}(1+1/\eta)^{\mathrm{evalD}}\rceil$; and `halt`.
--
--   The oracle is adversarial: guarantees are stated for every $O$ with $|O(j,u,\eta)-H^{(j)}(u)|\le\eta$ whenever $|u|\le h_0$, $\eta>0$, $j=0,1,2$. The only access to the unknown mixture is `sample`; the only access to $H$ is `prof`; $\chi$ is not accessible.
--
--   The input memory holds $d,k,B,\kappa,w_\star,\gamma,\varepsilon,\delta$ and the profile constants. The output tuple is read from fixed memory cells after `halt`. The randomness of a run is a product of a coin tape, a Gaussian tape and an i.i.d. sample stream.
--
--   `RunGuarantee` is the guarantee on one input: on every run the program halts within a work budget and a sample budget and outputs a legal tuple (equal weights in the equal class), and on a measurable set of runs of probability at least $1-\delta$ the output has $D_{\mathrm{par}}\le\varepsilon$.
--
--   **Formalization Note** Admissible programs have rational literals only, so a literal cannot smuggle in the unknown parameters; the profile constants are inputs. Sample counts and work are worst-case, in line with "All branches have a predetermined polynomial operation budget" (p.48).
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), p.3 (PDF p.5); Definition A.1 item 3, p.13; (43), p.25; Appendix G.2–G.3, p.48 (PDF p.50)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MixScale_Profile
import Definitions.Def_MixScale_Model

open MeasureTheory ProbabilityTheory

namespace MixScale

/-!
# The sampling real RAM with an approximate profile oracle

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*,
STOC 2027 submission manuscript (sha256 5277f95e…7c6c). p.3 (PDF p.5): "Our polynomial-time
guarantees use the real-arithmetic model and the efficient profile evaluation assumptions of
definition A.1"; Definition A.1 item 3, p.13 (PDF p.15): "Evaluations of `H, H′, H″` to error
`η_eval` can be obtained in time polynomial in `η_eval⁻¹`, with fixed degree"; Appendix G.3, p.48
(PDF p.50): "We use real arithmetic with elementary function evaluation and the effective profile
access of definition A.1"; (43), p.25: the algorithm draws `g, g′ ∼ N(0, I_d)`; p.48: "All branches
have a predetermined polynomial operation budget". No instruction list is given, so this machine is
a reading of these sentences. It follows the pattern of `GaussMixHH.Machine` (41014cbf).

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (exact `+ − × ÷`,
literals, indirect load and store through integer pointers, pointer set, copy, increment and
decrement, and the comparison jumps `r ≤ 0` and `p ≤ p′`).

**Formalization Note.**
* Extensions: a pointer-to-real cast; `√`, `exp`, `log`, `cos`, `sin` of a register (elementary
  function evaluation; `Real.sqrt`, `Real.log` are Lean-total: `√x = 0` for `x < 0`,
  `log 0 = 0`, `log x = log |x|`); a fair coin; a standard Gaussian draw; `sample`; the profile
  oracle `prof`; `halt`.
* Real literals are rational and the core `accept`/`reject` do not occur (`Admissible`). This
  restricts the existentially chosen program, never the input. No constructor carries a function.
  The profile constants are inputs, not literals.
* Input layout (`initState`): pointer `0` holds `d`, pointer `1` holds `k`, all other pointers
  `0`; memory cells `0, 1, …, 18` hold `d, k, B, κ, w★, γ, ε, δ, q, α, c₀, λ, z₀, C_χ, h₀, Hb 0,
  Hb 1, Hb 2, Hb 3` (`inputList`); every other cell is `0`.
* Output layout (`output`): with stride `s = d + d² + 1`, component `j : Fin k` (0-based) has center
  coordinate `i` in cell `−(1 + j s + i)`, scale entry `(a, b)` in cell `−(1 + j s + d + a d + b)` and
  weight in cell `−(1 + j s + d + d²)`; the output is read from memory after `halt`.
* `sample q` writes the coordinates of the next unread sample `X ∈ ℝ^d` to cells `p[q], …,
  p[q] + d − 1`. It is the only access the program has to the unknown mixture.
* `prof j dst a e` sets `r[dst] := O j r[a] r[e]`, where `O` is the oracle. The oracle is
  adversarial: the guarantees are stated for every `O` with `|O j u η − H^{(j)}(u)| ≤ η` whenever
  `|u| ≤ h₀` and `η > 0` (`AdmissibleOracle`), `j = 0, 1, 2`; outside that range its answers are
  arbitrary. This is the only access the program has to `H`. The profile `χ` is never accessible.
* Cost: every executed instruction adds `1` to `work`, except `sample`, which adds `d`, and
  `prof j dst a e`, which adds `⌈evalC · (1 + 1/r[e])^evalD⌉₊` if `r[e] > 0` and `1` otherwise
  ("time polynomial in `η⁻¹`, with fixed degree"). An invalid program counter is stuck and
  charged, so only `halt` halts. After `halt` the state stutters at no cost. `samplesUsed`
  counts the executed `sample` instructions.
* Randomness: a tape of independent fair bits (one per executed `coin`), a tape of independent
  standard Gaussians (one per executed `gauss`), and the i.i.d. sample stream (the `n`-th executed
  `sample` reads entry `n`). `sampleSpace μ` is the product of the three laws, with the stream
  i.i.d. `μ`.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerReal d q`: `r[d] := (p[q] : ℝ)`.
* `sqrt`, `exp`, `log`, `cos`, `sin` `d a`: `r[d] := f(r[a])`.
* `coin d`: `r[d] := 1` if the next coin is `true`, else `0`.
* `gauss d`: `r[d] :=` the next entry of the Gaussian tape.
* `sample q`: `M[p[q] + i] := X i` for `i < d`, where `X` is the next unread sample.
* `prof j d a e`: `r[d] := O j r[a] r[e]` (the `j`-th derivative of `H` at `r[a]`, tolerance `r[e]`).
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerReal (dst pointer : ℕ)
  | sqrt (dst src : ℕ)
  | exp (dst src : ℕ)
  | log (dst src : ℕ)
  | cos (dst src : ℕ)
  | sin (dst src : ℕ)
  | coin (dst : ℕ)
  | gauss (dst : ℕ)
  | sample (pointer : ℕ)
  | prof (which : Fin 3) (dst arg tol : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every dimension and every input. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P`; extension instructions are placeholders, always dispatched by
`step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A profile oracle: `O j u η` is the answer to the query "`H^{(j)}(u)` to tolerance `η`". -/
abbrev Oracle := Fin 3 → ℝ → ℝ → ℝ

/-- The oracle answers every query with `|u| ≤ h₀` and `η > 0` within `η` of
`H^{(j)}(u)` (derivatives within `[−h₀, h₀]`), `j = 0, 1, 2` (Definition A.1, item 3). -/
def AdmissibleOracle (S : ProfileSpec) (O : Oracle) : Prop :=
  ∀ (j : Fin 3) (u η : ℝ), |u| ≤ S.h0 → 0 < η →
    |O j u η - iteratedDerivWithin (j : ℕ) S.H (Set.Icc (-S.h0) S.h0) u| ≤ η

/-- A machine state: the core configuration, the coin and Gaussian tape cursors, the number of
samples read, the halted flag and the work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  coinCursor : ℕ
  gaussCursor : ℕ
  samplesUsed : ℕ
  halted : Bool
  work : ℕ

/-- The randomness of a run in dimension `d`: coin tape, Gaussian tape, sample stream. -/
abbrev Omega (d : ℕ) := (ℕ → Bool) × (ℕ → ℝ) × (ℕ → Vec d)

/-- Write `x ∈ ℝ^d` to the memory cells `base, …, base + d − 1`. -/
noncomputable def writeSample {d : ℕ} (mem : ℤ → ℝ) (base : ℤ) (x : Vec d) : ℤ → ℝ :=
  fun a => if h : base ≤ a ∧ a - base < d then x ⟨(a - base).toNat, by omega⟩ else mem a

/-- The work charged for a profile query with tolerance `η`. -/
noncomputable def profCost (S : ProfileSpec) (η : ℝ) : ℕ :=
  if 0 < η then ⌈S.evalC * (1 + 1 / η) ^ S.evalD⌉₊ else 1

/-- One step of `P` in dimension `d` with oracle `O` on the randomness `ω`. -/
noncomputable def step (S : ProfileSpec) (P : Program) (d : ℕ) (O : Oracle) (ω : Omega d)
    (s : State) : State :=
  if s.halted then s else
    let t : State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    let setReg (r : ℕ) (v : ℝ) : State :=
      { t with core := { t.core with regs := Function.update s.core.regs r v } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerReal r q) => setReg r (s.core.ptrs q : ℝ)
    | some (.sqrt r a) => setReg r (Real.sqrt (s.core.regs a))
    | some (.exp r a) => setReg r (Real.exp (s.core.regs a))
    | some (.log r a) => setReg r (Real.log (s.core.regs a))
    | some (.cos r a) => setReg r (Real.cos (s.core.regs a))
    | some (.sin r a) => setReg r (Real.sin (s.core.regs a))
    | some (.coin r) =>
        { setReg r (if ω.1 s.coinCursor then 1 else 0) with coinCursor := s.coinCursor + 1 }
    | some (.gauss r) =>
        { setReg r (ω.2.1 s.gaussCursor) with gaussCursor := s.gaussCursor + 1 }
    | some (.sample q) =>
        { t with
          work := s.work + d
          samplesUsed := s.samplesUsed + 1
          core := { t.core with
            mem := writeSample s.core.mem (s.core.ptrs q) (ω.2.2 s.samplesUsed) } }
    | some (.prof j r a e) =>
        { setReg r (O j (s.core.regs a) (s.core.regs e)) with
          work := s.work + profCost S (s.core.regs e) }
    | some .halt => { t with halted := true }

/-- The state after `n` steps from `s₀`. -/
noncomputable def run (S : ProfileSpec) (P : Program) (d : ℕ) (O : Oracle) (s₀ : State)
    (ω : Omega d) (n : ℕ) : State :=
  (step S P d O ω)^[n] s₀

/-- The input list `d, k, B, κ, w★, γ, ε, δ, q, α, c₀, λ, z₀, C_χ, h₀, Hb 0, …, Hb 3`. -/
noncomputable def inputList (S : ProfileSpec) (d k : ℕ) (B κ wstar γ ε δ : ℝ) : List ℝ :=
  [(d : ℝ), (k : ℝ), B, κ, wstar, γ, ε, δ, S.q, S.α, S.c0, S.lam, S.z0, S.Cχ, S.h0,
    S.Hb 0, S.Hb 1, S.Hb 2, S.Hb 3]

/-- The initial state: program counter, registers, cursors and work `0`; pointer `0` holds `d`,
pointer `1` holds `k`; memory holds `inputList` from cell `0`, every other cell is `0`. -/
noncomputable def initState (S : ProfileSpec) (d k : ℕ) (B κ wstar γ ε δ : ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun q => if q = 0 then (d : ℤ) else if q = 1 then (k : ℤ) else 0,
      fun a => if 0 ≤ a then (inputList S d k B κ wstar γ ε δ).getD a.toNat 0 else 0⟩,
    0, 0, 0, false, 0⟩

/-- The output stride `d + d² + 1`. -/
def outStride (d : ℕ) : ℕ := d + d * d + 1

/-- The output tuple read from memory (layout in the module note). -/
noncomputable def output (d k : ℕ) (s : State) : Params d k :=
  fun j =>
    (WithLp.toLp 2 (fun i : Fin d => s.core.mem (-(1 + (j : ℤ) * outStride d + (i : ℤ)))),
      Matrix.of (fun a b : Fin d =>
        s.core.mem (-(1 + (j : ℤ) * outStride d + d + (a : ℤ) * d + (b : ℤ)))),
      s.core.mem (-(1 + (j : ℤ) * outStride d + d + (d : ℤ) * d)))

/-- The fair-coin tape. -/
noncomputable def coinTape : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

/-- The tape of independent standard Gaussians. -/
noncomputable def gaussTape : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

open Classical in
/-- The i.i.d. sample stream with marginal `μ` (the zero measure if `μ` is not a probability
measure). -/
noncomputable def streamLaw {d : ℕ} (μ : Measure (Vec d)) : Measure (ℕ → Vec d) :=
  if h : IsProbabilityMeasure μ then
    haveI := h
    Measure.infinitePi (fun _ : ℕ => μ)
  else 0

/-- The law of the randomness of a run: coins, Gaussians and an i.i.d. `μ` sample stream,
mutually independent. -/
noncomputable def sampleSpace {d : ℕ} (μ : Measure (Vec d)) : Measure (Omega d) :=
  coinTape.prod (gaussTape.prod (streamLaw μ))

/-- The guarantee of a program `P` on one input, for weight class `W`, truth `Θ` with component
laws `Pc` and oracle `O`, with time budget `T` and sample budget `Nmax`:
1. on every `ω` the run halts, with work at most `T` and at most `Nmax` samples, and outputs a
   legal tuple (with all weights `1/k` if `W = eq`);
2. on a measurable set of `ω` of probability at least `1 − δ`, the output has `D_par ≤ ε`. -/
def RunGuarantee (S : ProfileSpec) (P : Program) (W : WeightClass) {d k : ℕ}
    (B κ wstar γ ε δ : ℝ) (Θ : Params d k) (Pc : Fin k → Measure (Vec d)) (O : Oracle)
    (T Nmax : ℝ) : Prop :=
  (∀ ω : Omega d, ∃ n,
      (run S P d O (initState S d k B κ wstar γ ε δ) ω n).halted = true ∧
      ((run S P d O (initState S d k B κ wstar γ ε δ) ω n).work : ℝ) ≤ T ∧
      ((run S P d O (initState S d k B κ wstar γ ε δ) ω n).samplesUsed : ℝ) ≤ Nmax ∧
      IsLegal κ (output d k (run S P d O (initState S d k B κ wstar γ ε δ) ω n)) ∧
      (W = .eq → EqualWeights (output d k (run S P d O (initState S d k B κ wstar γ ε δ) ω n)))) ∧
    ∃ E : Set (Omega d), MeasurableSet E ∧
      E ⊆ {ω | ∀ n, (run S P d O (initState S d k B κ wstar γ ε δ) ω n).halted = true →
        Dpar (output d k (run S P d O (initState S d k B κ wstar γ ε δ) ω n)) Θ ≤ ε} ∧
      1 - δ ≤ (sampleSpace (mixLaw Θ Pc) E).toReal

end MixScale


