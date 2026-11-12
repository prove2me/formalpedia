-- Prove2me | Definitions.Def_GMMPostSamp_Main_Machine
-- name    : GMMPostSamp_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:25:55.61488+00:00
-- url     : https://prove2.me/theorems/736c0b71-320a-4268-a18c-938d912bfac9
-- title:
--   The randomized real RAM of §2.1 (SmaleNinth core, √, exp, log, Γ, uniform and Gaussian tapes, CDF/quantile of fixed 1-D families, oracle calls), input/output layout and Problem 1
-- statement:
--   The computational model of §2.1 ("the real RAM model, where standard operations take $O(1)$ time … explicit one-dimensional sampling, CDF, or inverse CDF evaluation takes $O(1)$ time … for standard distributions") is read as the following unit-cost machine. Its core is the published real pointer machine `SmaleNinth.RAMInstr`: exact $+,-,\times,\div$ on real registers, real literals, indirect real memory through integer pointer registers, pointer set/copy/increment/decrement, and the jumps "$r\le0$" and "$p\le p'$". It adds pointer $+,-,\times$; conversion of an integer-valued real to a pointer (a non-integer makes the machine stuck, so there is no floor); pointer-to-real; $\sqrt{\cdot}$, $\exp$, $\log$ and $\Gamma$; a draw from a tape of i.i.d. $\mathrm{Unif}[0,1]$ values and a draw from a tape of i.i.d. $\mathcal N(0,1)$ values; the CDF $F(x)=P(X\le x)$ and the quantile $F^{-1}(u)=\inf\{x:u\le F(x)\}$ of a **fixed** list of families — $\mathcal N(m,s^2)$, $\mathrm{Beta}(p,q)$ and the noncentral $\chi^2_\nu(\lambda)$ — with parameters read from registers; an **oracle call** that applies a given oracle map to a block of memory cells (only Proposition 5 uses a non-empty oracle, $\nabla V$); and `halt`.
--
--   A program is **admissible** if all its real literals are rational and it does not use the core's `accept`/`reject`. Each executed instruction costs one step. The input list occupies memory cells $0,1,\dots$; outputs are read from cells $-1,-2,\dots$ at the first halted state: labels as values $1,\dots,k$, permutations as $c(i)+1$, parameters as $w_1,\dots,w_k$ followed by the coordinates of $\mu_1,\dots,\mu_k$, points as coordinates. A run that never halts, or an invalid output, yields `none`. The randomness is the tape pair with law $\mathrm{Unif}[0,1]^{\otimes\mathbb N}\otimes\mathcal N(0,1)^{\otimes\mathbb N}$; "every run" means every tape pair whose uniform cells lie in $[0,1]$.
--
--   A posterior sampler receives $(k,d,n,\sigma,\delta,\alpha_1,\dots,\alpha_k,x_{[n]})$. **Problem 1** for a program $P$:
--   $$\Pr_{x_{[n]}\sim\text{Model 1}}\Big[\mathrm{TV}\big(\mathrm{Law}_P(x_{[n]}),\pi_x\big)>\delta\Big]\le\delta,$$
--   where $\mathrm{Law}_P(x)$ is the output law on $[k]^n\cup\{\text{none}\}$ over the tapes and $\pi_x$ the label posterior.
--
--   **Formalization Note.** There is no eigensolver, SVD, root-finding or matrix primitive, and no program-supplied distribution: a CDF or quantile instruction for a distribution chosen by the program would sample $\pi_x$ in one step. The Model-1 probability of the failure set is its outer measure under the law of $x_{[n]}$; probabilities of output events are tape-law (outer) measures of their preimages.
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 9 §2.1 (computational model); p. 17 Problem 1

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-!
# The machine: a unit-cost randomized real RAM with uniform and Gaussian tapes

Kumar, Sarkar, Tian, Zhu, *Posterior Sampling in Gaussian Mixture Models Beyond the
Clusterability Threshold*, STOC 2027 submission (manuscript sha256 ba5079cd…), §2.1, p. 9:
"We work in the real RAM model, where standard operations take O(1) time. We also assume that
explicit one-dimensional sampling, CDF, or inverse CDF evaluation takes O(1) time; our
applications only use this for standard distributions (e.g., uniform or Gaussian)."

**Formalization Note (the reading of §2.1).**
* The core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ`: exact `+ − × ÷`
  (`x / 0 = 0`), real literals, indirect real memory `M[p[q]]` through integer pointer
  registers, pointer set/copy/increment/decrement, the jumps `r ≤ 0` and `p ≤ p'`.
* Added (unit cost each): pointer `+ − ×`; `toPtr` (`p := r` when `r` is an integer, otherwise
  the machine is stuck: no floor, no integrality test); `ofPtr` (`r := p`); `√` (`Real.sqrt`),
  `exp`, `log` (`Real.log`, `log 0 = 0`), `Γ` (`Real.Gamma`); `unif` (the next cell of a tape of
  i.i.d. `Unif[0,1]` values); `gauss` (the next cell of a tape of i.i.d. `N(0,1)` values);
  `cdf f` and `icdf f` for the CDF `F(x) = P(X ≤ x)` and the quantile
  `F⁻¹(u) = inf {x : u ≤ F(x)}` of a **fixed** list of one-dimensional families `f`: the normal
  `N(m, s²)`, `Beta(p, q)` and the noncentral `χ²_ν(λ)`, parameters read from registers;
  `query`: the oracle instruction (used only by Proposition 5's `∇V` oracle; every other
  statement runs programs with the empty oracle, under which `query` writes nothing); `halt`.
* There is no eigensolver, no SVD, no root finding and no program-supplied distribution.
* `Admissible`: every real literal is rational, and the core's `accept`/`reject` do not occur.
  Every executed instruction costs one step; only `halt` halts; a program counter outside the
  program stays stuck.
* **Input**: memory cells `0, 1, …, ℓ−1` hold the input list (as reals); every other cell,
  register and pointer is `0`. **Output**: read at the first halted state from memory cells
  `−1, −2, …` (see the decoders). A run that never halts has no output.
* **Randomness**: the tape pair `(u, g)` has law `tapeLaw` = i.i.d. `Unif[0,1]` ⊗ i.i.d. `N(0,1)`.
  "Every run" means every tape pair whose uniform cells lie in `[0, 1]` (`TapeOK`).
-/

namespace Machine

/-- The fixed one-dimensional families with unit-cost CDF and inverse CDF. -/
inductive Family where
  /-- `N(m, s²)` with parameters `(m, s)`. -/
  | normal
  /-- `Beta(p, q)`. -/
  | beta
  /-- The noncentral chi-square `χ²_ν(λ)` with parameters `(ν, λ)`. -/
  | ncChiSq

/-- The density of the central `χ²_ν` law at `x > 0`. -/
noncomputable def chiSqDensity (ν x : ℝ) : ℝ :=
  x ^ (ν / 2 - 1) * Real.exp (-x / 2) / (2 ^ (ν / 2) * Real.Gamma (ν / 2))

/-- The law of the family `f` with parameters `(p₁, p₂)`. -/
noncomputable def familyLaw : Family → ℝ → ℝ → Measure ℝ
  | .normal, m, s => gaussianReal m (s ^ 2).toNNReal
  | .beta, p, q => volume.withDensity fun x =>
      (Set.Icc (0 : ℝ) 1).indicator
        (fun x => ENNReal.ofReal (x ^ (p - 1) * (1 - x) ^ (q - 1) *
          Real.Gamma (p + q) / (Real.Gamma p * Real.Gamma q))) x
  | .ncChiSq, ν, lam => volume.withDensity fun x =>
      (Set.Ioi (0 : ℝ)).indicator
        (fun x => ∑' j : ℕ, ENNReal.ofReal (Real.exp (-lam / 2) * (lam / 2) ^ j /
          (Nat.factorial j) * chiSqDensity (ν + 2 * j) x)) x

/-- The CDF `F(x) = P(X ≤ x)` of the family `f` with parameters `(p₁, p₂)`. -/
noncomputable def familyCdf (f : Family) (p₁ p₂ x : ℝ) : ℝ :=
  (familyLaw f p₁ p₂ (Set.Iic x)).toReal

/-- The quantile `F⁻¹(u) = inf {x : u ≤ F(x)}`. -/
noncomputable def familyQuantile (f : Family) (p₁ p₂ u : ℝ) : ℝ :=
  sInf {x | u ≤ familyCdf f p₁ p₂ x}

/-- An instruction. -/
inductive Instr where
  /-- A `SmaleNinth` core instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `p[dst] := p[a] + p[b]`. -/
  | padd (dst a b : ℕ)
  /-- `p[dst] := p[a] − p[b]`. -/
  | psub (dst a b : ℕ)
  /-- `p[dst] := p[a] * p[b]`. -/
  | pmul (dst a b : ℕ)
  /-- `p[dst] := r[src]` if `r[src]` is an integer; stuck otherwise. -/
  | toPtr (dst src : ℕ)
  /-- `r[dst] := p[src]`. -/
  | ofPtr (dst src : ℕ)
  /-- `r[dst] := √ r[src]`. -/
  | sqrt (dst src : ℕ)
  /-- `r[dst] := exp r[src]`. -/
  | exp (dst src : ℕ)
  /-- `r[dst] := log r[src]`. -/
  | log (dst src : ℕ)
  /-- `r[dst] := Γ(r[src])`. -/
  | gamma (dst src : ℕ)
  /-- `r[dst] :=` the next uniform tape cell. -/
  | unif (dst : ℕ)
  /-- `r[dst] :=` the next Gaussian tape cell. -/
  | gauss (dst : ℕ)
  /-- `r[dst] := F_f(r[x]; r[a], r[b])`. -/
  | cdf (f : Family) (dst x a b : ℕ)
  /-- `r[dst] := F_f⁻¹(r[u]; r[a], r[b])`. -/
  | icdf (f : Family) (dst u a b : ℕ)
  /-- Oracle call: the oracle is applied to the `p[len]` memory cells from `M[p[src]]` on, and
  its answer is written to the memory cells from `M[p[dst]]` on. -/
  | query (src dst len : ℕ)
  /-- Halt. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- An oracle: a map from query lists to answer lists. -/
abbrev Oracle := List ℝ → List ℝ

/-- The empty oracle (every `query` writes nothing). -/
def noOracle : Oracle := fun _ => []

/-- Every real literal is rational, and the core's `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The core table of `P` (extension instructions are placeholders, dispatched by `step`). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state. -/
structure State where
  /-- Program counter, real registers, pointer registers, real memory. -/
  core : SmaleNinth.RAMConfig
  /-- Next unread uniform tape cell. -/
  ucur : ℕ
  /-- Next unread Gaussian tape cell. -/
  gcur : ℕ
  /-- Number of oracle calls so far. -/
  queries : ℕ
  /-- Halted flag. -/
  halted : Bool

/-- A tape pair: uniform cells and Gaussian cells. -/
abbrev Tape := (ℕ → ℝ) × (ℕ → ℝ)

/-- The law of the tapes: i.i.d. `Unif[0,1]` cells, independent of i.i.d. `N(0,1)` cells. -/
noncomputable def tapeLaw : Measure Tape :=
  (Measure.infinitePi fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)).prod
    (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)

/-- A tape pair in the support: every uniform cell lies in `[0, 1]`. -/
def TapeOK (τ : Tape) : Prop := ∀ i, τ.1 i ∈ Set.Icc (0 : ℝ) 1

/-- One step of `P` with oracle `O` on tape `τ`. Halted states do not change. -/
noncomputable def step (P : Program) (O : Oracle) (τ : Tape) (s : State) : State :=
  if s.halted then s else
    let next : SmaleNinth.RAMConfig := { s.core with pc := s.core.pc + 1 }
    let setReg (d : ℕ) (v : ℝ) : State :=
      { s with core := { next with regs := Function.update s.core.regs d v } }
    let setPtr (d : ℕ) (v : ℤ) : State :=
      { s with core := { next with ptrs := Function.update s.core.ptrs d v } }
    match P[s.core.pc]? with
    | none => s
    | some (.core _) => { s with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.padd d a b) => setPtr d (s.core.ptrs a + s.core.ptrs b)
    | some (.psub d a b) => setPtr d (s.core.ptrs a - s.core.ptrs b)
    | some (.pmul d a b) => setPtr d (s.core.ptrs a * s.core.ptrs b)
    | some (.toPtr d a) =>
        if (s.core.regs a : ℝ) = (⌊s.core.regs a⌋ : ℝ) then setPtr d ⌊s.core.regs a⌋ else s
    | some (.ofPtr d a) => setReg d (s.core.ptrs a : ℝ)
    | some (.sqrt d a) => setReg d (Real.sqrt (s.core.regs a))
    | some (.exp d a) => setReg d (Real.exp (s.core.regs a))
    | some (.log d a) => setReg d (Real.log (s.core.regs a))
    | some (.gamma d a) => setReg d (Real.Gamma (s.core.regs a))
    | some (.unif d) =>
        { s with core := { next with regs := Function.update s.core.regs d (τ.1 s.ucur) },
                 ucur := s.ucur + 1 }
    | some (.gauss d) =>
        { s with core := { next with regs := Function.update s.core.regs d (τ.2 s.gcur) },
                 gcur := s.gcur + 1 }
    | some (.cdf f d x a b) =>
        setReg d (familyCdf f (s.core.regs a) (s.core.regs b) (s.core.regs x))
    | some (.icdf f d u a b) =>
        setReg d (familyQuantile f (s.core.regs a) (s.core.regs b) (s.core.regs u))
    | some (.query src dst len) =>
        let xs : List ℝ := List.ofFn fun i : Fin (s.core.ptrs len).toNat =>
          s.core.mem (s.core.ptrs src + i)
        let ys := O xs
        let base := s.core.ptrs dst
        let mem' : ℤ → ℝ := fun z =>
          if base ≤ z ∧ z < base + ys.length then ys.getD (z - base).toNat 0 else s.core.mem z
        { s with core := { next with mem := mem' }, queries := s.queries + 1 }
    | some .halt => { s with core := next, halted := true }

/-- The initial state on the input list `xs`: memory cells `0, …, |xs| − 1` hold `xs`. -/
noncomputable def initState (xs : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then xs.getD z.toNat 0 else 0⟩, 0, 0, 0, false⟩

/-- The state after `t` steps. -/
noncomputable def run (P : Program) (O : Oracle) (xs : List ℝ) (τ : Tape) (t : ℕ) : State :=
  (step P O τ)^[t] (initState xs)

/-- Every run of `P` on `xs` (every tape pair in the support) halts within `T` steps, having made
at most `Q` oracle calls. -/
def RunsWithin (P : Program) (O : Oracle) (xs : List ℝ) (T Q : ℝ) : Prop :=
  ∀ τ : Tape, TapeOK τ → ∃ t : ℕ, (t : ℝ) ≤ T ∧ (run P O xs τ t).halted = true ∧
    ((run P O xs τ t).queries : ℝ) ≤ Q

/-- Every run of `P` on `xs` halts within `T` steps (no oracle). -/
def HaltsWithin (P : Program) (xs : List ℝ) (T : ℝ) : Prop :=
  ∀ τ : Tape, TapeOK τ → ∃ t : ℕ, (t : ℝ) ≤ T ∧ (run P noOracle xs τ t).halted = true

open Classical in
/-- The first halted state of the run, `none` if the run never halts. -/
noncomputable def finalState (P : Program) (O : Oracle) (xs : List ℝ) (τ : Tape) :
    Option State :=
  if h : ∃ t, (run P O xs τ t).halted = true then some (run P O xs τ (Nat.find h)) else none

/-- Output cell `j` (0-based): memory cell `−(j + 1)`. -/
def outCell (s : State) (j : ℕ) : ℝ := s.core.mem (-((j : ℤ) + 1))

open Classical in
/-- A real `v` read as a label in `[k]`: `v = m + 1` with `m : Fin k`; anything else is
invalid. -/
noncomputable def decodeLabel (k : ℕ) (v : ℝ) : Option (Fin k) :=
  if h : ∃ m : Fin k, v = (m : ℝ) + 1 then some (Classical.choose h) else none

open Classical in
/-- The labelling `ι_[n]` in output cells `0, …, n − 1` (values `1, …, k`); `none` if a cell is
not a valid label. -/
noncomputable def decodeLabels (k n : ℕ) (s : State) : Option (Fin n → Fin k) :=
  if h : ∀ j : Fin n, (decodeLabel k (outCell s j)).isSome then
    some fun j => (decodeLabel k (outCell s j)).get (h j)
  else none

open Classical in
/-- A permutation `c ∈ S_k` in output cells `0, …, k − 1` (`c(i) + 1` in cell `i`); `none` if
the cells are not the values of a permutation. -/
noncomputable def decodePerm (k : ℕ) (s : State) : Option (Equiv.Perm (Fin k)) :=
  match decodeLabels k k s with
  | none => none
  | some f => if h : Function.Bijective f then some (Equiv.ofBijective f h) else none

/-- A point of `ℝ^d` from output cells `off, …, off + d − 1`. -/
noncomputable def decodePoint (d off : ℕ) (s : State) : E d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm fun l => outCell s (off + l)

/-- A parameter `θ = (w, µ)` from output cells: `w_i` in cell `i`, coordinate `l` of `µ_i` in
cell `k + d i + l`. -/
noncomputable def decodeParam (k d : ℕ) (s : State) : Param k d :=
  (fun i => outCell s i, fun i => decodePoint d (k + d * i) s)

/-- The coordinates of a point of `ℝ^d` as a list. -/
noncomputable def pointCells {d : ℕ} (x : E d) : List ℝ := List.ofFn fun l => x l

/-- The observations `x_[n]` as a list, `x_1` first, coordinates in order. -/
noncomputable def dataCells {d n : ℕ} (x : Fin n → E d) : List ℝ :=
  (List.ofFn fun j => pointCells (x j)).flatten

/-- A parameter `θ = (w, µ)` as a list: `w_1, …, w_k`, then `µ_1, …, µ_k`. -/
noncomputable def paramCells {k d : ℕ} (θ : Param k d) : List ℝ :=
  List.ofFn θ.1 ++ (List.ofFn fun i => pointCells (θ.2 i)).flatten

/-- The input of a posterior sampler: `k, d, n, σ, δ, α_1, …, α_k, x_[n]`. -/
noncomputable def samplerInput {k d n : ℕ} (σ δ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d) :
    List ℝ :=
  [(k : ℝ), (d : ℝ), (n : ℝ), σ, δ] ++ List.ofFn α ++ dataCells x

/-- The output law of a labelling program on input `xs`, as a mass function on
`Option ([k]^n)` (`none`: no halt, or an invalid output), under the tape law. -/
noncomputable def labelLaw (P : Program) (k n : ℕ) (xs : List ℝ)
    (o : Option (Fin n → Fin k)) : ℝ :=
  (tapeLaw {τ | (finalState P noOracle xs τ).bind (decodeLabels k n) = o}).toReal

/-- `TV(Law(output), π)` for a mass function `p` on `Option ([k]^n)` and a target `π` on
`[k]^n` (extended by `π(none) = 0`). -/
noncomputable def tvLabels {k n : ℕ} (p : Option (Fin n → Fin k) → ℝ)
    (π : (Fin n → Fin k) → ℝ) : ℝ :=
  tvFin p fun o => match o with
    | none => 0
    | some ι => π ι

/-- **Problem 1** for the program `P` at `(k, d, n, σ, α, δ)`: the Model-1 probability of the
set of observations `x_[n]` on which the output law of `P` on `(k, d, n, σ, δ, α, x_[n])` is
more than `δ` away in TV from the label posterior `π_x` is at most `δ`. -/
def SolvesProblem1 (P : Program) (k d n : ℕ) (σ : ℝ) (α : Fin k → ℝ) (δ : ℝ) : Prop :=
  xLaw k d n σ α {x | δ < tvLabels (labelLaw P k n (samplerInput σ δ α x)) (labelPost σ α x)}
    ≤ ENNReal.ofReal δ

end Machine

end GMMPostSamp.Main


