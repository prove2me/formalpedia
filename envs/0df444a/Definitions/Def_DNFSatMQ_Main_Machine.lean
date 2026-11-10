-- Prove2me | Definitions.Def_DNFSatMQ_Main_Machine
-- name    : DNFSatMQ_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:33:21.320743+00:00
-- url     : https://prove2.me/theorems/e0ff5b53-1be7-41e5-96eb-8e430738df61
-- title:
--   Learners and samplers on the fair-coin RAM: EX⁺ stream, MQ and ε oracle, sampler law D_h, Problem 1.1, Definitions 4.1–4.2
-- statement:
--   The paper names no machine model. Its algorithms run here on the published log-cost RAM `TargetedSamplers.Program`: a finite instruction list, each instruction costing $1$ plus the bit lengths it touches, with random access to an input tape and a finite fair-coin tape, a read-once witness tape, one oracle, an output tape and a $\bot$ output.
--
--   **Resources.** The input $n, s$ (or $d, s$) is written in unary. **$\mathrm{EX}^+_f$** is the witness tape, holding a stream of independent uniform samples from $F$, $n$ bits each. **$\mathrm{MQ}_f$** is the oracle on queries $0x$ with $|x| = n$, answered $f(x)$. A real parameter $\varepsilon$ (and $\delta$) is reached only by **comparison queries** $1\,0\,v$ ($1\,1\,v$) asking "$\varepsilon \le v$?" for a rational $v$ written in the query. For Theorem 9.1, `realOracle g θ δ` answers "$g(x) \le v$?".
--
--   **Probabilities.** `probCoinsSamples T F E` is the probability of $E$ for $T$ uniform fair coins and $T$ independent samples from $U_F$; `probCoins T E` for $T$ coins only. `HaltsWithin P τ t`: the run halts with total cost $\le t$ and every coin access is within the supplied tape (`CoinsInBounds`). The past-end sentinel is not an extra parameter input. `outWord` is the output word of a halted run ($\bot$ or no halt gives none), `mqCount` the number of $0$-tagged queries, `witnessRead` the number of witness bits read.
--
--   **Sampler.** $D_h$ (`samplerLaw PS y n R`) is the law on $\{0,1\}^n \cup \{\bot\}$ of the fixed sampler program `PS` run on the learner's output word $y$ with $R$ uniform coins, an empty witness tape and no oracle; an output of length $\ne n$ counts as $\bot$.
--
--   **Problem 1.1** (p. 2). `SolvesP11 hyp PL PS TL R TS SZ n s ε φ hF` holds when (i) the learner `PL` halts within $T_L$ and outputs a decodable hypothesis of size at most $SZ$ on every coin string and every $\mathrm{EX}^+$ stream; (ii) on every word $y$ the learner outputs, the sampler halts within $T_S$ on every one of its $R$-bit coin strings; (iii) with probability $\ge 2/3$ over the learner's coins and samples, it outputs $y$ encoding (through `hyp`) a hypothesis of size $\le SZ$ with $H = h^{-1}(1) \neq \emptyset$,
--   $$d_{TV}(U_H, U_F) \le \varepsilon/2, \qquad d_{TV}(D_h, U_H) \le \varepsilon/2 .$$
--   `ptfHyp` reads a PTF, `circuitHyp` a circuit.
--
--   **Definition 4.1** (`IsDensifier P γ T_den`): for all $n, s \ge 1$, $\varepsilon,\delta \in (0,1)$, $\gamma(n,s,1/\varepsilon,1/\delta) \in (0,1]$, and for every nonempty $s$-term DNF the program halts within $\lceil T_{den}(n,s,1/\varepsilon,1/\delta)\rceil$ and always outputs a decodable conjunction list; with probability $\ge 1-\delta$ the list satisfies the bounds with $|F\setminus G| \le \varepsilon |F|$ and $\sum_i |C_i| \le |F|/\gamma(n,s,1/\varepsilon,1/\delta)$.
--
--   **Definition 4.2** (`IsUDLearner P T_learn S_learn`): for every ambient bound $n$, target dimension $d \le n$, $s \ge 1$, and valid accuracy/confidence parameters, every run returns a decodable bounded-fan-in circuit of size at most $S_{learn}(n,s,1/\varepsilon,1/\delta)$ within $\lceil T_{learn}(n,s,1/\varepsilon,1/\delta)\rceil$ time. Its uniform error is at most $\varepsilon$ with probability at least $1-\delta$. This is the source's bound on targets with at most $n$ variables; the bound functions need not be monotone.
--
--   **Formalization Note.** A randomized algorithm has an unbounded supply of fair coins. The RAM's coin tape is finite and random-access, so in Definitions 4.1 and 4.2 the guarantees are required for every coin-tape length $L$ at least the time bound; an algorithm that reads its coins in order satisfies this. In Problem 1.1 the learner has exactly $T_L$ coins and the sampler exactly $R$ coins, which is how "uses poly random bits" is made literal.
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Problem 1.1 and Theorem 1.2, p. 2 (PDF 3); Definitions 4.1–4.2, p. 10 (PDF 11)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Codes
import Definitions.Def_TargetedSamplers_Machine

namespace DNFSatMQ.Main

open TargetedSamplers

/-! Conventions for running the learners and samplers of the paper on the published fair-coin
log-cost RAM `TargetedSamplers.Program` (the paper names no machine model). -/

/-- The input tape holding the natural numbers `k₁, …, k_j` in unary, each followed by a `0`
(e.g. `n` and `s` for a learner). -/
def unaryInput (ks : List ℕ) : List Bool :=
  (ks.map fun k => List.replicate k true ++ [false]).flatten

/-- The point of `{0,1}ⁿ` written as the bit string `x` (bit `i` is coordinate `i`). -/
def ptOfList (n : ℕ) (x : List Bool) : Pt n := fun i => x.getD i false

/-- The answer to a comparison query about the real number `a`: the query string is a rational
code `v` (`decodeRat`), and the answer is `1` if `a ≤ v`, `0` otherwise (also `0` on a malformed
query). This is how a program accesses a real parameter such as `ε`. -/
noncomputable def cmpAnswer (a : ℝ) (q : List Bool) : ℕ :=
  match decodeRat q with
  | some (v, _) => if a ≤ (v : ℝ) then 1 else 0
  | none => 0

/-- The oracle of a learner for a Boolean target `f` on `n` variables, with accuracy parameter `ε`
and, optionally, confidence parameter `δ`:
* `0 :: x` with `|x| = n` is the membership query `MQ_f(x)`, answered `f(x) ∈ {0,1}`;
* `1 0 :: v` asks whether `ε ≤ v`; `1 1 :: v` asks whether `δ ≤ v` (answered `0` when there is
  no `δ`). Every other query is answered `0`. -/
noncomputable def dnfOracle {n : ℕ} (f : Pt n → Bool) (ε : ℝ) (δ : Option ℝ) :
    List Bool → ℕ
  | false :: x => if x.length = n then (f (ptOfList n x)).toNat else 0
  | true :: false :: q => cmpAnswer ε q
  | true :: true :: q => match δ with
      | some d => cmpAnswer d q
      | none => 0
  | _ => 0

/-- The oracle giving access to a real-valued `g : {0,1}^d → ℝ` with parameters `θ, δ`:
`0 :: x ++ v` with `|x| = d` asks whether `g(x) ≤ v`; `1 0 :: v` asks whether `θ ≤ v`;
`1 1 :: v` asks whether `δ ≤ v`. -/
noncomputable def realOracle {d : ℕ} (g : Pt d → ℝ) (θ δ : ℝ) : List Bool → ℕ
  | false :: q => if d ≤ q.length then cmpAnswer (g (ptOfList d (q.take d))) (q.drop d) else 0
  | true :: false :: q => cmpAnswer θ q
  | true :: true :: q => cmpAnswer δ q
  | _ => 0

/-- The witness tape holding the stream of `EX⁺_f` samples `w 0, w 1, …`, each written as its
`n` bits. A program reads it once, left to right. -/
def sampleTape {n K : ℕ} {F : Finset (Pt n)} (w : Fin K → {x // x ∈ F}) : List Bool :=
  (List.ofFn fun j => List.ofFn (w j).1).flatten

/-- Every coin access is within the supplied fair-bit tape. The sentinel past its end is not
an input carrying the accuracy parameter or a running-time bound. -/
def CoinsInBounds (P : Program) (τ : Tapes) : Prop :=
  ∀ (k d a : ℕ), (P.config τ k).halted = false →
    P[(P.config τ k).pc]? = some (.readCoin d a) →
    (P.config τ k).mem a < τ.coins.length

/-- The run halts with bit cost at most `t` and accesses only supplied fair coins. -/
def HaltsWithin (P : Program) (τ : Tapes) (t : ℕ) : Prop :=
  (∃ v, P.RunsIn τ t v) ∧ CoinsInBounds P τ

/-- The output word of a halted run: `some y` if the run halts with output `y`, and `none` if it
halts with `⊥` or never halts. -/
noncomputable def outWord (P : Program) (τ : Tapes) : Option (List Bool) :=
  match P.final τ with
  | some st => st.result
  | none => none

/-- The number of membership queries (`0`-tagged oracle queries) of the run. -/
noncomputable def mqCount (P : Program) (τ : Tapes) : ℕ :=
  ((P.queriesAsked τ).filter fun q => q.head? = some false).length

/-- The number of witness bits read by the run (`0` if it does not halt). -/
noncomputable def witnessRead (P : Program) (τ : Tapes) : ℕ :=
  match P.final τ with
  | some st => st.wcursor
  | none => 0

open Classical in
/-- `Pr_{r, w}[E(r, w)]` for `T` fair coins `r ∈ {0,1}^T` and `T` independent `EX⁺_f` samples
`w ∈ F^T`, all uniform (the counting measure normalised by `2^T |F|^T`). -/
noncomputable def probCoinsSamples {n : ℕ} (T : ℕ) (F : Finset (Pt n))
    (E : (Fin T → Bool) → (Fin T → {x // x ∈ F}) → Prop) : ℝ :=
  ((Finset.univ.filter fun rw : (Fin T → Bool) × (Fin T → {x // x ∈ F}) => E rw.1 rw.2).card : ℝ)
    / ((2 : ℝ) ^ T * (F.card : ℝ) ^ T)

open Classical in
/-- `Pr_r[E(r)]` for `T` uniform fair coins `r ∈ {0,1}^T`. -/
noncomputable def probCoins (T : ℕ) (E : (Fin T → Bool) → Prop) : ℝ :=
  ((Finset.univ.filter fun r : Fin T → Bool => E r).card : ℝ) / (2 : ℝ) ^ T

/-- The tapes of a learner for the target `f` on `n` variables in Problem 1.1 or Definition 4.1:
input `n, s` in unary, coins `r`, the `EX⁺_f` stream `w` on the witness tape, and the oracle
`dnfOracle f ε δ`. -/
noncomputable def learnerTapes {n T : ℕ} (s : ℕ) (F : Finset (Pt n)) (f : Pt n → Bool) (ε : ℝ) (δ : Option ℝ)
    (r : Fin T → Bool) (w : Fin T → {x // x ∈ F}) : Tapes :=
  ⟨unaryInput [n, s], List.ofFn r, sampleTape w, dnfOracle f ε δ⟩

/-- The point of `{0,1}ⁿ ∪ {⊥}` a sampler run reports: an output word of length `n`, or `⊥`
(output `⊥`, an output of the wrong length, or no halt). -/
def toPoint (n : ℕ) : Option (List Bool) → Option (Pt n)
  | some z => if z.length = n then some (ptOfList n z) else none
  | none => none

/-- `D_h`: the output law on `{0,1}ⁿ ∪ {⊥}` of the sampler program `PS` run on the learner's output
word `y`, with `R` uniform fair coins, an empty witness tape and no oracle ("depends only on the
learner's output, with no further access to `EX⁺_f` and `MQ_f`"). -/
noncomputable def samplerLaw (PS : Program) (y : List Bool) (n R : ℕ) : PMF (Option (Pt n)) :=
  (PMF.uniformOfFintype (Fin R → Bool)).map fun r =>
    toPoint n (outWord PS ⟨y, List.ofFn r, [], noOracle⟩)

/-- **Problem 1.1** (p. 2) solved on one instance, for a hypothesis representation `hyp` (which
maps an output word to the satisfying set `H = h⁻¹(1)` it encodes and its size), by the learner
program `PL` and the sampler program `PS`, with learning time `TL`, sampler random bits `R`,
sampler time `TS` and hypothesis size bound `SZ`. The target is the DNF `φ` with `F ≠ ∅`.
* the learner halts within `TL` and outputs an encoded hypothesis of size at most `SZ` on every run;
* on every output word `y` of the learner, the sampler halts within `TS` on every coin string;
* with probability `≥ 2/3` over the coins and the samples, the learner outputs a word `y` encoding
  a hypothesis of size `≤ SZ` with `H ≠ ∅`, `d_TV(U_H, U_F) ≤ ε/2` and `d_TV(D_h, U_H) ≤ ε/2`. -/
def SolvesP11 (hyp : (n : ℕ) → List Bool → Option (Finset (Pt n) × ℕ)) (PL PS : Program)
    (TL R TS SZ : ℕ) (n s : ℕ) (ε : ℝ) (φ : SamplingAC0.DNF (Fin n))
    (hF : (satSet φ).Nonempty) : Prop :=
  (∀ (r : Fin TL → Bool) (w : Fin TL → {x // x ∈ satSet φ}),
      HaltsWithin PL (learnerTapes s (satSet φ) φ.eval ε none r w) TL ∧
      ∃ y H sz, outWord PL (learnerTapes s (satSet φ) φ.eval ε none r w) = some y ∧
        hyp n y = some (H, sz) ∧ sz ≤ SZ) ∧
  (∀ (r : Fin TL → Bool) (w : Fin TL → {x // x ∈ satSet φ}) (y : List Bool),
      outWord PL (learnerTapes s (satSet φ) φ.eval ε none r w) = some y →
      ∀ r' : Fin R → Bool, HaltsWithin PS ⟨y, List.ofFn r', [], noOracle⟩ TS) ∧
  probCoinsSamples TL (satSet φ) (fun r w =>
      ∃ y, outWord PL (learnerTapes s (satSet φ) φ.eval ε none r w) = some y ∧
        ∃ H sz, hyp n y = some (H, sz) ∧ sz ≤ SZ ∧
          ∃ hH : H.Nonempty,
            SSNonExt.TV (unifBot H hH) (unifBot (satSet φ) hF) ≤ ε / 2 ∧
            SSNonExt.TV (samplerLaw PS y n R) (unifBot H hH) ≤ ε / 2) ≥ 2 / 3

/-- The PTF representation: the output word starts with a polynomial expression `p`; the
hypothesis is `h(x) = 1{p(x) ≥ 0}` and its size is the size of `p`. -/
noncomputable def ptfHyp (n : ℕ) (y : List Bool) : Option (Finset (Pt n) × ℕ) :=
  (decodePolyExpr n y).map fun p => (ptfSet p, p.size)

/-- The circuit representation (§4, p. 10): the output word starts with a bounded-fan-in
evaluation circuit; its size is its number of gates. -/
def circuitHyp (n : ℕ) (y : List Bool) : Option (Finset (Pt n) × ℕ) :=
  (decodeCircuit n y).map fun C => (circuitSet C, C.size)

/-- **Definition 4.1** (p. 10), on the machine, together with the running time `T_den` of
Theorem 4.3: `P` is a `γ`-densifier for DNF formulas that runs in time `T_den(n, s, 1/ε, 1/δ)`.
For every `n, s ≥ 1`, `ε, δ ∈ (0, 1)` and nonempty `s`-term DNF `f`, given `n, s` (input tape),
`ε, δ` (comparison queries), `EX⁺_f` (witness tape) and `MQ_f` (oracle), and with any supply of
`L ≥ ⌈T_den⌉` fair coins (and `L` samples): every run halts within `⌈T_den⌉` and outputs a list of conjunctions, and with probability
`≥ 1 − δ` the output is a list `c₁, …, c_m` of conjunctions with `|F \ G| ≤ ε|F|` and
`Σᵢ |Cᵢ| ≤ |F| / γ(n, s, 1/ε, 1/δ)`, `G = ⋃ᵢ Cᵢ`. The function `γ` takes values in `(0, 1]`
on this domain.

**Formalization Note.** A randomized algorithm has an unbounded supply of fair coins; on the RAM,
whose coin tape is finite and random-access, this is "for every coin-tape length `L ≥ ⌈T_den⌉`".
An algorithm that reads its coins in order has this property. -/
def IsDensifier (P : Program) (γ Tden : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  (∀ (n s : ℕ), 1 ≤ n → 1 ≤ s → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    0 < γ n s (1 / ε) (1 / δ) ∧ γ n s (1 / ε) (1 / δ) ≤ 1) ∧
  ∀ (n s : ℕ), 1 ≤ n → 1 ≤ s → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∀ φ : SamplingAC0.DNF (Fin n), φ.length ≤ s → (satSet φ).Nonempty →
    ∀ L : ℕ, ⌈Tden n s (1 / ε) (1 / δ)⌉₊ ≤ L →
      (∀ (r : Fin L → Bool) (w : Fin L → {x // x ∈ satSet φ}),
          HaltsWithin P (learnerTapes s (satSet φ) φ.eval ε (some δ) r w)
            ⌈Tden n s (1 / ε) (1 / δ)⌉₊ ∧
          ∃ y cs, outWord P (learnerTapes s (satSet φ) φ.eval ε (some δ) r w) = some y ∧
            decodeConjList n y = some cs) ∧
      probCoinsSamples L (satSet φ) (fun r w =>
          ∃ y cs, outWord P (learnerTapes s (satSet φ) φ.eval ε (some δ) r w) = some y ∧
            decodeConjList n y = some cs ∧
            (((satSet φ) \ listUnion cs).card : ℝ) ≤ ε * (satSet φ).card ∧
            (listVolume cs : ℝ) ≤ (satSet φ).card / γ n s (1 / ε) (1 / δ)) ≥ 1 - δ

/-- The tapes of a uniform-distribution learner (Definition 4.2) for `f` on `d` variables: input
`d, s` in unary, coins `r`, no samples, and the oracle `MQ_f` with comparison access to `ε, δ`. -/
noncomputable def udTapes {d T : ℕ} (s : ℕ) (f : Pt d → Bool) (ε δ : ℝ) (r : Fin T → Bool) : Tapes :=
  ⟨unaryInput [d, s], List.ofFn r, [], dnfOracle f ε (some δ)⟩

/-- The error `Pr_{x∼U_d}[h(x) ≠ f(x)]` of a hypothesis under the uniform distribution. -/
noncomputable def uniformError {d : ℕ} (h f : Pt d → Bool) : ℝ :=
  ((Finset.univ.filter fun x => h x ≠ f x).card : ℝ) / 2 ^ d

/-- **Definition 4.2** (p. 10), on the machine, with the learning time `T_learn` and output size
`S_learn` of Theorem 4.3: for every `d ≥ 0`, `s ≥ 1`, `ε, δ ∈ (0, 1)` and `s`-term DNF
`f : {0,1}^d → {0,1}` and every ambient bound `n ≥ d`, given `d, s, ε, δ` and `MQ_f`,
and with any supply of `L ≥ ⌈T_learn(n, s, 1/ε, 1/δ)⌉` fair coins: every run halts
within `⌈T_learn(n, s, 1/ε, 1/δ)⌉`,
every run outputs a circuit of size `≤ S_learn(n, s, 1/ε, 1/δ)`, and with probability `≥ 1 − δ` it
outputs a circuit `h` with `Pr_{x∼U_d}[h(x) ≠ f(x)] ≤ ε` (coin supply: as in `IsDensifier`). -/
def IsUDLearner (P : Program) (Tlearn Slearn : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (n d s : ℕ), d ≤ n → 1 ≤ s → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∀ φ : SamplingAC0.DNF (Fin d), φ.length ≤ s →
    ∀ L : ℕ, ⌈Tlearn n s (1 / ε) (1 / δ)⌉₊ ≤ L →
      (∀ r : Fin L → Bool,
          HaltsWithin P (udTapes s φ.eval ε δ r) ⌈Tlearn n s (1 / ε) (1 / δ)⌉₊ ∧
          ∃ y C, outWord P (udTapes s φ.eval ε δ r) = some y ∧
            decodeCircuit d y = some C ∧ (C.size : ℝ) ≤ Slearn n s (1 / ε) (1 / δ)) ∧
      probCoins L (fun r =>
          ∃ y C, outWord P (udTapes s φ.eval ε δ r) = some y ∧ decodeCircuit d y = some C ∧
            uniformError C.eval φ.eval ≤ ε) ≥ 1 - δ

/-- The tapes of a program given oracle access to a real-valued `g : {0,1}^d → ℝ` (Theorem 9.1):
input `d` in unary, coins `r`, no witness, and `realOracle g θ δ`. -/
noncomputable def realTapes {d T : ℕ} (g : Pt d → ℝ) (θ δ : ℝ) (r : Fin T → Bool) : Tapes :=
  ⟨unaryInput [d], List.ofFn r, [], realOracle g θ δ⟩

end DNFSatMQ.Main


