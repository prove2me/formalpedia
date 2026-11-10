-- Prove2me | Definitions.Def_MinSumRadiiPTAS_Main_Machine
-- name    : MinSumRadiiPTAS_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:00:59.544702+00:00
-- url     : https://prove2.me/theorems/e2785179-bc7d-4280-b97a-7a673051bb4e
-- title:
--   Input and output layouts of the §6–§7 algorithms and the success event of Theorem 1.1 on the published distance-oracle real RAM
-- statement:
--   All running times are counted on the published randomized distance-oracle real RAM `MinSumFPT` (its instructions, step function, tape law and labelling output are reused unchanged).
--
--   1. **Extended start state** `initStateExt n k ε reals X lists`: the published start state `MinSumFPT.initState n k ε 0` ($n, k$ in integer memory $0, 1$; $\varepsilon$ in real memory $0$; real memory $1$ is the unused $\delta$ slot, $0$) with, in addition, the real parameters $x_j$ (here $\lambda, R$ or $\theta$) in real memory $2 + j$; the client set $X$ as a 0/1 array in integer memory $2, \dots, n+1$; and the input ball lists as one stream from address $n + 2 + |\mathrm{reals}|$ on, each list as its length followed by its balls, a ball stored as its center (integer memory) and its radius (real memory) at the same address. `runExt` iterates the published `MinSumFPT.step` from it.
--   2. **Ball-list output** `OutputsBalls s S`: the state has halted, its integer memory at $-1$ holds the length $m \ge 0$ and for $t < m$ address $-2 - t$ holds a ball (center a point of `Fin n`, radius $\ge 0$); $S$ is that list.
--   3. **Pair output** (Theorem 7.2) `OutputsPairs s ps`: the state has halted, integer memory $-1$ holds the number of pairs, and from address $-2$ on each pair $(S_0, (S_1, S_2, \theta))$ is stored as three well-formed ball lists followed by $\theta$ in real memory at the next address; $ps$ is the decoded list of `BipointPair`s.
--   4. **Success event of Theorem 1.1** `goodTapes P n k ε d T`: the tapes $\omega$ for which the published run of $P$ on $(n, k, \varepsilon, \delta = 0, d)$ has, after $\lfloor T\rfloor$ steps, halted with a labelling $\sigma$ (`MinSumFPT.OutputsLabelling`) of MSR cost $\le (1+\varepsilon)\,\mathrm{opt}$.
--
--   **Formalization Note** The layouts are total: every state decodes, and the validity predicates say when the decoding is the intended one. Output balls must have nonnegative radii; otherwise a negative-radius entry would lower the cost of an output.
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, Theorem 1.1 p. 2, Lemma 6.2 and Theorem 6.1 p. 24, Lemma 6.7 p. 27, Theorems 7.2–7.3 p. 28

import Mathlib
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumRadiiPTAS_Main_Basic

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-!
# Input and output layouts of the algorithmic statements on the published machine

Grandoni, Gupta, Yadav, *A PTAS for the Minimum Sum of Radii Problem* (STOC 2027 submission,
SHA-256 99b43d49…): Theorem 1.1 (p. 2), Lemma 6.2, Theorem 6.1 (p. 24), Lemma 6.7 (p. 27),
Theorems 7.2–7.3 (p. 28). The running times are counted on the published randomized
distance-oracle real RAM `MinSumFPT` (instructions, `step`, `tapeLaw` and `OutputsLabelling`
reused unchanged).

**Formalization Note.** `MinSumFPT.initState` carries only `n, k, ε, δ`. The subroutines of §§6–7
also receive real parameters (`λ`, `R`, `θ`), a client set and lists of balls; `initStateExt` is
`MinSumFPT.initState n k ε 0` with these written into otherwise-zero cells, and `runExt` iterates the
published `MinSumFPT.step` from it.

* Real parameters `reals = [x₀, x₁, …]`: real memory `mem (2 + j) = x_j`.
* Client set `X`: integer memory `imem (2 + v) = 1` if `v ∈ X`, `0` otherwise, for `v < n`.
* Ball lists: one stream starting at address `b₀ = n + 2 + |reals|`; each list is its length (in
  `imem`) followed by its balls, ball `B` as `imem = c_B` (the point index) and `mem = r_B` at the
  same address.
* Output ball list (`readBalls · (-1)`): its length `m` at `imem (-1)`, ball `t < m` at address
  `-2 - t` (center in `imem`, radius in `mem`).
* Output collection of pairs `(S₀, (S₁, S₂, θ))` (Theorem 7.2): their number at `imem (-1)`; from
  address `-2` on, for each pair the ball lists `S₀`, `S₁`, `S₂` in the format above (length at the
  current address, entries below it), then `θ` in `mem` at the next address. -/

/-- One cell of the ball stream: an integer-memory value and a real-memory value. -/
noncomputable def ballStream {n : ℕ} (lists : List (List (Ball n))) : List (ℤ × ℝ) :=
  lists.flatMap (fun l => ((l.length : ℤ), (0 : ℝ)) :: l.map (fun B => (((B.center : ℕ) : ℤ),
    B.radius)))

/-- The start state with `n, k` in `imem 0, 1`, `ε` in `mem 0`, `mem 1 = 0` (the unused `δ`
slot), and the real parameters, the client set and the ball lists in the layout above. -/
noncomputable def initStateExt (n k : ℕ) (ε : ℝ) (reals : List ℝ) (X : Finset (Fin n))
    (lists : List (List (Ball n))) : MinSumFPT.State :=
  let s := MinSumFPT.initState n k ε 0
  let b₀ : ℤ := (n : ℤ) + 2 + (reals.length : ℤ)
  let st := ballStream lists
  { s with
    cfg := { s.cfg with
      mem := fun a =>
        if a = 0 then ε
        else if 2 ≤ a ∧ a < 2 + (reals.length : ℤ) then reals.getD (a - 2).toNat 0
        else if b₀ ≤ a ∧ a < b₀ + (st.length : ℤ) then (st.getD (a - b₀).toNat (0, 0)).2
        else 0 }
    imem := fun a =>
      if a = 0 then (n : ℤ)
      else if a = 1 then (k : ℤ)
      else if 2 ≤ a ∧ a < 2 + (n : ℤ) then
        (if ∃ v ∈ X, ((v : ℕ) : ℤ) = a - 2 then 1 else 0)
      else if b₀ ≤ a ∧ a < b₀ + (st.length : ℤ) then (st.getD (a - b₀).toNat (0, 0)).1
      else 0 }

/-- The state after `t` steps of the published step function from `initStateExt`. -/
noncomputable def runExt (P : MinSumFPT.Program) (n k : ℕ) (ε : ℝ) (reals : List ℝ)
    (X : Finset (Fin n)) (lists : List (List (Ball n))) (d : Fin n → Fin n → ℝ) (ω : ℕ → ℝ)
    (t : ℕ) : MinSumFPT.State :=
  (MinSumFPT.step P d ω)^[t] (initStateExt n k ε reals X lists)

/-- The raw entries `(center, radius)` of the ball list stored at address `pos` of a state: the
length `imem pos`, then the entries at `pos − 1, pos − 2, …`. -/
def readBallsRaw (s : MinSumFPT.State) (pos : ℤ) : List (ℤ × ℝ) :=
  (List.range (s.imem pos).toNat).map (fun t => (s.imem (pos - 1 - (t : ℤ)),
    s.cfg.mem (pos - 1 - (t : ℤ))))

/-- The ball list stored at address `pos` (entries whose center is not a point are dropped; the
validity predicate excludes them). -/
noncomputable def readBalls (n : ℕ) (s : MinSumFPT.State) (pos : ℤ) : List (Ball n) :=
  (readBallsRaw s pos).filterMap (fun e => (MinSumFPT.toPoint n e.1).map (fun c => ⟨c, e.2⟩))

/-- The ball list at `pos` is well formed: a nonnegative length, every center a point of `Fin n`
and every radius nonnegative. -/
def ValidBallsAt (n : ℕ) (s : MinSumFPT.State) (pos : ℤ) : Prop :=
  0 ≤ s.imem pos ∧ ∀ e ∈ readBallsRaw s pos, 0 ≤ e.1 ∧ e.1 < (n : ℤ) ∧ 0 ≤ e.2

/-- The state has halted with the well-formed ball list `l` as its output. -/
def OutputsBalls {n : ℕ} (s : MinSumFPT.State) (l : List (Ball n)) : Prop :=
  s.halted = true ∧ ValidBallsAt n s (-1) ∧ readBalls n s (-1) = l

/-- The address after the ball list stored at `pos`. -/
def nextPos (s : MinSumFPT.State) (pos : ℤ) : ℤ := pos - 1 - ((s.imem pos).toNat : ℤ)

/-- The start addresses of `m` consecutive pairs from address `pos`: a pair occupies three ball lists
and one real cell. -/
def pairStarts (s : MinSumFPT.State) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | m + 1, pos => pos :: pairStarts s m (nextPos s (nextPos s (nextPos s pos)) - 1)

/-- A pair `(S₀, S_bp)` with `S_bp = (S₁, S₂, θ)` (Theorem 7.2, p. 28). -/
structure BipointPair (n : ℕ) where
  /-- The guessed balls `S₀`. -/
  S0 : List (Ball n)
  /-- The first solution `S₁` of the bipoint solution. -/
  S1 : List (Ball n)
  /-- The second solution `S₂` of the bipoint solution. -/
  S2 : List (Ball n)
  /-- The convex coefficient `θ`. -/
  θ : ℝ

/-- The pair stored at address `pos`. -/
noncomputable def pairAt (n : ℕ) (s : MinSumFPT.State) (pos : ℤ) : BipointPair n :=
  ⟨readBalls n s pos, readBalls n s (nextPos s pos), readBalls n s (nextPos s (nextPos s pos)),
    s.cfg.mem (nextPos s (nextPos s (nextPos s pos)))⟩

/-- The state has halted with a well-formed collection of pairs as its output, namely `ps`. -/
def OutputsPairs {n : ℕ} (s : MinSumFPT.State) (ps : List (BipointPair n)) : Prop :=
  s.halted = true ∧ 0 ≤ s.imem (-1) ∧
    (∀ pos ∈ pairStarts s (s.imem (-1)).toNat (-2),
      ValidBallsAt n s pos ∧ ValidBallsAt n s (nextPos s pos) ∧
        ValidBallsAt n s (nextPos s (nextPos s pos))) ∧
    (pairStarts s (s.imem (-1)).toNat (-2)).map (pairAt n s) = ps

/-- The tapes on which `P`, run for `⌊T⌋₊` steps on the MSR instance `(n, k, d)` with error `ε`, has
written a labelling of MSR cost at most `(1 + ε) · opt` (Theorem 1.1). -/
def goodTapes (P : MinSumFPT.Program) (n k : ℕ) (ε : ℝ) (d : Fin n → Fin n → ℝ) (T : ℝ) :
    Set (ℕ → ℝ) :=
  {ω | ∃ σ : Fin n → Fin k, MinSumFPT.OutputsLabelling (MinSumFPT.run P n k ε 0 d ω ⌊T⌋₊) σ ∧
    msrCost d σ ≤ (1 + ε) * msrOpt d k}

end MinSumRadiiPTAS.Main


