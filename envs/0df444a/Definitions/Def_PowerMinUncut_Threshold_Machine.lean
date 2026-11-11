-- Prove2me | Definitions.Def_PowerMinUncut_Threshold_Machine
-- name    : PowerMinUncut_Threshold_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:43:47.598766+00:00
-- url     : https://prove2.me/theorems/eda1e5ad-2ce2-4295-a7ff-7ef611588911
-- title:
--   Binary encodings, fair coin strings, the randomized rounding machine and the UGC-conditional promise problem
-- statement:
--   All numbers are written in **binary** over the alphabet $\{0,1,\mathrm{sep},\mathrm{minus},\mathrm{hash}\}$: a natural number is its bits followed by a separator, an integer carries an optional sign, and a rational is its reduced numerator and denominator. A graph is encoded as $N$ followed by the triples $(i,j,w_{ij})$ of its edges of nonzero weight, $i<j$, in lexicographic order; the input of the rounding algorithm is the graph followed by $\zeta$ and $\omega$; its output is the list of rational vectors $r_i\in\mathbb Q^k$, one per vertex, representing the unit vectors $v_i=r_i/\sqrt{r_i\cdot r_i}$ (positive root).
--
--   A **randomized algorithm** is one deterministic one-tape Turing machine (Cook's model, the platform definition `CookPvsNP.TM`) over a finite tape alphabet containing these symbols, started on the input followed by a string of fair coins; probabilities are fractions of coin strings:
--   $$\mathrm{coinFrac}(L,\mathrm{good})=\frac{\#\{c\in\{0,1\}^L:\mathrm{good}(c)\}}{2^L}.$$
--   For fixed $k,q$ the machine $M$ with constants $c,d$ is a **bounded-bit rounding algorithm** if, for every graph with nonnegative rational weights of total one and all rationals $\zeta>0$, $0<\omega<1$, with
--   $$T=\big\lfloor c\,(1+\ell+N+|E|+\max(1,1/\zeta)+1+\log(1/\omega))^d\big\rfloor$$
--   ($\ell$ the binary input length): on every coin string of length $T$ the machine halts within $T$ steps and outputs the encoding, of length at most $T$, of nonzero vectors $r_i\in\mathbb Q^k$; and the fraction of coin strings whose output has cost $\sum_{ij\in E}w_{ij}\|v_i+v_j\|^q\le (C_{k,q}+\zeta)\,\mathrm{OPT}_{k,q}(G)$ is at least $1-\omega$.
--
--   The **promise problem** with thresholds $c<s$ asks to distinguish $\mathrm{OPT}_{k,q}(G)\le c$ from $\mathrm{OPT}_{k,q}(G)\ge s$ on graphs with nonnegative rational weights of total one; `PromiseNPHard k q c s` says it is NP-hard in the sense of the platform's `OptInapprox.MaxCut.GapNPHard`: every NP language over every finite alphabet maps, by a polynomial-time computable function (Cook's model), members to YES instances and non-members to NO instances, with graphs written by the binary encoding above.
--
--   **Formalization Note.** The coin length $T$ is also the time and output bound, so all three resources are bounded on every coin string, not in expectation. `coinFrac` copies the platform's `AcceptSubcube.coinFrac` (whose module belongs to another paper). The encodings are injective: binary words are separator-delimited and rationals are in lowest terms.
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 1, Theorem 1 (second and third paragraphs); p. 35, Theorem 11; p. 49, §10 (graphs of total weight one); pp. 49–50, Theorem 13

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_PowerMinUncut_Threshold_Instance

/-!
# Binary encodings, fair coin strings, and the randomized rounding machine

Xie, *Sharp Power Loss Thresholds for Vector Min Uncut*, STOC 2027 submission (manuscript
sha256 391063da…), p. 1 (Theorem 1, second paragraph), p. 35 (Theorem 11), p. 49 (§10: graphs
with nonnegative rational weights of total one, the promise problem).

Conventions.
* Instances are written over the five-letter alphabet `Sym`. A natural number is written in binary
  (`Nat.bits`, least significant bit first, `0` is the empty word) followed by `sep`; an integer is
  an optional `minus` and its absolute value; a rational is its reduced numerator and its
  denominator. All numbers, in particular the weights, `ζ` and `ω`, are in binary.
* `encGraph G` is `N`, then for every edge `{i, j}` of nonzero weight with `i < j`, in
  lexicographic order, the triple `i, j, w_ij`.
* `encInput G ζ ω` is `encGraph G`, `hash`, `ζ`, `ω`; the machine's tape initially holds
  `encInput G ζ ω`, `hash`, then the coin string (`zero`/`one`).
* A randomized algorithm is one deterministic Cook machine (`CookPvsNP.TM`, the platform
  definition) over a finite tape alphabet `Γ ⊇ Sym` reading its input and a string of fair coins;
  its success probability is the fraction of coin strings of the given length on which it succeeds
  (pattern of the platform's `AcceptSubcube.coinFrac`).
* `PromiseNPHard k q c s`: the promise problem `OPT_{k,q} ≤ c` versus `OPT_{k,q} ≥ s` on graphs of
  total weight one is NP-hard in the sense of the platform's `OptInapprox.MaxCut.GapNPHard`.
* An output is the word `encVecs r`: for every vertex `i` in order, the `k` rational coordinates of
  `r_i ∈ ℚ^k`. The vector it represents at vertex `i` is `v_i = r_i / √(r_i · r_i)` (positive root).
-/

namespace PowerMinUncut.Threshold

open WGraph

/-- The alphabet of instance and output encodings. -/
inductive Sym where
  | zero
  | one
  | sep
  | minus
  | hash
  deriving DecidableEq

instance : Fintype Sym where
  elems := {Sym.zero, Sym.one, Sym.sep, Sym.minus, Sym.hash}
  complete := by intro x; cases x <;> simp

/-- A bit as a symbol. -/
def bitSym (b : Bool) : Sym := if b then Sym.one else Sym.zero

/-- A natural number in binary, terminated by `sep`. -/
def encNat (n : ℕ) : List Sym := (Nat.bits n).map bitSym ++ [Sym.sep]

/-- An integer: an optional `minus`, then its absolute value in binary. -/
def encInt (z : ℤ) : List Sym := (if z < 0 then [Sym.minus] else []) ++ encNat z.natAbs

/-- A rational number in lowest terms: numerator, then denominator. -/
def encRat (x : ℚ) : List Sym := encInt x.num ++ encNat x.den

/-- Binary encoding of a weighted graph: `N`, then the triples `(i, j, w_ij)` of the edges of nonzero
weight with `i < j` in lexicographic order. -/
def encGraph (G : WGraph) : List Sym :=
  encNat G.N ++
    (List.finRange G.N).flatMap fun i => (List.finRange G.N).flatMap fun j =>
      if i < j ∧ G.w i j ≠ 0 then encNat i ++ encNat j ++ encRat (G.w i j) else []

/-- The algorithm's input `(G, ζ, ω)`. -/
def encInput (G : WGraph) (ζ ω : ℚ) : List Sym :=
  encGraph G ++ [Sym.hash] ++ encRat ζ ++ encRat ω

/-- The initial tape: the input, `hash`, and the coin string. -/
def coinTape (G : WGraph) (ζ ω : ℚ) (coins : List Bool) : List Sym :=
  encInput G ζ ω ++ [Sym.hash] ++ coins.map bitSym

/-- Encoding of an output `r : V → ℚ^k`: the coordinates `r i j` in order. -/
def encVecs {N k : ℕ} (r : Fin N → Fin k → ℚ) : List Sym :=
  (List.finRange N).flatMap fun i => (List.finRange k).flatMap fun j => encRat (r i j)

/-- The unit vector `r / √(r · r)` represented by a rational vector `r` (positive root). -/
noncomputable def ratUnit {k : ℕ} (r : Fin k → ℚ) : EuclideanSpace ℝ (Fin k) :=
  (Real.sqrt (∑ j, ((r j : ℚ) : ℝ) ^ 2))⁻¹ • WithLp.toLp 2 (fun j => ((r j : ℚ) : ℝ))

/-- Cost of the output `r`: `Σ_{ij ∈ E} w_ij ‖v_i + v_j‖^q` at `v_i = r_i / √(r_i · r_i)`. -/
noncomputable def roundCost (G : WGraph) (k q : ℕ) (r : Fin G.N → Fin k → ℚ) : ℝ :=
  G.cost k q fun i => ratUnit (r i)

/-- Probability over fair coins: the exact fraction of the `2^L` coin strings of length `L`
satisfying `good` (copied from the platform's `AcceptSubcube.coinFrac`). -/
noncomputable def coinFrac (L : ℕ) (good : List Bool → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun c : Fin L → Bool => good (List.ofFn c))).card : ℝ) / 2 ^ L

/-- The machine `M` (tape alphabet `Γ ⊇ Sym` via `ι`) started on `x` halts within `T` steps and its
output (Cook's convention: tape from the head rightwards, trailing blanks removed) is `o`. -/
def OutputsWithin {Γ : Type} (ι : Sym ↪ Γ) (M : CookPvsNP.TM Γ) (T : ℕ) (x o : List Sym) :
    Prop :=
  M.HaltsWithin T (x.map ι) ∧ M.output (M.run T (M.init (x.map ι))) = o.map (some ∘ ι)

/-- The resource bound `c · (1 + ℓ + |V| + |E| + max(1, 1/ζ) + (1 + log(1/ω)))^d` of Theorems 1
and 11, rounded down, where `ℓ` is the binary input length. -/
noncomputable def resBound (c d : ℕ) (G : WGraph) (ζ ω : ℚ) : ℕ :=
  ⌊(c : ℝ) * (1 + ((encInput G ζ ω).length : ℝ) + (G.N : ℝ) + (G.numEdges : ℝ) +
      max 1 (1 / (ζ : ℝ)) + (1 + Real.log (1 / (ω : ℝ)))) ^ d⌋₊

/-- **Bounded-bit randomized rounding** (Theorem 1, second paragraph; Theorem 11): the machine `M`
with constants `c, d` (fixed before the input) has, on every graph with nonnegative rational
weights of total one and all rationals `ζ > 0`, `0 < ω < 1`, with `T = resBound c d G ζ ω`:
* on **every** coin string of length `T`: it halts within `T` steps and outputs the encoding, of
  length at most `T`, of rational vectors `r_i ∈ ℚ^k \ {0}`, one per vertex (exact feasibility;
  `T` bounds time, random bits and output length deterministically);
* the fraction of coin strings on which the output's cost is at most `(C_{k,q} + ζ) OPT_{k,q}(G)`
  is at least `1 - ω`. -/
def IsRandRounding (k q : ℕ) {Γ : Type} (ι : Sym ↪ Γ) (M : CookPvsNP.TM Γ) (c d : ℕ) : Prop :=
  ∀ G : WGraph, G.total = 1 → ∀ ζ ω : ℚ, 0 < ζ → 0 < ω → ω < 1 →
    (∀ coins : Fin (resBound c d G ζ ω) → Bool,
      ∃ r : Fin G.N → Fin k → ℚ, (∀ i, r i ≠ 0) ∧ (encVecs r).length ≤ resBound c d G ζ ω ∧
        OutputsWithin ι M (resBound c d G ζ ω) (coinTape G ζ ω (List.ofFn coins)) (encVecs r)) ∧
    1 - (ω : ℝ) ≤ coinFrac (resBound c d G ζ ω) (fun coins =>
      ∃ r : Fin G.N → Fin k → ℚ,
        OutputsWithin ι M (resBound c d G ζ ω) (coinTape G ζ ω coins) (encVecs r) ∧
        roundCost G k q r ≤ (Ckp k q + (ζ : ℝ)) * OPT k q G)

/-- **UGC-conditional promise problem** (Theorem 1, third paragraph; Theorem 13; §10.11): it is
NP-hard (the platform's `OptInapprox.MaxCut.GapNPHard`: every NP language over every finite alphabet
reduces in polynomial time, Cook's model) to distinguish `OPT_{k,q}(G) ≤ c` from `OPT_{k,q}(G) ≥ s`
on graphs with nonnegative rational weights of total one (§10, p. 49), encoded in binary by
`encGraph`. -/
def PromiseNPHard (k q : ℕ) (c s : ℚ) : Prop :=
  OptInapprox.MaxCut.GapNPHard encGraph
    (fun G : WGraph => G.total = 1 ∧ OPT k q G ≤ (c : ℝ))
    (fun G : WGraph => G.total = 1 ∧ (s : ℝ) ≤ OPT k q G)

end PowerMinUncut.Threshold


