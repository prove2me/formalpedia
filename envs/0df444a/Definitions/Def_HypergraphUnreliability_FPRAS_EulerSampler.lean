-- Prove2me | Definitions.Def_HypergraphUnreliability_FPRAS_EulerSampler
-- name    : HypergraphUnreliability_FPRAS_EulerSampler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:08.01392+00:00
-- url     : https://prove2.me/theorems/723445b3-d0ee-4c44-b7dc-a139c04a4ee5
-- title:
--   The rational Euler sampler, fixed-bit categorical draws, batching and the median
-- statement:
--   This is the finite-bit sampler shared by both algorithms, with parameters: the hypergraph, rational rates $r$, a cut value $\Lambda$, a step $h$, a number $L$ of steps, a bit width $q$, a batch size $S$ and a number $b$ of batches.
--
--   From a live state, one **Euler step** gives probability $hr_e/2$ to each safe labeled copy, $h(\kappa_w(x)-\Lambda)$ to the cemetery, and the residual to staying. There are at most $2m+2$ categories.
--
--   A **$q$-bit draw** reads $q$ fresh bits as an integer $J\in\{0,\dots,2^q-1\}$ and selects the half-open cumulative interval containing $J/2^q$.
--
--   One **sample** draws a pair from the uniform distribution on the $N=\binom n2$ pairs and performs $L$ Euler steps with fresh $q$-bit draws. Its reward is $N/\binom K2$ in a live terminal state and $0$ after absorption. The estimator takes $b$ exact rational batch averages of $S$ independent samples and returns their median.
--
--   The definition also records the laws with exact draws and with fair bits, so that discretization and fixed-bit errors can be compared.
--
--   **Formalization Note** Each sample has a fixed block of $(L+1)q$ bits; stopping early after absorption reads fewer of them and does not change the result. The categories of a step are ordered by label, then copy, then cemetery, then staying.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), §§7.2–7.4, pp. 9–10; §8, p. 11; §9.4, p. 14

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Contraction
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

/-- Half-open cumulative selection (§7.3, p. 10): return the first category whose cumulative interval
contains `u`, and `d` if `u` lies beyond all intervals. A category of mass `0` is never selected. -/
def selectCategory {α : Type} : List (ℚ × α) → α → ℚ → α
  | [], d, _ => d
  | (p, a) :: t, d, u => if u < p then a else selectCategory t d (u - p)

/-- The integer `J = ∑_{i<q} ω(off+i) 2^{q-1-i} ∈ {0, …, 2^q - 1}` given by `q` fresh bits. -/
def bitsValue (ω : ℕ → Bool) (off q : ℕ) : ℕ :=
  ∑ i ∈ Finset.range q, if ω (off + i) then 2 ^ (q - 1 - i) else 0

/-- The `q`-bit draw from a rational categorical distribution, §7.3: `J / 2^q` selects the half-open
cumulative interval containing it. -/
def fixedBitDraw {α : Type} (cats : List (ℚ × α)) (d : α) (ω : ℕ → Bool) (off q : ℕ) : α :=
  selectCategory cats d ((bitsValue ω off q : ℚ) / 2 ^ q)

/-- The law of the `q`-bit draw under `q` fair bits. -/
def fixedBitLaw {α : Type} (cats : List (ℚ × α)) (d : α) (q : ℕ) (y : α) : ℝ :=
  fairProb q (fun ω => fixedBitDraw cats d (tapeBit ω) 0 q = y)

/-- The exact categorical law of a list of masses and categories. -/
def categoryMass {α : Type} (cats : List (ℚ × α)) (y : α) : ℚ :=
  ((cats.filter (fun c => c.2 = y)).map Prod.fst).sum

/-- The parameters shared by both algorithms: the hypergraph, the copy rates `r e / 2`, the cut
value `Λ`, the Euler step `h`, the number of steps `L`, the bit width `q`, the batch size `S` and the
number of batches `b`. -/
structure SamplerParams (n m : ℕ) where
  H : LabeledHypergraph n (Fin m)
  r : Fin m → ℚ
  Λ : ℚ
  h : ℚ
  L : ℕ
  q : ℕ
  S : ℕ
  b : ℕ

namespace SamplerParams

variable {n m : ℕ} (P : SamplerParams n m)

/-- One rational Euler step from the live state `x`, (7.3) and §9.4: probability `h r_e / 2` to each
safe labeled copy, in increasing order of `(e, c)`; `h (κ_w(x) - Λ)` to the cemetery; the residual to
staying. At most `2m + 2` categories. -/
def eulerCategories (w : VertexPair n) (x : MarkedState n) :
    List (ℚ × Option (MarkedState n)) :=
  ((List.finRange m).flatMap (fun e =>
      ([false, true] : List Bool).filterMap (fun c =>
        if P.H.IsSafe w x e c then some (P.h * (P.r e / 2), some (P.H.contract x e c)) else none))) ++
    [(P.h * (P.H.killRate P.r w x - P.Λ), none),
     (1 - P.h * (P.H.safeRate P.r w x + P.H.killRate P.r w x - P.Λ), some x)]

/-- The exact Euler transition kernel; the cemetery is absorbing. -/
def eulerKernel (w : VertexPair n) :
    Option (MarkedState n) → Option (MarkedState n) → ℚ
  | some x, y => categoryMass (P.eulerCategories w x) y
  | none, y => if y = none then 1 else 0

/-- The law of `k` exact Euler steps from the initial singleton state. -/
def eulerLaw (w : VertexPair n) : ℕ → Option (MarkedState n) → ℚ
  | 0, y => if y = some MarkedState.init then 1 else 0
  | k + 1, y => ∑ x, eulerLaw w k x * P.eulerKernel w x y

/-- The original vertex pairs, in lexicographic order. -/
def pairList (n : ℕ) : List (VertexPair n) :=
  (List.finRange n).flatMap (fun a => (List.finRange n).filterMap (fun b =>
    if h : a < b then
      some ⟨{a, b}, Finset.card_pair (ne_of_lt h)⟩
    else none))

/-- The uniform target distribution on the `N = binom(n, 2)` pairs. -/
def pairCategories (n : ℕ) : List (ℚ × Option (VertexPair n)) :=
  (pairList n).map (fun w => ((1 : ℚ) / (n.choose 2 : ℕ), some w))

/-- The bits used by one sample: a draw for the pair and one per update. Stopping early after
absorption reads fewer of them without changing the result. -/
def sampleBits : ℕ := (P.L + 1) * P.q

/-- The Euler chain driven by the bits at offset `off`: the `i`-th update uses the bits at
`off + (i + 1) q`; the cemetery is absorbing, and a contraction recomputes everything. -/
def eulerRun (w : VertexPair n) (ω : ℕ → Bool) (off : ℕ) : ℕ → Option (MarkedState n)
  | 0 => some MarkedState.init
  | i + 1 =>
    match eulerRun w ω off i with
    | none => none
    | some x => fixedBitDraw (P.eulerCategories w x) (some x) ω (off + (i + 1) * P.q) P.q

/-- The protected pair and terminal state of one sample whose bits start at `off`, §7.4, p. 10. -/
def sampleOutcome (ω : ℕ → Bool) (off : ℕ) :
    Option (VertexPair n) × Option (MarkedState n) :=
  let w := fixedBitDraw (pairCategories n) none ω off P.q
  match w with
  | none => (none, none)
  | some w' => (some w', P.eulerRun w' ω off P.L)

/-- The reward of one sample: `N / binom(K, 2)` in a live terminal state, `0` after absorption. -/
def sampleReward (ω : ℕ → Bool) (off : ℕ) : ℚ :=
  terminalReward (P.sampleOutcome ω off).2

/-- The law of the pair and terminal state of one sample, under fair bits. -/
def sampleLaw (a : Option (VertexPair n) × Option (MarkedState n)) : ℝ :=
  fairProb P.sampleBits (fun ω => P.sampleOutcome (tapeBit ω) 0 = a)

/-- The law of the pair and terminal state with exact categorical draws: uniform pair, then `L`
exact Euler steps. -/
def exactSampleLaw (a : Option (VertexPair n) × Option (MarkedState n)) : ℝ :=
  match a with
  | (some w, y) => ((n.choose 2 : ℕ) : ℝ)⁻¹ * ((P.eulerLaw w P.L y : ℚ) : ℝ)
  | (none, _) => 0

/-- The exact rational average of the `j`-th batch of `S` independent samples. -/
def batchAverage (ω : ℕ → Bool) (j : ℕ) : ℚ :=
  (∑ i ∈ Finset.range P.S, P.sampleReward ω ((j * P.S + i) * P.sampleBits)) / P.S

/-- The median of the `b` batch averages (`b` odd in both algorithms). -/
def medianOfBatches (ω : ℕ → Bool) : ℚ :=
  (((List.range P.b).map (P.batchAverage ω)).insertionSort (· ≤ ·)).getD (P.b / 2) 0

/-- The real rates of the absorbing process of these parameters. -/
def chainRate (w : VertexPair n) : Option (MarkedState n) → Option (MarkedState n) → ℝ :=
  P.H.absorbingRate (fun e => ((P.r e : ℚ) : ℝ)) ((P.Λ : ℚ) : ℝ) w

/-- The exact Euler law, as real numbers. -/
def eulerLawReal (w : VertexPair n) (y : Option (MarkedState n)) : ℝ :=
  ((P.eulerLaw w P.L y : ℚ) : ℝ)

/-- All bits used by the median-of-batches estimator; fixed before the run. -/
def totalBits : ℕ := P.b * P.S * P.sampleBits

end SamplerParams

end HypergraphUnreliability.FPRAS


