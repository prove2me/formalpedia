-- Prove2me | Definitions.Def_StreamingWeightedSetCover1523_LowerBound_Model
-- name    : StreamingWeightedSetCover1523_LowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:45.625191+00:00
-- url     : https://prove2.me/theorems/d5974de9-0e44-4a14-bd76-6954ebf5b4c9
-- title:
--   Weighted set cover, multipass streaming machines, densities and protocol runs
-- statement:
--   General objects used throughout the mission.
--
--   1. **Weighted set cover.** An instance consists of finitely many indexed identifiers $i\in\iota$, each carrying a subset $S_i$ of a finite universe $U$ and a real weight $w_i$; repeated contents keep separate identifiers. A family $F\subseteq\iota$ is a cover if $\bigcup_{i\in F}S_i=U$, its cost is $\sum_{i\in F}w_i$, and
--   $$\mathrm{OPT}=\min\{\mathrm{cost}(F): F \text{ a cover}\}\in\mathbb R\cup\{+\infty\},$$
--   with $\mathrm{OPT}=+\infty$ when no cover exists.
--
--   2. **Streaming machines.** A deterministic multipass machine reading a stream of $L$ items has a state set $Q$, an initial state, a transition $Q\times\mathrm{Item}\to Q$ for every pass number and every stream position, and an answer map from states. A pass applies the transitions to the items in the order $1,\dots,L$; after $p$ passes the answer is the answer map at the final state. Computation is unrestricted; everything retained from the input lies in the state.
--
--   3. **Densities and relative entropy.** On a finite set with uniform law $U$, a density is a function $f\ge 0$ with $\mathbb E_U f=1$, and
--   $$\mathrm{Ent}(f)=\mathbb E_U[f\ln f]$$
--   (natural logarithm, $0\ln 0=0$). For a nonempty set $R$ of $r$-tuples, $f_i(x)=|\{t\in R:t_i=x\}|\,/\,(|R|\cdot\Pr_U[x])$ is the density of the $i$-th coordinate of a uniform element of $R$, and $\bar f=r^{-1}\sum_i f_i$.
--
--   4. **Protocol runs.** For a deterministic two-party protocol tree (the published `DetCCHard.Protocol`: internal nodes owned by Alice or Bob with a bit function of the owner's input, leaves labelled by an output bit), the run on $(x,y)$ passes through the node named by a bit sequence $w$ when following the bits sent from the root reproduces $w$; the transcript is the full bit sequence up to the leaf. The acceptance probability of a randomized protocol under an input law is the average over inputs and over input-independent coins of the indicator that the reached leaf is labelled `true`.
--
--   These are the operational models on which every statement of the mission is evaluated.
--
--   **Formalization Note** The optimum is a minimum in `WithTop ℝ`, so it never returns a default value on an uncoverable instance. The transition of a machine may depend on the pass number and stream position; this only enlarges the class of machines.
-- source:
--   Ali Vakilian, Streaming Weighted Set Cover Requires (Nearly) Linear Space, STOC 2027 submission #1523 (October 2026), §1 (PDF p. 2), §1.1 (PDF p. 3), §2.4 (PDF p. 11), §3 (PDF pp. 13–14); citation basis: submitted artifact, sha256 16f3c2dfc6183f4752aece654f17f2cb6a47fbe55659e6906ad7bd3524d6223f

import Mathlib
import Definitions.Def_DetCCHard_Protocol

open MeasureTheory
open scoped BigOperators ENNReal

namespace StreamingWeightedSetCover1523.LowerBound
noncomputable section

/-! General objects used by the mission (Vakilian, STOC 2027 submission #1523, §1, §1.1, §2.4, §3):
weighted set cover with an extended optimum, multipass streaming machines with a bounded
state set, densities and relative entropy with respect to the uniform law, and runs of
two-party protocol trees (the published `DetCCHard.Protocol`). -/

/-- A weighted set cover instance (§1, PDF p. 2): indexed input identifiers `ι`, each carrying a
subset of the finite universe `U` and a real weight. Repeated contents keep separate identifiers. -/
structure WSCInstance (ι U : Type) where
  sets : ι → Finset U
  weight : ι → ℝ

namespace WSCInstance

variable {ι U : Type}

/-- `F` is a feasible solution: the union of its sets is the whole universe. -/
def IsCover (I : WSCInstance ι U) (F : Finset ι) : Prop :=
  ∀ u : U, ∃ i ∈ F, u ∈ I.sets i

/-- The cost of a family of identifiers: the sum of their weights. -/
def cost (I : WSCInstance ι U) (F : Finset ι) : ℝ :=
  ∑ i ∈ F, I.weight i

/-- `OPT`: the least cost of a feasible solution, computed as a minimum over the finite set of all
covers, in `WithTop ℝ`; an uncoverable instance has `OPT = ⊤` (no default-zero infimum). -/
def opt [Fintype ι] (I : WSCInstance ι U) : WithTop ℝ := by
  classical
  exact (Finset.univ.filter fun F : Finset ι => I.IsCover F).inf
    fun F => ((I.cost F : ℝ) : WithTop ℝ)

/-- The instance has at least one cover. -/
def Coverable (I : WSCInstance ι U) : Prop :=
  ∃ F : Finset ι, I.IsCover F

end WSCInstance

/-- A deterministic multipass streaming machine (§1.1, PDF p. 3) reading a stream of `L` items of
type `Item`, with working-state set `Q` and answer type `Out`. The transition may depend
arbitrarily on the pass number and the stream position (computation is unrestricted); everything
retained from the input lies in the state. The answer is a function of the final state. -/
structure Machine (L : ℕ) (Item Q Out : Type) where
  init : Q
  step : ℕ → Fin L → Q → Item → Q
  out : Q → Out

namespace Machine

variable {L : ℕ} {Item Q Out : Type}

/-- One pass, number `j`, over the stream `xs` in the fixed order `0, 1, …, L-1`, from state `q`. -/
def onePass (m : Machine L Item Q Out) (j : ℕ) (xs : Fin L → Item) (q : Q) : Q :=
  (List.finRange L).foldl (fun q i => m.step j i q (xs i)) q

/-- The state after passes `0, …, p-1`, starting from the initial state. -/
def finalState (m : Machine L Item Q Out) (p : ℕ) (xs : Fin L → Item) : Q :=
  (List.range p).foldl (fun q j => m.onePass j xs q) m.init

/-- The answer after `p` passes. -/
def run (m : Machine L Item Q Out) (p : ℕ) (xs : Fin L → Item) : Out :=
  m.out (m.finalState p xs)

end Machine

/-- The mean of `f` under the uniform law on a finite nonempty type, `E_U f`. -/
def uniformMean {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

/-- A density relative to the uniform law (§2.4, PDF p. 11): nonnegative with `E_U f = 1`. -/
def IsDensity {α : Type} [Fintype α] (f : α → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ uniformMean f = 1

/-- `Ent f = E_U[f ln f]`, relative entropy to the uniform law in nats (§2.4, PDF p. 11);
`Real.log 0 = 0` gives the convention `0 ln 0 = 0`. -/
def Ent {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  uniformMean fun x => f x * Real.log (f x)

/-- Given a nonempty event `R` of `r`-tuples over a finite alphabet, the density relative to the
uniform law of the `i`-th coordinate of a uniform element of `R` (§3, Lemma 3.2):
`f_i(x) = Pr[X_i = x | R] / (1/|α|)`. -/
def condMarginal {α : Type} [Fintype α] [DecidableEq α] {r : ℕ} (R : Finset (Fin r → α))
    (i : Fin r) (x : α) : ℝ :=
  (Fintype.card α : ℝ) * ((R.filter fun t => t i = x).card : ℝ) / (R.card : ℝ)

/-- `f̄ = r⁻¹ ∑ᵢ fᵢ`, the density of the coordinate at an independent uniform position. -/
def avgMarginal {α : Type} [Fintype α] [DecidableEq α] {r : ℕ} (R : Finset (Fin r → α))
    (x : α) : ℝ :=
  (∑ i : Fin r, condMarginal R i x) / (r : ℝ)

/-- The run of a deterministic protocol tree (published `DetCCHard.Protocol`: internal nodes owned
by Alice or Bob with a bit function of the owner's input, leaves labelled by an output bit) on
`(x, y)` passes through the node named by the bit sequence `w` (§3, PDF p. 12). -/
def protocolReaches {X Y : Type} : DetCCHard.Protocol X Y → List Bool → X → Y → Prop
  | _, [], _, _ => True
  | .leaf _, _ :: _, _, _ => False
  | .alice f p₀ _, false :: w, x, y => f x = false ∧ protocolReaches p₀ w x y
  | .alice f _ p₁, true :: w, x, y => f x = true ∧ protocolReaches p₁ w x y
  | .bob g p₀ _, false :: w, x, y => g y = false ∧ protocolReaches p₀ w x y
  | .bob g _ p₁, true :: w, x, y => g y = true ∧ protocolReaches p₁ w x y

/-- The transcript of `(x, y)`: the sequence of all bits sent until a leaf is reached. -/
def protocolTranscript {X Y : Type} : DetCCHard.Protocol X Y → X → Y → List Bool
  | .leaf _, _, _ => []
  | .alice f p₀ p₁, x, y =>
      if f x then true :: protocolTranscript p₁ x y else false :: protocolTranscript p₀ x y
  | .bob g p₀ p₁, x, y =>
      if g y then true :: protocolTranscript p₁ x y else false :: protocolTranscript p₀ x y

/-- Acceptance probability of a randomized protocol: the input `i` is drawn with weight `law i`,
split into Alice's and Bob's parts by `split`, and the coins `ω ∼ P` (public and private, independent
of the input) select a deterministic tree, whose leaf output `true` means accept. -/
def acceptProb {I X Y Ω : Type} [Fintype I] [MeasurableSpace Ω] (law : I → ℝ)
    (split : I → X × Y) (P : Measure Ω) (tree : Ω → DetCCHard.Protocol X Y) : ℝ :=
  ∑ i, law i * (P {ω | (tree ω).eval (split i).1 (split i).2 = true}).toReal

end
end StreamingWeightedSetCover1523.LowerBound


