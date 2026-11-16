-- Prove2me | Definitions.Def_LEDPCount_Supplement_InteractiveLocal
-- name    : LEDPCount_Supplement_InteractiveLocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:58:01.709181+00:00
-- url     : https://prove2.me/theorems/786d1472-7067-4680-b6e5-e774a236945d
-- title:
--   Fully interactive local algorithms on graphs, their transcript law, $(\varepsilon,\delta)$-LEDP on a graph family, and accuracy
-- statement:
--   In the **local model for graph data**, each vertex $i\in[n]$ of an $n$-vertex graph $G$ is a party holding its adjacency vector $A_i\in\{0,1\}^n$ as its private input. A **fully interactive local algorithm** interacts with the parties only through local randomizers. It runs for $T$ steps; write $\Pi_t$ for the transcript after step $t$, with $\Pi_0$ empty. At step $t$:
--
--   1. as an arbitrary randomized function of $\Pi_{t-1}$, the algorithm makes a *choice* $c$, which selects a party $i=\mathrm{party}(c)$ and assigns it a local randomizer $R_c:\{0,1\}^n\to\mathcal M$ that is an $(\varepsilon',\delta')$-**local randomizer** for some $\varepsilon'>0$, $\delta'\in[0,1)$ (Definition 2.14): for all $a,a'\in\{0,1\}^n$ differing in exactly one coordinate and every measurable $S\subseteq\mathcal M$,
--   $$
--   \Pr[R_c(a)\in S]\le e^{\varepsilon'}\Pr[R_c(a')\in S]+\delta';
--   $$
--   2. party $i$ applies $R_c$ to $A_i$ with fresh coins and sends the message $m$;
--   3. the pair $(c,m)$ is appended to the transcript.
--
--   The **complete transcript** is $\Pi(G)=\Pi_T$, and the output $\hat f(G)$ is a randomized function of $\Pi(G)$.
--
--   For a family $\mathcal G$ of graphs on $[n]$, the algorithm is **$(\varepsilon,\delta)$-LEDP on $\mathcal G$** (Definition 2.13) if for every pair $G,G'\in\mathcal G$ of edge-neighbouring graphs (differing in exactly one edge, Definition 2.11) and every measurable set $S$ of transcripts,
--   $$
--   \Pr[\Pi(G)\in S]\le e^{\varepsilon}\Pr[\Pi(G')\in S]+\delta .
--   $$
--   It **counts a pattern $H$ on $\mathcal G$ with additive error at most $\alpha$ with probability at least $2/3$** if for every $G\in\mathcal G$
--   $$
--   \Pr\bigl[\,|\hat f(G)-f_H(G)|\le\alpha\,\bigr]\ge\tfrac23,
--   $$
--   where $f_H(G)$ is the number of non-induced copies of $H$ in $G$.
--
--   These are the algorithm class, the privacy notion and the accuracy notion of the lower bound Theorem 5.3, which holds against every such algorithm, however many rounds of interaction it uses.
--
--   **Formalization Note** The paper's rounds are serialized: a round that selects several parties becomes consecutive steps, one per selected party, whose choices may ignore the in-round messages; the transcript records the choice $c$, from which the selected party, its randomizer and the parameters are read off. Choices and messages live in arbitrary measurable spaces (a protocol whose randomizers have different output spaces uses their disjoint union); choices and the output are Markov kernels; the number of steps $T$ is an arbitrary natural number fixed by the algorithm. The transcript law is defined by recursion on the number of steps (kernel composition). Bits are `Bool`; "differing in exactly one coordinate" is the published `PrivLearn.Generic.Neighbors`, the DP inequality is the published `ContinualCounting.IsApproxDP`, $A_i$ is the published `LEDPCount.adjRow`, edge neighbours are `LEDPCount.EdgeNeighbors` and $f_H$ is `LEDPCount.subgraphCount`. The two-round protocol `LEDPCount.TwoRoundLocal` of the base mission is a special case.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), §2.4, Local Differential Privacy, Definitions 2.12–2.14, pp.16–17 (PDF pp.18–19); Theorem 5.3, p.56 (PDF p.58)

import Mathlib
import Definitions.Def_ContinualCounting_IsApproxDP
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_LEDPCount_EdgeNeighbors
import Definitions.Def_LEDPCount_subgraphCount
import Definitions.Def_LEDPCount_TwoRoundLocal

namespace LEDPCount.Supplement

open MeasureTheory ProbabilityTheory

/-- A fully interactive local algorithm on `n`-vertex graphs (Chen–Peng, *The Power of Interaction
in Locally Edge-Private Subgraph Counting*, arXiv:2611.05038, held version sha256 d18032b0…, §2.4,
"Local Differential Privacy", p.16–17, PDF p.18–19, and Definitions 2.12–2.14): every vertex `i` is
a party holding its adjacency vector `A_i ∈ {0,1}^n`. The algorithm runs for `T` steps. At step `t`
it draws a *choice* `c ∈ Ch` from `choose t`, a Markov kernel of the transcript so far (so the
choice is an arbitrary randomized function of the past transcript); the choice selects the party
`party c` and the local randomizer `R_c = fun a => rand a c : {0,1}^n → M`, which is an
`(ε', δ')`-local randomizer (Definition 2.14) for some `ε' > 0`, `δ' ∈ [0, 1)`. The selected party
applies `R_c` to its own adjacency vector with fresh coins and sends the message `m ∈ M`. The
transcript records every pair `(c, m)`. The output is drawn from the Markov kernel `output`
applied to the complete transcript.

**Formalization Note** The paper's rounds are serialized: a round in which several parties are
selected becomes consecutive steps, one per selected party, whose choices depend on the transcript
before the round only (the kernels may ignore the in-round messages), so every round-based
algorithm of §2.4 is one of these; the transcript records the choice `c`, from which the selected
party, the randomizer and its parameters are read off. The message space `M` and the choice space
`Ch` are arbitrary measurable spaces (a protocol whose randomizers have different output spaces
uses their disjoint union). The number of steps `T` is a fixed but arbitrary natural number. Bits
are `Bool`; "differing in exactly one coordinate" is the published `PrivLearn.Generic.Neighbors`,
and the local-randomizer inequality is the published `ContinualCounting.IsApproxDP`. The published
`LEDPCount.TwoRoundLocal` is a special case. -/
structure InteractiveLocal (n : ℕ) (Ch M : Type) [MeasurableSpace Ch] [MeasurableSpace M] where
  /-- The number of steps. -/
  T : ℕ
  /-- The choice made at step `t`, as a randomized function of the transcript of steps `< t`. -/
  choose : (t : ℕ) → Kernel (Fin t → Ch × M) Ch
  choose_markov : ∀ t, IsMarkovKernel (choose t)
  /-- The party selected by a choice. -/
  party : Ch → Fin n
  party_measurable : Measurable party
  /-- The local randomizer assigned by a choice, as a kernel in the choice for each input `a`;
  `fun a => rand a c` is the randomizer `R_c : {0,1}^n → M`. -/
  rand : (Fin n → Bool) → Kernel Ch M
  rand_markov : ∀ a, IsMarkovKernel (rand a)
  /-- Every assigned randomizer is an `(ε', δ')`-local randomizer (Definition 2.14). -/
  rand_local : ∀ c : Ch, ∃ ε' δ' : ℝ, 0 < ε' ∧ 0 ≤ δ' ∧ δ' < 1 ∧
    ContinualCounting.IsApproxDP PrivLearn.Generic.Neighbors (fun a => rand a c) ε' δ'
  /-- The (randomized) output, a function of the complete transcript. -/
  output : Kernel (Fin T → Ch × M) ℝ
  output_markov : IsMarkovKernel output

namespace InteractiveLocal

variable {n : ℕ} {Ch M : Type} [MeasurableSpace Ch] [MeasurableSpace M]

instance (A : InteractiveLocal n Ch M) (t : ℕ) : IsMarkovKernel (A.choose t) := A.choose_markov t

instance (A : InteractiveLocal n Ch M) (a : Fin n → Bool) : IsMarkovKernel (A.rand a) :=
  A.rand_markov a

instance (A : InteractiveLocal n Ch M) : IsMarkovKernel A.output := A.output_markov

/-- The message sent on the graph `G` after the choice `c`: the selected party `i = party c`
applies the randomizer `R_c` to its adjacency vector `A_i` (the published `LEDPCount.adjRow`). -/
noncomputable def msgKernel (A : InteractiveLocal n Ch M) (G : SimpleGraph (Fin n)) :
    Kernel Ch M where
  toFun c := A.rand (LEDPCount.adjRow G (A.party c)) c
  measurable' := by
    have hF : Measurable fun p : Ch × (Fin n → Bool) => A.rand p.2 p.1 :=
      measurable_from_prod_countable_left fun a => (A.rand a).measurable
    have hg : Measurable fun c : Ch => (c, LEDPCount.adjRow G (A.party c)) :=
      measurable_id.prodMk ((measurable_from_top (f := LEDPCount.adjRow G)).comp
        A.party_measurable)
    exact hF.comp hg

/-- One step on the graph `G`: the choice `c ∼ choose t (history)`, then the message
`m ∼ R_c(A_{party c})`, returned as the pair `(c, m)`. -/
noncomputable def stepKernel (A : InteractiveLocal n Ch M) (G : SimpleGraph (Fin n)) (t : ℕ) :
    Kernel (Fin t → Ch × M) (Ch × M) :=
  (Kernel.id ×ₖ A.msgKernel G) ∘ₖ A.choose t

/-- Appending the pair of step `t` to the transcript of steps `< t` is measurable. -/
lemma measurable_snoc (t : ℕ) :
    Measurable fun p : (Fin t → Ch × M) × (Ch × M) => (Fin.snoc p.1 p.2 : Fin (t + 1) → Ch × M) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [Fin.snoc_last] using measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

/-- The law of the transcript of the first `t` steps on the graph `G`, defined by recursion on
`t`: the empty transcript, then each step appends `(c, m) ∼ stepKernel t` with fresh coins. -/
noncomputable def histLaw (A : InteractiveLocal n Ch M) (G : SimpleGraph (Fin n)) :
    (t : ℕ) → Measure (Fin t → Ch × M)
  | 0 => Measure.dirac (Fin.elim0 : Fin 0 → Ch × M)
  | t + 1 => Kernel.mapOfMeasurable (Kernel.id ×ₖ A.stepKernel G t)
      (fun p => (Fin.snoc p.1 p.2 : Fin (t + 1) → Ch × M)) (measurable_snoc t) ∘ₘ histLaw A G t

/-- The law of the complete transcript `Π(G)` on the graph `G` (§2.4, p.17, PDF p.19). -/
noncomputable def transcript (A : InteractiveLocal n Ch M) (G : SimpleGraph (Fin n)) :
    Measure (Fin A.T → Ch × M) :=
  A.histLaw G A.T

/-- The law of the algorithm's output on the graph `G`. -/
noncomputable def outputLaw (A : InteractiveLocal n Ch M) (G : SimpleGraph (Fin n)) : Measure ℝ :=
  A.output ∘ₘ A.transcript G

/-- Definition 2.13 (Local Edge Differential Privacy) for an algorithm on a graph family `𝒢`
(p.17, PDF p.19, and "LEDP algorithm on `G_{n,d}`", p.56, PDF p.58): the complete transcript is
`(ε, δ)`-DP for every edge-neighbouring pair `G ∼ G'` (Definition 2.11) of graphs in `𝒢`:
`Pr[Π(G) ∈ S] ≤ e^ε Pr[Π(G') ∈ S] + δ` for every measurable `S`.

**Formalization Note** The inequality is the published `ContinualCounting.IsApproxDP`; the ranges
`ε > 0`, `δ ∈ [0, 1)` of Definition 2.13 are hypotheses of the theorems using it. -/
def IsLEDPOn (A : InteractiveLocal n Ch M) (𝒢 : Set (SimpleGraph (Fin n))) (ε δ : ℝ) : Prop :=
  ContinualCounting.IsApproxDP
    (fun G G' : SimpleGraph (Fin n) => LEDPCount.EdgeNeighbors G G' ∧ G ∈ 𝒢 ∧ G' ∈ 𝒢)
    A.transcript ε δ

/-- `A` counts the pattern `H` on the graph family `𝒢` with additive error at most `α` with
probability at least `2/3` (p.56, PDF p.58): for every `G ∈ 𝒢`,
`Pr[|f̂_H(G) − f_H(G)| ≤ α] ≥ 2/3`, where `f̂_H(G)` is the output and `f_H(G)` is the published
`LEDPCount.subgraphCount`. -/
def CountsWithError (A : InteractiveLocal n Ch M) {k : ℕ} (H : SimpleGraph (Fin k))
    [DecidableRel H.Adj] (𝒢 : Set (SimpleGraph (Fin n))) (α : ℝ) : Prop :=
  ∀ G ∈ 𝒢, ENNReal.ofReal (2 / 3) ≤
    A.outputLaw G {y : ℝ | |y - LEDPCount.subgraphCount H G| ≤ α}

end InteractiveLocal

end LEDPCount.Supplement


