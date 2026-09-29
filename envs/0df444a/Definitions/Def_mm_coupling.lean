-- Prove2me | Definitions.Def_mm_coupling
-- name    : mm_coupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T20:08:45.316354+00:00
-- url     : https://prove2.me/theorems/14bdabfb-f56d-4160-822c-12ad31f26a0a
-- title:
--   Markovian couplings, the torus, colorings, and the hardcore model
-- statement:
--   This file provides the vocabulary of Chapter 5 of Levin–Peres–Wilmer — Markovian couplings — together with the concrete chains on which the chapter's coupling arguments run.
--
--   **Markovian couplings.** A Markovian coupling of a chain $P$ is a chain $Q$ on ordered pairs of states satisfying three requirements: each coordinate moves like $P$,
--   $$\sum_{y'}Q\bigl((x,y),(x',y')\bigr)=P(x,x'),\qquad \sum_{x'}Q\bigl((x,y),(x',y')\bigr)=P(y,y'),$$
--   $Q$ is a genuine transition matrix, and the two copies run together once they meet: from a diagonal state $(x,x)$, $Q$ gives no mass to off-diagonal pairs (the "sticky" convention of Section 5.2). The diagonal $\{(v,v):v\in V\}$ is defined as a set of pair-states, so that the coupling time becomes the hitting time of the diagonal in the trajectory calculus of Mission I.
--
--   **The discrete torus.** The graph on $\mathbb Z_n^d$ (configurations $\{0,\dots,d-1\}\to\mathbb Z_n$) joining $x\ne y$ exactly when they agree in all coordinates but one and differ by $\pm1\pmod n$ in that coordinate — the stage for the coupling bound on the lazy torus walk.
--
--   **Proper colorings and the Metropolis chain on them.** A $q$-coloring $x$ of a graph $G$ is **proper** when adjacent vertices always receive different colors. On the set of proper colorings, the Metropolis chain proposes a uniform (vertex, color) pair and accepts when the recolored configuration is again proper: two distinct proper colorings $x\ne y$ are linked with probability
--   $$1/(nq)\ \text{ if they differ at exactly one vertex},\qquad 0\ \text{otherwise},$$
--   ($n$ the number of vertices), the diagonal absorbing the rejected mass.
--
--   **The hardcore model.** A Boolean configuration $\sigma$ on the vertices of $G$ is **hardcore** when no two adjacent vertices are both occupied — occupied sites form an independent set. With fugacity $\lambda$, a configuration carries weight $\lambda^{|\sigma|}$ ($|\sigma|$ = number of occupied sites) if hardcore and $0$ otherwise, and the hardcore distribution is the normalization
--   $$\pi(\sigma)=\frac{w(\sigma)}{\sum_\tau w(\tau)}.$$
--
--   **Restriction of a chain.** For a predicate on states, the submatrix of $P$ on the states satisfying it (no renormalization) — used to regard the Glauber dynamics of the hardcore model as a chain on the admissible configurations.
--
--   **Conventions.** Division is total ($r/0=0$), so every quantity is defined without side conditions; stochasticity and stationarity claims are the accompanying theorems' business.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 5, Sections 5.2-5.4 and Sections 3.1, 3.3.4, pp. 63-71

import Definitions.Def_mm_mixing
import Definitions.Def_mm_path

/-!
Couplings of Markov chains, following Levin–Peres–Wilmer, *Markov Chains and
Mixing Times*, Chapter 5.

A Markovian coupling of a chain `P` is a chain on pairs whose two coordinate
processes are each copies of `P` (LPW §5.2); we additionally record the
convention (5.2) that the two chains stay together once they have met.  The
coupling time is the hitting time of the diagonal, so its tail probabilities
are `setAvoidTailProb` of the pair chain.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **Markovian coupling** of the chain `P` satisfying the
stay-together convention (5.2): a transition matrix `Q` on pairs whose first
and second marginals are both `P`, and which moves diagonal states to
diagonal states (LPW §5.2). -/
def IsMarkovianCoupling (P : Matrix V V ℝ) (Q : Matrix (V × V) (V × V) ℝ) : Prop :=
  IsStochastic Q ∧
  (∀ p : V × V, ∀ x' : V, ∑ y', Q p (x', y') = P p.1 x') ∧
  (∀ p : V × V, ∀ y' : V, ∑ x', Q p (x', y') = P p.2 y') ∧
  ∀ x : V, ∀ q : V × V, q.1 ≠ q.2 → Q (x, x) q = 0

/-- The diagonal `{(x,x) : x ∈ Ω}` of the pair space — the target set of the
coupling time `τ_couple` (LPW §5.2, Eq. (5.3)). -/
def pairDiagonal (V : Type*) [Fintype V] [DecidableEq V] : Finset (V × V) :=
  Finset.univ.filter fun p : V × V => p.1 = p.2

/-- The `d`-dimensional discrete **torus** `ℤ_n^d`: configurations
`Fin d → ZMod n`, adjacent when they differ in exactly one coordinate by
`±1` (LPW §5.3.2). -/
def torusGraph (d n : ℕ) : SimpleGraph (Fin d → ZMod n) where
  Adj x y := x ≠ y ∧ ∃ j : Fin d,
    (∀ i : Fin d, i ≠ j → x i = y i) ∧ (y j = x j + 1 ∨ y j = x j - 1)
  symm := by
    constructor
    rintro x y ⟨hxy, j, hoff, hj⟩
    refine ⟨Ne.symm hxy, j, fun i hi => (hoff i hi).symm, ?_⟩
    rcases hj with h | h
    · exact Or.inr (by rw [h]; ring)
    · exact Or.inl (by rw [h]; ring)
  loopless := ⟨fun x h => h.1 rfl⟩

instance torusGraphAdjDecidable (d n : ℕ) : DecidableRel (torusGraph d n).Adj :=
  fun x y =>
    inferInstanceAs (Decidable (x ≠ y ∧ ∃ j : Fin d,
      (∀ i : Fin d, i ≠ j → x i = y i) ∧ (y j = x j + 1 ∨ y j = x j - 1)))

/-- A **proper `q`-coloring** of a graph: adjacent vertices receive distinct
colors (LPW §3.1). -/
def IsProperColoring {Vv : Type*} (G : SimpleGraph Vv) {q : ℕ} (x : Vv → Fin q) : Prop :=
  ∀ v w : Vv, G.Adj v w → x v ≠ x w

variable {Vv : Type*} [Fintype Vv] [DecidableEq Vv]

instance {G : SimpleGraph Vv} [DecidableRel G.Adj] {q : ℕ} :
    DecidablePred fun c : Vv → Fin q => IsProperColoring G c :=
  fun c => inferInstanceAs (Decidable (∀ v w : Vv, G.Adj v w → c v ≠ c w))

/-- Off-diagonal transition probabilities of the **Metropolis chain on proper
`q`-colorings** (LPW §5.4.1, cf. Example 3.5): propose a uniform vertex `v`
and a uniform color `k`; recolor `v` with `k` if the result is again proper.
A proper coloring `y ≠ x` is reachable in one step iff it differs from `x` at
exactly one vertex, in which case its probability is `1/(nq)`. -/
def coloringStep (G : SimpleGraph Vv) [DecidableRel G.Adj] (q : ℕ)
    (x y : {c : Vv → Fin q // IsProperColoring G c}) : ℝ :=
  if (Finset.univ.filter fun v : Vv => x.1 v ≠ y.1 v).card = 1 then
    ((Fintype.card Vv : ℝ) * q)⁻¹
  else 0

/-- The **Metropolis chain on proper `q`-colorings** of `G`
(LPW §5.4.1). -/
def coloringMetropolis (G : SimpleGraph Vv) [DecidableRel G.Adj] (q : ℕ) :
    Matrix {c : Vv → Fin q // IsProperColoring G c}
      {c : Vv → Fin q // IsProperColoring G c} ℝ :=
  fun x y =>
    if y = x then 1 - ∑ z ∈ ({x}ᶜ : Finset {c : Vv → Fin q // IsProperColoring G c}),
      coloringStep G q x z
    else coloringStep G q x y

/-- A **hardcore configuration**: an independent set of occupied vertices
(LPW §3.3.1). -/
def IsHardcore (G : SimpleGraph Vv) (σ : Vv → Bool) : Prop :=
  ∀ v w : Vv, G.Adj v w → ¬(σ v = true ∧ σ w = true)

instance {G : SimpleGraph Vv} [DecidableRel G.Adj] :
    DecidablePred (IsHardcore G) :=
  fun σ => inferInstanceAs (Decidable (∀ v w : Vv, G.Adj v w → ¬(σ v = true ∧ σ w = true)))

/-- The unnormalized weight `λ^{#occupied}` of a hardcore configuration, `0`
for non-hardcore configurations (LPW §3.3.4). -/
def hardcoreWeight (G : SimpleGraph Vv) [DecidableRel G.Adj] (lam : ℝ)
    (σ : Vv → Bool) : ℝ :=
  if IsHardcore G σ then lam ^ (Finset.univ.filter fun v : Vv => σ v = true).card
  else 0

/-- The **hardcore model with fugacity `λ`** on `G`:
`π(σ) ∝ λ^{#occupied σ}` on hardcore configurations (LPW §3.3.4). -/
def hardcoreDist (G : SimpleGraph Vv) [DecidableRel G.Adj] (lam : ℝ) :
    (Vv → Bool) → ℝ :=
  fun σ => hardcoreWeight G lam σ / ∑ τ : Vv → Bool, hardcoreWeight G lam τ

/-- The restriction of a chain to the states satisfying `p` (used to view a
chain supported on a subset of configurations as a chain on that subset). -/
def subChain (P : Matrix V V ℝ) (p : V → Prop) [DecidablePred p] :
    Matrix {x : V // p x} {x : V // p x} ℝ :=
  fun a b => P a.1 b.1

end

end MarkovMixing


