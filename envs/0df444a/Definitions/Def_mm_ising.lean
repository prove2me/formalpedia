-- Prove2me | Definitions.Def_mm_ising
-- name    : mm_ising
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T17:25:26.108782+00:00
-- url     : https://prove2.me/theorems/f55a6b8f-1871-4c42-9b8d-b13a32b14351
-- title:
--   The Ising model, its graphs, and block dynamics
-- statement:
--   This file defines the Ising model and its dynamics, following Chapter 15 of Levin–Peres–Wilmer (the single-site dynamics itself is the generic heat bath of Mission II).
--
--   **Spins and the Gibbs distribution.** Spin configurations on the vertex set of a finite graph $G$ assign $\pm1$ to each vertex (encoded over Booleans, $\mathrm{true}\mapsto+1$). At inverse temperature $\beta$, a configuration $\sigma$ carries the **Gibbs weight**
--   $$w(\sigma)=\exp\Bigl(\beta\sum_{\{v,w\}\in E(G)}\sigma(v)\,\sigma(w)\Bigr),$$
--   each edge counted once (the code halves an ordered double sum), and the **Ising distribution** is the normalization $\pi(\sigma)=w(\sigma)/\sum_\tau w(\tau)$. Agreeing neighbours raise the weight, and $\beta$ tunes how strongly.
--
--   **The concrete graphs.** The **cycle** $\mathbb Z_n$ joins each residue to its two neighbours $x\pm1$; the **rooted $b$-ary tree of depth $k$** has as vertices the words of length at most $k$ over a $b$-letter alphabet, a node being joined to the $b$ one-letter extensions of its word (its children).
--
--   **Block dynamics.** For a distribution $\pi$ on configurations and a block $W$ of vertices, one **block update** re-samples the configuration on $W$ from $\pi$ conditioned on agreeing with the current configuration off $W$:
--   $$G_W(\sigma,\tau)=\mathbf 1\{\tau\equiv\sigma\ \text{off}\ W\}\;\frac{\pi(\tau)}{\sum_{\eta\equiv\sigma\ \text{off}\ W}\pi(\eta)}.$$
--   The **block dynamics** for a family of blocks $V_1,\dots,V_b$ picks a block uniformly at random and performs a block update there: $\frac1b\sum_iG_{V_i}$. Single-site Glauber dynamics is the special case of singleton blocks; the comparison between the two is Theorem 15.9, a milestone of this mission.
--
--   **Conventions.** Division is total ($r/0=0$), so the block update is defined for every $\pi$; for the Ising distribution all weights are positive exponentials and no junk case is ever reached.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 15, Sections 15.1, 15.3-15.5 (and Section 3.3.5), pp. 199-209

import Definitions.Def_mm_mcmc
import Definitions.Def_mm_mixing
import Definitions.Def_mm_spectral
import Mathlib.Analysis.Complex.Trigonometric

/-!
The Ising model and its Glauber dynamics, following Levin–Peres–Wilmer,
*Markov Chains and Mixing Times*, Chapter 15 (and §3.3.5).

Spin configurations are encoded as `σ : Vv → Bool`, with `true ↦ +1` and
`false ↦ −1`.  The Gibbs distribution at inverse temperature `β` is
`π(σ) ∝ exp(β ∑_{{v,w} ∈ E} σ(v)σ(w))`, each edge counted once.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {Vv : Type*} [Fintype Vv] [DecidableEq Vv]

/-- The spin value `±1` of a site. -/
def spin (σ : Vv → Bool) (v : Vv) : ℝ :=
  if σ v then 1 else -1

/-- The unnormalized Gibbs weight
`exp(β ∑_{{v,w} ∈ E} σ(v)σ(w))` of a configuration (each edge counted once;
LPW Ch. 15). -/
def isingWeight (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ)
    (σ : Vv → Bool) : ℝ :=
  Real.exp (β * 2⁻¹ * ∑ v, ∑ w, if G.Adj v w then spin σ v * spin σ w else 0)

/-- The **Ising model** at inverse temperature `β` on the graph `G`
(LPW Ch. 15). -/
def isingDist (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) :
    (Vv → Bool) → ℝ :=
  fun σ => isingWeight G β σ / ∑ τ : Vv → Bool, isingWeight G β τ

/-- The cycle graph on `ℤ_n` (`n ≥ 3`). -/
def cycleGraph (n : ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel fun x y => y = x + 1

instance (n : ℕ) : DecidableRel (cycleGraph n).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ (y = x + 1 ∨ x = y + 1)))

/-- The vertex set of the rooted `b`-ary tree of depth `k`: words over
`Fin b` of length at most `k`. -/
def TreeVertex (b k : ℕ) : Type :=
  Σ j : Fin (k + 1), Fin j.val → Fin b

instance (b k : ℕ) : Fintype (TreeVertex b k) :=
  inferInstanceAs (Fintype (Σ j : Fin (k + 1), Fin j.val → Fin b))

instance (b k : ℕ) : DecidableEq (TreeVertex b k) :=
  inferInstanceAs (DecidableEq (Σ j : Fin (k + 1), Fin j.val → Fin b))

/-- The rooted `b`-ary tree of depth `k`: `y` is a child of `x` when the
word `y` extends the word `x` by one letter (LPW §15.4). -/
def aryTree (b k : ℕ) : SimpleGraph (TreeVertex b k) :=
  SimpleGraph.fromRel fun x y =>
    ∃ h : y.1.val = x.1.val + 1,
      ∀ i : Fin x.1.val, y.2 ⟨i.val, by omega⟩ = x.2 i

/-- One **block update** at the block `W`: re-sample the configuration on
`W` from `π` conditioned on agreeing with the current configuration off `W`
(LPW §15.5). -/
def blockUpdate {S : Type*} [Fintype S] [DecidableEq S]
    (π : (Vv → S) → ℝ) (W : Finset Vv) :
    Matrix (Vv → S) (Vv → S) ℝ :=
  fun σ τ =>
    if ∀ w ∉ W, τ w = σ w then
      π τ / ∑ η ∈ Finset.univ.filter (fun η : Vv → S => ∀ w ∉ W, η w = σ w), π η
    else 0

/-- The **block dynamics** for blocks `V_1, …, V_b`: pick a block uniformly
at random and perform a block update there (LPW §15.5). -/
def blockDynamics {S : Type*} [Fintype S] [DecidableEq S]
    (π : (Vv → S) → ℝ) {b : ℕ} (blocks : Fin b → Finset Vv) :
    Matrix (Vv → S) (Vv → S) ℝ :=
  fun σ τ => (b : ℝ)⁻¹ * ∑ i : Fin b, blockUpdate π (blocks i) σ τ

end

end MarkovMixing


