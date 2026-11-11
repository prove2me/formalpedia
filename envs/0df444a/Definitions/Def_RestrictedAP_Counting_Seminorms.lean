-- Prove2me | Definitions.Def_RestrictedAP_Counting_Seminorms
-- name    : RestrictedAP_Counting_Seminorms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:03.009263+00:00
-- url     : https://prove2.me/theorems/da0c0324-2b01-4a16-a89e-6a20661ea904
-- title:
--   The $\mu$-seminorm, pairwise connectedness, $\|\cdot\|_{\nu,\alpha}$ and decay functions
-- statement:
--   For a distribution $\mu$ on $\Sigma\times\Gamma\times\Phi$ and $f:\Sigma^n\to\mathbb C$, the **$\mu$-seminorm** (Definition 2.17) is
--   $$\|f\|_\mu=\sup_{\substack{g:\Gamma^n\to\mathbb C,\ h:\Phi^n\to\mathbb C\\ 1\text{-bounded}}}\Big|\mathbb E_{(x,y,z)\sim\mu^{\otimes n}}[f(x)g(y)h(z)]\Big|.$$
--   A distribution $\mu$ on $\Sigma^3$ is **pairwise connected** if for each pair of coordinates the bipartite graph whose two sides are copies of $\Sigma$, with an edge $(a,b)$ whenever $a$ and $b$ occur together (in those two coordinates) in an atom of $\mu$, is connected on its non-isolated vertices. For a distribution $\nu$ on $\Sigma$ and $\alpha>0$ (Definition 2.18), $M_{\nu,\alpha}$ is the set of pairwise connected distributions $\mu$ on $\Sigma^3$ with no $(\mathbb Z,+)$-embedding, with $\mu_x=\nu$ or $\mu_y=\nu$ or $\mu_z=\nu$, and with every atom of probability at least $\alpha$; and (Definition 2.19)
--   $$\|f\|_{\nu,\alpha}=\sup_{\mu\in M_{\nu,\alpha}}\|f\|_\mu ,$$
--   written $\|f\|_\nu$ when $\alpha$ is clear. A **decay function** (pp. 6–7) is $w:(0,1)\to(0,1)$, monotonically increasing, with $w(\varepsilon)\le\varepsilon$; a two-argument decay function $w:(0,1)\times\mathbb N\to(0,1)$ has these properties in its first argument. The sequence of Lemma 4.1 is $\varepsilon_0=1/2$, $\varepsilon_{i+1}=w(\varepsilon_i,i)$.
--
--   **Formalization Note.** Pairwise connectedness is not defined in the paper; it is the notion of the cited [BKM24b], encoded by `PairwiseConnected` through `SimpleGraph.Reachable`. Suprema are real `sSup`s: the set in `muSeminorm` is nonempty and bounded by $\max|f|$; in `nuNorm` it is bounded by $\max|f|$ and, if $M_{\nu,\alpha}$ is empty, the value is $0$. Decay functions are typed `ℝ → ℝ` (`ℝ → ℕ → ℝ`) with the properties required on $(0,1)$ (`IsDecay`, `IsDecay2`); `decaySeq w i` is $\varepsilon_i$.
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 12, Definitions 2.17–2.19; pp. 6–7; p. 23 (Lemma 4.1's sequence)

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions

namespace RestrictedAP.Counting

/-!
# The `μ`-seminorm, pairwise connectedness and `‖·‖_{ν,α}`; decay functions

Bhangale, Khot, Liu, Minzer, *A Counting Lemma for Somewhat Restricted 3-APs*,
arXiv:2608.17365 (copy sha256 de0b96c1…), p. 12, Definitions 2.17–2.19; pp. 6–7 (decay
functions and `w`-separated scales).

* `muSeminorm μ f` is `‖f‖_μ = sup_{g, h 1-bounded} |E_{μ^{⊗n}}[f(x) g(y) h(z)]|`
  (Definition 2.17). The set of values is nonempty and bounded by `max |f|`, so the real `sSup`
  is the supremum.
* **Pairwise connected** is not defined in the paper (it is the notion of the cited [BKM24b]).
  `PairwiseConnected μ`: for each pair of coordinates of `μ` on `Sig^3`, the bipartite graph
  whose two vertex sides are copies of `Sig` and whose edges are the pairs `(a, b)` occurring
  together in an atom of `μ` is connected on the vertices that lie in the support of the two
  marginals (any two such vertices are joined by a path).
* `MSet ν α` is `M_{ν,α} = M_ν ∩ M_α` (Definition 2.18) and `nuNorm ν α f` is
  `‖f‖_{ν,α} = sup_{μ ∈ M_{ν,α}} ‖f‖_μ` (Definition 2.19); the paper's `‖f‖_ν` is
  `nuNorm ν α f` with the `α` of the context. When `M_{ν,α}` is empty the real `sSup` is `0`,
  the supremum of the empty family of nonnegative numbers.
* Decay functions (pp. 6–7, Lemmas 4.1, 4.4): by default `w : (0,1) → (0,1)` monotonically
  increasing with `w(ε) ≤ ε` (`IsDecay`); the two-argument version `w : (0,1) × ℕ → (0,1)`
  (`IsDecay2`) has the same properties in its first argument for every second argument.
  Functions are typed on `ℝ` and the properties are required on `(0,1)` only.
  `decaySeq w` is `ε_0 = 1/2`, `ε_{i+1} = w(ε_i, i)` (Lemma 4.1).
-/

/-- `‖f‖_μ` (Definition 2.17) for `μ` on `Sig × Γ × Φ` and `f : Sig^n → ℂ`. -/
noncomputable def muSeminorm {Sig Γ Φ : Type*} [Fintype Sig] [Fintype Γ] [Fintype Φ] {n : ℕ}
    (μ : Sig × Γ × Φ → ℝ) (f : (Fin n → Sig) → ℂ) : ℝ :=
  sSup {r | ∃ (g : (Fin n → Γ) → ℂ) (h : (Fin n → Φ) → ℂ), (∀ y, ‖g y‖ ≤ 1) ∧ (∀ z, ‖h z‖ ≤ 1) ∧
    r = ‖∑ t : Fin n → Sig × Γ × Φ, (tensorPow μ n t : ℂ) * f (fun i => (t i).1) *
      g (fun i => (t i).2.1) * h (fun i => (t i).2.2)‖}

/-- The bipartite graph on `A ⊕ B` whose edges are the pairs `(a, b)` with `R a b`. -/
def bipartiteGraph {A B : Type*} (R : A → B → Prop) : SimpleGraph (A ⊕ B) :=
  SimpleGraph.fromRel (fun u v => match u, v with
    | Sum.inl a, Sum.inr b => R a b
    | _, _ => False)

/-- The bipartite graph of `R` is connected on its non-isolated vertices: any two vertices
that carry an edge are joined by a path. -/
def BipartiteConnected {A B : Type*} (R : A → B → Prop) : Prop :=
  ∀ u v : A ⊕ B,
    (match u with | Sum.inl a => ∃ b, R a b | Sum.inr b => ∃ a, R a b) →
    (match v with | Sum.inl a => ∃ b, R a b | Sum.inr b => ∃ a, R a b) →
    (bipartiteGraph R).Reachable u v

/-- `μ` on `Sig^3` is pairwise connected: for each of the three pairs of coordinates the
bipartite graph of pairs occurring in an atom of `μ` is connected (the [BKM24b] notion). -/
def PairwiseConnected {Sig : Type*} (μ : Sig × Sig × Sig → ℝ) : Prop :=
  BipartiteConnected (fun a b : Sig => ∃ c, μ (a, b, c) ≠ 0) ∧
  BipartiteConnected (fun a c : Sig => ∃ b, μ (a, b, c) ≠ 0) ∧
  BipartiteConnected (fun b c : Sig => ∃ a, μ (a, b, c) ≠ 0)

/-- `M_{ν,α} = M_ν ∩ M_α` (Definition 2.18): pairwise connected distributions on `Sig^3` with no
`(ℤ,+)`-embedding, one of whose marginals is `ν`, all of whose atoms have probability `≥ α`. -/
def MSet {Sig : Type*} [Fintype Sig] [DecidableEq Sig] (ν : Sig → ℝ) (α : ℝ) :
    Set (Sig × Sig × Sig → ℝ) :=
  {μ | IsDist μ ∧ PairwiseConnected μ ∧ ¬ DistHasEmbedding ℤ μ ∧
    (marginal μ 0 = ν ∨ marginal μ 1 = ν ∨ marginal μ 2 = ν) ∧ AtomsAtLeast μ α}

/-- `‖f‖_{ν,α} = sup_{μ ∈ M_{ν,α}} ‖f‖_μ` (Definition 2.19). -/
noncomputable def nuNorm {Sig : Type*} [Fintype Sig] [DecidableEq Sig] {n : ℕ}
    (ν : Sig → ℝ) (α : ℝ) (f : (Fin n → Sig) → ℂ) : ℝ :=
  sSup ((fun μ => muSeminorm μ f) '' MSet ν α)

/-- A decay function `w : (0,1) → (0,1)`, monotonically increasing, with `w(ε) ≤ ε`. -/
def IsDecay (w : ℝ → ℝ) : Prop :=
  (∀ ε, 0 < ε → ε < 1 → 0 < w ε ∧ w ε ≤ ε) ∧
  (∀ ε ε', 0 < ε → ε ≤ ε' → ε' < 1 → w ε ≤ w ε')

/-- A two-argument decay function `w : (0,1) × ℕ → (0,1)`: for every `i`, `w(·, i)` is a decay
function. -/
def IsDecay2 (w : ℝ → ℕ → ℝ) : Prop :=
  ∀ i, IsDecay (fun ε => w ε i)

/-- The sequence `ε_0 = 1/2`, `ε_{i+1} = w(ε_i, i)` of Lemma 4.1. -/
noncomputable def decaySeq (w : ℝ → ℕ → ℝ) : ℕ → ℝ
  | 0 => 1 / 2
  | i + 1 => w (decaySeq w i) i

end RestrictedAP.Counting


