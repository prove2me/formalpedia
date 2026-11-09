-- Prove2me | Definitions.Def_QueryDepthMIS_TwoHopBound
-- name    : QueryDepthMIS_TwoHopBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:35:16.745549+00:00
-- url     : https://prove2.me/theorems/eb7f72be-bfde-413a-b058-4b611de61953
-- title:
--   Conclusion of the two-hop lemma for constants $\beta, \epsilon$
-- statement:
--   For reals $\beta, \epsilon$, `TwoHopBound β ε` is the following statement. For every simple graph $G$ on $n \ge 2$ vertices, every integer $\ell > 10^3$, all sets of positions $P_1, P_2$ with $|P_1| = |P_2| = \ell$ and positions $p_1, p_2, p_3$ with
--   $$
--   P_1 < P_2 < p_1 < p_2 < p_3 < \beta n,
--   $$
--   every set of already exposed positions $S \subseteq [\beta n] = \{1, \dots, \lfloor \beta n \rfloor\}$ such that
--
--   1. $S$ contains $p_1$ and all positions of $[\max P_2] \setminus P_1 \setminus P_2$,
--   2. $S$ contains no position of $P_1 \cup P_2 \cup \{p_2, p_3\}$,
--   3. for some integer $1 \le \tau < \min P_1$, $[\tau] \subseteq S$ and $\Delta(G_{\mathrm{alive}}(\tau + 1, n)) \le n/2$,
--
--   and every value of the exposed positions $\pi(S)$,
--   $$
--   \Pr_{P_1 \cup P_2 \cup \{p_2, p_3\}}[\mathcal G \mid \pi(S)] \le \frac{1 - \epsilon}{(e\ell)^2}.
--   $$
--   Here $A < B$ for sets of positions means $\max A < \min B$. Lemma 3.3 asserts that this holds for some $\beta, \epsilon \in (0, 0.1)$; Claim 3.7 and Corollary 3.9 use those constants.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.3, pp.12–13

import Mathlib
import Definitions.Def_QueryDepthMIS_condProb
import Definitions.Def_QueryDepthMIS_aliveSet
import Definitions.Def_QueryDepthMIS_maxDegOn
import Definitions.Def_QueryDepthMIS_twoHopEvent

set_option autoImplicit false

namespace QueryDepthMIS

/-- The conclusion of the two-hop lemma for given constants `β, ε` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.3,
pp.12–13). `TwoHopBound β ε` says: for every simple graph `G` on `n ≥ 2` vertices, every
`ℓ > 10³`, all sets of positions `P₁, P₂` with `|P₁| = |P₂| = ℓ` and positions `p₁, p₂, p₃` with
`P₁ < P₂ < p₁ < p₂ < p₃ < βn`, every set of exposed positions `S ⊆ [βn] = {1, …, ⌊βn⌋}` such that

* `S` contains `p₁` and all positions in `[max P₂] \ P₁ \ P₂`,
* `S` contains no position of `P₁ ∪ P₂ ∪ {p₂, p₃}`,
* for some integer `1 ≤ τ < min P₁`, `[τ] ⊆ S` and `Δ(G_alive(τ + 1, n)) ≤ n/2`,

and every value `ω₀` of the exposed positions, the event `G` (`twoHopEvent`) has conditional
probability at most `(1 − ε)/(eℓ)²`.

**Formalization Note** The paper's `Pr_{P₁∪P₂∪{p₂,p₃}}[G | π(S)]` is `condProb … S ω₀`; the
condition `Δ(G_alive(τ + 1, n)) ≤ n/2` is evaluated at `ω₀` (it depends only on the positions
`[τ] ⊆ S`). `A < B` for sets of positions means every element of `A` is smaller than every element
of `B`. -/
def TwoHopBound (β ε : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
    2 ≤ Fintype.card V →
    ∀ (ℓ : ℕ), 10 ^ 3 < ℓ →
    ∀ (P₁ P₂ : Finset ℕ), P₁.card = ℓ → P₂.card = ℓ →
    ∀ (p₁ p₂ p₃ : ℕ),
      (∀ x ∈ P₁, ∀ y ∈ P₂, x < y) → (∀ y ∈ P₂, y < p₁) → p₁ < p₂ → p₂ < p₃ →
      (p₃ : ℝ) < β * (Fintype.card V : ℝ) →
    ∀ (S : Finset ℕ), (∀ q ∈ S, 1 ≤ q ∧ (q : ℝ) ≤ β * (Fintype.card V : ℝ)) →
      p₁ ∈ S →
      (∀ q, 1 ≤ q → q ≤ P₂.sup id → q ∉ P₁ → q ∉ P₂ → q ∈ S) →
      (∀ q ∈ S, q ∉ P₁ ∧ q ∉ P₂ ∧ q ≠ p₂ ∧ q ≠ p₃) →
    ∀ (τ : ℕ), 1 ≤ τ → (∀ x ∈ P₁, τ < x) → (∀ q, 1 ≤ q → q ≤ τ → q ∈ S) →
    ∀ (ω₀ : Perm V),
      (maxDegOn G (aliveSet G (rank ω₀) (τ + 1) (Fintype.card V)) : ℝ) ≤
        (Fintype.card V : ℝ) / 2 →
      condProb (twoHopEvent G P₁ P₂ p₁ p₂ p₃) S ω₀ ≤ (1 - ε) / (Real.exp 1 * ℓ) ^ 2

end QueryDepthMIS


