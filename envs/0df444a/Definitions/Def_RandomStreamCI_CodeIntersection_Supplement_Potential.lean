-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Potential
-- name    : RandomStreamCI_CodeIntersection_Supplement_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:44:57.341285+00:00
-- url     : https://prove2.me/theorems/5408fc9b-753e-4e48-bf77-55e912d91794
-- title:
--   Binomial weighted vertex and incoming-edge potentials
-- statement:
--   For a nonnegative integer $m$ and signed integer $r$, define
--   $$\beta_m(r)=\begin{cases}2^{-m}\binom mr,&0\le r\le m,\\0,&\text{otherwise}.\end{cases}$$
--   A threshold $\kappa$ is positive on $\{0,\ldots,n\}$. Its separate admissibility predicate requires $\kappa(n)\le\tau$ and increments zero or one. The vertex and incoming-edge potentials are the actual sums (79), (81), and (88), weighting each codeword and observed score threshold by $\beta_{n-k_c}(\tau-j)$, each posterior excess by its positive part above $2\eta$, and each conditioning event by its actual mass. Here $k_c=|T_c\cap A|$.
--
--   The threshold sum is finite, $\kappa(k_c)\le j\le\min(k_c,\tau)$; omitted terms vanish for positive $\eta$. Incoming edge index $t$ means arrival at layer $t+1$. Also defined are $\eta=e^{-s^2/(4n)}$, $\kappa(k)=\lceil k/2+s\rceil+1$, and the finite maximum in (93). The maximum is zero at $n=0$, used nowhere in Lemma 26. Zero-mass conditionings retain the base zero posterior. No potential inequality is assumed.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, release papers-1/71.pdf, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Definition 20 and (78)--(81), pp. 17--18; (88), p. 19; (92)--(93), p. 20

import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_OPI

noncomputable section

namespace RandomStreamCI.CodeIntersection.Supplement

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- (80): signed binomial argument; negative r and r>m have mass zero. -/
def beta (m : ℕ) (r : ℤ) : ℝ :=
  if 0 ≤ r ∧ r ≤ (m : ℤ) then (Nat.choose m r.toNat : ℝ) / (2 : ℝ) ^ m else 0

/-- Positive threshold values only on the used domain {0,...,n}. -/
def PositiveThreshold (n : ℕ) (κ : ℕ → ℕ) : Prop := ∀ k ≤ n, 1 ≤ κ k

/-- (78), used only for Lemma 23. Total extension outside {0,...,n} is irrelevant. -/
def AdmissibleThreshold (n τ : ℕ) (κ : ℕ → ℕ) : Prop :=
  PositiveThreshold n κ ∧ κ n ≤ τ ∧ ∀ k < n, κ (k+1) = κ k ∨ κ (k+1) = κ k + 1

/-- Actual generalized vertex potential (79),(81). All omitted infinite-sum terms vanish.
Unreachable vertex events contribute zero, using the published posterior convention (10). -/
def vertexPotential {n w : ℕ} {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    (B : BranchingProgram n Alphabet w) (C : Finset (Word n Alphabet))
    (η : ℝ) (κ : ℕ → ℕ) (τ t : ℕ) : ℝ :=
  ∑ v : Fin w, ∑ A ∈ (Finset.univ : Finset (Address n Alphabet)).powersetCard t,
    streamProbability (B.vertexEvent t v A) *
      ∑ c ∈ C, ∑ j ∈ Finset.Icc (κ (observedCount c A)) (min (observedCount c A) τ),
        beta (n - observedCount c A) ((τ : ℤ) - (j : ℤ)) *
          max (B.posterior t v A (fun H => j ≤ value H c A) - 2 * η) 0

/-- Actual incoming-edge potential (88); t labels the edge arriving at layer t+1. -/
def edgePotential {n w : ℕ} {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    (B : BranchingProgram n Alphabet w) (C : Finset (Word n Alphabet))
    (η : ℝ) (κ : ℕ → ℕ) (τ : ℕ) (t : Fin (Fintype.card (Address n Alphabet))) : ℝ :=
  ∑ e : Fin w × Input n Alphabet,
    ∑ A ∈ (Finset.univ : Finset (Address n Alphabet)).powersetCard (t.val+1),
      streamProbability (B.edgeEvent t e A) *
        ∑ c ∈ C, ∑ j ∈ Finset.Icc (κ (observedCount c A)) (min (observedCount c A) τ),
          beta (n - observedCount c A) ((τ : ℤ) - (j : ℤ)) *
            max (B.edgePosterior t e A (fun H => j ≤ value H c A) - 2 * η) 0

/-- The eta and kappa of (92); the ceiling is taken before adding one. -/
def surplusEta (n : ℕ) (s : ℝ) : ℝ := Real.exp (-(s^2 / (4 * (n : ℝ))))

def surplusThreshold (s : ℝ) (k : ℕ) : ℕ := ⌈(k : ℝ) / 2 + s⌉₊ + 1

/-- Finite maximum in (93). For n=0 its empty supremum is 0; Lemma 26 requires n>=1. -/
def growthMaximum (n τ : ℕ) (κ : ℕ → ℕ) : ℝ :=
  sSup (↑((Finset.range n).image (fun k => ((n : ℝ) - k) / 2 *
    beta (n - k - 1) ((τ : ℤ) - (κ k : ℤ)))) : Set ℝ)

end RandomStreamCI.CodeIntersection.Supplement


