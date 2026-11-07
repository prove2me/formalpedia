-- Prove2me | Definitions.Def_TTTSampling_alg3Step
-- name    : TTTSampling_alg3Step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:53.724399+00:00
-- url     : https://prove2.me/theorems/1aa9179e-e8c7-4367-b806-9e764ff667a7
-- title:
--   One iteration of the while loop of Algorithm 3, initial state, $\Phi_x$ and $M_j$
-- statement:
--   The state of the inner loop of Algorithm 3 after iteration $j$ is the multiset $\mathcal S^j$ of particles (partial sequences), the class $\mathcal F^{j+1}$, and the cache of obtained oracle values. It is **terminal** when $\mathcal S^j\cap\Sigma^{<n}=\emptyset$.
--
--   1. **Step** (Lines 5–10): if the state is not terminal, let $z_j$ be the lexicographically first element of $\mathcal S^{j-1}\cap\Sigma^{<n}$, call Algorithm 2 with $w=z_j$, $\mathcal G=\mathcal F^j$, $M=\bar R$, obtaining $(\mathcal T_j,\mathcal G_j)$, and move to $\mathcal S^j=(\mathcal S^{j-1}\setminus\{z_j\})\cup\mathcal T_j$, $\mathcal F^{j+1}=\mathcal G_j$. A terminal state is left unchanged.
--   2. **Initial state** of a round (Lines 3–4): $\mathcal S^0$ is $N$ copies of the empty sequence and $\mathcal F^1=\{\mu\in\mathcal F\mid \hat\mu(y)/\mu(y)\le\bar R\ \forall y\in\Sigma\}$; Line 4 reads $\hat\mu(y)$ for every $y\in\Sigma$.
--   3. $\Phi_x(\mathcal S)=\sum_{x'\in\mathcal S}\frac{\mathbb 1\{x'\preceq x\}}{\hat\mu(x')}$ (proof of Lemma 3.10) and $M(\mathcal S)=\sum_{x\in\mathcal S}\frac{\mu^\star(x)}{\hat\mu(x)}$ (p.28), sums over the multiset with multiplicity.
--
--   **Formalization Note** "Lexicographically first" is the minimum in the lexicographic order on lists induced by a linear order on $\Sigma$. The update removes one copy of $z_j$ and adds $\mathcal T_j$ with multiplicity. The filter of Line 4 is one-sided, as printed, and multiplicative.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Algorithm 3, Lines 3–10, p.12 (PDF p.14); pp.27–28 (PDF pp.29–30)

import Mathlib
import Definitions.Def_TTTSampling_alg2
import Definitions.Def_TTTSampling_Rbar

open Classical

namespace TTTSampling

/-- The **state of the inner loop of Algorithm 3** after iteration `j`: the multiset `𝒮^j` of
particles, the class `ℱ^{j+1}`, and the cache `Q` of nodes whose `µ̂`-value has been obtained. -/
structure A3State (α : Type) (n : ℕ) where
  S : Multiset (List α)
  cls : Finset (PMF (Fin n → α))
  Q : Finset (List α)

/-- A state is **terminal** when `𝒮 ∩ Σ^{<n} = ∅` (the while condition of Line 5 fails). -/
def A3State.Terminal {α : Type} {n : ℕ} (s : A3State α n) : Prop :=
  ∀ x ∈ s.S, n ≤ x.length

/-- **One iteration of the while loop of Algorithm 3** (Lines 5–10).

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Algorithm 3,
printed p.12 (PDF p.14): "Let z_j be the lexicographically first element of 𝒮^{j−1} ∩ Σ^{<n}.
Call Algorithm 2 with the node w ← z_j, the class 𝒢 ← ℱ^j, and M = R̄; suppose it returns
(𝒯_j, 𝒢_j) … Set 𝒮^j ← (𝒮^{j−1} \ {z_j}) ∪ 𝒯_j. Set ℱ^{j+1} ← 𝒢_j."

On a terminal state the step is the identity (the paper's `𝒮^j := 𝒮^J` for `j > J`, p.26).

**Formalization Note**
* "Lexicographically first" is the minimum in Mathlib's lexicographic order on `List α` (for a
  linear order on `Σ`).
* `(𝒮^{j−1} \ {z_j}) ∪ 𝒯_j` removes **one** copy of `z_j` and adds `𝒯_j` with multiplicity
  (multiset sum), as the counting in Lemmas 3.9 and 3.11 requires.
* The cache grows by the nodes Algorithm 2 reads. -/
noncomputable def alg3Step {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (R : ℝ)
    (μh : List α → NNReal) (s : A3State α n) : PMF (A3State α n) :=
  if h : ∃ x ∈ s.S, x.length < n then
    let z : List α := (s.S.toFinset.filter (fun x => x.length < n)).min'
      (by obtain ⟨x, hx, hl⟩ := h; exact ⟨x, by simp [hx, hl]⟩)
    (alg2 R (Rbar R) μh z s.cls).map fun o => ⟨s.S.erase z + o.1, o.2.1, s.Q ∪ o.2.2⟩
  else PMF.pure s

/-- The **initial state of a round** of Algorithm 3 (Lines 3–4), given the cache `Q` carried from
earlier rounds: `𝒮^0` is `N` copies of the empty sequence, `ℱ^1 = {µ ∈ ℱ | µ̂(y)/µ(y) ≤ R̄ ∀y ∈ Σ}`
(one-sided, as printed; multiplicatively `µ̂(y) ≤ R̄·µ(y)`), and Line 4 reads `µ̂(y)` for each
`y ∈ Σ`. -/
noncomputable def alg3Init {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (C_N : ℕ)
    (R δ : ℝ) (F : Finset (PMF (Fin n → α))) (μh : List α → NNReal) (Q : Finset (List α)) :
    A3State α n :=
  ⟨Multiset.replicate (Npart C_N F.card R δ) [],
   F.filter (fun μ => ∀ y : α, (μh [y] : ℝ) ≤ (Rbar R : ℝ) * prefixMass μ [y]),
   Q ∪ Finset.univ.image (fun y : α => [y])⟩

/-- `Φ_x(𝒮) = Σ_{x′∈𝒮} 1{x′ ⪯ x}/µ̂(x′)` (proof of Lemma 3.10, printed p.27), summed over the
multiset with multiplicity. -/
noncomputable def Phi {α : Type} [DecidableEq α] (μh : List α → NNReal) (x : List α)
    (S : Multiset (List α)) : ℝ :=
  (S.map (fun x' => if x' <+: x then 1 / (μh x' : ℝ) else 0)).sum

/-- `M(𝒮) = Σ_{x∈𝒮} µ⋆(x)/µ̂(x)` (p.28: `M_j := Σ_{x∈𝒮^j} µ⋆(x)/µ̂(x)`), with multiplicity. -/
noncomputable def Mval {α : Type} [Fintype α] [DecidableEq α] {n : ℕ} (μs : PMF (Fin n → α))
    (μh : List α → NNReal) (S : Multiset (List α)) : ℝ :=
  (S.map (fun x => prefixMass μs x / (μh x : ℝ))).sum

end TTTSampling


