-- Prove2me | Definitions.Def_MulticlassDS_Compress_Probability
-- name    : MulticlassDS_Compress_Probability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:03:40.681926+00:00
-- url     : https://prove2.me/theorems/7462003f-b319-45bd-9271-14cad112d845
-- title:
--   Definitions 31, 33, pp. 19–20 — i.i.d. probabilities, realizable distributions, list PAC learners
-- statement:
--   Let $\mathcal D$ be a (discrete) distribution on a set $\mathcal Z$. For an event $E \subseteq \mathcal Z^m$,
--   $$\Pr_{s\sim\mathcal D^m}[s\in E] = \sum_{s \in \mathcal Z^m} \Big(\prod_{i=1}^m \mathcal D(s_i)\Big)\,\mathbf 1[s\in E].$$
--
--   1. A distribution $\mathcal D$ over $\mathcal X\times\mathcal Y$ is **$\mathcal H$-realizable** if for every $m$ a random sample $S\sim\mathcal D^m$ is $\mathcal H$-realizable with probability $1$; for a discrete distribution this means every sample drawn from the support of $\mathcal D$ is $\mathcal H$-realizable.
--   2. $\mathcal D$ is **realizable by the menu $\mu$** (Definition 33) if every $(x,y)$ in the support of $\mathcal D$ has $y\in\mu(x)$, equivalently every sample $S\sim\mathcal D^m$ is realizable by $\mu$ with probability $1$.
--   3. **List PAC learner** (Definition 31). An algorithm $A$ with sample size $n$ and list size $p$ is a list PAC learner with success probability $\alpha>0$ for $\mathcal H$ if its output $\mu_S = A(S)$ is always a $p$-menu and for every $\mathcal H$-realizable distribution $\mathcal D$,
--   $$\Pr_{(S,(x,y))\sim\mathcal D^{n+1}}\big[y\in\mu_S(x)\big]\ \ge\ \alpha .$$
--
--   These are the probabilistic notions in which Propositions 32 and 34 and Fact 14 are stated.
--
--   **Formalization Note** Distributions are probability mass functions (`PMF`), probabilities take values in $[0,\infty]$ (`ℝ≥0∞`) and real bounds are compared through `ENNReal.ofReal`. The paper's general measure-theoretic setting ("standard measurability assumptions", p. 3) is not attempted; its own constructions (a uniform distribution on a sample, a mixed strategy over the examples of a sample) are discrete. In $(S,(x,y))\sim\mathcal D^{n+1}$, $S$ is the first $n$ coordinates (`Fin.init`) and $(x,y)$ the last.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 3 (realizable distributions), p. 19 Definition 31, p. 20 Definition 33

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Compression

open scoped ENNReal

namespace MulticlassDS.Compress

/-- The probability `Pr_{s ∼ D^m}[s ∈ E]` of an event `E ⊆ Z^m` under `m` i.i.d. draws from a
discrete distribution `D`. -/
noncomputable def iidProb {Z : Type*} (D : PMF Z) (m : ℕ) (E : Set (Fin m → Z)) : ℝ≥0∞ :=
  ∑' s : Fin m → Z, (∏ i, D (s i)) * E.indicator 1 s

/-- p. 3 (and the pattern of Definition 33, p. 20): `D` is `H`-realizable if for every `m` a
random sample `S ∼ D^m` is `H`-realizable with probability 1; for a discrete `D`, every sample
drawn from the support of `D` is `H`-realizable. -/
def IsRealizableDist {X Y : Type*} (H : Set (X → Y)) (D : PMF (X × Y)) : Prop :=
  ∀ (m : ℕ) (s : Fin m → X × Y), (∀ i, s i ∈ D.support) → IsRealizable H s

/-- Definition 33, p. 20: `D` is realizable by the menu `μ`, i.e. every example `(x, y)` in the
support of `D` has `y ∈ μ(x)`. -/
def MenuRealizableDist {X Y : Type*} (μ : X → Set Y) (D : PMF (X × Y)) : Prop :=
  ∀ z ∈ D.support, z.2 ∈ μ z.1

/-- Definition 31, p. 19: a learner `A` mapping samples of size `n` to menus is a list PAC
learner for `H` with list size `p` and success probability `α > 0`: its menus always have at
most `p` labels, and for every `H`-realizable `D`,
`Pr_{(S,(x,y)) ∼ D^{n+1}}[y ∈ A(S)(x)] ≥ α`. -/
def IsListPACLearner {X Y : Type*} (H : Set (X → Y)) (n p : ℕ) (α : ℝ)
    (A : (Fin n → X × Y) → X → Set Y) : Prop :=
  0 < α ∧ (∀ (S : Fin n → X × Y) (x : X), (A S x).encard ≤ p) ∧
    ∀ D : PMF (X × Y), IsRealizableDist H D →
      ENNReal.ofReal α ≤
        iidProb D (n + 1) {s | (s (Fin.last n)).2 ∈ A (Fin.init s) (s (Fin.last n)).1}

end MulticlassDS.Compress


