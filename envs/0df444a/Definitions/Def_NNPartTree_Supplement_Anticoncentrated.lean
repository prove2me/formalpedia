-- Prove2me | Definitions.Def_NNPartTree_Supplement_Anticoncentrated
-- name    : NNPartTree_Supplement_Anticoncentrated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:10:38.83928+00:00
-- url     : https://prove2.me/theorems/705ae794-2854-416a-bbfd-d06696da388b
-- title:
--   $(L,\Delta)$-anticoncentration, $(B,r)$- and $B$-subgaussianity, and the uniform law on a dataset
-- statement:
--   Let $\mathcal{M}$ be a distribution on $\mathbb{R}^d$ (Definition B.1).
--
--   1. $\mathcal{M}$ is **$(L, \Delta)$-anticoncentrated** if for every unit vector $h \in \mathbb{R}^d$,
--   $$\sup_{t \in \mathbb{R}} \Pr_{z \sim \mathcal{M}}\big[\,|\langle h, z\rangle - t| \le r\,\big] \le L r + \Delta \quad \text{for all } r \in [0, 1].$$
--   2. $\mathcal{M}$ is **$(B, r)$-subgaussian** if for every unit vector $h$ and every integer $1 \le p \le r$,
--   $$\mathbb{E}_{z \sim \mathcal{M}}\big[|\langle h, z\rangle|^p\big]^{1/p} \le B\sqrt{p}.$$
--   3. $\mathcal{M}$ is **$B$-subgaussian** if it is $(B, r)$-subgaussian for every $r \in \mathbb{N}$.
--
--   In addition, for a dataset $\mathbf{P} = (p_1, \dots, p_m)$ of points of $\mathbb{R}^d$, the **uniform distribution over $\mathbf{P}$** puts mass $1/m$ on each listed point (with multiplicity).
--
--   With $\Delta = 0$, anticoncentration says that every one-dimensional projection has no atoms and puts mass at most $L r$ on every interval of half-width $r \le 1$. These are the "Gaussian-like" hypotheses under which Theorem 5 verifies the degree-bound hypothesis of the main theorem.
--
--   **Formalization Note** The supremum over $t$ is stated for every $t$. The moment is a lower integral in $[0, \infty]$ and the bound is written in the equivalent form $\mathbb{E}|\langle h, z\rangle|^p \le (B\sqrt p)^p$, so a distribution with an infinite moment is not subgaussian. For $m = 0$ the uniform law is the zero measure; Theorem 5 only uses it as the marginal of a probability measure.
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Definition B.1, p.34 (PDF p.34); Theorem 5, p.34

import Mathlib
import Definitions.Def_NNPartTree_Machine

set_option autoImplicit false

namespace NNPartTree.Supplement

open MeasureTheory
open scoped ENNReal

/-- **`(L, Δ)`-anticoncentration** (Definition B.1, p.34, PDF p.34).
S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*,
arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Definition B.1, p.34.

A distribution `M` on `ℝᵈ` is `(L, Δ)`-anticoncentrated if for every unit vector `h`, every `t ∈ ℝ`
and every `r ∈ [0, 1]`, `Pr_{z∼M}[|⟨h, z⟩ − t| ≤ r] ≤ L r + Δ`.

**Formalization Note** The printed `sup_{t ∈ ℝ}` is a `∀ t`. The probability is read off the measure
with `toReal`; every statement applies the predicate to a probability measure. -/
def Anticoncentrated {d : ℕ} (M : Measure (Pt d)) (L Δ : ℝ) : Prop :=
  ∀ h : Pt d, ‖h‖ = 1 → ∀ t : ℝ, ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
    (M {z | |inner ℝ h z - t| ≤ r}).toReal ≤ L * r + Δ

/-- **`(B, r)`-subgaussian** (Definition B.1, p.34): for every unit vector `h` and every integer
`1 ≤ p ≤ r`, `(E_{z∼M}|⟨h, z⟩|^p)^{1/p} ≤ B √p`.

**Formalization Note** The moment is a lower integral in `[0, ∞]`, and the bound is stated in the
equivalent form `E|⟨h, z⟩|^p ≤ (B √p)^p`, so an infinite moment does not satisfy it. -/
def SubgaussianUpTo {d : ℕ} (M : Measure (Pt d)) (B : ℝ) (r : ℕ) : Prop :=
  ∀ h : Pt d, ‖h‖ = 1 → ∀ p : ℕ, 1 ≤ p → p ≤ r →
    ∫⁻ z, ‖inner ℝ h z‖ₑ ^ p ∂M ≤ ENNReal.ofReal ((B * Real.sqrt p) ^ p)

/-- **`B`-subgaussian** (Definition B.1, p.34): `(B, r)`-subgaussian for every `r ∈ ℕ`. -/
def Subgaussian {d : ℕ} (M : Measure (Pt d)) (B : ℝ) : Prop :=
  ∀ r : ℕ, SubgaussianUpTo M B r

/-- The **uniform distribution over a dataset** `P = (p₁, …, p_m)` (Theorem 5, p.34): mass `1/m` on
each listed point, with multiplicity. For `m = 0` it is the zero measure. -/
noncomputable def datasetLaw {d m : ℕ} (P : Fin m → Pt d) : Measure (Pt d) :=
  (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (P i)

end NNPartTree.Supplement


