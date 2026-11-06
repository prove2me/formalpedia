-- Prove2me | Definitions.Def_YuStrategic_Optimality_PathSpace
-- name    : YuStrategic_Optimality_PathSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:20.085753+00:00
-- url     : https://prove2.me/theorems/70cf2309-da95-46cb-b7de-362449243105
-- title:
--   Path space $\Omega=(\mathbb X\times\mathbb A)^\infty$, its coordinates $x_n,a_n,h_n$, and $\delta_x$
-- statement:
--   Let $\mathbb X$ (states) and $\mathbb A$ (actions) be Borel spaces. The **path space** of a discrete-time controlled process is
--   $$\Omega=(\mathbb X\times\mathbb A)^\infty,\qquad \omega=(x_0,a_0,x_1,a_1,\dots),$$
--   with the product topology and the product $\sigma$-algebra. For $n\ge0$ the coordinate maps are the state $x_n(\omega)$, the action $a_n(\omega)$, and the history
--   $$h_n(\omega)=(x_0,a_0,\dots,x_{n-1},a_{n-1},x_n)\in H_n=(\mathbb X\times\mathbb A)^n\times\mathbb X .$$
--   The pair $(h_n,a_n)$ is the extended history $h_n'=(x_0,a_0,\dots,x_n,a_n)\in H_n'$. The initial state of a history $h_n$ is its first coordinate $x_0$. Finally, $\delta_x$ denotes the Dirac measure at $x$, regarded as an element of the space $\mathcal P(\mathbb X)$ of probability measures.
--
--   These are the coordinates in which strategic measures, policies with structural constraints (Markov, semi-Markov) and the initial-state sections $\tilde{\mathcal S}_\star(x)$ are described.
--
--   **Formalization Note.** $\Omega$ is `Path X A := ℕ → X × A`; histories use the published `BertsekasShreve.BorelInfinite.Hist X A n = (Fin n → X × A) × X`. The module also records, as an instance, that every Borel space is second countable (it is homeomorphic to a subspace of a separable metric space); this is a consequence of being a Borel space and is what lets Mathlib put the Borel structure and the weak topology on $\Omega$ and $\mathcal P(\Omega)$.
-- source:
--   Yu, On Strategic Measures and Optimality Properties in Discrete-Time Stochastic Control with Universally Measurable Policies, arXiv:2206.06492v3, §2.1 p. 4 (Borel spaces), §2.2 p. 6 (Ω, h_n, h'_n), p. 5 (δ_x)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy

namespace YuStrategic.Optimality

open MeasureTheory

/-- Every Borel space (Yu, arXiv:2206.06492v3, §2.1, p. 4: a Borel subset of a Polish space,
i.e. `BertsekasShreve.AnalyticSelection.IsBorelSpace`) is second countable: it is homeomorphic to
a subspace of a separable metric space. This structural instance lets Mathlib equip the product
spaces `X × A`, `ℕ → X × A` and the space of probability measures on them with their Borel
structures and the weak topology.

**Formalization Note.** This is a consequence of the hypothesis `IsBorelSpace X`, not an extra
assumption. -/
instance secondCountable_of_isBorelSpace (X : Type) [TopologicalSpace X]
    [BertsekasShreve.AnalyticSelection.IsBorelSpace X] : SecondCountableTopology X := by
  obtain ⟨Z, mZ, _, _, B, _, ⟨e⟩⟩ :=
    BertsekasShreve.AnalyticSelection.IsBorelSpace.exists_homeomorph_borel (X := X)
  let _ := mZ
  have : SecondCountableTopology Z := inferInstance
  exact e.isEmbedding.secondCountableTopology

/-- The path space `Ω = (X × A)^∞` (Lean name `Path X A`) of Yu, arXiv:2206.06492v3, §2.2, p. 6: a path is
`ω = (x₀, a₀, x₁, a₁, …)`, stored as the sequence `n ↦ (xₙ, aₙ)`. It carries the product
topology and the product σ-algebra (Mathlib's instances on `ℕ → X × A`). -/
abbrev Path (X A : Type) := ℕ → X × A

/-- The state coordinate `xₙ(ω)` (§2.2, p. 6). -/
def stateAt {X A : Type} (n : ℕ) (ω : Path X A) : X := (ω n).1

/-- The action coordinate `aₙ(ω)` (§2.2, p. 6). -/
def actAt {X A : Type} (n : ℕ) (ω : Path X A) : A := (ω n).2

/-- The history `hₙ(ω) = (x₀, a₀, …, x_{n−1}, a_{n−1}, xₙ)` of a path (§2.2, p. 6), as an element of
`Hₙ = (X × A)^n × X`, stored as `BertsekasShreve.BorelInfinite.Hist X A n`: the pair of the past
state–action pairs `(i ↦ (xᵢ, aᵢ))_{i<n}` and the current state `xₙ`. The pair
`(histAt n ω, actAt n ω)` is the paper's `h′ₙ = (x₀, a₀, …, xₙ, aₙ) ∈ H′ₙ`. -/
def histAt {X A : Type} (n : ℕ) (ω : Path X A) : BertsekasShreve.BorelInfinite.Hist X A n :=
  (fun i => ω i, (ω n).1)

/-- The initial state `x₀` of a history `hₙ = (x₀, a₀, …, xₙ)` (§2.2, p. 6): the current state
when `n = 0`, and the state of the first pair otherwise. -/
def x0 {X A : Type} : {n : ℕ} → BertsekasShreve.BorelInfinite.Hist X A n → X
  | 0, h => h.2
  | _ + 1, h => (h.1 0).1

/-- The Dirac measure `δₓ` as an element of `P(X)` (§2.1, p. 5, "Miscellaneous notation"). -/
noncomputable def diracPM {X : Type} [MeasurableSpace X] (x : X) : ProbabilityMeasure X :=
  ⟨Measure.dirac x, inferInstance⟩

end YuStrategic.Optimality


