-- Prove2me | Definitions.Def_SpatialSorting_Supplement_Integrated
-- name    : SpatialSorting_Supplement_Integrated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:35:56.478342+00:00
-- url     : https://prove2.me/theorems/2172e64d-6274-4e03-be85-cf2812d4b082
-- title:
--   Definition 1.6 — the Integrated event $\mathrm{Integrated}(c,\delta)$
-- statement:
--   Let $\rho\in\Delta_{q-1}$ be a density vector and $c,\delta$ positive reals. Write $N_L=|I_L|$ for the number of free sites. A configuration $\sigma\in\Omega_{\Lambda^L,\rho}$ (colours on $I_L$, the collar wired to colour $0$, fixed colour counts) belongs to $\mathrm{Integrated}(c,\delta)$ when the following holds:
--
--   for every region $R\subseteq I_L$ (not necessarily connected) of boundary length $|\partial_E R|\le c\sqrt{|R|}$, and every colour $i\in\{0,1,\dots,q-1\}$,
--   $$
--   \rho_i|R|-\delta N_L\ \le\ |\{v\in R:\sigma_v=i\}|\ \le\ \rho_i|R|+\delta N_L .
--   $$
--
--   The Integrated event says that colours are spread out: every low-perimeter region carries, up to a macroscopic error $\delta N_L$, its fair share $\rho_i|R|$ of each colour. It is the high-temperature counterpart of the Sorted event.
--
--   **Formalization Note** The definition is the predicate on configurations; membership in $\Omega_{\Lambda^L,\rho}$ is imposed where the event is measured (`integratedProb`), as for the base `Sorted`. The region test is a real comparison, both bounds are inclusive, the empty region and $R=I_L$ are included. The predicate is defined for all real $c,\delta$; positivity is a hypothesis of the theorem.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 1.6, p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_N
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_nV
import Definitions.Def_SpatialSorting_Supplement_bdryLen
open Classical Filter Topology

namespace SpatialSorting.Supplement

/-- Definition 1.6 (the Integrated event): a configuration `σ` is in `Integrated(c, δ)` when, for every
region `R ⊆ I_L` of boundary length at most `c √|R|` and every colour `i ∈ {0, …, q − 1}`, the number of
sites of `R` with colour `i` lies between `ρ_i |R| − δ N_L` and `ρ_i |R| + δ N_L`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 1.6, p. 9 (PDF p. 10).

Formalization Notes:
- `Integrated(c, δ)` is a subset of `Ω_{Λ^L,ρ}`; here it is the predicate, and membership in
  `omegaRho ρ L` is imposed where the event is measured (`integratedProb`), as for the base `Sorted`.
- Regions are arbitrary (not necessarily connected) subsets of `I_L`, including `∅` and `I_L`; the
  test `|∂_E R| ≤ c √|R|` is a real comparison, and both bounds of the count are inclusive.
- The colour count is the base `nV R (extendBy 0 (I L) σ) i`; `N_L` is the base `N L = |I_L|`.
- The source takes `c, δ > 0`; the predicate is defined for all real `c, δ` and the theorem assumes
  positivity. -/
def Integrated {q : ℕ} [NeZero q] (ρ : Fin q → ℝ) (L : ℕ) (c δ : ℝ) (σ : Coloring q L) : Prop :=
  ∀ R : Finset (ℤ × ℤ), R ⊆ I L → (bdryLen L R : ℝ) ≤ c * Real.sqrt (R.card : ℝ) →
    ∀ i : Fin q,
      ρ i * (R.card : ℝ) - δ * (N L : ℝ) ≤ (nV R (extendBy 0 (I L) σ) i : ℝ) ∧
      (nV R (extendBy 0 (I L) σ) i : ℝ) ≤ ρ i * (R.card : ℝ) + δ * (N L : ℝ)

end SpatialSorting.Supplement


