-- Prove2me | Definitions.Def_HardcoreSlices_downUp
-- name    : HardcoreSlices_downUp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:49.20851+00:00
-- url     : https://prove2.me/theorems/bc0c98b8-f5d6-40b4-849e-4b51bdb742c1
-- title:
--   The closure, the conditional law $\mu_{|\tau}$ and the weighted down-up walk
-- statement:
--   For a family $F$ of sets of size $d$, its **downward closure** is the pure $d$-dimensional complex with facets $F$. For a weight $w$ on $F$ and a face $\tau$, let $Z_\tau=\sum_{S\in F,\,\tau\subseteq S}w(S)$, and let $\mu_{|\tau}(S)=w(S)/Z_\tau$ on the facets containing $\tau$.
--
--   The **down-up walk** of a $d$-dimensional complex $X$ with a distribution $\pi$ on its facets moves from a facet $\sigma$ as follows: choose $v\in\sigma$ uniformly, then choose a facet containing $\sigma\setminus\{v\}$ with probability proportional to its weight. So
--   $$P(\sigma,\sigma')=\frac1d\sum_{v\in\sigma}\mathbf 1\{\sigma\setminus\{v\}\subseteq\sigma'\}\frac{\pi(\sigma')}{\sum_{\rho\supseteq\sigma\setminus\{v\}}\pi(\rho)}.$$
--
--   The predicate `MixesInPoly` says the walk has total variation at most $\varepsilon$ from $\pi$, from every facet, at every time $t\ge K(m+1+\log(1/\varepsilon))^r$.
--
--   **Formalization Note** The walk is a matrix on the facets as a subtype. The published `SteurerHDX.downUp` is for the uniform measure, so it does not apply. The conditional law is carried by the facets $\sigma\supseteq\tau$ of the complex, in bijection with the facets $\sigma\setminus\tau$ of the link. Mixing is stated with $\forall t\ge$ bound rather than `MarkovMixing.mixingTime`, whose infimum of an empty set is $0$.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), §1, p.1 (complexes, µ|τ, down-up walk); Lemma 6.4, p.28 (Zτ)

import Mathlib
import Definitions.Def_SteurerHDX_faces
import Definitions.Def_mm_mixing

open Classical

namespace HardcoreSlices

variable {V : Type*} [DecidableEq V]

/-- The downward closure of a family of sets: the faces of the complex with facets `F`
(Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), §1, p.1; Definitions 1.6 and 1.7, p.3). -/
def downClosure [Fintype V] (F : Finset (Finset V)) : Finset (Finset V) :=
  Finset.univ.filter (fun τ => ∃ σ ∈ F, τ ⊆ σ)

/-- `Zτ = Σ_{S∈F, τ⊆S} w(S)` for a family `F` of facets (p.28, Lemma 6.4). -/
noncomputable def facetMass (F : Finset (Finset V)) (w : Finset V → ℝ) (τ : Finset V) : ℝ :=
  ∑ S ∈ F.filter (fun S => τ ⊆ S), w S

/-- The law `µ|τ` (p.1) with `µ ∝ w` on the facets `F`: `S ↦ w(S) / Zτ` on the facets `S ⊇ τ`, and `0`
elsewhere.

**Formalization Note.** The page puts `µ|τ` on the facets `σ \ τ` of the link. Here the same law is
carried by the facets `σ ⊇ τ` of the complex, through the bijection `σ ↦ σ \ τ`. -/
noncomputable def condLaw (F : Finset (Finset V)) (w : Finset V → ℝ) (τ S : Finset V) : ℝ :=
  if S ∈ F ∧ τ ⊆ S then w S / facetMass F w τ else 0

/-- `min_{τ∈X(d)} µ(τ)` of Theorem 1.2 (p.1).

**Formalization Note.** The infimum is over a finite type, so it is attained when `X(d)` is nonempty, which
`HDXConc.IsTopDensity` guarantees. -/
noncomputable def muMin (X : Finset (Finset V)) (d : ℕ) (π : Finset V → ℝ) : ℝ :=
  ⨅ σ : {σ // σ ∈ SteurerHDX.faces X d}, π σ

/-- **The down-up walk.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), §1, p.1: "from the current facet `τ ∈ X(d)` we choose `v ∈ τ` uniformly
at random, and among all facets containing `τ \ {v}` we choose one proportional to its weight under `µ`."

**Formalization Note.** The matrix lives on the facets `X(d)` as a subtype. The published
`SteurerHDX.downUp` is the walk of the uniform measure; this one carries the weight `π`. The denominator is
positive for `π` positive on `X(d)`, since the current facet itself is in the sum. -/
noncomputable def downUp (X : Finset (Finset V)) (d : ℕ) (π : Finset V → ℝ) :
    Matrix {σ // σ ∈ SteurerHDX.faces X d} {σ // σ ∈ SteurerHDX.faces X d} ℝ :=
  fun σ σ' => (1 / (d : ℝ)) * ∑ v ∈ σ.1,
    if σ.1.erase v ⊆ σ'.1 then
      π σ'.1 / ∑ ρ ∈ (SteurerHDX.faces X d).filter (fun ρ => σ.1.erase v ⊆ ρ), π ρ
    else 0

/-- "The down-up walk mixes in polynomial-time" (Theorems 1.8 and 1.9, p.4), with the time bound
`K (m + 1 + log 1/ε)^r`: from every facet and for every `ε ∈ (0, 1)`, the walk is within total variation
`ε` of `π` at every time `t` at least that bound.

**Formalization Note.** The conclusion is written with `∀ t ≥ bound`, not with
`MarkovMixing.mixingTime`, whose `sInf` of an empty set would be `0`. -/
def MixesInPoly (X : Finset (Finset V)) (d : ℕ) (π : Finset V → ℝ) (K r m : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℕ, (K : ℝ) * ((m : ℝ) + 1 + Real.log ε⁻¹) ^ r ≤ t →
    ∀ σ : {σ // σ ∈ SteurerHDX.faces X d},
      MarkovMixing.tvDist (MarkovMixing.rowDist (downUp X d π) t σ) (fun σ' => π σ'.1) ≤ ε

end HardcoreSlices


