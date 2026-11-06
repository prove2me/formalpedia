-- Prove2me | Definitions.Def_PottsRapidMixing_RandomCluster
-- name    : PottsRapidMixing_RandomCluster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:28.652713+00:00
-- url     : https://prove2.me/theorems/9dd82e00-6867-41c4-8e6b-87cbbbd0c295
-- title:
--   Random-cluster laws $\phi^\zeta$ and FK dynamics
-- statement:
--   For a finite graph $K=(V,E)$, $p\in(0,1)$ and real $q>0$, the *random-cluster law* on edge configurations $\omega\subseteq E$ is
--   $$\phi_{K,p,q}(\omega)\propto\Bigl(\frac{p}{1-p}\Bigr)^{|\omega|}q^{c(V,\omega)},$$
--   with $c(V,\omega)$ the number of components of $(V,\omega)$. With a boundary partition $\zeta$, the law $\phi^\zeta_K$ has $c(V,\omega)$ replaced by the number of components after the vertices in each block of $\zeta$ are identified. *FK dynamics* $P_{\mathrm{FK}}$ picks a uniform edge $e$ and resamples it: from $\mathrm{Ber}(\hat p)$ if $e$ is a cut edge of $\omega\cup\{e\}$ and from $\mathrm{Ber}(p)$ otherwise.
--
--   The Edwards–Sokal coupling links $\phi$ to the Potts law, and the proof compares the chain $M$ with FK dynamics.
--
--   **Formalization Note** Edge configurations are the coordinates $E\to\{0,1\}$. A partition is given by a graph $\zeta$ on the vertices, whose connectivity gives the blocks. $P_{\mathrm{FK}}$ is defined as the Glauber chain of $\phi$; a verification file checks on the one-edge graph that it draws the cut edge from $\mathrm{Ber}(\hat p)$ with $\hat p=p/(p+q(1-p))$.
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, p.4 (ϕ), pp.16, 18 (ϕ^ζ_{F⁺}), p.10 (FK dynamics)

import Mathlib
import Definitions.Def_mm_mcmc

open scoped Classical

namespace PottsRapidMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spanning subgraph `(V, A)` of `K` with open edge set `A` (Blanca, Gheissari, Park, Zhang,
arXiv:2610.42059, p.4). Edge configurations are the coordinates `K.edgeSet → Bool`. -/
def edgeGraph (K : SimpleGraph V) (A : K.edgeSet → Bool) : SimpleGraph V :=
  SimpleGraph.fromRel (fun a b => ∃ h : K.Adj a b, A ⟨s(a, b), h⟩ = true)

/-- `|ω|`, the number of open edges. -/
noncomputable def numOpen {K : SimpleGraph V} (A : K.edgeSet → Bool) : ℕ :=
  (Finset.univ.filter (fun e => A e = true)).card

/-- The number of connected components of a graph on a finite vertex set. -/
noncomputable def numComps (K : SimpleGraph V) : ℕ := Nat.card K.ConnectedComponent

/-- The random-cluster law on `K` with boundary identifications `ζ`
(arXiv:2610.42059, pp.4, 16, 18): `ϕ^ζ_K(ω) ∝ (p/(1−p))^{|ω|} q^{c_ζ(ω)}`, where `c_ζ(ω)` counts the
components of `(V, ω)` after the vertices joined by `ζ` are identified.

**Formalization Note.** The partition is given by a graph `ζ` on the vertices: two vertices lie
in one block when `ζ` connects them, so `c_ζ(ω)` is the number of components of `(V, ω) ⊔ ζ`. `q`
is real, as the page needs at `q ≥ 1`; exponents are natural numbers, so no `rpow` occurs. -/
noncomputable def rcBoundary (K : SimpleGraph V) (p q : ℝ) (ζ : SimpleGraph V) :
    (K.edgeSet → Bool) → ℝ :=
  fun ω => (p / (1 - p)) ^ numOpen ω * q ^ numComps (edgeGraph K ω ⊔ ζ) /
    ∑ ω' : K.edgeSet → Bool, (p / (1 - p)) ^ numOpen ω' * q ^ numComps (edgeGraph K ω' ⊔ ζ)

/-- The random-cluster law `ϕ_{K,p,q}(ω) ∝ (p/(1−p))^{|ω|} q^{c(V,ω)}` (arXiv:2610.42059, p.4):
`rcBoundary` with no identifications. -/
noncomputable def rcLaw (K : SimpleGraph V) (p q : ℝ) : (K.edgeSet → Bool) → ℝ :=
  rcBoundary K p q ⊥

/-- FK dynamics `P_FK` (arXiv:2610.42059, p.10): pick a uniform edge and resample it from `ϕ` given
the other edges.

**Formalization Note.** The page describes the update as `Ber(p̂)` at a cut edge of `ω ∪ {e}` and
`Ber(p)` otherwise; these are the conditional probabilities of `ϕ`, so this is the Glauber chain
of `ϕ` on `E → Bool`. The identification is checked in
`Solutions/verification/PottsRapidMixing_Examples` on the one-edge graph. -/
noncomputable def fkChain (K : SimpleGraph V) (p q : ℝ) :
    Matrix (K.edgeSet → Bool) (K.edgeSet → Bool) ℝ :=
  MarkovMixing.glauber (rcLaw K p q)

end PottsRapidMixing


