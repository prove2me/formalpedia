-- Prove2me | Definitions.Def_RandOrderCSP_poiLaw
-- name    : RandOrderCSP_poiLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:14.880246+00:00
-- url     : https://prove2.me/theorems/fbb50bc8-95da-4a14-9352-92486642cc56
-- title:
--   Poisson sparsification $\mathrm{Poi}(G,\lambda)$
-- statement:
--   The **Poisson sparsification** of $G$ with parameter $\lambda>0$ keeps the vertex set, samples independent $X_j\sim\mathrm{Poi}(\lambda)$ for $j\in\mathcal E_G$, and replaces $j$ by $X_j$ copies with the same endpoints and color. The module defines the law of the count vector $(X_j)_j$, the hypergraph built from a count vector, and the rate $\alpha n^{-(k-1)}$ used with $G^n$.
--
--   **Formalization Note** The random hypergraph is a function of the count vector, so events and expectations over $H$ are taken over the product of Poisson measures.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §4.1, p.16

import Mathlib
import Definitions.Def_RandOrderCSP_Hypergraph

open MeasureTheory ProbabilityTheory

namespace RandOrderCSP

/-- **Poisson sparsification** (§4.1, p.16).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.16: "The Poisson sparsification of G with
parameter λ > 0 is the distribution Poi(G, λ) over hypergraphs H sampled as follows: Deterministically,
𝒱_H = 𝒱_G. For each edge j ∈ ℰ_G, sample X_j ∼ Poi(λ) mutually independently. Set
ℰ_H := ⋃_{j∈ℰ_G} ({j} × [X_j]). For every j ∈ ℰ_G and t ∈ [X_j], set M_H((j, t), ℓ) := M_G(j, ℓ)."

`poiLaw E λ` is the law of the count vector `X = (X_j)_{j ∈ ℰ_G}` (independent `Poi(λ)` counts),
`sparsify G X` the hypergraph `H` built from a count vector, and `sparsifyColor Y X` the inherited
coloring (`f′(j, t) := f(j)`).

**Formalization Note.** The random hypergraph is a function of the count vector, so probabilities
and expectations over `H ∼ Poi(G, λ)` are taken over `X ∼ poiLaw E λ` (a product of Mathlib's
`poissonMeasure`). The edge `(j, t)`, `t ∈ [X_j]`, is `⟨j, t⟩ : Σ j, Fin (X j)`. -/
noncomputable def poiLaw (E : Type) [Fintype E] (lam : NNReal) : Measure (E → ℕ) :=
  Measure.pi fun _ : E => poissonMeasure lam

/-- The hypergraph `H` of `Poi(G, λ)` with count vector `X` (p.16). -/
def sparsify {k : ℕ} {V E : Type} (G : Hypergraph k V E) (X : E → ℕ) :
    Hypergraph k V (Σ j, Fin (X j)) where
  M := fun h ℓ => G.M h.1 ℓ
  row_inj := fun h => G.row_inj h.1

/-- The coloring of the sparsification: every copy retains its color (p.16). -/
def sparsifyColor {E C : Type} (Y : E → C) (X : E → ℕ) : (Σ j, Fin (X j)) → C :=
  fun h => Y h.1

/-- The rate `α n^{-(k-1)}` of the sparsifications `Poi(G^n, α n^{-(k-1)})` (p.16). -/
noncomputable def poiRate (α : ℝ) (n k : ℕ) : NNReal :=
  (α / (n : ℝ) ^ (k - 1)).toNNReal

end RandOrderCSP


