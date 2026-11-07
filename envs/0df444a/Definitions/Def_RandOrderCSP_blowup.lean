-- Prove2me | Definitions.Def_RandOrderCSP_blowup
-- name    : RandOrderCSP_blowup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:06:58.907977+00:00
-- url     : https://prove2.me/theorems/539135a7-1d96-4d63-b328-d417618b09f2
-- title:
--   The $n$-fold blowup $G^n$
-- statement:
--   The **$n$-fold blowup** of a $k$-uniform hypergraph $G$ has vertices $\mathcal V_G\times[n]$, edges $\mathcal E_G\times[n]^k$, and $M_{G^n}((j,\tau),\ell)=(M_G(j,\ell),\tau_\ell)$. Each copy of an edge retains the color of the original.
--
--   Random instances of the lower bound are sparse subsamples of this hypergraph.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §4.1, pp.15–16

import Mathlib
import Definitions.Def_RandOrderCSP_Hypergraph

namespace RandOrderCSP

/-- **n-fold blowup** (§4.1, pp.15–16).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), pp.15–16: "𝒱_{G^n} := 𝒱_G × [n],
ℰ_{G^n} := ℰ_G × [n]^k, and, for j ∈ ℰ_G, τ = (τ₁, …, τ_k) ∈ [n]^k, and ℓ ∈ [k]:
M_{G^n}((j, τ), ℓ) := (M_G(j, ℓ), τ_ℓ)." A colored hypergraph's blowup gives every copy `(j, τ)` the
color of `j` (`blowupColor`).

**Formalization Note.** `[n]` is `Fin n` and `[n]^k` is `Fin k → Fin n`. -/
def blowup {k : ℕ} {V E : Type} (G : Hypergraph k V E) (n : ℕ) :
    Hypergraph k (V × Fin n) (E × (Fin k → Fin n)) where
  M := fun e ℓ => (G.M e.1 ℓ, e.2 ℓ)
  row_inj := fun e _ _ h => G.row_inj e.1 (congrArg Prod.fst h)

/-- The coloring of the blowup: every copy of an edge retains its color (p.16). -/
def blowupColor {k : ℕ} {E C : Type} (Y : E → C) (n : ℕ) : E × (Fin k → Fin n) → C :=
  fun e => Y e.1

end RandOrderCSP


