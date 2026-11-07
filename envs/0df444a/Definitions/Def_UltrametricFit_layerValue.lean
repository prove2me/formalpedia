-- Prove2me | Definitions.Def_UltrametricFit_layerValue
-- name    : UltrametricFit_layerValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:43.61741+00:00
-- url     : https://prove2.me/theorems/69b54b7e-e9af-4bae-b062-321901c1d6bb
-- title:
--   The layers $D_1<\dots<D_L$ of an instance
-- statement:
--   Let $D_1<D_2<\dots<D_L$ be the $L$ distinct values of $X$ on pairs of distinct species. These are the layers of the LP and the only values the algorithm outputs. There are no layers exactly when $n\le1$.
--
--   **Formalization Note** Layers are numbered from $1$, as in the paper. `layerValue X ℓ` is $D_\ell$ for $\ell\in\{1,\dots,L\}$, obtained from the increasing enumeration of the finite set of values, and the junk value $0$ elsewhere. Every statement of the mission reads it only for $\ell\in\{1,\dots,L\}$.
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), §2, p.6

import Mathlib

namespace UltrametricFit

/-- The set of distinct distances of `X`: its values on pairs `i ≠ j`. -/
noncomputable def distinctValues {n : ℕ} (X : Fin n → Fin n → ℝ) : Finset ℝ :=
  (Finset.univ : Finset (Fin n)).offDiag.image fun q => X q.1 q.2

/-- `L`, the number of distinct distances in `X`, Charikar, Gao, STOC 2027 submission (manuscript
sha256 87af12a2…), §2, p.6. It is `0` exactly when `n ≤ 1`. -/
noncomputable def numLayers {n : ℕ} (X : Fin n → Fin n → ℝ) : ℕ :=
  (distinctValues X).card

/-- **The layers** `D₁ < D₂ < ⋯ < D_L`, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), §2, p.6: "We will use D1 < D2 < · · · < DL to denote the L distinct distance in X."

**Formalization Note.** Layers are numbered from `1` as on the page: `layerValue X ℓ` is `D_ℓ` for
`ℓ ∈ {1, …, L}`, namely the `(ℓ − 1)`-th entry of the increasing enumeration
`Finset.orderEmbOfFin`. Outside that range the value is the junk `0`; every statement of this
mission reads `layerValue X ℓ` only for `ℓ ∈ Finset.Icc 1 (numLayers X)`. -/
noncomputable def layerValue {n : ℕ} (X : Fin n → Fin n → ℝ) (ℓ : ℕ) : ℝ :=
  if h : 1 ≤ ℓ ∧ ℓ ≤ numLayers X then
    (distinctValues X).orderEmbOfFin rfl ⟨ℓ - 1, by unfold numLayers at h; omega⟩
  else 0

end UltrametricFit


