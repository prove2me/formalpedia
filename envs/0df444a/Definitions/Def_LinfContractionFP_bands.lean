-- Prove2me | Definitions.Def_LinfContractionFP_bands
-- name    : LinfContractionFP_bands
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:07.72305+00:00
-- url     : https://prove2.me/theorems/c9d12671-5ba3-463c-9f64-b738ec506816
-- title:
--   The extremal bands $R_\pm$, $S_\pm$ of $\sigma+b$ (display (7))
-- statement:
--   For a secret $\sigma$, shift $b$ and tolerance $\tau$, let $\sigma'_i=\sigma_i+b_i$, $H'=\max_i\sigma'_i$ and $L'=\min_i\sigma'_i$. The **extremal bands** are
--   $$R_+=\{i:\sigma'_i>H'-\tau\},\quad S_+=\{i:\sigma'_i>H'-8\tau\},\quad R_-=\{i:\sigma'_i<L'+\tau\},\quad S_-=\{i:\sigma'_i<L'+8\tau\}.$$
--   $R_\pm$ are the coordinates Amplify must label correctly; $S_\pm$ are the larger bands on which the potentials are defined.
--
--   **Formalization Note** The bands are strict, as printed.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), display (7) and the band definitions, p.14

import Mathlib

open scoped Classical

namespace LinfContractionFP

/-- The extremal bands of the shifted vector `σ' = σ + b` at tolerance `τ` (display (7), p.14):
with `H' = max_i σ'_i` and `L' = min_i σ'_i`,
`R₊ = {i : σ'_i > H' − τ}`, `S₊ = {i : σ'_i > H' − 8τ}`, `R₋ = {i : σ'_i < L' + τ}`,
`S₋ = {i : σ'_i < L' + 8τ}`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), display (7) and the band
definitions, p.14: "σ'_i := σ_i + b_i, H' := max_i σ'_i, L' := min_i σ'_i, (7) we introduce the
extremal bands R+ := {i : σ'_i > H' − τ}, S+ := {i : σ'_i > H' − 8τ}, R− := {i : σ'_i < L' + τ},
S− := {i : σ'_i < L' + 8τ}".

**Formalization Note.** The bands are strict (`>`, `<`), as printed; they are `Finset`s of the
finite coordinate type `κ`. `H'` and `L'` are `⨆` and `⨅` over `κ` (attained when `κ` is
nonempty). `bandRplus σ b τ` etc. take the secret `σ`, the shift `b` and the tolerance `τ`. -/
noncomputable def bandRplus {κ : Type} [Fintype κ] (σ b : κ → ℝ) (τ : ℝ) : Finset κ :=
  Finset.univ.filter fun i => (σ + b) i > (⨆ j, (σ + b) j) - τ

/-- `S₊ = {i : σ'_i > H' − 8τ}` (display (7), p.14). -/
noncomputable def bandSplus {κ : Type} [Fintype κ] (σ b : κ → ℝ) (τ : ℝ) : Finset κ :=
  Finset.univ.filter fun i => (σ + b) i > (⨆ j, (σ + b) j) - 8 * τ

/-- `R₋ = {i : σ'_i < L' + τ}` (display (7), p.14). -/
noncomputable def bandRminus {κ : Type} [Fintype κ] (σ b : κ → ℝ) (τ : ℝ) : Finset κ :=
  Finset.univ.filter fun i => (σ + b) i < (⨅ j, (σ + b) j) + τ

/-- `S₋ = {i : σ'_i < L' + 8τ}` (display (7), p.14). -/
noncomputable def bandSminus {κ : Type} [Fintype κ] (σ b : κ → ℝ) (τ : ℝ) : Finset κ :=
  Finset.univ.filter fun i => (σ + b) i < (⨅ j, (σ + b) j) + 8 * τ

end LinfContractionFP


