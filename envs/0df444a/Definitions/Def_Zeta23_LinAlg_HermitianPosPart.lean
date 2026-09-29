-- Prove2me | Definitions.Def_Zeta23_LinAlg_HermitianPosPart
-- name    : Zeta23_LinAlg_HermitianPosPart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:00:04.332682+00:00
-- url     : https://prove2.me/theorems/bb1dc2e3-f53a-4d32-9166-e641032e59ea
-- title:
--   Positive and negative parts of a Hermitian matrix via spectral calculus
-- statement:
--   This bundle defines the spectral positive/negative-part construction for Hermitian matrices, part of the self-contained `RHLinalg` linear-algebra development accompanying §3 of the paper (written by the paper's authors, incorporated unchanged). It works over any `RCLike` field and finite index type.
--
--   **`specMap`**: for a Hermitian matrix $A = U\,\mathrm{diag}(\lambda)\,U^H$ (Mathlib's spectral decomposition) and a real function $f$, the matrix
--   $$\mathrm{specMap}(h_A, f) := U\,\mathrm{diag}(f \circ \lambda)\,U^H$$
--   — the functional calculus applied through the eigenbasis (equivalent to `Matrix.IsHermitian.cfc`, reproduced to keep imports light and the eigenvalue bookkeeping explicit).
--
--   **`hermPosPart`** $A_+ := U\,\mathrm{diag}(\lambda^+)\,U^H$ and **`hermNegPart`** $A_- := U\,\mathrm{diag}(\lambda^-)\,U^H$, where $\lambda^+ = \max(\lambda, 0)$ and $\lambda^- = \max(-\lambda, 0)$: the positive and negative parts, satisfying $A = A_+ - A_-$, both positive semidefinite, $A_+A_- = 0$, and $\mathrm{rank}\,A_+ = n_+(A)$ (the positive index).
--
--   In the project this explicit spectral construction is what the rank–trace inequality proof needs; the bundle is consumed by `Assembly/Inputs.lean` and `Assembly.lean` (the decomposition $\hat A = P + Q$ of prop:block and the counting inequalities of §4) on the way to Theorems A, B, C.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/HermitianPosPart.lean

import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_PosIndex

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/

/-!
# Positive and negative parts of a Hermitian matrix

For a Hermitian matrix `Q` with spectral decomposition `Q = U diag(λ) Uᴴ`,
define `Q₊ := U diag(λ⁺) Uᴴ` and `Q₋ := U diag(λ⁻) Uᴴ` where
`λ⁺ = max(λ,0)`, `λ⁻ = max(−λ,0)`.

Then `Q = Q₊ − Q₋`, both are PSD, `Q₊ Q₋ = 0`, and `rank Q₊ = n₊(Q)`.

This is equivalent to the CFC `Q⁺`/`Q⁻` via `Matrix.IsHermitian.cfc_eq`, but
the direct spectral construction keeps the eigenvalue bookkeeping explicit,
which is what the rank–trace proof needs.
-/

noncomputable section

open Matrix Finset Unitary
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Apply a real function to a Hermitian matrix via its spectral decomposition:
`specMap hA f := U diag(f ∘ λ) Uᴴ`. (This is `Matrix.IsHermitian.cfc`, reproduced
here to keep imports light and bookkeeping explicit.) -/
def specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix n n 𝕜 :=
  conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
    (diagonal (fun i => (f (hA.eigenvalues i) : 𝕜)))











section PosNegPart

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)

/-- Positive part `A₊ := U diag(λ⁺) Uᴴ`. -/
def hermPosPart : Matrix n n 𝕜 := specMap hA (·⁺)

/-- Negative part `A₋ := U diag(λ⁻) Uᴴ`. -/
def hermNegPart : Matrix n n 𝕜 := specMap hA (·⁻)













end PosNegPart

end RHLinalg


