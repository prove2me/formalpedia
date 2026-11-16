-- Prove2me | Definitions.Def_SmoothBerr_Supplement_BerrLe
-- name    : SmoothBerr_Supplement_BerrLe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:51:18.852535+00:00
-- url     : https://prove2.me/theorems/06a1d427-dde1-49a1-b102-e15728314815
-- title:
--   Backward error at most $\varepsilon$: $\mathrm{berr}(A,b,\tilde x)\le\varepsilon$
-- statement:
--   For a linear system $Ax=b$ with $A\in\mathbb R^{n\times n}$, the **backward error** of a vector $\tilde x$ is
--   $$
--   \mathrm{berr}(A,b,\tilde x):=\min\bigl\{\varepsilon\ge0:\ (A+\Delta)\tilde x=b\ \text{for some }\Delta\text{ with }\|\Delta\|_2\le\varepsilon\|A\|_2\bigr\},
--   $$
--   where $\|\cdot\|_2$ is the spectral norm. Hence $\mathrm{berr}(A,b,\tilde x)\le\varepsilon$ holds exactly when $\varepsilon\ge0$ and there is a perturbation $\Delta$ with $(A+\Delta)\tilde x=b$ and $\|\Delta\|_2\le\varepsilon\|A\|_2$: the vector $\tilde x$ exactly solves a nearby system.
--
--   This predicate is the success criterion of every backward-error statement of the mission (Theorems 2.2, 2.3, 4.3, 4.4, 9.2).
--
--   **Formalization Note** The predicate encodes the minimum definition, not the folklore ratio $\|A\tilde x-b\|_2/(\|A\|_2\|\tilde x\|_2)$: with Lean's convention $x/0=0$ that ratio would give $\tilde x=0$ backward error $0$ on every system. When no perturbation exists (for example $A=0$, $b\ne0$) the predicate is false. The spectral norm is the published `GaussianMatrix.specNorm`.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), §3, p.4 (definition of berr)

import Mathlib
import Definitions.Def_GaussianMatrix_basic

open Matrix GaussianMatrix

namespace SmoothBerr.Supplement

/-- **Backward error at most `ε`** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to
backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…,
§3, p.4): for the linear system `A x = b`, the vector `x̃` has
`berr(A, b, x̃) := min{ε ≥ 0 : (A + Δ)x̃ = b for some Δ with ‖Δ‖₂ ≤ ε‖A‖₂}`, and
`berr(A, b, x̃) ≤ ε` holds iff `ε ≥ 0` and some `Δ` with `(A + Δ)x̃ = b` has `‖Δ‖₂ ≤ ε‖A‖₂`.

**Formalization Note** The predicate encodes the paper's min-definition, not the folklore ratio
`‖Ax̃ − b‖₂/(‖A‖₂‖x̃‖₂)` (with Lean's `x / 0 = 0` that ratio would make `x̃ = 0` a solution of
every system). When no `Δ` exists (e.g. `A = 0`, `b ≠ 0`) the minimum is over the empty set and
`berr ≤ ε` fails. `‖·‖₂` is the published spectral norm `GaussianMatrix.specNorm`. -/
def BerrLe {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∃ Δ : Matrix (Fin n) (Fin n) ℝ, (A + Δ) *ᵥ x = b ∧ specNorm Δ ≤ ε * specNorm A

end SmoothBerr.Supplement


