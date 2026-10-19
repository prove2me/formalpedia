-- Prove2me | Definitions.Def_OAI_Combinatorics_SphericalRamsey_MonochromaticObstruction
-- name    : OAI_Combinatorics_SphericalRamsey_MonochromaticObstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:06:45.921969+00:00
-- url     : https://prove2.me/theorems/415de36e-7be5-497a-8dd3-93a4c137ef6b
-- title:
--   Derivation energy of a point and the induced fifty-colouring
-- statement:
--   Let $n\in\mathbb{N}$ and let $D:\mathbb{R}\to\mathbb{R}$ be a derivation over $\mathbb{Z}$ (additive and satisfying $D(xy)=xD(y)+yD(x)$).
--
--   1. **Energy.** For $y\in\mathbb{R}^n$, the derivation energy is
--   $$
--   \mathcal{E}_D(y)=\sum_{j=1}^n D(y_j)^2 .
--   $$
--   2. **Colouring.** For a function $e:\mathbb{R}^n\to\mathbb{R}$, the colour of $y$ is the residue
--   $$
--   \lfloor3e(y)\rfloor\bmod50\in\{0,\dots,49\}.
--   $$
--
--   Such derivations are highly non-measurable, so the colouring $y\mapsto\lfloor3\mathcal{E}_D(y)\rfloor\bmod50$ is far from geometric. It is nevertheless rigid enough to forbid monochromatic copies of the witness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SphericalRamsey/MonochromaticObstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SphericalRamsey/MonochromaticObstruction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GrahamSpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_GrahamSpherical
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_Model

namespace OAI

noncomputable section
open scoped BigOperators
namespace GrahamSpherical

/-- The actual finite squared Euclidean energy of the entrywise derivation. -/
def derivationEnergy {n : ℕ} (D : Derivation ℤ ℝ ℝ) (y : Point n) : ℝ :=
  ∑ j : Fin n, (D (y j)) ^ 2

/-- Native integer floor and Euclidean remainder, reindexed into Fin 50. -/
def energyColor {n : ℕ} (e : Point n → ℝ) (y : Point n) : Fin 50 :=
  ⟨((Int.floor (3 * e y)) % 50).toNat, by
    have h0 := Int.emod_nonneg (Int.floor (3 * e y)) (by norm_num : (50 : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos (Int.floor (3 * e y)) (by norm_num : (0 : ℤ) < 50)
    omega⟩

end GrahamSpherical

end

end OAI


