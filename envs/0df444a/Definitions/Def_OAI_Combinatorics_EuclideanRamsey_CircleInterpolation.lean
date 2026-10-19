-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
-- name    : OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:26:04.34919+00:00
-- url     : https://prove2.me/theorems/e7c5340e-347a-4162-b82f-8e329d246963
-- title:
--   Secant lines and paired secant quadrics over the coordinate field
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it.
--
--   Let $a_0,\dots,a_{s-1}$ be points of the plane $\mathbb R^2$ and $K\subseteq\mathbb R$ the field generated over $\mathbb Q$ by their coordinates. Write $\tilde a_i=(1,a_{i0},a_{i1})$ for the augmented points.
--
--   1. **Secant rows.** For $i,j$, the coefficients $\ell_{ij}=\bigl(a_{i0}a_{j1}-a_{j0}a_{i1},\ a_{i1}-a_{j1},\ a_{j0}-a_{i0}\bigr)\in K^3$ of an affine function $x\mapsto\langle\ell_{ij},\tilde x\rangle$ that vanishes at $a_i$ and $a_j$.
--   2. **Secant values.** The determinant
--   $$
--   \Delta(i,j,k)=(a_{j0}-a_{i0})(a_{k1}-a_{i1})-(a_{j1}-a_{i1})(a_{k0}-a_{i0}),
--   $$
--   which vanishes exactly when $a_i,a_j,a_k$ are collinear.
--   3. **Paired secant matrices.** $M=\ell_{ij}\ell_{kl}^{\mathsf T}$. Its quadratic form $\tilde x^{\mathsf T}M\tilde x=\langle\ell_{ij},\tilde x\rangle\langle\ell_{kl},\tilde x\rangle$ vanishes at $a_i,a_j,a_k,a_l$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CircleInterpolation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CircleInterpolation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle

namespace OAI

/- The secant equations and quadratic isolators have coefficients in the coordinate field. -/
noncomputable section
namespace EuclideanRamsey.CircleConsequence

def secantRow {s : ℕ} (a : Fin s → Space 2) (i j : Fin s) :
    Option (Fin 2) → Coeff a
  | none => coordinate a i 0 * coordinate a j 1 - coordinate a j 0 * coordinate a i 1
  | some k => if k = 0 then coordinate a i 1 - coordinate a j 1
      else coordinate a j 0 - coordinate a i 0

def secantValue {s : ℕ} (a : Fin s → Space 2) (i j k : Fin s) : Coeff a :=
  (coordinate a j 0-coordinate a i 0)*(coordinate a k 1-coordinate a i 1) -
  (coordinate a j 1-coordinate a i 1)*(coordinate a k 0-coordinate a i 0)

def pairedSecantMatrix {s : ℕ} (a : Fin s → Space 2)
    (i j k l : Fin s) : Matrix (Option (Fin 2)) (Option (Fin 2)) (Coeff a) :=
  fun α β => secantRow a i j α * secantRow a k l β

end EuclideanRamsey.CircleConsequence

end

end OAI


