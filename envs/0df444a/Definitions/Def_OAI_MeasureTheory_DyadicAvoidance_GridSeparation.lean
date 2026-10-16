-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
-- name    : OAI_MeasureTheory_DyadicAvoidance_GridSeparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T02:59:09.066688+00:00
-- url     : https://prove2.me/theorems/7480af0c-658b-4f82-9d9c-1507b992e9b8
-- title:
--   Periodic grid keys and dyadic cell addresses of real numbers
-- statement:
--   This file defines integer keys recording in which cell of a uniform grid, taken modulo $1$, a real number lies. Write $\{x\} = x - \lfloor x \rfloor \in [0,1)$ for the fractional part of a real number $x$.
--
--   1. **Periodic key.** For real numbers $q$ and $x$,
--   $$
--   \operatorname{key}_q(x) = \big\lfloor q\,\{x\} \big\rfloor \in \mathbb{Z}.
--   $$
--   When $q$ is a positive integer, $\operatorname{key}_q(x)$ is the index $j$ of the grid cell $[\,j/q, (j+1)/q)$ containing $\{x\}$. The file records three elementary properties: $\operatorname{key}_q(x+1) = \operatorname{key}_q(x)$ for all real $q$ and $x$; $\operatorname{key}_q(x) \ge 0$ whenever $q \ge 0$; and $\operatorname{key}_q(x) < q$ whenever $q$ is a positive natural number.
--
--   2. **Dyadic key.** For $b \in \mathbb{N}$ and $x \in \mathbb{R}$, the dyadic key of $x$ at resolution $b$ is the periodic key for the mesh $2^{-(b+2)}$, viewed as an element of the finite index set $\{0,1,\dots,2^{b+2}-1\}$:
--   $$
--   \kappa_b(x) = \big\lfloor 2^{b+2}\,\{x\} \big\rfloor \in \{0,1,\dots,2^{b+2}-1\}.
--   $$
--   Thus $\kappa_b(x) = j$ exactly when $\{x\} \in [\,j\,2^{-(b+2)}, (j+1)\,2^{-(b+2)})$. The file proves that $\kappa_b(x) = \kappa_b(y)$ if and only if $\operatorname{key}_{2^{b+2}}(x) = \operatorname{key}_{2^{b+2}}(y)$, for all $b \in \mathbb{N}$ and $x, y \in \mathbb{R}$.
--
--   Dyadic keys are the coordinates at which random Boolean tables are read in the dyadic avoidance construction. A table entry consulted at resolution $b$ depends on the point $x$ only through the dyadic cell of mesh $2^{-(b+2)}$, taken modulo $1$, that contains $x$; consequently every quantity built from such reads is one-periodic and constant on these cells.
--
--   **Formalization Note** The dyadic key is a term of `Fin (2 ^ (b + 2))`, obtained from the integer key by `Int.toNat`; the bounds `periodicKey_nonneg` and `periodicKey_lt` justify this conversion, and `dyadicKey_eq_iff` states that it loses no information.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridSeparation.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridSeparation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α

noncomputable section

namespace Problem310.GridSeparation

/-- The periodic key of a real point in a grid of mesh `1 / q`. -/
def periodicKey (q x : ℝ) : ℤ := ⌊q * Int.fract x⌋

lemma periodicKey_add_one (q x : ℝ) :
    periodicKey q (x + 1) = periodicKey q x := by
  simp [periodicKey]

lemma periodicKey_nonneg {q : ℝ} (hq : 0 ≤ q) (x : ℝ) :
    0 ≤ periodicKey q x := by
  exact Int.floor_nonneg.mpr (mul_nonneg hq (Int.fract_nonneg x))

lemma periodicKey_lt (q : ℕ) (hq : 0 < q) (x : ℝ) :
    periodicKey (q : ℝ) x < (q : ℤ) := by
  apply Int.floor_lt.mpr
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have := mul_lt_mul_of_pos_left (Int.fract_lt_one x) hq'
  simpa using this

/-- A finite-table address for the periodic dyadic grid. -/
def dyadicKey (b : ℕ) (x : ℝ) : Fin (2 ^ (b + 2)) :=
  ⟨(periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) x).toNat,
    (Int.toNat_lt (periodicKey_nonneg (by positivity) x)).mpr
      (periodicKey_lt _ (by positivity) x)⟩

lemma dyadicKey_eq_iff (b : ℕ) (x y : ℝ) :
    dyadicKey b x = dyadicKey b y ↔
      periodicKey ((2 : ℝ) ^ (b + 2)) x =
        periodicKey ((2 : ℝ) ^ (b + 2)) y := by
  constructor
  · intro h
    have hv := congrArg (fun k : Fin (2 ^ (b + 2)) => (k.val : ℤ)) h
    dsimp [dyadicKey] at hv
    rw [Int.toNat_of_nonneg (periodicKey_nonneg (by positivity) x),
      Int.toNat_of_nonneg (periodicKey_nonneg (by positivity) y)] at hv
    simpa using hv
  · intro h
    apply Fin.ext
    dsimp [dyadicKey]
    have h' : periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) x =
        periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) y := by simpa using h
    rw [h']

end Problem310.GridSeparation

end

end OAI


