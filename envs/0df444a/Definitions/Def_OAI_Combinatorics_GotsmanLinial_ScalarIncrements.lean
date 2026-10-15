-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
-- name    : OAI_Combinatorics_GotsmanLinial_ScalarIncrements
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:06:12.664708+00:00
-- url     : https://prove2.me/theorems/9711fc45-67f1-40bf-9821-a6f8b7942237
-- title:
--   The coupling potential $\tfrac12 (t-m)|t-m|$ and its increment bounds
-- statement:
--   For a centre $m \in \mathbb{R}$, the coupling potential is the function $\phi_m : \mathbb{R} \to \mathbb{R}$,
--   $$
--   \phi_m(t) = \tfrac12\,(t - m)\,|t - m| ,
--   $$
--   which equals $\tfrac12 (t-m)^2$ to the right of $m$ and $-\tfrac12 (t-m)^2$ to the left. The file records the following properties, valid for all real $m, u, v$:
--
--   1. $\phi_m(m) = 0$.
--   2. Increment bounds: if $u \le v$ (equality allowed), then
--   $$
--   \frac{(v-u)^2}{4} \;\le\; \phi_m(v) - \phi_m(u) \;\le\; \frac{v-u}{2}\bigl(|u - m| + |v - m|\bigr).
--   $$
--   The lower bound is also stated as a separate lemma.
--   3. $\phi_m$ is strictly increasing; consequently $\phi_m(u) \le \phi_m(v) \iff u \le v$, $\phi_m(u) < \phi_m(v) \iff u < v$, and $\phi_m(u) = \phi_m(v) \iff u = v$.
--
--   In the one-sided coupling estimate of the Gotsman–Linial proof, $\phi_m$ converts displacements into telescoping increments: the lower bound controls squared distances $(v-u)^2$, while the upper bound is a trapezoid-type estimate in terms of the distances of the endpoints from the centre.
--
--   **Formalization Note** The definition is `couplingPotential m t`; the lemmas are `couplingPotential_self`, `couplingPotential_increment_bounds`, `couplingPotential_increment_lower`, `strictMono_couplingPotential` and the simp lemmas `couplingPotential_le_iff`, `couplingPotential_lt_iff`, `couplingPotential_eq_iff`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/ScalarIncrements.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/ScalarIncrements.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GotsmanLinial mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments

namespace OAI

/-!
# Scalar inequalities for the one-sided coupling estimate

The increasing function `couplingPotential m t = (t-m)|t-m|/2` controls
squared distances from below and has a trapezoidal increment bound from above.
All arguments here are algebraic, by splitting according to the positions of
the endpoints relative to the center `m`.
-/

namespace LeanBlast.GotsmanLinial

/-- The scalar potential used in the one-sided coupling argument. -/
noncomputable def couplingPotential (m t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (t - m) * |t - m|

@[simp] theorem couplingPotential_self (m : ℝ) : couplingPotential m m = 0 := by
  simp [couplingPotential]

/-- Both increment inequalities hold even when the endpoints coincide. -/
theorem couplingPotential_increment_bounds (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    (v - u) ^ 2 / 4 ≤ couplingPotential m v - couplingPotential m u ∧
      couplingPotential m v - couplingPotential m u ≤
        (v - u) / 2 * (|u - m| + |v - m|) := by
  by_cases hum : u ≤ m
  · by_cases hvm : v ≤ m
    · simp only [couplingPotential, abs_of_nonpos (sub_nonpos.mpr hum),
        abs_of_nonpos (sub_nonpos.mpr hvm)]
      constructor
      · nlinarith [sq_nonneg (v - u),
          mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hvm)]
      · nlinarith
    · have hmv : m ≤ v := (not_le.mp hvm).le
      simp only [couplingPotential, abs_of_nonpos (sub_nonpos.mpr hum),
        abs_of_nonneg (sub_nonneg.mpr hmv)]
      constructor
      · nlinarith [sq_nonneg (u + v - 2 * m)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hum) (sub_nonneg.mpr hmv)]
  · have hmu : m ≤ u := (not_le.mp hum).le
    have hmv : m ≤ v := hmu.trans huv
    simp only [couplingPotential, abs_of_nonneg (sub_nonneg.mpr hmu),
      abs_of_nonneg (sub_nonneg.mpr hmv)]
    constructor
    · nlinarith [sq_nonneg (v - u),
        mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hmu)]
    · nlinarith

theorem couplingPotential_increment_lower (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    (v - u) ^ 2 / 4 ≤ couplingPotential m v - couplingPotential m u :=
  (couplingPotential_increment_bounds m huv).1

theorem strictMono_couplingPotential (m : ℝ) : StrictMono (couplingPotential m) := by
  intro u v huv
  have h := couplingPotential_increment_lower m huv.le
  have hs := mul_pos (sub_pos.mpr huv) (sub_pos.mpr huv)
  nlinarith

@[simp] theorem couplingPotential_le_iff (m u v : ℝ) :
    couplingPotential m u ≤ couplingPotential m v ↔ u ≤ v :=
  (strictMono_couplingPotential m).le_iff_le

@[simp] theorem couplingPotential_lt_iff (m u v : ℝ) :
    couplingPotential m u < couplingPotential m v ↔ u < v :=
  (strictMono_couplingPotential m).lt_iff_lt

@[simp] theorem couplingPotential_eq_iff (m u v : ℝ) :
    couplingPotential m u = couplingPotential m v ↔ u = v :=
  (strictMono_couplingPotential m).injective.eq_iff

end LeanBlast.GotsmanLinial

end OAI


