-- Prove2me | Definitions.Def_GreenTao_ProgressionCS
-- name    : GreenTao_ProgressionCS
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T21:16:36.9856+00:00
-- url     : https://prove2.me/theorems/b20cccbe-1fce-46c6-8706-dab15b9be235
-- title:
--   Progression forms, Cauchy–Schwarz factors, and cube weights
-- statement:
--   Fix a dimension $d$, a distinguished progression position $j\in\{0,\ldots,d\}$, and write $\sigma_j$ for the increasing enumeration of the other positions. Put
--
--   $$c_i=\sigma_j(i)-j,\qquad a_{i\ell}=1-c_i/c_\ell,\qquad\phi_i(y)=\sum_\ell a_{i\ell}y_\ell.$$
--
--   Rational coefficients use the project's modular interpretation. For $S_l=\{d-l,\ldots,d-1\}$, the point $y^\omega$ selects the copied coordinate $y'_i$ when $\omega_i=1$ and the original $y_i$ otherwise. The stage averages $J_l$ and factors $P_l$ are the quantities in Green–Tao equations (5.17) and (5.18), with the distinguished function evaluated at $\sum_i y_i$ and the other functions at $\phi_i(y)$. The accumulated factor is
--
--   $$P=\prod_{l=0}^{d-1}P_l^{\,2^{d-1-l}}.$$
--
--   For a majorant $\mu$, define the cube weight
--
--   $$W(x,h)=\mathbb E_r\prod_{i=0}^{d-1}\prod_{\substack{\omega\in\{0,1\}^d\\\omega_i=0}}\mu\!\left(x+c_i r+\sum_\ell a_{i\ell}\omega_\ell h_\ell\right),$$
--
--   and the weighted cube average
--
--   $$C_d^W(f)=\mathbb E_{x,h}W(x,h)\prod_{\omega\in\{0,1\}^d}f(x+\omega\cdot h).$$
--
--   These are the finite data used to separate the Cauchy–Schwarz part of Proposition 5.3 from its linear-forms moment estimates. The expression for $W$ uses the progression difference to replace redundant fiber coordinates in equation (5.25), and pairs the two equal square-root factors in each omitted coordinate.
--
--   **Formalization Note.** Definitions are total. Their identification with the source's progression argument is used for $d\ge2$ and prime moduli larger than $d$. The stage averages retain the square-root formulation of equation (5.17); the final weight uses its paired formulation.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5 Lemma 5.4, equations (5.17)–(5.22), the forms φ_i and uniform-cover reparameterization in the proof of Proposition 5.3, and equation (5.25). The cube weight is the same weight reparameterized by the progression difference r; it has the coefficients x+c_i r+Σ_l(1−c_i/c_l)ω_l h_l.

import Definitions.Def_GreenTao_Uniformity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Pi

open scoped BigOperators

namespace GreenTao

/-- Consecutive progression coefficients translated so that the distinguished coefficient is zero. -/
def csCoeff (d : ℕ) (j : Fin (d + 1)) (i : Fin d) : ℤ :=
  ((j.succAbove i).val : ℤ) - (j.val : ℤ)

/-- Rational coefficients of the coordinate forms of Proposition 5.3. -/
def csRatCoeff (d : ℕ) (j : Fin (d + 1)) (i l : Fin d) : ℚ :=
  1 - (csCoeff d j i : ℚ) / (csCoeff d j l : ℚ)

/-- The coordinate forms used in Green--Tao Proposition 5.3, after making the
distinguished coefficient zero. -/
noncomputable def csForm (d : ℕ) {m : ℕ+} (j : Fin (d + 1)) (i : Fin d)
    (y : Fin d → ZMod (m : ℕ)) : ZMod (m : ℕ) :=
  ∑ l : Fin d, ratCoeff m (csRatCoeff d j i l) * y l

/-- The last `l` coordinates, duplicated after `l` Cauchy--Schwarz steps. -/
def csTail (d l : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun i => d - l ≤ i.val

/-- The point `y^(S)` of Green--Tao §5: choose an independent copy in the
coordinates where the cube digit is one. -/
def partialCubePoint {d : ℕ} {α : Type} (S : Finset (Fin d))
    (y y' : Fin d → α) (ω : S → Bool) : Fin d → α := fun i =>
  if hi : i ∈ S then if ω ⟨i, hi⟩ then y' i else y i else y i

/-- The finite stage averages `J_l` in equation (5.17). Unused copy coordinates
are averaged too; they do not alter the uniform average. -/
noncomputable def csStage (d : ℕ) {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ) (l : ℕ) : ℝ :=
  avg fun y : Fin d → ZMod (m : ℕ) => avg fun y' : Fin d → ZMod (m : ℕ) =>
    ∏ ω : csTail d l → Bool,
      F j (∑ a, partialCubePoint (csTail d l) y y' ω a) *
      ∏ i : Fin d,
        if i ∈ csTail d l then
          Real.sqrt (μ (csForm d j i (partialCubePoint (csTail d l) y y' ω)))
        else F (j.succAbove i) (csForm d j i (partialCubePoint (csTail d l) y y' ω))

/-- The factor `P_l` of equation (5.18). -/
noncomputable def csStepFactor (d : ℕ) {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (l : Fin d) : ℝ :=
  avg fun y : Fin d → ZMod (m : ℕ) => avg fun y' : Fin d → ZMod (m : ℕ) =>
    ∏ ω : csTail d l.val → Bool,
      μ (csForm d j l.rev (partialCubePoint (csTail d l.val) y y' ω))

/-- The product of Cauchy--Schwarz losses in equation (5.21). -/
noncomputable def csFactor (d : ℕ) {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) : ℝ :=
  ∏ l : Fin d, csStepFactor d j μ l ^ (2 ^ (d - 1 - l.val))

/-- The weight `W(x,h)` in equation (5.25), after replacing the redundant fiber
coordinates by the progression difference. The coordinates with `ω i = true`
duplicate those with `ω i = false` and have already been paired. -/
noncomputable def csWeight (d : ℕ) {m : ℕ+} (j : Fin (d + 1))
    (μ : ZMod (m : ℕ) → ℝ) (x : ZMod (m : ℕ))
    (h : Fin d → ZMod (m : ℕ)) : ℝ :=
  avg fun r : ZMod (m : ℕ) => ∏ i : Fin d,
    ∏ ω : Fin d → Bool with ω i = false,
      μ (x + (csCoeff d j i : ZMod (m : ℕ)) * r +
        ∑ l : Fin d, ratCoeff m (csRatCoeff d j i l) * (if ω l then h l else 0))

/-- A Gowers cube average with the weight from the sparse Cauchy--Schwarz argument. -/
noncomputable def weightedCubeAvg (d : ℕ) {m : ℕ+}
    (W : ZMod (m : ℕ) → (Fin d → ZMod (m : ℕ)) → ℝ)
    (f : ZMod (m : ℕ) → ℝ) : ℝ :=
  avg fun x => avg fun h : Fin d → ZMod (m : ℕ) =>
    W x h * ∏ ω : Fin d → Bool, f (x + ∑ i : Fin d, if ω i then h i else 0)

end GreenTao


