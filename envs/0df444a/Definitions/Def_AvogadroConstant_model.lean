-- Prove2me | Definitions.Def_AvogadroConstant_model
-- name    : AvogadroConstant_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T17:15:38.583391+00:00
-- url     : https://prove2.me/theorems/e5d490ce-ef7f-47be-8059-d541559edde5
-- title:
--   Model of amount of substance, molar quantities and the Avogadro constant
-- statement:
--   This definition file fixes the model in which every statement of the mission is expressed.
--
--   A **unit system** is a triple of strictly positive real numbers: a mass unit $\mathrm{g}$ (the
--   gram), a second mass unit $\mathrm{Da}$ (the dalton), and an amount-of-substance unit $\mathrm{mol}$
--   (the mole), all read on one common scale. Positivity of each is part of the data.
--
--   On top of it the file records the quantities the SI uses to relate a count of entities to an amount
--   of substance:
--
--   1. the **Avogadro number** $N_0 = 6.02214076 \times 10^{23}$, written as the exact rational
--      $602214076 \times 10^{15}$ (the value fixed by the 2019 revision of the SI), together with its
--      positivity;
--   2. the **Avogadro constant** $N_A = N_0/\mathrm{mol}$, together with its positivity;
--   3. the **amount of substance** $n(X) = N(X)/N_A$ of a sample of $N(X)$ entities;
--   4. the **molar mass** $M(X) = m(X)\,N_A$ of an entity of mass $m(X)$;
--   5. the **molar volume** $V_m = v\,N_A$ of an entity occupying volume $v$;
--   6. the **elementary amount** $n_a = 1/N_A$, the amount of substance of a single entity;
--   7. the **crystal entity count** $k\,V/v_{\text{cell}}$ of a crystal of volume $V$ whose unit cell
--      has volume $v_{\text{cell}}$ and contains $k$ entities.
--
--   Items 3–7 take the Avogadro constant as an explicit argument rather than reading it off a fixed
--   unit system, so that the same notions can be used with the pre-2019 (measured) and post-2019
--   (fixed) values.
--
--   **Formalization Note** All quantities are real numbers; division is Lean's total division, so the
--   derived quantities are defined — with the usual junk value — also when the divisor is zero. The
--   statements of the mission supply the nondegeneracy they need, either from the positivity proofs
--   carried by the unit system or as an explicit hypothesis.
-- source:
--   Wikipedia, "Avogadro constant" (uploaded PDF snapshot), sections "Definition" and "History / X-ray crystallography"; SI 2019 redefinition of the mole, https://en.wikipedia.org/wiki/Avogadro_constant

import Mathlib

namespace AvogadroConstant

/-- A choice of a mass unit (`gram`), a second mass unit (`dalton`) and an
amount-of-substance unit (`mole`), all measured on a common positive scale. -/
structure MassAmountUnits where
  gram : ℝ
  dalton : ℝ
  mole : ℝ
  gram_pos : 0 < gram
  dalton_pos : 0 < dalton
  mole_pos : 0 < mole

/-- The Avogadro number `N₀ = 6.02214076 × 10²³`, the exact SI value fixed in 2019. -/
noncomputable def avogadroNumber : ℝ := 602214076 * 10 ^ 15

lemma avogadroNumber_pos : 0 < avogadroNumber := by
  unfold avogadroNumber; positivity

/-- The Avogadro constant `N_A = N₀ / mol`. -/
noncomputable def avogadroConstant (U : MassAmountUnits) : ℝ := avogadroNumber / U.mole

lemma avogadroConstant_pos (U : MassAmountUnits) : 0 < avogadroConstant U :=
  div_pos avogadroNumber_pos U.mole_pos

/-- The amount of substance `n(X) = N(X) / N_A` of a sample containing `N` entities. -/
noncomputable def amountOfSubstance (NA N : ℝ) : ℝ := N / NA

/-- The molar mass `M(X) = m(X) · N_A` obtained from the mass `m` of one entity. -/
noncomputable def molarMass (NA m : ℝ) : ℝ := m * NA

/-- The molar volume `V_m = v · N_A` obtained from the volume `v` occupied by one entity. -/
noncomputable def molarVolume (NA v : ℝ) : ℝ := v * NA

/-- The elementary amount `n_a = 1 / N_A`: the amount of substance of a single entity. -/
noncomputable def elementaryAmount (NA : ℝ) : ℝ := 1 / NA

/-- The number of entities in a crystal of volume `V` whose unit cell has volume
`vCell` and contains `k` entities. -/
noncomputable def crystalEntityCount (V vCell : ℝ) (k : ℕ) : ℝ := (k : ℝ) * (V / vCell)

end AvogadroConstant


