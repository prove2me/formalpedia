-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementX
-- name    : Formalism_HermitianCurvature_StatementX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:03.022826+00:00
-- url     : https://prove2.me/theorems/637dd85c-9158-4364-a756-9cfa750f710a
-- title:
--   Statement X
-- statement:
--   Definitions and structural lemmas for Statement X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementX.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.X
open Matrix
def MinorScale : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (κ : K) (l : ℕ) (hl : l ≤ n),
    ((Matrix.of (fun a b : Fin n => κ ^ ((a : ℕ) + (b : ℕ)) * Z a b)).submatrix
        (Fin.castLE hl) (Fin.castLE hl)).det =
      κ ^ (l * (l - 1)) * (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det
def MinorScaleGen : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (α β : Fin n → K) (l : ℕ) (hl : l ≤ n),
    ((Matrix.of (fun a b : Fin n => α a * β b * Z a b)).submatrix
        (Fin.castLE hl) (Fin.castLE hl)).det =
      (∏ i : Fin l, α (Fin.castLE hl i) * β (Fin.castLE hl i)) *
        (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det
def ScaleExponents : Prop :=
  (∀ l : ℤ, l * (l - 1) - (l - 1) * (l - 2) = 2 * l - 2) ∧
  (∀ i s : ℤ, (i - 1 + s) * (i - 2 + s) - (i - 1) * (i - 2) = s * (2 * i + s - 3))
def GermPowers : Prop :=
  ∀ s : ℚ, -2 * ((s - 1) * (s + 2) / 2) + 3 * (s - 1) = -(s - 1) ^ 2 ∧
    -2 * (s - 1) + (s - 1) + s * (s - 1) = (s - 1) ^ 2
def SlicePowers : Prop :=
  ∀ s M : ℤ, 2 * (s - 1) * (M + s - 2) - 2 * (s - 1) * (M - 2) - 2 * (s - 1) = 2 * (s - 1) ^ 2
def WeightExponent : Prop :=
  ∀ k r j s : ℤ,
    (k + 2 * r + 1 - 2 * (j - 1)) = k + 1 + 2 * (r - j + 1) ∧
    (k + 2 * r + 1 - 2 * ((r + 1) - 1)) = k + 1 ∧
    2 * s * (k - 1) + 4 * s * (r + 1 - j) + 2 * s * (s - 1) =
      2 * s * ((k + 2 * r + 1 - 2 * (j - 1)) + s - 3)
end Formalism.FourierDecayAlt.X


