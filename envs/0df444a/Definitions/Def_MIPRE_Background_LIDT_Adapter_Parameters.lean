-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Adapter_Parameters
-- name    : MIPRE_Background_LIDT_Adapter_Parameters
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:11:29.235393+00:00
-- url     : https://prove2.me/theorems/cd70c5a5-6721-4424-97df-a00295709496
-- title:
--   Definitions of Parameters: The seeded-CL adapter, part 7: the parameter corollary The reduction of `Adapter/Reduction.lean` concludes with the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Adapter.Parameters` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 7: the parameter corollary. The reduction of `Adapter/Reduction.lean` concludes with the *canonical-line* error `lidtError m d q k (3m ε)`, with `k` free subject to `k ≥ 400 m d`. Blueprint `thm:lidt-cl-soundness` asks instead for `δ_CL(ε, q, m, d, 1) = a (dm)^a (ε^b + q^{-b} + 2^{-bmd})`, for universal `a ≥ 1` and `0 < b < 1`. `rem:lidt-cl-adapter` lists turning one into the other as a separate quantitative obligation, to be done "honestly against the explicit constants"; this file does it, and is stated separately from the reduction so that a failure here could…
--
--   **Definitions** (4): `MIPRE.LIDT.clA` (The constant of `δ_CL`.); `MIPRE.LIDT.clB` (The exponent of `δ_CL`.); `MIPRE.LIDT.clK` (The sampling parameter the corollary chooses for the canonical-line theorem.); `MIPRE.LIDT.deltaCL` (**`δ_CL` at `ldc = 1`** (blueprint `thm:lidt-cl-soundness`).).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Adapter.Parameters` (`MIPRE/Background/LIDT/Adapter/Parameters.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 3 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Parameters.lean; blueprint lem:lidt-cl-adapter-params

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Parameters.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game

/-!
# The seeded-CL adapter, part 7: the parameter corollary

The reduction of `Adapter/Reduction.lean` concludes with the *canonical-line* error
`lidtError m d q k (3m ε)`, with `k` free subject to `k ≥ 400 m d`. Blueprint
`thm:lidt-cl-soundness` asks instead for

`δ_CL(ε, q, m, d, 1) = a (dm)^a (ε^b + q^{-b} + 2^{-bmd})`,

for universal `a ≥ 1` and `0 < b < 1`. `rem:lidt-cl-adapter` lists turning one into the other as
a separate quantitative obligation, to be done "honestly against the explicit constants"; this
file does it, and is stated separately from the reduction so that a failure here could not
silently weaken the reduction.

The choice is `b = 1/40000`, `a = 2·10^11` and `k = 400 m³ d + 400 m`. Term by term, with
`ε' = 3 m ε`:

* `ε'^b = (3m)^b ε^b ≤ 3m · ε^b`, since `x^b ≤ x` for `x ≥ 1` and `b ≤ 1`;
* `(d/q)^b = d^b · q^{-b} ≤ d · q^{-b}`, likewise;
* `exp(-k / (2560000 m²)) ≤ 2^{-bmd}`, which is where `k` is chosen: it needs
  `k ≥ 2560000 · b · m³ d · ln 2 = 64 (ln 2) m³ d ≈ 44.4 m³ d`, and `400 m³ d` clears it with
  room. The `400 m` summand is there only so that `k > 0` and `k ≥ 400 m d` hold for every
  `m, d ≥ 1`.

The prefactor is then `100000 k² m⁴ · 3md ≤ 1.92·10^11 (dm)^11`, using `k ≤ 800 m³ d`, and
`(dm)^11 ≤ (dm)^a`.

`d ≥ 1` is needed and not cosmetic: at `d = 0` the blueprint's `δ_CL` is identically zero, so no
positive error can be bounded by it.
-/

namespace MIPRE.LIDT

/-! ## The constants -/

/-- The exponent of `δ_CL`. -/
noncomputable def clB : ℝ := 1 / 40000

/-- The constant of `δ_CL`. -/
def clA : ℝ := 2 * 10 ^ 11

/-- The sampling parameter the corollary chooses for the canonical-line theorem. -/
def clK (m d : ℕ) : ℕ := 400 * m ^ 3 * d + 400 * m

/-- **`δ_CL` at `ldc = 1`** (blueprint `thm:lidt-cl-soundness`). -/
noncomputable def deltaCL (q m d : ℕ) (ε : ℝ) : ℝ :=
  clA * ((d * m : ℕ) : ℝ) ^ clA *
    (ε ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d)))

/-! ## The sampling parameter -/

/-! ## The three terms -/

/-! ## The prefactor -/

/-! ## The corollary -/

end MIPRE.LIDT


