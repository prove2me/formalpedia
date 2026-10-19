-- Prove2me | Definitions.Def_OAIQWUFI001
-- name    : OAIQWUFI001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:44:47.344987+00:00
-- url     : https://prove2.me/theorems/6038b9bc-195f-490d-9c94-2310307b6a01
-- title:
--   OpenAI universal F∞ group split: spheres, discs and sphere-fillable spaces (definitions bundle 2 of 9)
-- statement:
--   The four definitions behind the Whitehead statement of the split of OpenAI's proof that a single group of type $F_\infty$ contains every finitely presented group (OpenAI, *A universal group of type F∞*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). They are ported to Lean 4.33.1 and Mathlib 0df444a, and the bundle uses only Mathlib.
--
--   - `Cellular.Disk n` and `Cellular.Sphere n`: the closed unit ball and the unit sphere about $0$ in `Fin n → ℝ`. With Mathlib's sup norm these are the cube $[-1,1]^n$ and its boundary.
--   - `Cellular.boundary n`: the inclusion of `Sphere n` into `Disk n`.
--   - `Cellular.SphereFillable Y`: every continuous map from `Sphere n` to $Y$ extends over `Disk n`, for every $n$.
--
--   Module: `CellularLifting.lean`.
--
--   The statement `OAI.UniversalFInfinity.Cellular.contractible_of_sphereFillable` (Whitehead's theorem, contractible case) imports only this bundle. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/UniversalGroup at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology


namespace UniversalFInfinity.Cellular
universe u v w

abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def boundary (n : ℕ) : Sphere n → Disk n :=
  fun x => ⟨x.1, sphere_subset_closedBall x.2⟩

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

noncomputable section

def SphereFillable (Y : Type u) [TopologicalSpace Y] : Prop :=
  ∀ n (a : C(Sphere n,Y)), ∃ e : C(Disk n,Y), ∀ x, e (boundary n x) = a x

end
end UniversalFInfinity.Cellular

end OAI
end


