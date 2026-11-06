-- Prove2me | Definitions.Def_AnytimeAdaVR_Path
-- name    : AnytimeAdaVR_Path
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:46.50038+00:00
-- url     : https://prove2.me/theorems/56dfb768-6912-463f-81b8-111cbca71a76
-- title:
--   The three continuing paths S, M, D
-- statement:
--   The anytime algorithm runs three independent **paths**: **S** (block averaging, for the basic regime), **M** (recursive variance reduction, for average smoothness) and **D** (AdaGrad-Norm, for noiseless gradients). The order S, M, D is the tie-breaking order of validation.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5, p.7; §5.3, p.9

import Mathlib

namespace AnytimeAdaVR

/-- **The three continuing paths S, M, D.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction
across Smoothness and Noise Conditions* (preprint, 2026), §5, p.7: "the algorithm maintains
independent paths S, M, and D for the basic, average-smooth, and noiseless guarantees,
respectively." The constructor order `S, M, D` is the paper's tie-breaking order (§5.3, p.9). -/
inductive Path
  | S
  | M
  | D
  deriving DecidableEq, Inhabited

instance : Fintype Path :=
  ⟨{.S, .M, .D}, by intro x; cases x <;> simp⟩

end AnytimeAdaVR


