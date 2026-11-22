-- Prove2me | Definitions.Def_Formalism_ZetaNonvanishing_Assembly
-- name    : Formalism_ZetaNonvanishing_Assembly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:59.546802+00:00
-- url     : https://prove2.me/theorems/422a71db-087d-4891-a106-871f1cb9df8e
-- title:
--   Assembly
-- statement:
--   Definitions and structural lemmas for Assembly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/Assembly.lean

import Definitions.Def_Formalism_ZetaRealNonvanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Formalism
section SlopeTestRemainingChoices
variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
end SlopeTestRemainingChoices
section Mellin
variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
end Mellin
section Main
variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
def Hf (σ₀ C : ℝ) (x : ℝ) : ℝ := G χ x + C * x ^ σ₀
def Imel (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), ((Hf χ σ₀ C x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
def q0 (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  -1 + s * (1 + (gammaF χ : ℂ)) + C * s * (s - 1) / (s - σ₀)
def Afun (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  -deriv (Pfun χ) s - Pfun χ s + s * (1 + (gammaF χ : ℂ)) * Pfun χ s
    + C * s * (s - 1) * Pfun χ s / (s - σ₀)
def Phi (σ₀ C : ℝ) (s : ℂ) : ℂ := dslope (Afun χ σ₀ C) 1 s / (s * Pfun χ s)
def qfun (σ₀ C : ℝ) (s : ℂ) : ℂ := q0 χ σ₀ C s - s * (s - 1) * Imel χ σ₀ C s
end Main
end Formalism


