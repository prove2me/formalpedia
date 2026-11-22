-- Prove2me | Definitions.Def_Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo
-- name    : Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:23.301156+00:00
-- url     : https://prove2.me/theorems/bebcd0d5-4871-4f93-8cdc-17db212c6789
-- title:
--   Riemann Zeta One Ne Zero Of Real Mem Ioo
-- statement:
--   Definitions and structural lemmas for Riemann Zeta One Ne Zero Of Real Mem Ioo, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RiemannZetaOneNeZeroOfRealMemIoo.lean

import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
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
section Fam
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)
def ccOC (i : ι) : ℂ :=
  deriv (DirichletCharacter.LFunction (χ i)) 1 / DirichletCharacter.LFunction (χ i) 1
def linOC (i : ι) (s : ℂ) : ℂ := -1 + (1 + (Real.eulerMascheroniConstant : ℂ) - ccOC χ i) * s
def EOC (s : ℂ) : ℂ := riemannZeta₁ s * ∏ j, DirichletCharacter.LFunction (χ j) s
def nOC (i : ι) (s : ℂ) : ℂ :=
  -(deriv riemannZeta₁ s / riemannZeta₁ s)
    + deriv (DirichletCharacter.LFunction (χ i)) s / DirichletCharacter.LFunction (χ i) s
    + linOC χ i s
def aOC (i : ι) (s : ℂ) : ℂ :=
  -deriv riemannZeta₁ s * ∏ j, DirichletCharacter.LFunction (χ j) s
    + riemannZeta₁ s * deriv (DirichletCharacter.LFunction (χ i)) s
        * ∏ j ∈ Finset.univ.erase i, DirichletCharacter.LFunction (χ j) s
    + linOC χ i s * EOC χ s
def AOC (s : ℂ) : ℂ := ∑ i, (w i : ℂ) * aOC χ i s
def HOC (ε C θ : ℝ) (x : ℝ) : ℝ := ε * ∑ i, w i * (Gz x - Gchi (χ i) x) + C * x ^ θ
def IOC (ε C θ : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), ((HOC χ w ε C θ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
def PhiOC (ε C θ : ℝ) (s : ℂ) : ℂ :=
  ε * dslope (AOC χ w) 1 s / (s * EOC χ s) + C / (s - θ)
end Fam
end Formalism


