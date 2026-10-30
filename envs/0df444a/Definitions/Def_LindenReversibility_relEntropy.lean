-- Prove2me | Definitions.Def_LindenReversibility_relEntropy
-- name    : LindenReversibility_relEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:31.383985+00:00
-- url     : https://prove2.me/theorems/bd00fa3b-55e7-4a2b-9f47-00984dc5d127
-- title:
--   Relative entropy $S(\rho\|\sigma) = \mathrm{Tr}\,\rho\ln\rho - \mathrm{Tr}\,\rho\ln\sigma$ (eq. 9)
-- statement:
--   For two square complex matrices $\rho,\sigma$ indexed by a finite set $I$, the **relative entropy** of $\rho$ with respect to $\sigma$ is
--
--   $$
--   S(\rho\|\sigma) = \begin{cases} \operatorname{Tr}\rho\ln\rho - \operatorname{Tr}\rho\ln\sigma & \text{if } \ker\sigma\subseteq\ker\rho \ (\text{i.e. } \operatorname{supp}\rho\subseteq\operatorname{supp}\sigma),\\ +\infty & \text{otherwise,}\end{cases}
--   $$
--
--   with natural logarithms and the convention $0\ln 0 = 0$. On density matrices it is the Umegaki relative entropy of eq. (9) of the paper, a number in $[0,+\infty]$.
--
--   It is the distance-like quantity from which the relative entropy of entanglement (11) is built, and the quantity in Donald's identity (10).
--
--   **Formalization Note** The value lies in $[0,+\infty]$ (`ℝ≥0∞`). $\operatorname{Tr}\rho\ln\rho$ is computed as the trace of the continuous functional calculus of $x\mapsto x\ln x$, and $\ln\sigma$ by the functional calculus of the logarithm, which is $0$ on $\ker\sigma$; the support condition makes this convention harmless. The real number inside is nonnegative on density matrices (Klein's inequality), which are the only arguments used in the mission, so the cast to $[0,+\infty]$ loses nothing. The body is that of the published `QAlgorithms.QuantumLoss.umegakiEntropy` without its two density-proof arguments.
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eq. (9), p.2

import Mathlib

open scoped ENNReal

namespace LindenReversibility

open Classical in
/-- Linden, Popescu, Schumacher, Westmoreland, *Reversibility of local transformations of
multiparticle entanglement*, arXiv:quant-ph/9912039v1, eq. (9), p.2: the (Umegaki) relative
entropy `S(ρ‖σ) = Tr ρ ln ρ − Tr ρ ln σ`.

**Formalization Note.** Natural logarithms, as printed ("ln"). The value lies in `ℝ≥0∞`: it is
`+∞` unless `supp ρ ⊆ supp σ`, written as `ker σ ≤ ker ρ`; this guard is what makes the junk
value `log 0 = 0` of `cfc Real.log σ` on `ker σ` harmless. `x ln x` is the continuous function
with value `0` at `0`. On density matrices the real number inside is `≥ 0` (Klein's inequality),
so `ENNReal.ofReal` loses nothing there; every statement of this mission applies it to density
matrices only. The body is that of the published `QAlgorithms.QuantumLoss.umegakiEntropy`
(`Def_QAlgorithms_Defs_ExtendedQuantumEntropy`) without its two density-proof arguments, which
cannot be supplied inside the infimum defining the relative entropy of entanglement. -/
noncomputable def relEntropy {I : Type*} [Fintype I] [DecidableEq I]
    (ρ σ : Matrix I I ℂ) : ℝ≥0∞ :=
  if LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin then
    ENNReal.ofReal (cfc (fun x : ℝ => x * Real.log x) ρ - ρ * cfc Real.log σ).trace.re
  else ⊤

end LindenReversibility


