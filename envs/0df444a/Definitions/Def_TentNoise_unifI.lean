-- Prove2me | Definitions.Def_TentNoise_unifI
-- name    : TentNoise_unifI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:39:54.261529+00:00
-- url     : https://prove2.me/theorems/5190a38e-778b-433c-b319-10f4a7f8977b
-- title:
--   The invariant law $\mu=\mathrm{Unif}[0,1]$ of the tent map
-- statement:
--   The **uniform law on the unit interval**, $\mu:=\mathrm{Unif}[0,1]$, is Lebesgue measure restricted to $[0,1]$. It is the invariant measure of the tent map $f(x)=1-2|x-\tfrac12|$: if $X\sim\mu$ then $f(X)\sim\mu$.
--
--   Every path law of the mission starts from $X_0\sim\mu$, and the one-step error $\varepsilon_P$ is an $L^2(\mu)$ norm.
--
--   **Formalization Note** The state space is encoded as $\mathbb R$; $\mu$ is the restriction of Lebesgue measure to $[0,1]$, a probability measure on $\mathbb R$ concentrated on $[0,1]$.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Definition 2.1, p.3 (PDF p.3)

import Mathlib

open MeasureTheory

namespace TentNoise

/-- The invariant law `µ := Unif[0, 1]` of the tent map
(Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Definition 2.1, p.3).

**Formalization Note** The state space is encoded as `ℝ`; `µ` is Lebesgue measure restricted to
`[0, 1]`, a probability measure on `ℝ` concentrated on `[0, 1]`. -/
noncomputable def unifI : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

end TentNoise


