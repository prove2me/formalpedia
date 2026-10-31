-- Prove2me | Definitions.Def_StrategicObfuscation_IsDetection
-- name    : StrategicObfuscation_IsDetection
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:01.672163+00:00
-- url     : https://prove2.me/theorems/db94f619-401a-424c-b5d0-f640059e9d15
-- title:
--   Detection probability $\pi(\sigma,e)$ with Assumption 1 in difference form
-- statement:
--   An applicant obfuscates a proposal with effort $e\ge 0$, and a reviewer with resources $\sigma\in[0,1]$ finds hard evidence of the idea's value with probability $\pi(\sigma,e)$. The function $\pi$ is a **detection probability** when:
--
--   1. $\pi(\sigma,e)\in[0,1]$ for $\sigma\in[0,1]$, $e\ge 0$;
--   2. $\pi(1,0)=1$, and $\sigma\mapsto\pi(\sigma,0)$ is strictly increasing on $[0,1]$, so $\pi(\sigma,0)<1$ for $\sigma<1$;
--   3. $\pi$ is weakly increasing in $\sigma$ and weakly decreasing in $e$;
--   4. for $\sigma<\sigma'$ in $[0,1]$ and $0\le e<e'$,
--
--   $$\pi(\sigma',e')-\pi(\sigma,e')\le\pi(\sigma',e)-\pi(\sigma,e),$$
--
--   with strict inequality whenever $\pi(\sigma,e')<\pi(\sigma,e)$.
--
--   This is the model's primitive: obfuscation hurts the reviewer more when the reviewer has more resources.
--
--   **Formalization Note** The paper states submodularity as $\partial^2\pi/\partial\sigma\partial e<0$. Condition 4 follows from it by integrating the mixed partial, and it also admits the paper's own example on p.14, whose $q$ is flat for $e\ge 1/2$. Nothing is assumed about $\pi$ outside $[0,1]\times[0,\infty)$.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), §2, p.8 and Assumption 1, p.9

import Mathlib

open Set

namespace StrategicObfuscation

/-- **The detection probability `π(σ, e)` of the model, with Assumption 1 in difference form.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), §2, p.8 (PDF p.8) and Assumption 1, p.9 (PDF p.9).

`π σ e` is the probability that a reviewer with resources `σ ∈ [0, 1]` finds hard evidence on a
proposal obfuscated with effort `e ≥ 0`. It is a probability, `π(1, 0) = 1`, `π(·, 0)` is strictly
increasing (so `π(σ, 0) < 1` for `σ < 1`), `π` is weakly increasing in `σ` and weakly decreasing in
`e`, and its differences in `σ` decrease in `e`: for `σ < σ'` and `0 ≤ e < e'`,
`π σ' e' - π σ e' ≤ π σ' e - π σ e`, strictly whenever `π σ e' < π σ e`.

**Formalization Note** The paper states submodularity as `∂²π/∂σ∂e < 0`. The difference form follows
from it by integrating the mixed partial, and it also admits the paper's own example on p.14, whose
`q` is flat for `e ≥ 1/2`. The strict clause is what makes every selection of the argmax monotone
in `σ`. No hypothesis looks at `π` outside `[0, 1] × [0, ∞)`. -/
structure IsDetection (π : ℝ → ℝ → ℝ) : Prop where
  /-- `π σ e` is a probability. -/
  mem_Icc : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ e, 0 ≤ e → π σ e ∈ Icc (0 : ℝ) 1
  /-- `π(1, 0) = 1`. -/
  one_zero : π 1 0 = 1
  /-- `π(·, 0)` is strictly increasing; with `π(1, 0) = 1` this gives `π(σ, 0) < 1` for `σ < 1`. -/
  strictMono_zero : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ σ' ∈ Icc (0 : ℝ) 1, σ < σ' → π σ 0 < π σ' 0
  /-- `π` is weakly increasing in `σ`. -/
  mono_sigma : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ σ' ∈ Icc (0 : ℝ) 1, σ ≤ σ' → ∀ e, 0 ≤ e → π σ e ≤ π σ' e
  /-- `π` is weakly decreasing in `e`. -/
  anti_effort : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ e e', 0 ≤ e → e ≤ e' → π σ e' ≤ π σ e
  /-- Differences in `σ` weakly decrease in `e`. -/
  submodular : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ σ' ∈ Icc (0 : ℝ) 1, σ < σ' → ∀ e e', 0 ≤ e → e < e' →
    π σ' e' - π σ e' ≤ π σ' e - π σ e
  /-- Differences in `σ` strictly decrease between two efforts that `π σ` separates. -/
  submodular_strict : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ σ' ∈ Icc (0 : ℝ) 1, σ < σ' → ∀ e e', 0 ≤ e → e < e' →
    π σ e' < π σ e → π σ' e' - π σ e' < π σ' e - π σ e

end StrategicObfuscation


