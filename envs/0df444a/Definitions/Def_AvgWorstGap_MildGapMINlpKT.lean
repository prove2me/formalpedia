-- Prove2me | Definitions.Def_AvgWorstGap_MildGapMINlpKT
-- name    : AvgWorstGap_MildGapMINlpKT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:51:19.168209+00:00
-- url     : https://prove2.me/theorems/c5432ff9-10d9-4e69-aba1-18e4158d590d
-- title:
--   $\mathrm{Mild}$-$\mathrm{Gap}_\rho$-$\mathrm{MIN}\ell$-$\mathrm{pKT}^O$
-- statement:
--   For an oracle $O$ and $\rho:\mathbb N\to\mathbb N$, $\mathrm{Mild}\text{-}\mathrm{Gap}_\rho\text{-}\mathrm{MIN}\ell\text{-}\mathrm{pKT}^O$ is the promise problem with
--   $$\mathrm{YES}=\{(x,1^s,1^t,1^\ell,1^a,1^b,1^c,1^d) : \ell\text{-}\mathrm{pK}^{t,O}_{b/a,d/c}(x)\le s\},$$
--   $$\mathrm{NO}=\{(x,1^s,1^t,1^\ell,1^a,1^b,1^c,1^d) : \ell\text{-}\mathrm{pK}^{t+\rho(|x|+\ell+a+b+c+d),O}_{(b-1)/a,(d-1)/c}(x)\ge s+\log\rho(t+\ell+a+b+c+d)\}.$$
--   $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MIN}\ell\text{-}\mathrm{pKT}^O\in\mathsf{prBPP}$ means that this holds for $\rho(n)=n^g$ with some constant $g$.
--
--   **Formalization Note** An instance belongs to YES or NO only if $2\le b<a$ and $2\le d<c$, so that all four parameters lie in $(0,1)$, the domain of Definition 3.5. $g$ is an integer $g\ge1$; $\log$ is base $2$; comparisons are in the extended reals; instances use the tuple encoding.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Definition 3.6, p.22

import Mathlib
import Definitions.Def_AvgWorstGap_lpK
import Definitions.Def_AvgWorstGap_InPrBPP
import Definitions.Def_NKtLB_tupleEnc

namespace AvgWorstGap

open NKtLB

/-- The instance `(x, 1^s, 1^t, 1^ℓ, 1^a, 1^b, 1^c, 1^d)` as one string. -/
def inst8 (x : List Bool) (s t ℓ a b c d : ℕ) : List Bool :=
  tupleEnc [x, unary s, unary t, unary ℓ, unary a, unary b, unary c, unary d]

/-- **`Mild-Gap_ρ-MINℓ-pKT^O`** (Def. 3.6, arXiv:2610.19162, version of October 30, 2026, p.22):
"`YES = { (x, 1^s, 1^t, 1^ℓ, 1^a, 1^b, 1^c, 1^d) | ℓ-pK^{t,O}_{b/a,d/c}(x) ≤ s }`,
`NO = { (x, 1^s, 1^t, 1^ℓ, 1^a, 1^b, 1^c, 1^d) | ℓ-pK^{t+ρ(|x|+ℓ+a+b+c+d),O}_{(b−1)/a,(d−1)/c}(x) ≥
s + log ρ(t + ℓ + a + b + c + d) }`."

**Formalization Note.** An instance is in YES or NO only if `2 ≤ b < a` and `2 ≤ d < c`, so that all
four parameters `b/a, (b−1)/a, d/c, (d−1)/c` lie in `(0, 1)`, the domain of Def. 3.5. `log` is
`Real.logb 2`; comparisons in `EReal`; instances encoded by `tupleEnc`. -/
def MildGapMINlpKT (O : Set (List Bool)) (ρ : ℕ → ℕ) : PromiseProblem where
  yes := {z | ∃ (x : List Bool) (s t ℓ a b c d : ℕ), z = inst8 x s t ℓ a b c d ∧
    2 ≤ b ∧ b < a ∧ 2 ≤ d ∧ d < c ∧
    lpK O t ℓ ((b : ℝ) / a) ((d : ℝ) / c) x ≤ (((s : ℝ)) : EReal)}
  no := {z | ∃ (x : List Bool) (s t ℓ a b c d : ℕ), z = inst8 x s t ℓ a b c d ∧
    2 ≤ b ∧ b < a ∧ 2 ≤ d ∧ d < c ∧
    ((((s : ℝ) + Real.logb 2 (ρ (t + ℓ + a + b + c + d)) : ℝ)) : EReal) ≤
      lpK O (t + ρ (x.length + ℓ + a + b + c + d)) ℓ (((b : ℝ) - 1) / a) (((d : ℝ) - 1) / c) x}

/-- **`Mild-Gap-MINℓ-pKT^O ∈ prBPP`** (Def. 3.6, p.22): "there is a constant `g > 0` such that
`Mild-Gapρ-MINℓ-pKT^O ∈ prBPP` with `ρ(n) = n^g`" (`g` an integer `≥ 1`). -/
def MildGapLInPrBPP (O : Set (List Bool)) : Prop :=
  ∃ g : ℕ, 1 ≤ g ∧ InPrBPP (MildGapMINlpKT O (fun n => n ^ g))

end AvgWorstGap


