-- Prove2me | Definitions.Def_AvgWorstGap_lpK
-- name    : AvgWorstGap_lpK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:50:22.364736+00:00
-- url     : https://prove2.me/theorems/732a461a-3453-4af4-86cb-02f6ab65f87a
-- title:
--   $\ell$-$pK^{t,O}_{\lambda,\gamma}(x)$
-- statement:
--   For $t,\ell\in\mathbb N$, $\lambda,\gamma\in(0,1)$, an oracle $O$ and a string $x$,
--   $$\ell\text{-}\mathrm{pK}^{t,O}_{\lambda,\gamma}(x)=\min\Big\{s\in\mathbb Z : \Pr_{\hat r\sim U_\ell}\big[\mathrm{pK}^{t,O}_\lambda(x\circ\hat r)\le s+\ell\big]\ge\gamma\Big\}.$$
--   This measure is the intermediate notion through which the proof of Lemma 3.4 passes, via Lemmas 3.7 and 3.8.
--
--   **Formalization Note** The value is the infimum of the qualifying integers in the extended reals: $+\infty$ if none qualifies, and $-\infty$ if all do, which cannot happen for $\gamma>0$. The function is defined for all real $\lambda,\gamma$. The domain $(0,1)$ is enforced in the instance guard of Mild-Gap-MIN$\ell$-pKT.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Definition 3.5, p.22

import Mathlib
import Definitions.Def_AvgWorstGap_pK

namespace AvgWorstGap

open NKtLB

/-- **`ℓ-pK^{t,O}_{λ,γ}(x)`** (Def. 3.5, arXiv:2610.19162, version of October 30, 2026, p.22):
"For `t, ℓ ∈ ℕ`, `λ, γ ∈ (0, 1)`, an oracle `O`, and a string `x ∈ {0, 1}∗`, we define
`ℓ-pK^{t,O}_{λ,γ}(x) ≜ min { s ∈ ℤ | Pr_{r̂∼Uℓ} [ pK^{t,O}_λ(x ◦ r̂) ≤ s + ℓ ] ≥ γ }`."

**Formalization Note.** The value is the infimum in `EReal` of the integers `s` that qualify: it is
the minimum when that set is nonempty and bounded below, `⊤` when it is empty and `⊥` when it is
all of `ℤ` (which cannot happen for `γ > 0`). Defined for every real `λ, γ`; the domain
`λ, γ ∈ (0,1)` is enforced in `MildGapMINlpKT`. -/
noncomputable def lpK (O : Set (List Bool)) (t ℓ : ℕ) (lam γ : ℝ) (x : List Bool) : EReal :=
  sInf {e : EReal | ∃ s : ℤ, e = ((s : ℝ) : EReal) ∧
    γ ≤ prob ℓ (fun rh => toEReal (pK O t lam (x ++ rh) []) ≤ (((s + ℓ : ℤ) : ℝ) : EReal))}

end AvgWorstGap


