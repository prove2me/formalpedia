-- Prove2me | Definitions.Def_TargetedSamplers_IsCondenser
-- name    : TargetedSamplers_IsCondenser
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:06:01.22306+00:00
-- url     : https://prove2.me/theorems/f7f963de-9442-41d0-abe4-5c053ccfdbb2
-- title:
--   Condensers (Definition 4.5)
-- statement:
--   For a function $f:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ and a distribution $X$, $f(X;U_d)$ is the distribution of $f(x;s)$ with $x\sim X$ and an independent uniform seed $s\in\{0,1\}^d$. $f$ is a **$[\rho\mapsto\rho']_{\sim\gamma}$-condenser** if for every $(n,\rho n)$-source $X$, $f(X;U_d)$ is $\gamma$-close to some $(m,\rho' m)$-source.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 4.5, p.21 (pdf p.23)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSource

namespace TargetedSamplers

/-- The distribution of `f(X; U_d)`: draw `x ∼ X` and an independent uniform seed `s ∈ {0,1}^d`, output
`f(x; s)`. -/
noncomputable def seededOutput {α β : Type*} {d : ℕ} (f : α → (Fin d → Bool) → β) (X : PMF α) :
    PMF β :=
  X.bind fun x => (PMF.uniformOfFintype (Fin d → Bool)).map (f x)

/-- `f : {0,1}ⁿ × {0,1}^d → {0,1}^m` is a `[ρ ↦ ρ′]_{∼γ}`-condenser (Chen, Doron, Ebtehaj, Tell,
Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, Definition 4.5, p.21): for every
`(n, ρn)`-source `X`, the distribution of `f(X; U_d)` is `γ`-close to some `(m, ρ′m)`-source. -/
def IsCondenser {n d m : ℕ} (ρ ρ' γ : ℝ) (f : (Fin n → Bool) → (Fin d → Bool) → (Fin m → Bool)) :
    Prop :=
  ∀ X : PMF (Fin n → Bool), IsSource n (ρ * n) X →
    ∃ Y : PMF (Fin m → Bool), IsSource m (ρ' * m) Y ∧ IsClose γ (seededOutput f X) Y

end TargetedSamplers


