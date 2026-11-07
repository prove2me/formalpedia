-- Prove2me | Definitions.Def_TargetedSamplers_IsSomewhereCondenser
-- name    : TargetedSamplers_IsSomewhereCondenser
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:07:44.120092+00:00
-- url     : https://prove2.me/theorems/7b737136-3ccb-4f86-b11f-5e0def97d802
-- title:
--   Somewhere-condensers (Definition 4.7)
-- statement:
--   A function $f:\{0,1\}^n\to(\{0,1\}^m)^\ell$ is a **$[\rho\mapsto\rho']^{1:\ell}_{\sim\gamma}$-somewhere-condenser** if for every $(n,\rho n)$-source $X$, $f(X)$ is $\gamma$-close to an $(m,\rho' m)^{1:\ell}$-source. The $\ell$ output coordinates are indexed by a finite type.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 4.7, p.21 (pdf p.23)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSomewhereSource

namespace TargetedSamplers

/-- `f : {0,1}ⁿ → ({0,1}^m)^ℓ` is a `[ρ ↦ ρ′]^{1:ℓ}_{∼γ}`-somewhere-condenser (Chen, Doron, Ebtehaj,
Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, Definition 4.7, p.21):
for every `(n, ρn)`-source `X`, `f(X)` is `γ`-close to an `(m, ρ′m)^{1:ℓ}`-source. The `ℓ` output
coordinates are indexed by the finite type `ι`. -/
def IsSomewhereCondenser {ι : Type} [Fintype ι] [DecidableEq ι] {n m : ℕ} (ρ ρ' γ : ℝ)
    (f : (Fin n → Bool) → ι → Fin m → Bool) : Prop :=
  ∀ X : PMF (Fin n → Bool), IsSource n (ρ * n) X →
    ∃ Z : PMF (ι → Fin m → Bool), IsSomewhereSource ι m (ρ' * m) Z ∧ IsClose γ (X.map f) Z

end TargetedSamplers


