-- Prove2me | Definitions.Def_TargetedSamplers_IsMerger
-- name    : TargetedSamplers_IsMerger
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:08:03.893049+00:00
-- url     : https://prove2.me/theorems/6b417746-08c0-4f42-a821-b4596d4ea6b2
-- title:
--   Mergers (Definition 4.9)
-- statement:
--   A function $M:(\{0,1\}^n)^\ell\times\{0,1\}^d\to\{0,1\}^m$ is a **$[\rho\mapsto\rho']^{\ell:1}_{\sim\gamma}$-merger** if for every $(n,\rho n)^{1:\ell}$-source $(X_1,\dots,X_\ell)$, the distribution $M(X_1,\dots,X_\ell;U_d)$ is $\gamma$-close to having min-entropy rate $\rho'$, that is, to some $(m,\rho' m)$-source.
--
--   **Formalization Note** The page writes $f(X_1,\dots,X_\ell;U_d)$ for $M(X_1,\dots,X_\ell;U_d)$.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 4.9, p.21 (pdf p.23)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSomewhereSource
import Definitions.Def_TargetedSamplers_IsCondenser

namespace TargetedSamplers

/-- `M : ({0,1}ⁿ)^ℓ × {0,1}^d → {0,1}^m` is a `[ρ ↦ ρ′]^{ℓ:1}_{∼γ}`-merger (Chen, Doron, Ebtehaj,
Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, Definition 4.9, p.21):
for every `(n, ρn)^{1:ℓ}`-source `(X_1, …, X_ℓ)`, the distribution `M(X_1, …, X_ℓ; U_d)` is `γ`-close to
having min-entropy rate `ρ′`, i.e. to some `(m, ρ′m)`-source.

**Formalization Note** The page writes `f(X_1, …, X_ℓ; U_d)` for `M(X_1, …, X_ℓ; U_d)`. The `ℓ`
coordinates are indexed by the finite type `ι`. -/
def IsMerger {ι : Type} [Fintype ι] [DecidableEq ι] {n d m : ℕ} (ρ ρ' γ : ℝ)
    (M : (ι → Fin n → Bool) → (Fin d → Bool) → Fin m → Bool) : Prop :=
  ∀ X : PMF (ι → Fin n → Bool), IsSomewhereSource ι n (ρ * n) X →
    ∃ Y : PMF (Fin m → Bool), IsSource m (ρ' * m) Y ∧ IsClose γ (seededOutput M X) Y

end TargetedSamplers


