-- Prove2me | Definitions.Def_TierneyMH_Shared_IsSymmetricSplit
-- name    : TierneyMH_Shared_IsSymmetricSplit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T11:29:26.074145+00:00
-- url     : https://prove2.me/theorems/644144c0-9644-4cb2-bcfa-c0608530d3d6
-- title:
--   Symmetric set $R$ on which $\mu$ and $\mu^T$ are equivalent and off which they are singular
-- statement:
--   Let $\mu$ be a measure on the product space $(E\times E,\mathcal E\otimes\mathcal E)$ and let $\mu^T(dx,dy)=\mu(dy,dx)$ be its transpose, the image of $\mu$ under the swap $(x,y)\mapsto(y,x)$. A set $R\subseteq E\times E$ is a **symmetric split** for $\mu$ if
--
--   1. $R\in\mathcal E\otimes\mathcal E$;
--   2. $R$ is symmetric: $(x,y)\in R$ if and only if $(y,x)\in R$;
--   3. $\mu$ and $\mu^T$ are mutually absolutely continuous on $R$: $\mu_R\ll\mu^T_R$ and $\mu^T_R\ll\mu_R$, where $\mu_R,\mu^T_R$ are the restrictions to $R$;
--   4. $\mu$ and $\mu^T$ are mutually singular on the complement $R^c$:
--
--   $$\mu|_{R^c}\;\perp\;\mu^T|_{R^c}.$$
--
--   Proposition 1 shows that such a set exists for every $\sigma$-finite $\mu$ and is unique up to sets null for both $\mu$ and $\mu^T$. For $\mu(dx,dy)=\pi(dx)Q(x,dy)$ it is the set of state pairs between which transitions are possible in both directions.
--
--   It is shared by two missions of this series and reviewed once for both: `01-reversibility` (Proposition 1, p. 2, and the set $R$ of Theorem 2, p. 3) and `03-mixture-proposals` (Proposition 1, p. 2, for the canonical split used to define $\alpha_{MH}$, p. 3).
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 2, Proposition 1 (the set R)

import Mathlib

open MeasureTheory

namespace TierneyMH.Shared

/-- `IsSymmetricSplit μ R` (Tierney 1998, Proposition 1, p. 2): for a measure `μ` on `E × E`
with transpose `μᵀ = μ.map Prod.swap` (`μᵀ(dx, dy) = μ(dy, dx)`), the set `R` is

* measurable in the product σ-algebra `ℰ ⊗ ℰ`,
* symmetric: `(x, y) ∈ R ↔ (y, x) ∈ R`,
* such that `μ` and `μᵀ` are mutually absolutely continuous on `R`
  (`μ|_R ≪ μᵀ|_R` and `μᵀ|_R ≪ μ|_R`),
* and mutually singular on the complement `Rᶜ` (`μ|_{Rᶜ} ⟂ μᵀ|_{Rᶜ}`). -/
def IsSymmetricSplit {E : Type*} [MeasurableSpace E] (μ : Measure (E × E)) (R : Set (E × E)) :
    Prop :=
  MeasurableSet R ∧ Prod.swap ⁻¹' R = R ∧
    μ.restrict R ≪ (μ.map Prod.swap).restrict R ∧
    (μ.map Prod.swap).restrict R ≪ μ.restrict R ∧
    μ.restrict Rᶜ ⟂ₘ (μ.map Prod.swap).restrict Rᶜ

end TierneyMH.Shared


