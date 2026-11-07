-- Prove2me | Definitions.Def_AvgValueAlloc_groupSum
-- name    : AvgValueAlloc_groupSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:20.853099+00:00
-- url     : https://prove2.me/theorems/13e483d3-29f7-4359-98af-dfe25692eb8e
-- title:
--   Group sums $G_A$ and $G^s_A$
-- statement:
--   For dyadic bands $I_\ell=\{j:2^\ell\le\rho_j<2^{\ell+1}\}$ ($\ell\in\mathbb Z$) and the shifted width-four partition $J_{\ell,s}=\{j:2^{2\ell+s}\le\rho_j<2^{2\ell+s+2}\}$ ($s\in\{0,1\}$),
--   $$
--   G_A(B)=\sum_\ell F^{I_\ell}_A(B),\qquad G^s_A(B)=\sum_\ell F^{J_{\ell,s}}_A(B).
--   $$
--   These sums relax inter-band competition in the analysis; actual items are never copied.
--
--   **Formalization Note** Bands are indexed by $\ell\in\mathbb Z$ via $\lfloor\log_2\rho_j\rfloor$, and the sums run over occupied groups only.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.1, p.4; §2.2, p.5

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_edgeLP

namespace AvgValueAlloc

/-- The dyadic band `ℓ` of a threshold: `2^ℓ ≤ ρ_j < 2^{ℓ+1}`. -/
def dyBand {n : ℕ} (ρ : Fin n → ℚ) (j : Fin n) : ℤ := Int.log 2 (ρ j)

/-- The shifted width-four group `ℓ` of a threshold: `2^{2ℓ+s} ≤ ρ_j < 2^{2ℓ+s+2}`. -/
def shBand {n : ℕ} (ρ : Fin n → ℚ) (s : ℕ) (j : Fin n) : ℤ := (Int.log 2 (ρ j) - s) / 2

/-- **Sum of group LPs over the occupied groups of a partition of the buyers.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.1, p.4: "For I_ℓ = {j : 2^ℓ ≤ ρ_j < 2^{ℓ+1}}
and c_ℓ = 2^{ℓ+1}, put G_A = Σ_ℓ F^{I_ℓ}_A"; §2.2, p.5: "the shifted width-four partition
J_{ℓ,s} = {j : 2^{2ℓ+s} ≤ ρ_j < 2^{2ℓ+s+2}} for a fixed s ∈ {0, 1}. Write G^s_A = Σ_ℓ F^{J_{ℓ,s}}_A."

`groupSum ρ grp A B = Σ_g F^{J_g}_A(B)` over the occupied groups `J_g = {j : grp j = g}`;
`Gdy ρ A B = G_A(B)` (dyadic bands), `Gsh ρ s A B = G^s_A(B)` (shifted width-four groups).

**Formalization Note.** Bands are indexed by `ℓ ∈ ℤ` (`Int.log 2`, thresholds may be below `1`);
the sum runs over the finitely many occupied groups, and empty groups contribute `0` in any case. -/
noncomputable def groupSum {n : ℕ} {ι : Type} [Fintype ι] (ρ : Fin n → ℚ) (grp : Fin n → ℤ)
    (A : ι → Vec n) (B : Fin n → ℝ) : ℝ :=
  ∑ g ∈ Finset.univ.image grp, Flp ρ (Finset.univ.filter fun j => grp j = g) A B

/-- `G_A(B) = Σ_ℓ F^{I_ℓ}_A(B)`. -/
noncomputable def Gdy {n : ℕ} {ι : Type} [Fintype ι] (ρ : Fin n → ℚ) (A : ι → Vec n)
    (B : Fin n → ℝ) : ℝ :=
  groupSum ρ (dyBand ρ) A B

/-- `G^s_A(B) = Σ_ℓ F^{J_{ℓ,s}}_A(B)`. -/
noncomputable def Gsh {n : ℕ} {ι : Type} [Fintype ι] (ρ : Fin n → ℚ) (s : ℕ) (A : ι → Vec n)
    (B : Fin n → ℝ) : ℝ :=
  groupSum ρ (shBand ρ s) A B

end AvgValueAlloc


