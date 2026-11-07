-- Prove2me | Definitions.Def_AvgValueAlloc_bandCount
-- name    : AvgValueAlloc_bandCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:39:41.925281+00:00
-- url     : https://prove2.me/theorems/9cd33ddb-c5c3-4936-82cc-57eae62ed0bc
-- title:
--   Band counts $k_\ell$
-- statement:
--   For funding items $M$, $k_\ell$ is the number of items with an in-band positive alternative: some $j$ with $2^\ell\le\rho_j<2^{\ell+1}$ and $v_j\ge\rho_j$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §3.1, p.7

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_groupSum

namespace AvgValueAlloc

/-- **`k_ℓ`: the number of funding items with an in-band positive alternative.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §3.1, p.7: "If k_ℓ items of M have an in-band
positive alternative".

`bandCount ρ M ℓ = |{t : ∃ j ∈ I_ℓ, v_{tj} ≥ ρ_j}|`, with `I_ℓ` the dyadic band `ℓ`. -/
def bandCount {n m : ℕ} (ρ : Fin n → ℚ) (M : Fin m → Vec n) (ℓ : ℤ) : ℕ :=
  (Finset.univ.filter fun t => ∃ j, dyBand ρ j = ℓ ∧ ρ j ≤ (M t j : ℚ)).card

end AvgValueAlloc


