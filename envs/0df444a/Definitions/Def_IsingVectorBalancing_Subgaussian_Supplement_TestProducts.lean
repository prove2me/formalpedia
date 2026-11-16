-- Prove2me | Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_TestProducts
-- name    : IsingVectorBalancing_Subgaussian_Supplement_TestProducts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:18:09.024103+00:00
-- url     : https://prove2.me/theorems/7fd45ab1-ab02-40f8-8551-564cc9c28bb1
-- title:
--   Spin-system test products and complete interpolation grid
-- statement:
--   For Euclidean vectors $w_i^a$ and a vector $u$, and for a real array $z$, define
--
--   $$\Phi_u^w(\sigma)=\prod_i(1-\langle u,w_i^{\sigma_i}\rangle),\qquad \Psi_z(\sigma)=\prod_i(1-z_{i,\sigma_i}).$$
--
--   The complete interpolation grid $\{0,\pm\delta\}^{nq}$ is indexed by all maps $[n]\times[q]\to\{0,1,2\}$, decoded respectively as $0,\delta,-\delta$. For $\delta>0$ this is a bijection, so every grid point occurs once. No coefficient sign restriction or size restriction is imposed. These are the test functions appearing in both Section 8 supporting lemmas.
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), pp. 18–19 (PDF 19–20), (25), (27)–(28)

import Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_Decomposition

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

/-- Section 8, preceding (25). -/
noncomputable def phi {n q d : ℕ} (w : Fin n → Fin q → Vec d)
    (u : Vec d) (σ : ColorConfiguration n q) : ℝ :=
  ∏ i, (1 - inner ℝ u (w i (σ i)))

/-- Section 8, preceding (27). -/
noncomputable def psi {n q : ℕ} (z : Fin n → Fin q → ℝ)
    (σ : ColorConfiguration n q) : ℝ := ∏ i, (1 - z i (σ i))

/-- A finite index for the complete grid {0,±δ}^{nq}; δ>0 makes it bijective. -/
abbrev GridIndex (n q : ℕ) := Fin n → Fin q → Fin 3

def gridPoint {n q : ℕ} (δ : ℝ) (z : GridIndex n q) (i : Fin n) (a : Fin q) : ℝ :=
  if z i a = 0 then 0 else if z i a = 1 then δ else -δ

end IsingVectorBalancing.Subgaussian.Supplement


