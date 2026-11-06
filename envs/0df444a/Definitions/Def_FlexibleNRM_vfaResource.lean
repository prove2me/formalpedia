-- Prove2me | Definitions.Def_FlexibleNRM_vfaResource
-- name    : FlexibleNRM_vfaResource
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:24:50.79925+00:00
-- url     : https://prove2.me/theorems/f5713691-e172-4dee-9b3d-ee6cf59adf85
-- title:
--   The auxiliary approximation $\hat\Psi_t(w)$ and $\psi_p(w)$
-- statement:
--   For a vector $w$ of remaining capacities, let
--   $$\psi_p(w)=\min_{i\in A_p}\frac{w_i}{c_i},\qquad \hat\Psi_t(w)=\sum_{j\in\mathcal J}\sum_{p\in\mathcal R_j}\hat\gamma_{jpt}\,\psi_p(w),$$
--   where the $\hat\gamma_{jpt}$ are adjustable parameters. At full capacities $\psi_p(c)=1$, and $\psi_p(w)=0$ when some resource of route $p$ is exhausted.
--
--   **Formalization Note** $w$ is an integer vector, because Lemma 5.2 evaluates $\psi_p$ at vectors with a component equal to $-1$.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, §3, p.9

import Mathlib
import Definitions.Def_FlexibleNRM_Network

namespace FlexibleNRM

/-- `ψ_p(w) = min_{i ∈ A_p} w_i / c_i`.

Zhu, Topaloglu, manuscript of November 16, 2022, §3, p.9.

**Formalization Note** `w` is an integer vector, because Lemma 5.2 evaluates `ψ_p` at
`w − ∑_{i ∈ A_p} e_i` for `w ∈ Z₊`, where a component can be `−1`. Truncated subtraction in `ℕ`
would change that statement. -/
noncomputable def psi {n m r : ℕ} (N : Network n m r) (p : Fin r) (w : Fin m → ℤ) : ℝ :=
  (N.A p).inf' (N.A_nonempty p) fun i => (w i : ℝ) / (N.c i : ℝ)

/-- The auxiliary approximation `Ψ̂_t(w) = ∑_j ∑_{p ∈ R_j} γ̂_jpt ψ_p(w)`.

Zhu, Topaloglu, manuscript of November 16, 2022, §3, p.9.

**Formalization Note** `γ j p t` is `γ̂_jpt`. Only its values at `p ∈ R j` are read. -/
noncomputable def vfaResource {n m r : ℕ} (N : Network n m r) (γ : Fin n → Fin r → ℕ → ℝ) (t : ℕ)
    (w : Fin m → ℤ) : ℝ :=
  ∑ j, ∑ p ∈ N.R j, γ j p t * psi N p w

end FlexibleNRM


