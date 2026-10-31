-- Prove2me | Definitions.Def_NestedLogitFPTAS_RoundedPath
-- name    : NestedLogitFPTAS_RoundedPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:40.989997+00:00
-- url     : https://prove2.me/theorems/7b35f3e6-23de-43f0-947f-d31089d7fd2a
-- title:
--   §3.7, pp.16–17 — the rounded path $\omega^*_k$, $\omega^*_{>k}$, $\rho^*_k$, $\rho^*_{>k}$
-- statement:
--   For an assortment $S=(S_1,\dots,S_M)$, the analysis of §3.7 uses the rounded quantities
--   $$
--   \omega_k^*=\big\langle(1+\xi_\omega)^{M-k}\,w_+(S_k)^{\gamma_k}\big\rangle_{\mathcal D_\omega},\qquad
--   \omega_{>k}^*=\big\langle(1+\xi_\omega)^{M-k}\,\omega_{[k+1,M]}(S)\big\rangle_{\mathcal D_\omega},
--   $$
--   $$
--   \rho_k^*=\big\langle(1-\xi_\rho)^{M-k}\,\mathcal R_k(S_k)\,w_+(S_k)^{\gamma_k}\big\rangle_{\mathcal D_\rho},\qquad
--   \rho_{>k}^*=\big\langle(1-\xi_\rho)^{M-k}\,\rho_{[k+1,M]}(S)\big\rangle_{\mathcal D_\rho},
--   $$
--   with $\omega^*_{>0}=\omega^*$ and $\rho^*_{>0}=\rho^*$. They form a path that the approximate dynamic program can traverse, and it is only used in the proof.
--
--   **Formalization Note** The nest $k$ : `Fin M` is the paper's $k+1$. `omegaStarAbove` and `rhoStarAbove` take the paper's index $j$, $0\le j\le M$.
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), §3.7, pp.16–17; Appendix A.2

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Grids

namespace NestedLogitFPTAS

namespace Instance

variable {n M : ℕ} (I : Instance n M)

/-- `ω*>ⱼ = ⟨(1+ξω)^{M-j}·ω[j+1,M](S)⟩_{Dω}`, §3.7, p.17, with the paper's index `0 ≤ j ≤ M`.

At `j = 0` this is `ω* = ⟨(1+ξω)^M·ω[1,M](S)⟩_{Dω}` of p.16, as Appendix A.2 sets `ω*>0 = ω*`; at
`j = M` the suffix is empty. -/
noncomputable def omegaStarAbove (ε : ℝ) (S : Finset (Fin n)) (j : ℕ) : ℝ :=
  roundDown (I.Domega ε) ((1 + I.xiOmega ε) ^ (M - j) * I.omegaRange (j + 1) M S)

/-- `ρ*>ⱼ = ⟨(1-ξρ)^{M-j}·ρ[j+1,M](S)⟩_{Dρ}`, §3.7, p.17, with the paper's index `0 ≤ j ≤ M`; at
`j = 0` this is `ρ*` of p.16. -/
noncomputable def rhoStarAbove (ε : ℝ) (S : Finset (Fin n)) (j : ℕ) : ℝ :=
  roundDown (I.Drho ε) ((1 - I.xiRho ε) ^ (M - j) * I.rhoRange (j + 1) M S)

/-- `ω*ₖ = ⟨(1+ξω)^{M-k}·w₊(Sₖ)^{γₖ}⟩_{Dω}`, §3.7, p.17. The nest `k : Fin M` is the paper's
`k + 1`, so the exponent is `M - (k + 1)`. -/
noncomputable def omegaStar (ε : ℝ) (S : Finset (Fin n)) (k : Fin M) : ℝ :=
  roundDown (I.Domega ε)
    ((1 + I.xiOmega ε) ^ (M - (k.val + 1)) * I.wplus k (I.part S k) ^ I.γ k)

/-- `ρ*ₖ = ⟨(1-ξρ)^{M-k}·Rₖ(Sₖ)·w₊(Sₖ)^{γₖ}⟩_{Dρ}`, §3.7, p.17, with the paper's `k + 1` for the
nest `k : Fin M`. -/
noncomputable def rhoStar (ε : ℝ) (S : Finset (Fin n)) (k : Fin M) : ℝ :=
  roundDown (I.Drho ε)
    ((1 - I.xiRho ε) ^ (M - (k.val + 1)) *
      (I.Rnest k (I.part S k) * I.wplus k (I.part S k) ^ I.γ k))

end Instance

end NestedLogitFPTAS


