-- Prove2me | Definitions.Def_ArgmaxDeFinetti_Supplement_IsDisentangler
-- name    : ArgmaxDeFinetti_Supplement_IsDisentangler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:41:33.546045+00:00
-- url     : https://prove2.me/theorems/bb884fee-b6ee-4c67-9b5b-3a1ebbb9e94f
-- title:
--   $(\varepsilon,\delta)$-disentanglers
-- statement:
--   A **channel** $\Lambda:D(\mathbb C^D)\to D(\mathbb C^d\otimes\mathbb C^d)$ (a linear, completely positive, trace-preserving map) is an **$(\varepsilon,\delta)$-disentangler** if
--
--   $$
--   \sup_{\rho\in D(\mathbb C^D)}D_{\mathrm{tr}}\big(\Lambda(\rho),\mathrm{SEP}(d,d)\big)\le\varepsilon
--   \qquad\text{and}\qquad
--   \sup_{\sigma\in\mathrm{SEP}(d,d)}\ \inf_{\rho\in D(\mathbb C^D)}D_{\mathrm{tr}}\big(\Lambda(\rho),\sigma\big)\le\delta .
--   $$
--
--   The first condition is soundness (every output is close to separable), the second coverage (every separable state is close to some output). Here $D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$.
--
--   Small, efficiently implementable disentanglers would let one ordinary quantum witness simulate two unentangled ones.
--
--   **Formalization Note** The input space is $\mathbb C^a$ for a finite index type $a$. The channel notion is the published completely-positive trace-preserving map. Coverage is written as: for every separable $\sigma$ and every $\eta>0$ some input state $\rho$ has $D_{\mathrm{tr}}(\Lambda(\rho),\sigma)\le\delta+\eta$, which is the infimum condition; no default value of an empty infimum can make it hold.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §5.1, eqs. (5.1)–(5.2), pp.36–37

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ArgmaxDeFinetti_hausdorff
import Definitions.Def_ArgmaxDeFinetti_Supplement_bext

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- An **`(ε, δ)`-disentangler**: a channel `Λ : D(ℂ^a) → D(ℂ^d ⊗ ℂ^d)` with
`sup_{ρ ∈ D(ℂ^a)} D_tr(Λ(ρ), SEP(d, d)) ≤ ε` (soundness, (5.1)) and
`sup_{σ ∈ SEP(d, d)} inf_{ρ ∈ D(ℂ^a)} D_tr(Λ(ρ), σ) ≤ δ` (coverage, (5.2)), Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §5.1, eqs. (5.1)–(5.2),
pp.36–37.

**Formalization Note** A channel is the published `WildeQIT.EntBreaking.IsQuantumChannel`: a `ℂ`-linear map on
matrices that is completely positive and trace preserving. The input space `ℂ^D` is `ℂ^a` for a finite index type
`a` (`D = |a|`). `D_tr` is `DimFreeShadow.traceDistance` (`½∥·∥₁`, (2.1)) and `D_tr(·, SEP)` the base `distSet`
(an infimum, (2.5)). The suprema are written as bounds for every `ρ`, resp. every `σ`, which is the same
condition. The infimum in (5.2) is written without `sInf`: `inf_ρ D_tr(Λ(ρ), σ) ≤ δ` is "for every `η > 0` some input
state `ρ` has `D_tr(Λ(ρ), σ) ≤ δ + η`". (A real `sInf` would be `0` on an empty input space and make coverage free.) -/
def IsDisentangler {a : Type} [Fintype a] [DecidableEq a] {d : ℕ}
    (Λ : Matrix a a ℂ →ₗ[ℂ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (ε δ : ℝ) : Prop :=
  WildeQIT.EntBreaking.IsQuantumChannel Λ ∧
    (∀ ρ : Matrix a a ℂ, WildeQIT.IsDensityOperator ρ →
      distSet DimFreeShadow.traceDistance (Λ ρ) (sepAB d d) ≤ ε) ∧
    (∀ σ ∈ sepAB d d, ∀ η : ℝ, 0 < η →
      ∃ ρ : Matrix a a ℂ, WildeQIT.IsDensityOperator ρ ∧ DimFreeShadow.traceDistance (Λ ρ) σ ≤ δ + η)

end Supplement

end ArgmaxDeFinetti


