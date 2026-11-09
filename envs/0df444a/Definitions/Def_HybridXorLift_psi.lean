-- Prove2me | Definitions.Def_HybridXorLift_psi
-- name    : HybridXorLift_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:44.411684+00:00
-- url     : https://prove2.me/theorems/27e3835d-e047-4c34-aa13-c03b07ce8b76
-- title:
--   Potential $\Psi_{I,\zeta}(h)$
-- statement:
--   Fix a nonempty set $I \subseteq [n]$ and an assignment $\zeta \in \{0,1\}^{\bar I}$, and let $X_{I,\zeta} = \{x : \sigma(x)_{\bar I} = \zeta\}$, $M_{I,\zeta} = |X_{I,\zeta}|$. For a history $h$ put $u_h = M_{I,\zeta}^{-1/2}(c_h(x))_{x \in X_{I,\zeta}}$; the **potential** is
--   $$
--   \Psi_{I,\zeta}(h) = u_h^* \,\Gamma_{I,\zeta}\, u_h = \frac{1}{M_{I,\zeta}} \sum_{x, x' \in X_{I,\zeta}} \overline{c_h(x)}\; \Gamma_{I,\zeta}(x, x')\; c_h(x').
--   $$
--   It measures how strongly the transcript amplitudes correlate with the parity of the blocks in $I$.
--
--   **Formalization Note** $\zeta$ is given as a full string of which only the coordinates outside $I$ are read. The quadratic form of the real symmetric kernel is real; the definition takes the real part of the complex sum, which changes nothing.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.2, Eq. (3.6), p.12 (PDF p.14)

import Definitions.Def_HybridXorLift_ParallelHybridAlg_ampl
import Definitions.Def_HybridXorLift_gammaKernel
import Definitions.Def_HybridXorLift_outer

namespace HybridXorLift

/-- The potential `Ψ_{I,ζ}(h) = u_h^* Γ_{I,ζ} u_h` with `u_h = M_{I,ζ}^{−1/2} (c_h(x))_{x ∈ X_{I,ζ}}`
(Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §3.2, Eq. (3.6), p.12 (PDF p.14)), where `X_{I,ζ} = {x : σ(x)_Ī = ζ}` and
`M_{I,ζ} = |X_{I,ζ}|`; that is,
`Ψ_{I,ζ}(h) = M_{I,ζ}^{−1} Σ_{x, x′ ∈ X_{I,ζ}} conj(c_h(x)) Γ_{I,ζ}(x, x′) c_h(x′)`.

**Formalization Note** `ζ ∈ {0,1}^Ī` is a full function of which only the values outside `I` are
read. The quadratic form of the real symmetric kernel `Γ_{I,ζ}` is real; the definition takes
the real part of the complex sum, which loses nothing. -/
noncomputable def psi {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α) (q : ℕ)
    (I : Finset (Fin n)) (ζ : Fin n → Bool) (h : List (Step (Fin n × Fin r))) : ℝ :=
  ((((Finset.univ.filter fun x : Fin n × Fin r → Bool => ∀ i ∉ I, outer x i = ζ i).card : ℂ))⁻¹ *
    ∑ x ∈ Finset.univ.filter (fun x : Fin n × Fin r → Bool => ∀ i ∉ I, outer x i = ζ i),
      ∑ x' ∈ Finset.univ.filter (fun x : Fin n × Fin r → Bool => ∀ i ∉ I, outer x i = ζ i),
        (starRingEnd ℂ) (A.ampl x h) * (gammaKernel q I x x' : ℂ) * A.ampl x' h).re

end HybridXorLift


