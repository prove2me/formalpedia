-- Prove2me | Definitions.Def_HolevoEntropyGain_arccotTrace
-- name    : HolevoEntropyGain_arccotTrace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:51.574914+00:00
-- url     : https://prove2.me/theorems/285e0ff4-5d4f-4122-b865-8810f2528ec8
-- title:
--   $\operatorname{Sp}\big[A\,\operatorname{arc\,cot}(2A)\big]$ through characteristic roots
-- statement:
--   For a complex square matrix $A$,
--
--   $$
--   \operatorname{Sp}\big[A\,\operatorname{arc\,cot}(2A)\big] = \sum_{\lambda}\lambda\,\operatorname{arc\,cot}(2\lambda),
--   $$
--
--   the sum over the roots $\lambda$ of the characteristic polynomial of $A$, counted with multiplicity. For a diagonalizable $A$ (such as $\Delta^{-1}\alpha$, with eigenvalues $\pm i\alpha_j$) this is the trace of the matrix function. It is the second term of the entropy formula (19).
--
--   **Formalization Note** The printed "Sp(Δ⁻¹α_β)arc cot(2Δ⁻¹α_β)" is read as the trace of the product, the only parse that is a number. One-mode check, canonical $\Delta$, $\alpha = N+\frac12$: the sum is $\alpha\log\frac{\alpha+1/2}{\alpha-1/2}$, and with the first term of (19) it gives $(N+1)\log(N+1)-N\log N$, the thermal entropy.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eq. (19), p.5

import Mathlib
import Definitions.Def_HolevoEntropyGain_complexArccot

namespace HolevoEntropyGain

/-- `Sp[A arc cot(2A)]`, the second term of (19), as the sum of `λ arc cot(2λ)` over the roots `λ` of
the characteristic polynomial of `A`, with multiplicity (Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eq. (19), p.5, PDF p.5).

**Formalization Note** (R6) The printed "Sp(Δ⁻¹α_β)arc cot(2Δ⁻¹α_β)" is read as the trace of the
product, the only parse that is a number. `Δ⁻¹α_β` is not normal, but it is diagonalizable with
eigenvalues `±iαⱼ`, so the sum over roots is `Sp f(A)`. One-mode check, canonical `Δ`, `α = N + ½`:
the sum is `α log((α + ½)/(α - ½))`, and with the first term of (19) it gives
`(N + 1) log(N + 1) - N log N`, the thermal entropy. -/
noncomputable def arccotTrace {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℂ :=
  (A.charpoly.roots.map fun l => l * complexArccot (2 * l)).sum

end HolevoEntropyGain


