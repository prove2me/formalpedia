-- Prove2me | Definitions.Def_BetheKS_centeredOverlap
-- name    : BetheKS_centeredOverlap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:12.24179+00:00
-- url     : https://prove2.me/theorems/445d3ae8-e9d6-456c-9b2f-7ef3fdea1ae5
-- title:
--   Centered overlap $\mathrm{ov}(\sigma,\widehat\sigma)$
-- statement:
--   For labelings $\sigma,\widehat\sigma:[n]\to[r]$ and community proportions $\pi$, the **centered overlap** is
--   $$
--   \operatorname{ov}(\sigma,\widehat\sigma):=\max_{\tau\in S_r}\frac1n\sum_{u=1}^n\Big[\mathbf 1\{\sigma(u)=\tau(\widehat\sigma(u))\}-\pi_{\tau(\widehat\sigma(u))}\Big].
--   $$
--   For a fixed $\tau$ the subtracted term is the agreement expected from independent labels with proportions $\pi$. An algorithm achieves weak recovery if its centered overlap is bounded below by a positive constant with probability tending to one.
--
--   **Formalization Note** The maximum is over `Equiv.Perm (Fin r)`. At $n=0$ the value is $0$.
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), §2.3, p.5

import Mathlib

set_option autoImplicit false

namespace BetheKS

/-- **Centered overlap** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), §2.3,
p.5: for labelings `σ, σ̂ : [n] → [r]` and community proportions `π`,
`ov(σ, σ̂) := max_{τ ∈ S_r} (1/n) ∑_{u=1}^n [1{σ(u) = τ(σ̂(u))} − π_{τ(σ̂(u))}]`.

**Formalization Note.** `S_r` is `Equiv.Perm (Fin r)`; the maximum is a finite `sup'`. At `n = 0`
the factor `1/n` is `0`, so `ov = 0`. -/
noncomputable def ov {r n : ℕ} (π : Fin r → ℝ) (σ σh : Fin n → Fin r) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun τ : Equiv.Perm (Fin r) =>
    (1 / (n : ℝ)) * ∑ u, ((if σ u = τ (σh u) then (1 : ℝ) else 0) - π (τ (σh u))))

end BetheKS


