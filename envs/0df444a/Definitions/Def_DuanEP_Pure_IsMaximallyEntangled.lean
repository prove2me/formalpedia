-- Prove2me | Definitions.Def_DuanEP_Pure_IsMaximallyEntangled
-- name    : DuanEP_Pure_IsMaximallyEntangled
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:41.885421+00:00
-- url     : https://prove2.me/theorems/9373bc97-198c-49b5-b2c9-a823428ea6ae
-- title:
--   Maximally entangled pure state of finite dimension $d$
-- statement:
--   A pure bipartite state with coefficients $\psi:I\times J\to\mathbb C$ is **maximally entangled of dimension $d$** if $d\ge 1$ and there are orthonormal vectors $u_0,\dots,u_{d-1}\in\ell^2(I)$ with
--
--   $$
--   \mathrm{Tr}_J|\psi\rangle\langle\psi|=\frac1d\sum_{k=0}^{d-1}|u_k\rangle\langle u_k| ,
--   $$
--
--   that is, its reduced density operator on the first component is $1/d$ times the projection onto a $d$-dimensional subspace. Equivalently, its Schmidt decomposition has exactly $d$ equal coefficients $1/\sqrt d$; its entanglement is then $\log d$.
--
--   **Formalization Note** The definition is basis-free (the $u_k$ are arbitrary); $\ell^2(I)$ is the platform's `QAlgorithms.RealRegisters.Hilbert` and $|u\rangle\langle u|$ the platform's `rankOne`. The requirement $d\ge 1$ excludes the vacuous zero marginal.
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 2 ("two-party maximally entangled state", "maximally entangled state in some finite Hilbert space")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_DuanEP_Pure_pureKernel

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P01

namespace DuanEP.Pure

/-- The pure bipartite state with coefficients `ψ : I × J → ℂ` is maximally entangled in a Hilbert
space of finite dimension `d` (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, p. 2: "a two-party maximally entangled state", "a useful
maximally entangled state in some finite Hilbert space"): `d ≥ 1` and its `I`-marginal
`Tr_J |ψ⟩⟨ψ|` equals `(1/d) ∑_{k<d} |u_k⟩⟨u_k|` for some orthonormal family `u_0,…,u_{d−1}` in
`ℓ²(I)`, i.e. `1/d` times the projection onto a `d`-dimensional subspace.

**Formalization Note** The definition is basis-free: the `u_k` are arbitrary orthonormal vectors
of the platform's `QAlgorithms.RealRegisters.Hilbert I = ℓ²(I)`, and `|u⟩⟨u|` is the platform's
`rankOne`. The condition `0 < d` excludes the vacuous `d = 0` (zero marginal). -/
def IsMaximallyEntangled {I J : Type} (ψ : I × J → ℂ) (d : ℕ) : Prop :=
  0 < d ∧ ∃ u : Fin d → Hilbert I, Orthonormal ℂ u ∧
    traceSecond (pureKernel ψ) = fun a a' => (d : ℂ)⁻¹ * ∑ k, rankOne (u k) a a'

end DuanEP.Pure


