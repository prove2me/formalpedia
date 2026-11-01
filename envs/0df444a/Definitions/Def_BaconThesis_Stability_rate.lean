-- Prove2me | Definitions.Def_BaconThesis_Stability_rate
-- name    : BaconThesis_Stability_rate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:02.027625+00:00
-- url     : https://prove2.me/theorems/564bf74c-aead-4c35-817f-5b48aa8b37ea
-- title:
--   The $p$-th order decoherence rate $(1/\tau_p)^p=\mathrm{Tr}[\Upsilon_J[\rho(0)]\,\Upsilon_J[\rho^{(p)}(0)]]$
-- statement:
--   Let $H$ be a system-environment Hamiltonian, $\rho(0)$ an initial system state, $\rho_E$ an environment state and $\rho(t)$ the reduced evolution (`evolvedState`). For a block $J$ and an order $p\ge 0$, the **$p$-th order decoherence rate** is
--   $$
--   \left(\frac1{\tau_p}\right)^{p}=\mathrm{Tr}\!\left[\Upsilon_J[\rho(0)]\;\Upsilon_J\big[\rho^{(p)}(0)\big]\right],
--   $$
--   where $\rho^{(p)}(0)=\frac{d^p\rho}{dt^p}(0)$ is the $p$-th time derivative of the evolved density matrix at $t=0$. For an encoded pure state, $\Upsilon_J[\rho(0)]=|j\rangle\langle j|$ and the rate is $\langle j|\Upsilon_J[\rho^{(p)}(0)]|j\rangle$.
--
--   These are the Taylor coefficients of the memory fidelity $\mathrm{Tr}[\Upsilon_J[\rho(0)]\Upsilon_J[\rho(t)]]$ at $t=0$ (Appendix A.6); a decoherence-free subsystem is one for which all of them vanish for $p\ge1$.
--
--   **Formalization Note** The rate is the complex number $(1/\tau_p)^p$ itself (no $p$-th root is taken). $\rho^{(p)}(0)$ is taken entrywise, `iteratedDeriv p (fun t : ℝ => ρ(t) a b) 0`; the entries of $\rho(t)$ are smooth in $t$, so this is the ordinary derivative.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §6.2, eq. (6.15), p.90 (PDF p.107); Appendix A.6, eq. (A.8), p.232 (PDF p.249)

import Mathlib
import Definitions.Def_BaconThesis_Stability_upsilon
import Definitions.Def_BaconThesis_Stability_evolvedState

namespace BaconThesis.Stability

/-- **The `p`-th order decoherence rate `(1/τ_p)^p = Tr[Υ_J[ρ(0)] Υ_J[ρ^{(p)}(0)]]`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§6.2, eq. (6.15), p.90 (PDF p.107), and Appendix A.6, eq. (A.8), p.232 (PDF p.249): "The `p`th order
decoherence rate `τ_p` for this evolution is given by `(1/τ_p)^p = Tr[Υ_J[ρ(0)] Υ_J[ρ^{(p)}(0)]]`,
where `ρ^{(p)}(0)` is the `p`th time derivative of the evolved density matrix `ρ(t)` evaluated at
`t = 0`."

For a system-environment Hamiltonian `H`, an initial system state `ρ0`, an environment state `ρE`, a
block `J` and an order `p`, `rate n d H ρ0 ρE J p` is `Tr[Υ_J[ρ0] Υ_J[ρ^{(p)}(0)]]`, where
`ρ(t) = evolvedState H ρ0 ρE t` and `ρ^{(p)}(0)` is its `p`-th time derivative at `t = 0`.

**Formalization Note.** The rate is the complex number `(1/τ_p)^p` itself (the book never takes the
`p`-th root in §6.2). `ρ^{(p)}(0)` is taken entrywise: the matrix whose `(a, b)` entry is
`iteratedDeriv p (fun t : ℝ => ρ(t) a b) 0`; every entry of `ρ(t)` is a smooth (indeed analytic)
function of the real time `t`, so this is the ordinary `p`-th derivative. `p = 0` gives
`Tr[Υ_J[ρ0] Υ_J[ρ0 Tr ρE]]`. -/
noncomputable def rate {𝒥 E : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype E] [DecidableEq E]
    (n d : 𝒥 → ℕ)
    (H : Matrix ((Σ K : 𝒥, Fin (n K) × Fin (d K)) × E) ((Σ K : 𝒥, Fin (n K) × Fin (d K)) × E) ℂ)
    (ρ0 : Matrix (Σ K : 𝒥, Fin (n K) × Fin (d K)) (Σ K : 𝒥, Fin (n K) × Fin (d K)) ℂ)
    (ρE : Matrix E E ℂ) (J : 𝒥) (p : ℕ) : ℂ :=
  Matrix.trace (upsilon n d J ρ0 *
    upsilon n d J (Matrix.of fun a b => iteratedDeriv p (fun t : ℝ => evolvedState H ρ0 ρE t a b) 0))

end BaconThesis.Stability


