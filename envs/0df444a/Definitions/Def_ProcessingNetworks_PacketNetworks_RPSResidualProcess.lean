-- Prove2me | Definitions.Def_ProcessingNetworks_PacketNetworks_RPSResidualProcess
-- name    : ProcessingNetworks_PacketNetworks_RPSResidualProcess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:00:49.972747+00:00
-- url     : https://prove2.me/theorems/0709d70d-5cc2-45c9-b0b6-867b6c494670
-- title:
--   The class-level residual process ξ and the event Ω2 (Section 12.7, before Lemma 12.23)
-- statement:
--   The **class-level residual process**, Section 12.7 (just before Lemma 12.23): for each class
--   $i$, $\xi_i^z(\tau,\omega) := \sum_{m=1}^\tau (s_i^z(m,\omega) - \hat s_i^z(m,\omega))$, where
--   $s_i^z(\tau,\omega)$ is the actual number of class-$i$ transfers in period $\tau$ (network
--   started at $z$, schedule $s(\tau) = f(Z(\tau-1),U(\tau))$) and $\hat s_i^z(\tau) :=
--   E[s_i^z(\tau)\mid Z^z(\tau-1)] = \int_0^1 f(Z^z(\tau-1),u)_i\,du$ (`shat`).
--   **$\Omega_2$** (Lemma 12.23) is the set of $\omega$ on which
--   $\xi^{z_\ell}(|z_\ell|,\omega)/|z_\ell| \to 0$ as $\ell\to\infty$, for a given sequence
--   $\{z_\ell\}$.
--
--   **Formalization note.** Both $s^z$ and $\hat s^z$ are built from the primitives (the policy,
--   the arrivals, the randomization variables) through mission XII's `policySched`/`policyState`,
--   so $\xi^z$ is the residual of the actual RPS network, not of a pair of arbitrary processes.
--   The conditional expectation given $Z(\tau-1)$ is the integral over the randomization variable
--   because $U(\tau)$ is uniform and independent of the past. The sequence index is 0-based
--   (`zseq 0` playing the book's $z_1$).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 251 (PDF p. 267), Section 12.7, Eqs. (12.63),(12.64)

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSRawModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory Filter

/-- `ŝ^z_i(τ) = E[s^z_i(τ) | Z^z(τ−1)]` (Section 12.7, before (12.62)): since `s(τ) = f(Z(τ−1),
U(τ))` with `U(τ)` uniform on `(0,1)` and independent of `Z(τ−1)`, this is
`∫₀¹ f(Z^z(τ−1), u)_i du`. -/
noncomputable def shat {I K : ℕ} {Ω : Type*} (fr : FixedRoutingData I K)
    (P : PacketPrimitives I I Ω) (z : Fin I → ℕ) (i : Fin I) (τ : ℕ) (ω : Ω) : ℝ :=
  ∫ uu in Set.Ioo (0 : ℝ) 1,
    (P.f (fun i' => (policyState fr.dat P z (τ - 1) ω i').toNat) uu i : ℝ)

/-- The class-level residual process `ξ^z_i(τ,ω) := ∑_{m=1}^{τ} (s^z_i(m,ω) − ŝ^z_i(m,ω))`,
Dai & Harrison p. 250 (PDF p. 266), for the network started at `z` under the policy of `P`. -/
noncomputable def xi {I K : ℕ} {Ω : Type*} (fr : FixedRoutingData I K)
    (P : PacketPrimitives I I Ω) (z : Fin I → ℕ) (i : Fin I) (τ : ℕ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.Icc 1 τ, ((policySched fr.dat P z m ω i : ℝ) - shat fr P z i m ω)

/-- `Ω₂` (Lemma 12.23): for the sequence `zseq` of initial states, the set of sample paths on
which `ξ^{zₗ}(|zₗ|,ω)/|zₗ| → 0` as `ℓ → ∞` (componentwise). The index `ℓ` is 0-based (`zseq 0`
playing the book's `z₁`). -/
def omega2 {I K : ℕ} {Ω : Type*} (fr : FixedRoutingData I K) (P : PacketPrimitives I I Ω)
    (zseq : ℕ → Fin I → ℕ) : Set Ω :=
  {ω | ∀ i : Fin I,
    Tendsto (fun ℓ => xi fr P (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω / sizeN (zseq ℓ)) atTop (nhds 0)}

end ProcessingNetworks.PacketNetworks


