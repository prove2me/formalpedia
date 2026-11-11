-- Prove2me | Definitions.Def_DQIShattered_Gibbs
-- name    : DQIShattered_Gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:44.166792+00:00
-- url     : https://prove2.me/theorems/644ebc42-2636-4361-a419-7ea7ddd67c6a
-- title:
--   The Hamiltonian $H_{B,J}$ and its Gibbs measure $\mu_{\beta,H_{B,J}}$
-- statement:
--   For $B\in\mathbb F_2^{M\times N}$ and couplings $J\in\{+1,-1\}^M$, the classical Hamiltonian on spin configurations $z\in\{+1,-1\}^N$ is (2.5):
--
--   $$H_{B,J}(z)=-\sum_{i=1}^M J_i\prod_{j:\,B_{ij}=1}z_j .$$
--
--   Its Gibbs measure at inverse temperature $\beta$ is (2.1):
--
--   $$\mu_{\beta,H}(z)=\frac{e^{-\beta H(z)}}{Z_{\beta,H}},\qquad Z_{\beta,H}=\sum_z e^{-\beta H(z)} .$$
--
--   The $(H,\beta,\varepsilon)$-Gibbs sampling problem of Definition 2.1 asks to sample from a law within total variation distance $\varepsilon$ of $\mu_{\beta,H}$. Total variation is the published $\tfrac12\ell^1$ distance `IsingLTL.BeliefProp.tvDist`.
--
--   Minimizing $H_{B,J}$ is Max-$k$-XORSAT for $Bx=v$.
--
--   **Formalization Note** Spins are written $z=(-1)^x$ with $x\in\mathbb F_2^N$, and couplings $J=(-1)^v$ with $v\in\mathbb F_2^M$. Both are bijections, so laws on spins and laws on $\mathbb F_2^N$ correspond exactly.
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Definition 2.1, pp.4–5, eq. (2.1); Theorem 2.4, p.5, eq. (2.5)

import Mathlib

namespace DQIShattered

open Finset

/-- **The Hamiltonian** `H_{B,J}` of (2.5) (Zhou, Shutty, Sellke, Jordan, arXiv:2609.40345, held version
sha256 0c7f6fdf…, Theorem 2.4, p.5), evaluated at the spin configuration `z = (−1)^x`:
`H_{B,J}(z) = −∑ᵢ Jᵢ ∏_{j : B_ij = 1} z_j` with `Jᵢ = (−1)^{vᵢ}`.

**Formalization Note** Spin configurations `z ∈ {+1, −1}^N` are written `z = (−1)^x` with `x ∈ 𝔽₂^N`, and
couplings `J ∈ {+1, −1}^M` as `J = (−1)^v` with `v ∈ 𝔽₂^M` ((3.5), p.10); both are bijections, so every
distribution on spins is a distribution on `𝔽₂^N` and conversely. -/
noncomputable def hamiltonian {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (v : Fin M → ZMod 2)
    (x : Fin N → ZMod 2) : ℝ :=
  -∑ i, (-1 : ℝ) ^ (v i).val * ∏ j ∈ univ.filter (fun j => B i j = 1), (-1 : ℝ) ^ (x j).val

/-- **The Gibbs measure** `µ_{β,H}(z) = e^{−βH(z)}/Z_{β,H}`, `Z_{β,H} = ∑_z e^{−βH(z)}` of (2.1)
(Definition 2.1, pp.4–5), for `H = H_{B,J}`, at the configuration `z = (−1)^x`. -/
noncomputable def gibbs {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (v : Fin M → ZMod 2) (β : ℝ)
    (x : Fin N → ZMod 2) : ℝ :=
  Real.exp (-β * hamiltonian B v x) / ∑ x' : Fin N → ZMod 2, Real.exp (-β * hamiltonian B v x')

end DQIShattered


