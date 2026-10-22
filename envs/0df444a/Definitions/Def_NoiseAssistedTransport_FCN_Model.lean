-- Prove2me | Definitions.Def_NoiseAssistedTransport_FCN_Model
-- name    : NoiseAssistedTransport_FCN_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:26.025987+00:00
-- url     : https://prove2.me/theorems/16611368-2853-45f0-ac5a-f309cd8acf93
-- title:
--   Eqs. (1)–(4), pp. 2–3 — single-excitation network Hamiltonian, dissipation, dephasing and sink Lindbladian, ρ(t) and p_sink(t); the FCN
-- statement:
--   This file fixes the network model of Caruso, Chin, Datta, Huelga and Plenio for the **fully connected network (FCN)** on $N$ sites, together with the states used in its analysis.
--
--   1. **Basis.** The single-excitation space has the orthonormal basis $|0\rangle, |1\rangle, \dots, |N\rangle, |N+1\rangle$: $|0\rangle$ is the zero-exciton state (its population $\rho_{00}$ is the population lost to the environment), $|j\rangle$ for $1 \le j \le N$ is one excitation on site $j$, and $|N+1\rangle$ is the sink. The raising and lowering operators are $\sigma_j^+ = |j\rangle\langle 0|$ and $\sigma_j^- = |0\rangle\langle j|$.
--   2. **Hamiltonian (Eq. (1) for the FCN, $\hbar = 1$).** $H$ has $\langle j|H|j\rangle = \omega_j$ and $\langle i|H|j\rangle = J$ for sites $i \ne j$, and vanishes on $|0\rangle$ and $|N+1\rangle$.
--   3. **Generator (Eqs. (2)–(4)).** For a real rate $r$ and an operator $c$, write $\mathcal D_{r,c}(\rho) = r\,[2c\rho c^\dagger - \{c^\dagger c, \rho\}]$. The master equation is $\dot\rho = \mathcal L(\rho)$ with
--   $$\mathcal L(\rho) = -i[H,\rho] + \sum_{j=1}^N \mathcal D_{\Gamma_j,\sigma_j^-}(\rho) + \sum_{j=1}^N \mathcal D_{\gamma_j,\sigma_j^+\sigma_j^-}(\rho) + \mathcal D_{\Gamma_{N+1},\sigma_{N+1}^+\sigma_k^-}(\rho),$$
--   where $\Gamma_j$ are the dissipation rates, $\gamma_j$ the dephasing rates, $\Gamma_{N+1}$ the sink rate and $k$ the site coupled to the sink. Here $\sigma_j^+\sigma_j^- = |j\rangle\langle j|$ and $\sigma_{N+1}^+\sigma_k^- = |N+1\rangle\langle k|$.
--   4. **Evolution and sink population.** $\rho(t) = e^{t\mathcal L}\rho_0$, and
--   $$p_{\rm sink}(t) = 2\Gamma_{N+1}\int_0^t \rho_{kk}(t')\,dt'.$$
--   The initial state is $|1\rangle\langle 1|$, a single excitation on site 1.
--   5. **States of §II.A.** $|\phi\rangle = N^{-1/2}\sum_{j=1}^N |j\rangle$, $|\psi_j\rangle = |1\rangle - |j\rangle$, $|\Psi\rangle = ((N-1)(N-2))^{-1/2}\sum_{j=2}^{N-1}(|1\rangle - |j\rangle)$, the pure state $|v\rangle\langle v|$ of a vector $v$, and the final state $\frac{N-2}{N-1}|\Psi\rangle\langle\Psi| + \frac{1}{N-1}|N+1\rangle\langle N+1|$ of Eq. (6).
--   6. **The FCN of §II.A and §II.C.** $\omega_j = 0$, $\Gamma_j = 0$, a uniform dephasing rate $\gamma_j = \gamma$, the sink attached to site $k = N$, and the start $|1\rangle\langle 1|$. Its state is $\rho(t)$ and its sink population is $p_{\rm sink}(t)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The basis is `Fin (N + 2)` in the paper's own numbering, with natural-number indices cast into it (`open Fin.NatCast`); sums over sites run over `Finset.Icc 1 N`. The hopping amplitude is $\langle i|H|j\rangle = J$, the normalization of (A1), (A34) and of the spectrum on p. 4; reading the sum over $j \ne l$ in Eq. (1) as spin operators would double it, but with $\sigma_j^\pm$ as defined on p. 3 the term $\sigma_j^-\sigma_l^+$ vanishes for $j\ne l$ and the literal reading also gives $J$. The rates multiply $2c\rho c^\dagger - \{c^\dagger c,\rho\}$ exactly as in Eqs. (2)–(4) (no ½). The exponential is `semigroupEvolution` of the published definition P16, i.e. `NormedSpace.exp` of $t\mathcal L$ as a continuous linear map on $(N+2)\times(N+2)$ complex matrices. The integrand of $p_{\rm sink}$ is the real part of $\rho_{kk}(t')$, which is real. $p_{\rm sink}$ is the integral of p. 3, not the sink entry $\rho_{N+1,N+1}$.
-- source:
--   Caruso et al., Highly efficient energy excitation transfer in light-harvesting complexes, arXiv:0901.4454v2, pp. 2–3, Eqs. (1)–(4), §I; p. 3, §II and §II.A (FCN, ω_j = γ_j = Γ_j = 0, sink at N); p. 4, §II.A (|φ⟩, |ψ_j⟩), Eqs. (6)–(7); p. 11, Appendix A.1, Eq. (A1)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16
noncomputable section
open scoped Matrix
open Fin.NatCast
open QAlgorithms.Papers.Independent.Dependency50.P16

namespace NoiseAssistedTransport.FCN

/-! Caruso, Chin, Datta, Huelga, Plenio, arXiv:0901.4454v2, §I (Eqs. (1)–(4), pp. 2–3) and §II
(p. 3). Single-excitation basis `Fin (N + 2)`: index `0` is the zero-exciton state `|0⟩`,
indices `1, …, N` are the sites, index `N + 1` is the sink (p. 3). `ℏ = 1`. -/

/-- The sites `1, …, N` of the basis `Fin (N + 2)` (p. 3). -/
def IsSite (N : ℕ) (i : Fin (N + 2)) : Prop := 1 ≤ i.val ∧ i.val ≤ N

instance (N : ℕ) (i : Fin (N + 2)) : Decidable (IsSite N i) :=
  inferInstanceAs (Decidable (1 ≤ i.val ∧ i.val ≤ N))

/-- Eq. (1) for the fully connected network (`ℏ v_{j,l} = J` for all sites `j ≠ l`, p. 3), with
`ℏ = 1` and the normalization of (A1)/(A34): `⟨i|H|i⟩ = ω_i`, `⟨i|H|j⟩ = J` for sites `i ≠ j`,
and `H` vanishes on the zero-exciton state and on the sink. -/
def hamiltonian (N : ℕ) (ω : ℕ → ℝ) (J : ℝ) : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ :=
  Matrix.of fun i j =>
    if IsSite N i ∧ IsSite N j then (if i = j then ((ω i.val : ℝ) : ℂ) else ((J : ℝ) : ℂ)) else 0

/-- One Lindblad term `r [2 c ρ c† − {c† c, ρ}]` of Eqs. (2)–(4). -/
def lindbladTerm {n : ℕ} (r : ℝ) (c : Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  ((r : ℝ) : ℂ) • ((2 : ℂ) • sandwich c cᴴ - LinearMap.mulLeft ℂ (cᴴ * c)
    - LinearMap.mulRight ℂ (cᴴ * c))

/-- The master-equation generator `L(ρ) = −i[H, ρ] + L_diss(ρ) + L_deph(ρ) + L_sink(ρ)`,
Eqs. (1)–(4): dissipation with `σ⁻_j = |0⟩⟨j|` at rate `Γ_j`, dephasing with
`σ⁺_j σ⁻_j = |j⟩⟨j|` at rate `γ_j`, and the sink decay with `σ⁺_{N+1} σ⁻_k = |N+1⟩⟨k|` at rate
`Γ_{N+1} = Γs` from the chosen site `k`. -/
def generator (N : ℕ) (ω Γ γ : ℕ → ℝ) (J Γs : ℝ) (k : ℕ) :
    Module.End ℂ (Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ) :=
  (-Complex.I) • (LinearMap.mulLeft ℂ (hamiltonian N ω J)
      - LinearMap.mulRight ℂ (hamiltonian N ω J))
  + ∑ j ∈ Finset.Icc 1 N,
      lindbladTerm (Γ j) (Matrix.single (0 : Fin (N + 2)) ((j : ℕ) : Fin (N + 2)) (1 : ℂ))
  + ∑ j ∈ Finset.Icc 1 N,
      lindbladTerm (γ j) (Matrix.single ((j : ℕ) : Fin (N + 2)) ((j : ℕ) : Fin (N + 2)) (1 : ℂ))
  + lindbladTerm Γs (Matrix.single ((N + 1 : ℕ) : Fin (N + 2)) ((k : ℕ) : Fin (N + 2)) (1 : ℂ))

/-- The state at time `t`, `ρ(t) = e^{tL} ρ₀`. -/
def evolve (N : ℕ) (ω Γ γ : ℕ → ℝ) (J Γs : ℝ) (k : ℕ)
    (ρ₀ : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ) (t : ℝ) : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ :=
  semigroupEvolution (generator N ω Γ γ J Γs k) t ρ₀

/-- The sink population `p_sink(t) = 2 Γ_{N+1} ∫₀ᵗ ρ_kk(t') dt'` (p. 3); the integrand is the real
part of the `(k, k)` entry of `ρ(t')`. -/
def sinkPop (N : ℕ) (ω Γ γ : ℕ → ℝ) (J Γs : ℝ) (k : ℕ)
    (ρ₀ : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ) (t : ℝ) : ℝ :=
  2 * Γs * ∫ s in (0 : ℝ)..t,
    (evolve N ω Γ γ J Γs k ρ₀ s ((k : ℕ) : Fin (N + 2)) ((k : ℕ) : Fin (N + 2))).re

/-- The initial state `|1⟩⟨1|`, a single excitation on site 1 (p. 3). -/
def initState (N : ℕ) : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ :=
  Matrix.single (1 : Fin (N + 2)) (1 : Fin (N + 2)) (1 : ℂ)

/-- The pure state `|v⟩⟨v|`. -/
def pureState {n : ℕ} (v : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec v (star v)

/-- The basis vector `|j⟩`. -/
def ket (N : ℕ) (j : ℕ) : Fin (N + 2) → ℂ := Pi.single ((j : ℕ) : Fin (N + 2)) (1 : ℂ)

/-- `|φ⟩ = N^{-1/2} Σ_{j=1}^{N} |j⟩` (§II.A, p. 4). -/
def phiState (N : ℕ) : Fin (N + 2) → ℂ :=
  (((Real.sqrt N)⁻¹ : ℝ) : ℂ) • ∑ j ∈ Finset.Icc 1 N, ket N j

/-- `|ψ_j⟩ = |1⟩ − |j⟩` (§II.A, p. 4). -/
def psiState (N : ℕ) (j : ℕ) : Fin (N + 2) → ℂ := ket N 1 - ket N j

/-- `|Ψ⟩ = ((N − 1)(N − 2))^{-1/2} Σ_{j ≠ N, 1} (|1⟩ − |j⟩)`, the sum over sites `j = 2, …, N − 1`
(Eq. (7), p. 4). -/
def bigPsi (N : ℕ) : Fin (N + 2) → ℂ :=
  (((Real.sqrt (((N : ℝ) - 1) * ((N : ℝ) - 2)))⁻¹ : ℝ) : ℂ) •
    ∑ j ∈ Finset.Icc 2 (N - 1), psiState N j

/-- The final state of Eq. (6), p. 4:
`(N − 2)/(N − 1) |Ψ⟩⟨Ψ| + 1/(N − 1) |N + 1⟩⟨N + 1|`. -/
def finalState (N : ℕ) : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ :=
  ((((N : ℝ) - 2) / ((N : ℝ) - 1) : ℝ) : ℂ) • pureState (bigPsi N)
  + (((1 / ((N : ℝ) - 1)) : ℝ) : ℂ) •
      Matrix.single ((N + 1 : ℕ) : Fin (N + 2)) ((N + 1 : ℕ) : Fin (N + 2)) (1 : ℂ)

/-- The FCN of §II.A and §II.C: `ω_j = 0`, `Γ_j = 0`, uniform dephasing `γ_j = γ`, sink attached
at site `k = N`, started in `|1⟩⟨1|`. Its state at time `t`. -/
def fcnEvolve (N : ℕ) (J γ Γs : ℝ) (t : ℝ) : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ :=
  evolve N (fun _ => 0) (fun _ => 0) (fun _ => γ) J Γs N (initState N) t

/-- The sink population `p_sink(t)` of the FCN of §II.A and §II.C. -/
def fcnSinkPop (N : ℕ) (J γ Γs : ℝ) (t : ℝ) : ℝ :=
  sinkPop N (fun _ => 0) (fun _ => 0) (fun _ => γ) J Γs N (initState N) t

end NoiseAssistedTransport.FCN


