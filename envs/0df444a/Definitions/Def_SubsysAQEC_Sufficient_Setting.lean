-- Prove2me | Definitions.Def_SubsysAQEC_Sufficient_Setting
-- name    : SubsysAQEC_Sufficient_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:38.007553+00:00
-- url     : https://prove2.me/theorems/7517c5f3-371d-4a3c-bc18-3aff1242193c
-- title:
--   §II–§III, pp. 2–4 — subsystem code, Kraus noise, transpose channel (9)–(10), recovery on 𝒫_ℰ, fidelity loss (6), ϵ-correctability, and the expression (13)
-- statement:
--   This file fixes the model of Mandayam and Ng's approximate quantum error correction framework for subsystem codes (§II, pp. 2–3, and §III B, pp. 3–4).
--
--   1. **Spaces.** The system space is $\mathcal H = \mathcal H_A\otimes\mathcal H_B \oplus \mathcal K$, with $\mathcal H_A,\mathcal H_B$ finite dimensional. Information is stored in $A$. The code $\mathcal C$ consists of all product states $\rho_A\otimes\rho_B$, with $\rho_A,\rho_B$ density operators (positive semidefinite, trace one).
--   2. **Noise.** The noise $\mathcal E$ is a completely positive trace-preserving map from operators on $\mathcal H_{AB}$ to operators on $\mathcal H$, with Kraus operators $E_1,\dots,E_N:\mathcal H_{AB}\to\mathcal H$, so $\mathcal E(\rho)=\sum_i E_i\rho E_i^\dagger$; it is trace preserving when $\sum_i E_i^\dagger E_i = P$, the identity on $\mathcal H_{AB}$. The operator $\mathcal E(P)=\sum_i E_iE_i^\dagger$ has support $\mathcal P_{\mathcal E}$; `outSupport` is the projector onto it.
--   3. **Transpose channel.** Its Kraus operators are
--   $$R^P_i = P\,E_i^\dagger\,\mathcal E(P)^{-1/2},$$
--   where the inverse square root is taken on the support of $\mathcal E(P)$ and is $0$ on its kernel.
--   4. **Recoveries.** A recovery is a CP map $\mathcal R:\mathcal B(\mathcal P_{\mathcal E})\to\mathcal B(\mathcal H_{AB})$ given by Kraus operators $R_k:\mathcal H\to\mathcal H_{AB}$, trace preserving on $\mathcal P_{\mathcal E}$: $\mathcal P_{\mathcal E}\big(\sum_k R_k^\dagger R_k\big)\mathcal P_{\mathcal E}=\mathcal P_{\mathcal E}$.
--   5. **Fidelity loss (6).** For a code state $\rho=\rho_A\otimes\rho_B$,
--   $$\eta_{\mathcal R}\{\rho\} = 1 - F^2\big(\mathrm{tr}_B\,\rho,\ \mathrm{tr}_B[(\mathcal R\circ\mathcal E)(\rho)]\big),\qquad F(\rho,\sigma)=\mathrm{tr}\sqrt{\rho^{1/2}\sigma\rho^{1/2}}.$$
--   6. **ϵ-correctability (p. 3).** $\mathcal C$ is $\epsilon$-correctable on $A$ under $\mathcal E$ when some recovery $\mathcal R$ has $\eta_{\mathcal R}\{\rho\}\le\epsilon$ for every code state $\rho$, i.e. information in $A$ can be recovered with fidelity at least $\sqrt{1-\epsilon}$.
--   7. **The expression (13).** For a family $\Delta_{ij}$ of operators on $\mathcal H_{AB}$ and unit vectors $\psi_A,\phi_B$,
--   $$\langle\phi_B|\sum_{ij}\Big[\langle\psi_A|\Delta_{ij}^\dagger\Delta_{ij}|\psi_A\rangle-\langle\psi_A|\Delta_{ij}^\dagger|\psi_A\rangle\langle\psi_A|\Delta_{ij}|\psi_A\rangle\Big]|\phi_B\rangle,$$
--   where $\langle\psi_A|X|\psi_A\rangle$ denotes the partial matrix element, an operator on $\mathcal H_B$. Also defined: the product vector $|\psi_A,\phi_B\rangle=|\psi_A\rangle\otimes|\phi_B\rangle$.
--
--   These are the objects in which the paper's sufficient condition (Theorem 2, Corollary 3) is stated.
--
--   **Formalization Note** $\mathcal H_{AB}$ is indexed by `a × b` (A first) and $\mathcal H$ by a separate finite type `o`; the noise's Kraus operators are rectangular `o × (a × b)` matrices, so the projector $P$ onto $\mathcal H_{AB}$ is the identity matrix and $P(\cdot)P$ disappears. The fidelity is the published `WildeQIT.fidelity` ($F^2$, with $F=\|\sqrt\rho\sqrt\sigma\|_1$, equal to the paper's $F$), the partial trace is `WildeQIT.partialTraceRight`, the channel action is `PeresTerno.krausUpdate`, states are `PeresTerno.IsDensityMatrix`, and the inverse square root and support projector are `QReversal.NearOpt.invSqrt` and `supportProj` (continuous functional calculus, with $(\sqrt0)^{-1}=0$). Full support of $\mathcal E(P)$ is not assumed, which is why recoveries are only required to be trace preserving on $\mathcal P_{\mathcal E}$. $\epsilon$-correctability is stated as the existence of a recovery rather than through the optimum $\eta_{\mathrm{op}}$ of (8); the two agree because the minimum in (8) is attained.
-- source:
--   Mandayam, Ng, Towards a Unified Framework for Approximate Quantum Error Correction, arXiv:1202.5139v2, pp. 2–4, (1)–(3), (5)–(7), ϵ-correctability (p. 3), (9)–(10), (13)

import Mathlib
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_QReversal_NearOpt_Setting

namespace SubsysAQEC.Sufficient

open Matrix QReversal.NearOpt PeresTerno WildeQIT
open scoped Kronecker ComplexOrder

/-! Mandayam–Ng, arXiv:1202.5139v2, §II (pp. 2–3) and §III B (p. 3).

`H_AB = H_A ⊗ H_B` is indexed by `a × b` (A first, as `⊗ₖ` and `partialTraceRight` expect); the
whole space `H = H_AB ⊕ K` is the output index type `o`. The noise `ℰ` has Kraus operators
`E i : Matrix o (a × b) ℂ`, so the projector `P` onto `H_AB` is the identity of `a × b`. -/

variable {a b o ι : Type} [Fintype a] [Fintype b] [Fintype o] [Fintype ι]
  [DecidableEq a] [DecidableEq b] [DecidableEq o]

/-- p. 2: `ℰ(P) = Σ_i E_i P E_i†`, with `P` the identity of `H_AB`. -/
noncomputable def noiseOfP (E : ι → Matrix o (a × b) ℂ) : Matrix o o ℂ :=
  krausUpdate E (1 : Matrix (a × b) (a × b) ℂ)

/-- p. 2: the noise `ℰ` is trace preserving, `Σ_i E_i† E_i = P`. -/
def IsTPNoise (E : ι → Matrix o (a × b) ℂ) : Prop :=
  ∑ i, (E i)ᴴ * E i = 1

/-- p. 2: the projector onto `𝒫_ℰ`, the support of `ℰ(P)`. -/
noncomputable def outSupport (E : ι → Matrix o (a × b) ℂ) : Matrix o o ℂ :=
  supportProj (noiseOfP E)

/-- (9)–(10), p. 3: the Kraus operators `R^P_i = P E_i† ℰ(P)^{-1/2}` of the transpose channel
`R_P`, the inverse square root being taken on the support of `ℰ(P)`. -/
noncomputable def transposeKraus (E : ι → Matrix o (a × b) ℂ) : ι → Matrix (a × b) o ℂ :=
  fun i => (E i)ᴴ * invSqrt (noiseOfP E)

/-- p. 2: a Kraus family `{R_k}` is a recovery `R : B(𝒫_ℰ) → B(H_AB)`, i.e. a CP map that is
trace preserving on `𝒫_ℰ`: `𝒫_ℰ (Σ_k R_k† R_k) 𝒫_ℰ = 𝒫_ℰ`. -/
def IsRecovery (E : ι → Matrix o (a × b) ℂ) {κ : Type} [Fintype κ]
    (R : κ → Matrix (a × b) o ℂ) : Prop :=
  outSupport E * (∑ k, (R k)ᴴ * R k) * outSupport E = outSupport E

/-- (6), p. 2: the fidelity loss `η_R{ρ} = 1 − F²(tr_B ρ, tr_B[(R ∘ ℰ)(ρ)])` of the code state
`ρ = ρ_A ⊗ ρ_B` under noise `ℰ` and recovery `R`. -/
noncomputable def fidelityLoss (E : ι → Matrix o (a × b) ℂ) {κ : Type} [Fintype κ]
    (R : κ → Matrix (a × b) o ℂ) (ρA : Matrix a a ℂ) (ρB : Matrix b b ℂ) : ℝ :=
  1 - fidelity (partialTraceRight (ρA ⊗ₖ ρB))
    (partialTraceRight (krausUpdate R (krausUpdate E (ρA ⊗ₖ ρB))))

/-- p. 3: the code `C = {ρ_A ⊗ ρ_B}` of (2) is `ϵ`-correctable on `A` under `ℰ`: some recovery
`R` has fidelity loss at most `ϵ` on every code state. -/
def IsEpsCorrectable (E : ι → Matrix o (a × b) ℂ) (ε : ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (R : κ → Matrix (a × b) o ℂ), IsRecovery E R ∧
    ∀ (ρA : Matrix a a ℂ) (ρB : Matrix b b ℂ), IsDensityMatrix ρA → IsDensityMatrix ρB →
      fidelityLoss E R ρA ρB ≤ ε

/-- The partial matrix element `⟨ψ_A| X |ψ_A⟩ ∈ B(H_B)` of an operator `X` on `H_AB`. -/
noncomputable def partialExpect (ψ : a → ℂ) (X : Matrix (a × b) (a × b) ℂ) : Matrix b b ℂ :=
  Matrix.of fun k l => ∑ i, ∑ j, star (ψ i) * X (i, k) (j, l) * ψ j

/-- (13), p. 4: the quantity maximized in `η_P`, at the pure product state `|ψ_A, φ_B⟩`:
`⟨φ_B| Σ_ij [⟨ψ_A|Δ_ij† Δ_ij|ψ_A⟩ − ⟨ψ_A|Δ_ij†|ψ_A⟩⟨ψ_A|Δ_ij|ψ_A⟩] |φ_B⟩`. -/
noncomputable def eq13Summand (Δ : ι → ι → Matrix (a × b) (a × b) ℂ) (ψ : a → ℂ)
    (φ : b → ℂ) : ℝ :=
  (star φ ⬝ᵥ ((∑ i, ∑ j, (partialExpect ψ ((Δ i j)ᴴ * Δ i j)
      - partialExpect ψ (Δ i j)ᴴ * partialExpect ψ (Δ i j))) *ᵥ φ)).re

/-- The product vector `|ψ_A, φ_B⟩ = |ψ_A⟩ ⊗ |φ_B⟩` in `H_AB`. -/
def prodVec (ψ : a → ℂ) (φ : b → ℂ) : a × b → ℂ :=
  fun p => ψ p.1 * φ p.2

end SubsysAQEC.Sufficient


