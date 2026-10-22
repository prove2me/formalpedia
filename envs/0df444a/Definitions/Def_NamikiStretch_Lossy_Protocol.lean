-- Prove2me | Definitions.Def_NamikiStretch_Lossy_Protocol
-- name    : NamikiStretch_Lossy_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:53.866275+00:00
-- url     : https://prove2.me/theorems/bf2ebfb8-092d-4897-9b0e-1787d6e423de
-- title:
--   (4), (13), (15)–(17), (A4), pp. 1–3, 5 — two-mode squeezed kernel, loss on the second mode, displacement conjugation, CV-Bell projection in Fock form, outcome β = (x+ip)/√2
-- statement:
--   This module fixes the objects of the teleportation-stretching protocol of Namiki (arXiv:1603.05292v1, §II.B). Every state and every intermediate object is described by its **number-basis kernel**: a single-mode operator $X$ by the matrix $K(m,n)=\langle m|X|n\rangle$, and an operator on a pair of modes by $K\big((r,b),(r',b')\big)=\langle r,b|X|r',b'\rangle$, the first index labelling the first mode. The Fock space, the displacement matrix $\langle m|D(z)|n\rangle$ with $D(z)=e^{za^\dagger-\bar z a}$, and the pure-loss kernel $\mathcal E_\eta$ are taken from the published modules `QAlgorithms_Papers_Independent_Dependency50_P39` and `QAlgorithms_Papers_Independent_Frontier30_P21`.
--
--   1. **Two-mode squeezed state** (eq. (4), p. 1). For $\xi\in(0,1)$, $|\psi_\xi\rangle=\sqrt{1-\xi^2}\sum_{n\ge0}\xi^n|n\rangle|n\rangle$ on the modes $(A',B)$. Its density kernel is
--   $$\langle k,b|\psi_\xi\rangle\langle\psi_\xi|k',b'\rangle=\begin{cases}(1-\xi^2)\,\xi^{k+k'} & k=b,\ k'=b',\\ 0&\text{otherwise.}\end{cases}$$
--   2. **Loss on the second mode.** $\mathcal I\otimes\mathcal E_\eta$ applies the pure-loss channel of transmissivity $\eta$ (App. B, (B5) with $N=0$) to the second mode of a two-mode kernel, slice by slice in the first index.
--   3. **Displacement conjugation** (eq. (13), p. 2). $\mathcal L_{D(z)}(K)=D(z)\,K\,D(z)^\dagger$, that is
--   $$\big(\mathcal L_{D(z)}K\big)(m,n)=\sum_{j,k\ge0}\langle m|D(z)|j\rangle\,K(j,k)\,\overline{\langle n|D(z)|k\rangle},$$
--   and its version acting on the second mode of a two-mode kernel.
--   4. **CV-Bell projection** (eqs. (15)–(16), p. 3, in the Fock form (A4), p. 5). The CV-Bell states are $|\Phi_\beta\rangle=(\mathbb 1\otimes D^\dagger(\beta))|\Phi_0\rangle$ with $|\Phi_0\rangle=(2\pi)^{-1/2}\sum_n|n\rangle|n\rangle$. For an input kernel $\rho$ on modes $(R,S)$ and a resource kernel $\omega$ on modes $(A',B)$, the unnormalized post-measurement kernel on $(R,B)$ for outcome $\beta$ is
--   $$\langle r,b|\,\langle\Phi_\beta|_{SA'}(\rho\otimes\omega)|\Phi_\beta\rangle_{SA'}\,|r',b'\rangle=\frac1{2\pi}\sum_{n,n',k,k'\ge0}\langle n|D(\beta)|k\rangle\,\rho\big((r,n),(r',n')\big)\,\omega\big((k,b),(k',b')\big)\,\overline{\langle n'|D(\beta)|k'\rangle}.$$
--   5. **Outcome** (p. 3, after (16)). The measurement outcome attached to $(x,p)\in\mathbb R^2$ is $\beta=(x+ip)/\sqrt2$; outcome averages are taken with Lebesgue measure $dx\,dp$.
--
--   These are the ingredients from which the effective teleportation-stretching relation (24) and the Theorem (26)–(27) are stated, so that the protocol is spelled out explicitly rather than hidden in an existential.
--
--   **Formalization Note** The CV-Bell states are improper vectors and are not formalized as vectors; the Bell projection is the absolutely convergent four-fold series above, obtained from (16) and (A4). Every series is a `tsum`, and every theorem that uses one also asserts its summability, so the default value of a divergent series never enters a statement. A single-mode kernel is embedded as a two-mode kernel with a one-point reference (`Unit`).
-- source:
--   Namiki, Teleportation stretching for single-mode Gaussian channels, arXiv:1603.05292v1, p. 1 (4); p. 2 (13); p. 3 (15)–(17) and the definition of β after (16); p. 5 (A4); p. 6 (B5)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21

/-!
Objects of R. Namiki, *Teleportation stretching for single-mode Gaussian channels*,
arXiv:1603.05292v1, §II.B (pp. 1, 3, 5): the two-mode squeezed state (4), the pure-loss channel
on the second mode, displacement conjugation (13), the CV-Bell projection (15)–(16) in its Fock
form (A4), and the outcome map β = (x + i p)/√2 of p. 3. Everything is a number-basis kernel;
every `tsum` is used in the theorems only together with its `Summable`/`HasSum`.
-/

noncomputable section

namespace NamikiStretch.Lossy

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21

/-- (4), p. 1: the density kernel of ψ_ξ = √(1−ξ²) Σₙ ξⁿ |n⟩|n⟩ on the modes (A′, B):
⟨(k,b)|ψ_ξ⟩⟨ψ_ξ|(k′,b′)⟩ = (1−ξ²) ξ^(k+k′) if k = b and k′ = b′, and 0 otherwise. -/
def tmsvKernel (ξ : ℝ) (p q : ℕ × ℕ) : ℂ :=
  if p.1 = p.2 ∧ q.1 = q.2 then (((1 - ξ ^ 2) * ξ ^ (p.1 + q.1) : ℝ) : ℂ) else 0

/-- 𝓘 ⊗ E_η: the vacuum-loss kernel of transmissivity η (App. B, (B5) with N = 0) acting on
the second mode, slice by slice in the first index. -/
def lossOnSecond {ι : Type*} (η : ℝ) (K : ι × ℕ → ι × ℕ → ℂ) (p q : ι × ℕ) : ℂ :=
  vacuumLossKernel η (fun m n => K (p.1, m) (q.1, n)) p.2 q.2

/-- Summand of ⟨m|D(z) K D(z)†|n⟩ = Σ_{j,k} ⟨m|D(z)|j⟩ K j k conj⟨n|D(z)|k⟩. -/
def dispConjTerm (z : ℂ) (K : ℕ → ℕ → ℂ) (m n : ℕ) (c : ℕ × ℕ) : ℂ :=
  displacementMatrix z m c.1 * K c.1 c.2 * star (displacementMatrix z n c.2)

/-- (13), p. 2: 𝓛_{D(z)}(K) = D(z) K D(z)† on number-basis kernels,
with D(z) = exp(z a† − z̄ a). -/
def dispConj (z : ℂ) (K : ℕ → ℕ → ℂ) (m n : ℕ) : ℂ :=
  ∑' c : ℕ × ℕ, dispConjTerm z K m n c

/-- 𝓘 ⊗ 𝓛_{D(z)}: displacement conjugation on the second mode. -/
def dispConjSecond {ι : Type*} (z : ℂ) (K : ι × ℕ → ι × ℕ → ℂ) (p q : ι × ℕ) : ℂ :=
  dispConj z (fun m n => K (p.1, m) (q.1, n)) p.2 q.2

/-- (16) with (A4): summand, at index i = (n, n′, k, k′), of
⟨(r,b)| ⟨Φ_β|_{SA′} (ρ_{RS} ⊗ ω_{A′B}) |Φ_β⟩_{SA′} |(r′,b′)⟩
= (2π)⁻¹ Σ ⟨n|D(β)|k⟩ ρ_{(r,n),(r′,n′)} ω_{(k,b),(k′,b′)} conj⟨n′|D(β)|k′⟩,
where ⟨Φ_β| = ⟨Φ₀|(𝟙 ⊗ D(β)) and ⟨Φ₀| = (2π)^{-1/2} Σₙ ⟨n|⟨n|. -/
def bellTerm {ι : Type*} (ω : ℕ × ℕ → ℕ × ℕ → ℂ) (ρ : ι × ℕ → ι × ℕ → ℂ) (β : ℂ)
    (p q : ι × ℕ) (i : ℕ × ℕ × ℕ × ℕ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * displacementMatrix β i.1 i.2.2.1 * ρ (p.1, i.1) (q.1, i.2.1) *
    ω (i.2.2.1, p.2) (i.2.2.2, q.2) * star (displacementMatrix β i.2.1 i.2.2.2)

/-- The unnormalized branch ⟨Φ_β|(ρ ⊗ ω)|Φ_β⟩ for the CV-Bell outcome β:
a kernel on (R, B). -/
def bellBranch {ι : Type*} (ω : ℕ × ℕ → ℕ × ℕ → ℂ) (ρ : ι × ℕ → ι × ℕ → ℂ) (β : ℂ)
    (p q : ι × ℕ) : ℂ :=
  ∑' i : ℕ × ℕ × ℕ × ℕ, bellTerm ω ρ β p q i

/-- p. 3 after (16): the outcome β = (x + i p)/√2 of the point (x, p) ∈ ℝ × ℝ. -/
def outcome (z : ℝ × ℝ) : ℂ := ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / ((Real.sqrt 2 : ℝ) : ℂ)

end NamikiStretch.Lossy


