-- Prove2me | Definitions.Def_SysBathGibbs_Algorithm
-- name    : SysBathGibbs_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:03.355776+00:00
-- url     : https://prove2.me/theorems/db1f9034-dc4d-4711-8288-f3dd289ee9e3
-- title:
--   The system-bath channel $\Phi=\mathbb E_T[\Phi_{\alpha,T}]$, the Gibbs state and $T_{\mathrm{total}}$
-- statement:
--   One round of the algorithm couples every site $x$ to $4^q-1$ bath qubits $E_{x,a}$. With frequencies $\omega=(\omega_{x,a})$ and interaction time $T$, the joint system evolves for $t\in[-T,T]$ under
--   $$
--   H(t)=H_n+\sum_{x,a}H_{E_{x,a}}(\omega_{x,a})+\alpha f_\sigma(t)\sum_{x,a}\big(A_{x,a}\otimes B_{x,a}+A_{x,a}^\dagger\otimes B_{x,a}^\dagger\big),
--   $$
--   with $H_{E}(\omega)=-\tfrac{\omega}{2}Z_E$, $B=|1\rangle\langle 0|$ and the Gaussian pulse $f_\sigma(t)=e^{-t^2/(4\sigma^2)}/\sqrt{\sigma\sqrt{2\pi}}$. The propagator $U_{\alpha,\omega,T}=\mathcal T\exp(-i\int_{-T}^{T}H(t)\,dt)$ is time ordered with later times on the left. The bath starts in $\tau_{E,\omega}=\bigotimes_{x,a}e^{-\tilde\beta H_{E_{x,a}}}/\operatorname{Tr}(\cdot)$, $\tilde\beta=2\beta/(2-\beta^2/(4\sigma^2))$. The frequencies are i.i.d. with density
--   $$
--   g_{\beta,\sigma}(\omega)=\frac{\beta}{\sqrt{2\pi s_{\beta,\sigma}}}e^{-(\beta\omega+1)^2/(2s_{\beta,\sigma})},\qquad s_{\beta,\sigma}=2-\frac{\beta^2}{4\sigma^2},
--   $$
--   and $T$ has density $\mu_{T_0}(t)=\frac{1}{6T_0}(t/T_0-1)^3e^{-(t/T_0-1)}\mathbf 1\{t\ge T_0\}$. The one-round and averaged channels are
--   $$
--   \Phi_{\alpha,T}(\rho)=\mathbb E_\omega\operatorname{Tr}_E\big(U_{\alpha,\omega,T}(\rho\otimes\tau_{E,\omega})U_{\alpha,\omega,T}^\dagger\big),\qquad \Phi=\mathbb E_T[\Phi_{\alpha,T}],
--   $$
--   at $\sigma=\beta/2$, and $m$ rounds output $\Phi^m(\rho_0)$. The target is $\rho_\beta=e^{-\beta H_n}/\operatorname{Tr}e^{-\beta H_n}$, the expected evolution time of $m$ rounds is $T_{\mathrm{total}}=2m\,\mathbb E[T]$, and (9.5) chooses $T_0=\max\{1,2\sigma\sqrt{2\log(1/(\alpha^2\sigma))}\}$.
--
--   This module fixes the algorithm whose output the goal theorem bounds.
--
--   **Formalization Note** The joint index set is system × bath with the system on the left of the Kronecker product, and $\operatorname{Tr}_E$ is the published `WildeQIT.partialTraceRight`. The time-ordered exponential is the sum of the Dyson series $D_0=\mathbf 1$, $D_{k+1}(s)=\int_{-T}^{s}-iH(r)D_k(r)\,dr$. Matrix-valued expectations are entrywise Bochner integrals against the product law of the frequencies and the law of $T$; the formulas are applied to every matrix, on which they are linear. The bath state is diagonal and is written through its populations. $T_{\mathrm{total}}$ is (1.9) before its last equality $2m\mathbb E[T]=10mT_0$.
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), §1.1.2 eqs. (1.3)–(1.9), pp.5–6; (2.11)–(2.12), pp.11–12; (9.5), p.73

import Definitions.Def_SysBathGibbs_Chain
import Definitions.Def_WildeQIT_partialTrace

open Matrix MeasureTheory
open scoped Kronecker

namespace SysBathGibbs

/-!
# The system-bath algorithm

Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), §1.1.2, (1.3)–(1.9), pp.5–6.

**Formalization Note.** The index set of the joint system is `Site n q × Bath n q`, with the system
on the left of the Kronecker product. A bath qubit's basis is `false = |0⟩`, `true = |1⟩`, with
`Z|0⟩ = |0⟩`. So `B = |1⟩⟨0|` has its entry `1` at row `true`, column `false`, and the population of
`|0⟩` in the bath state is `p₀(ω) = 1/(1 + e^{-β̃ω})`, as on p.25. The time-ordered exponential is
the Dyson series of `U' = -iH(t)U`, with later times on the left, (2.12). Matrix-valued integrals
are entrywise Bochner integrals (`matInt`). The formulas (1.5), (1.8) keep `σ` as a parameter, and
the channel is taken at `σ = β/2` as "throughout the manuscript" (p.10).
-/

/-- The bath: one qubit per label `(x, a)`, p.5. -/
abbrev Bath (n q : ℕ) := Label n q → Bool

/-- The joint system-bath matrices. -/
abbrev JointMat (n q : ℕ) := Matrix (Site n q × Bath n q) (Site n q × Bath n q) ℂ

/-- Entrywise Bochner integral of a matrix-valued function. -/
noncomputable def matInt {X ι κ : Type} [MeasurableSpace X] (μ : Measure X)
    (F : X → Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  Matrix.of fun i j => ∫ x, F x i j ∂μ

/-- The Gaussian pulse `f_σ(t) = e^{-t²/(4σ²)} / √(σ√(2π))`, (1.8). -/
noncomputable def pulse (σ t : ℝ) : ℝ :=
  Real.exp (-t ^ 2 / (4 * σ ^ 2)) / Real.sqrt (σ * Real.sqrt (2 * Real.pi))

/-- `s_{β,σ} = 2 - β²/(4σ²)`, (1.5). -/
noncomputable def sParam (β σ : ℝ) : ℝ := 2 - β ^ 2 / (4 * σ ^ 2)

/-- The frequency density `g_{β,σ}(ω) = β/√(2π s) · e^{-(βω+1)²/(2s)}`, (1.5). -/
noncomputable def freqDensity (β σ w : ℝ) : ℝ :=
  β / Real.sqrt (2 * Real.pi * sParam β σ) * Real.exp (-(β * w + 1) ^ 2 / (2 * sParam β σ))

/-- `β̃ = 2β/(2 - β²/(4σ²))`, p.5. -/
noncomputable def betaTilde (β σ : ℝ) : ℝ := 2 * β / sParam β σ

/-- The law of one bath frequency, with density `g_{β,σ}`. -/
noncomputable def freqLaw (β σ : ℝ) : Measure ℝ :=
  volume.withDensity fun w => ENNReal.ofReal (freqDensity β σ w)

/-- The interaction-time density
`μ_{T₀}(t) = (1/(6T₀)) (t/T₀ - 1)³ e^{-(t/T₀-1)} 1{t ≥ T₀}`, (1.6). -/
noncomputable def timeDensity (T₀ t : ℝ) : ℝ :=
  if T₀ ≤ t then 1 / (6 * T₀) * (t / T₀ - 1) ^ 3 * Real.exp (-(t / T₀ - 1)) else 0

/-- The law of the interaction time `T`, with density `μ_{T₀}`. -/
noncomputable def timeLaw (T₀ : ℝ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal (timeDensity T₀ t)

/-- The eigenvalue of `Z` on a bath qubit basis vector: `Z|0⟩ = |0⟩`, `Z|1⟩ = -|1⟩`. -/
def zVal (b : Bool) : ℝ := if b then -1 else 1

/-- The bath Hamiltonian `∑_{x,a} H_{E_{x,a}}(ω_{x,a})` with `H_{E_{x,a}}(ω) = -(ω/2) Z_{E_{x,a}}`,
p.5, as a diagonal matrix on the bath basis. -/
noncomputable def bathHam {n q : ℕ} (w : Label n q → ℝ) : Matrix (Bath n q) (Bath n q) ℂ :=
  Matrix.diagonal fun b => ((∑ l, (-(w l / 2) * zVal (b l)) : ℝ) : ℂ)

/-- The bath coupling `B_{x,a} = |1⟩⟨0|` on the qubit `l = (x, a)`, identity on the other qubits. -/
def bathCoupling {n q : ℕ} (l : Label n q) : Matrix (Bath n q) (Bath n q) ℂ :=
  Matrix.of fun b b' =>
    if b l = true ∧ b' l = false ∧ ∀ l', l' ≠ l → b l' = b' l' then 1 else 0

/-- One factor of `τ_{E,ω}`: the population of the basis vector `b` in
`e^{-β̃ H_E(ω)} / Tr e^{-β̃ H_E(ω)}`, with `H_E(ω) = -(ω/2) Z`, p.5. -/
noncomputable def bathWeight (βt w : ℝ) (b : Bool) : ℝ :=
  Real.exp (βt * w * zVal b / 2) / (Real.exp (βt * w / 2) + Real.exp (-(βt * w) / 2))

/-- The initial bath state `τ_{E,ω} = ⨂_{x,a} e^{-β̃ H_{E_{x,a}}(ω_{x,a})} / Tr(…)`, p.5. It is
diagonal in the bath basis, so the matrix exponentials are written out as `bathWeight`. -/
noncomputable def bathState {n q : ℕ} (βt : ℝ) (w : Label n q → ℝ) :
    Matrix (Bath n q) (Bath n q) ℂ :=
  Matrix.diagonal fun b => ((∏ l, bathWeight βt (w l) (b l) : ℝ) : ℂ)

/-- The time-dependent Hamiltonian (1.4), with `σ = β/2`:
`H(t) = H_n + ∑_{x,a} H_{E_{x,a}}(ω_{x,a}) + α f_σ(t) ∑_{x,a} (A_{x,a} ⊗ B_{x,a} + A†_{x,a} ⊗ B†_{x,a})`. -/
noncomputable def sbHam {n q : ℕ} (β : ℝ) (h : Fin (n - 1) → SysMat n q) (α : ℝ)
    (w : Label n q → ℝ) (t : ℝ) : JointMat n q :=
  (chainHam h ⊗ₖ (1 : Matrix (Bath n q) (Bath n q) ℂ)) +
    ((1 : SysMat n q) ⊗ₖ bathHam w) +
    (((α * pulse (β / 2) t : ℝ) : ℂ)) •
      ∑ l : Label n q,
        ((pauliString l.1 l.2.1 ⊗ₖ bathCoupling l) +
          ((pauliString l.1 l.2.1)ᴴ ⊗ₖ (bathCoupling l)ᴴ))

/-- The Dyson terms of `T exp(-i∫_{-T}^{s} H(r) dr)`, `paper.md` decision 7:
`D₀(s) = 1`, `D_{k+1}(s) = ∫_{-T}^{s} -i H(r) D_k(r) dr`. Later times are on the left, (2.12). -/
noncomputable def dyson {ι : Type} [Fintype ι] [DecidableEq ι] (H : ℝ → Matrix ι ι ℂ) (T : ℝ) :
    ℕ → ℝ → Matrix ι ι ℂ
  | 0, _ => 1
  | k + 1, s => Matrix.of fun i j =>
      ∫ r in (-T)..s, ((-Complex.I) • (H r * dyson H T k r)) i j

/-- The propagator `T exp(-i∫_{-T}^{T} H(t) dt)`, p.5: the sum of the Dyson series at `s = T`. -/
noncomputable def propagator {ι : Type} [Fintype ι] [DecidableEq ι] (H : ℝ → Matrix ι ι ℂ)
    (T : ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ∑' k, dyson H T k T i j

/-- The one-round channel `Φ_{α,T}(ρ) = E_ω[Tr_E(U_{α,ω,T} (ρ ⊗ τ_{E,ω}) U†_{α,ω,T})]`, (1.3), at
`σ = β/2`. The frequencies `ω_{x,a}` are i.i.d. with density `g_{β,σ}`. The formula is applied to
every matrix `ρ`, on which it is linear. -/
noncomputable def roundChannel {n q : ℕ} (β : ℝ) (h : Fin (n - 1) → SysMat n q) (α T : ℝ)
    (ρ : SysMat n q) : SysMat n q :=
  matInt (Measure.pi fun _ : Label n q => freqLaw β (β / 2)) fun w =>
    WildeQIT.partialTraceRight
      (propagator (sbHam β h α w) T *
        (ρ ⊗ₖ bathState (betaTilde β (β / 2)) w) *
        (propagator (sbHam β h α w) T)ᴴ)

/-- The averaged physical channel for a law `μ` of the interaction time, `E_T[Φ_{α,T}]`. -/
noncomputable def channelOf {n q : ℕ} (β : ℝ) (h : Fin (n - 1) → SysMat n q) (α : ℝ)
    (μ : Measure ℝ) (ρ : SysMat n q) : SysMat n q :=
  matInt μ fun T => roundChannel β h α T ρ

/-- The channel `Φ = Φ^{μ_{T₀}}_α = E_T[Φ_{α,T}]`, (1.3), (2.11), with `T` drawn from `μ_{T₀}`.
The output of `m` rounds is the iterate `(Phi β h α T₀)^[m]`, since each round uses fresh randomness. -/
noncomputable def Phi {n q : ℕ} (β : ℝ) (h : Fin (n - 1) → SysMat n q) (α T₀ : ℝ)
    (ρ : SysMat n q) : SysMat n q :=
  channelOf β h α (timeLaw T₀) ρ

/-- The Gibbs state `ρ_β = e^{-βH} / Tr e^{-βH}`, p.5. -/
noncomputable def gibbs {ι : Type} [Fintype ι] [DecidableEq ι] (β : ℝ) (H : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (Matrix.trace (NormedSpace.exp ((-(β : ℂ)) • H)))⁻¹ • NormedSpace.exp ((-(β : ℂ)) • H)

/-- The expected total Hamiltonian evolution time of `m` rounds, (1.9):
`T_total = E[∑_{j=1}^m 2T_j] = 2m E[T]`, before the last equality of (1.9). -/
noncomputable def Ttotal (T₀ : ℝ) (m : ℕ) : ℝ :=
  2 * m * ∫ t, t ∂(timeLaw T₀)

/-- The choice of the minimum interaction time in (9.5), (7.9), with `σ = β/2`:
`T₀ = max{1, 2σ √(2 log(1/(α²σ)))}`. -/
noncomputable def T0Choice (β α : ℝ) : ℝ :=
  max 1 (2 * (β / 2) * Real.sqrt (2 * Real.log (1 / (α ^ 2 * (β / 2)))))

end SysBathGibbs


