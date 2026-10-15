-- Prove2me | Definitions.Def_QAmpEst_Est_Setting
-- name    : QAmpEst_Est_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:56:17.32007+00:00
-- url     : https://prove2.me/theorems/b829b739-da7f-44c5-b02c-1654c3a0f48c
-- title:
--   §2 and §4, pp. 5–18 — S_χ, S₀, Q of (1) and Q(φ, ϕ) of (10), Ψ₁, Ψ₀, a, θ_a, Ψ± of (3), and the state and outcome law of Est_Amp(A, χ, M)
-- statement:
--   The amplitude-amplification setting of §2 and the algorithm $\mathbf{Est\_Amp}(\mathcal A,\chi,M)$ of §4.
--
--   Let $\mathcal H = \mathbb C^\iota$ have a finite computational basis $\{|x\rangle : x \in \iota\}$ with a distinguished zero state $|0\rangle$. Let $\mathcal A$ be a unitary matrix on $\mathcal H$ (a quantum algorithm without measurements) and let $\chi : \iota \to \{0,1\}$ be a Boolean function; a basis state $|x\rangle$ is *good* when $\chi(x) = 1$ and *bad* otherwise.
--
--   1. $\mathbf S_\chi$ maps $|x\rangle \mapsto -|x\rangle$ if $\chi(x) = 1$ and $|x\rangle \mapsto |x\rangle$ if $\chi(x) = 0$; $\mathbf S_0$ changes the sign of the amplitude of $|0\rangle$ only. The amplification operator (1) is
--   $$\mathbf Q = \mathbf Q(\mathcal A,\chi) = -\mathcal A\,\mathbf S_0\,\mathcal A^{-1}\,\mathbf S_\chi .$$
--   2. For real angles $\varphi, \phi$ (10), $\mathbf S_\chi(\phi)$ multiplies the amplitude of each good state by $e^{\imath\phi}$, $\mathbf S_0(\varphi)$ multiplies the amplitude of $|0\rangle$ by $e^{\imath\varphi}$, and $\mathbf Q(\mathcal A,\chi,\varphi,\phi) = -\mathcal A\,\mathbf S_0(\varphi)\,\mathcal A^{-1}\,\mathbf S_\chi(\phi)$.
--   3. $|\Psi\rangle = \mathcal A|0\rangle$ decomposes as $|\Psi\rangle = |\Psi_1\rangle + |\Psi_0\rangle$ into its projections on the good and bad subspaces. For any vector $|\Upsilon\rangle$, $a_\Upsilon = \langle \Upsilon_1|\Upsilon_1\rangle$ is the probability that measuring it gives a good state. The initial success probability is $a = \langle\Psi_1|\Psi_1\rangle$, and $\theta_a = \arcsin\sqrt a$, so that $\sin^2\theta_a = a$ and $0 \le \theta_a \le \pi/2$ (5).
--   4. For $0 < a < 1$, (3) defines
--   $$|\Psi_\pm\rangle = \frac{1}{\sqrt 2}\Big(\frac{1}{\sqrt a}|\Psi_1\rangle \pm \frac{\imath}{\sqrt{1-a}}|\Psi_0\rangle\Big).$$
--   5. $\mathbf{Est\_Amp}(\mathcal A,\chi,M)$ prepares $|0\rangle\mathcal A|0\rangle$ on $\mathbb C^M\otimes\mathcal H$, applies the unitary $(F_M^{-1}\otimes I)\,\Lambda_M(\mathbf Q)\,(F_M\otimes I)$, measures the first register, obtaining $y \in \{0,\dots,M-1\}$ with probability $\sum_{z}|\langle y, z|\text{final state}\rangle|^2$, and outputs $\tilde a = \sin^2(\pi y/M)$.
--
--   Everything in the mission's theorems is computed from $\mathcal A$, $\chi$, $|0\rangle$ and $M$ through these definitions; in particular $a$ is a function of $\mathcal A$ and $\chi$, not a free parameter.
--
--   **Formalization Note** The paper writes $\chi : \mathbb Z \to \{0,1\}$; a quantum register has finitely many basis states, so the label set is an arbitrary finite type $\iota$, and $\{0,1\}$ is `Bool`. $\mathcal A^{-1}$ is written as the conjugate transpose $\mathcal A^\dagger$, which equals the inverse whenever $\mathcal A$ is unitary; every theorem that uses $\mathbf Q$ assumes unitarity. $|\Psi_\pm\rangle$ are defined for every $a$, but are only meaningful (and only used) for $0 < a < 1$.
-- source:
--   arXiv:quant-ph/0005055v1, §2 p. 5 and (1); (3) and (5), p. 6; (10), p. 11; Algorithm Est_Amp, p. 18

import Mathlib
import Definitions.Def_QAmpEst_Est_Fourier

namespace QAmpEst.Est

open scoped Real Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `S_χ` (p. 5): `|x⟩ ↦ −|x⟩` if `χ(x) = 1`, `|x⟩ ↦ |x⟩` if `χ(x) = 0`. -/
def signGood (χ : ι → Bool) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun x => if χ x then -1 else 1)

/-- `S₀` (p. 5): changes the sign of the amplitude iff the state is the zero state `|z0⟩`. -/
def signZero (z0 : ι) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun x => if x = z0 then -1 else 1)

/-- The amplification operator `Q = Q(A, χ) = −A S₀ A⁻¹ S_χ` of (1), p. 5, with `A⁻¹` written
as the conjugate transpose `star A` (the two agree when `A` is unitary). -/
def Qop (A : Matrix ι ι ℂ) (χ : ι → Bool) (z0 : ι) : Matrix ι ι ℂ :=
  -(A * signZero z0 * star A * signGood χ)

/-- `S_χ(ϕ)` (p. 11): `|x⟩ ↦ e^{ıϕ}|x⟩` if `χ(x) = 1`, `|x⟩ ↦ |x⟩` if `χ(x) = 0`. -/
noncomputable def phaseGood (χ : ι → Bool) (ϕ : ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun x => if χ x then Complex.exp ((ϕ : ℂ) * Complex.I) else 1)

/-- `S₀(φ)` (p. 11): multiplies the amplitude by `e^{ıφ}` iff the state is `|z0⟩`. -/
noncomputable def phaseZero (z0 : ι) (φ : ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun x => if x = z0 then Complex.exp ((φ : ℂ) * Complex.I) else 1)

/-- The generalized operator `Q(A, χ, φ, ϕ) = −A S₀(φ) A⁻¹ S_χ(ϕ)` of (10), p. 11. -/
noncomputable def Qgen (A : Matrix ι ι ℂ) (χ : ι → Bool) (z0 : ι) (φ ϕ : ℝ) : Matrix ι ι ℂ :=
  -(A * phaseZero z0 φ * star A * phaseGood χ ϕ)

/-- `|Ψ⟩ = A|0⟩`, the state obtained by applying `A` to the zero state `|z0⟩`. -/
def initState (A : Matrix ι ι ℂ) (z0 : ι) : ι → ℂ :=
  A.mulVec (Pi.single z0 1)

/-- `|Υ₁⟩`: the projection of `v` onto the good subspace spanned by `{|x⟩ : χ(x) = 1}`. -/
def goodPart (χ : ι → Bool) (v : ι → ℂ) : ι → ℂ :=
  fun x => if χ x then v x else 0

/-- `|Υ₀⟩`: the projection of `v` onto the bad subspace spanned by `{|x⟩ : χ(x) = 0}`. -/
def badPart (χ : ι → Bool) (v : ι → ℂ) : ι → ℂ :=
  fun x => if χ x then 0 else v x

/-- `a_Υ = ⟨Υ₁|Υ₁⟩`: the probability that measuring `v` in the computational basis gives a
good state. -/
noncomputable def goodProb (χ : ι → Bool) (v : ι → ℂ) : ℝ :=
  ∑ x, if χ x then Complex.normSq (v x) else 0

/-- The initial success probability `a = ⟨Ψ₁|Ψ₁⟩` of `A` (p. 6, (5)). -/
noncomputable def succProb (A : Matrix ι ι ℂ) (χ : ι → Bool) (z0 : ι) : ℝ :=
  goodProb χ (initState A z0)

/-- The angle `θ_a = arcsin √a`, so that `sin²(θ_a) = a` and `0 ≤ θ_a ≤ π/2` for `0 ≤ a ≤ 1`
((5), p. 6). -/
noncomputable def theta (a : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt a)

/-- `|Ψ₊⟩ = (1/√2)((1/√a)|Ψ₁⟩ + (ı/√(1−a))|Ψ₀⟩)` of (3), p. 6 (meaningful for `0 < a < 1`). -/
noncomputable def psiPlus (A : Matrix ι ι ℂ) (χ : ι → Bool) (z0 : ι) : ι → ℂ :=
  fun x => (1 / Real.sqrt 2 : ℂ) *
    ((1 / Real.sqrt (succProb A χ z0) : ℂ) * goodPart χ (initState A z0) x +
      Complex.I * (1 / Real.sqrt (1 - succProb A χ z0) : ℂ) * badPart χ (initState A z0) x)

/-- `|Ψ₋⟩ = (1/√2)((1/√a)|Ψ₁⟩ − (ı/√(1−a))|Ψ₀⟩)` of (3), p. 6 (meaningful for `0 < a < 1`). -/
noncomputable def psiMinus (A : Matrix ι ι ℂ) (χ : ι → Bool) (z0 : ι) : ι → ℂ :=
  fun x => (1 / Real.sqrt 2 : ℂ) *
    ((1 / Real.sqrt (succProb A χ z0) : ℂ) * goodPart χ (initState A z0) x -
      Complex.I * (1 / Real.sqrt (1 - succProb A χ z0) : ℂ) * badPart χ (initState A z0) x)

/-- Step 1 of `Est_Amp(A, χ, M)` (p. 18): the two-register state `|0⟩ A|0⟩`. -/
def estAmpInput (M : ℕ) (A : Matrix ι ι ℂ) (z0 : ι) : Fin M × ι → ℂ :=
  fun p => if (p.1 : ℕ) = 0 then initState A z0 p.2 else 0

/-- The state of `Est_Amp(A, χ, M)` after step 4 (p. 18):
`(F_M⁻¹ ⊗ I) Λ_M(Q) (F_M ⊗ I)` applied to `|0⟩ A|0⟩`, with `Q = −A S₀ A⁻¹ S_χ` and
`F_M = ShorAlgorithms.Shared.fourierMatrix M`. -/
noncomputable def estAmpState (M : ℕ) (A : Matrix ι ι ℂ) (χ : ι → Bool) (z0 : ι) :
    Fin M × ι → ℂ :=
  ((qftInv M ⊗ₖ (1 : Matrix ι ι ℂ)) * ctrlPow M (Qop A χ z0) *
      (ShorAlgorithms.Shared.fourierMatrix M ⊗ₖ (1 : Matrix ι ι ℂ))).mulVec (estAmpInput M A z0)

/-- Step 5 of `Est_Amp(A, χ, M)`: the probability that measuring the first register of the
final state gives `y` (the second register is summed out). -/
noncomputable def outcomeProb (M : ℕ) (A : Matrix ι ι ℂ) (χ : ι → Bool) (z0 : ι) (y : Fin M) :
    ℝ :=
  ∑ z, Complex.normSq (estAmpState M A χ z0 (y, z))

/-- Step 6 of `Est_Amp(A, χ, M)`: the output `ã = sin²(π y / M)` on outcome `y`. -/
noncomputable def estimate (M : ℕ) (y : Fin M) : ℝ :=
  Real.sin (π * ((y : ℕ) : ℝ) / (M : ℝ)) ^ 2

end QAmpEst.Est


