-- Prove2me | Definitions.Def_QRepeaterBench_Dephasing_Model
-- name    : QRepeaterBench_Dephasing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:49.871381+00:00
-- url     : https://prove2.me/theorems/54ab0fcd-3e77-471c-b9d5-cd9c46594acf
-- title:
--   Phase operator Z, binomial weights P_m(p,d), the qudit dephasing channel P_d, its Choi matrix, H(P), I_C, I_RC, the flux Φ and σ̃ (Eqs. (21), (23), (38)–(43), (67), (89)–(92))
-- statement:
--   This file fixes the objects of the qudit dephasing benchmark of Pirandola and Laurenza.
--
--   Let $d\ge 2$ and let $\{|j\rangle\}_{j=0}^{d-1}$ be the computational basis of a qudit. Put $\omega=e^{2\pi i/d}$ and let $Z$ be the **generalized phase operator**, $Z|j\rangle=\omega^j|j\rangle$ (Eq. (23)). For a dephasing probability $p\in[0,1]$ the **binomial weights** are
--
--   $$P_m(p,d)=\binom{d-1}{m}p^m(1-p)^{d-1-m},\qquad m=0,\dots,d-1,$$
--
--   and the **generalized dephasing channel** is given by its Kraus form (Eq. (89))
--
--   $$\mathcal P_d(\rho)=\sum_{m=0}^{d-1}E_m\rho E_m^\dagger,\qquad E_m=\sqrt{P_m(p,d)}\,Z^m .$$
--
--   For a map $\mathcal E$ on $d\times d$ matrices, the **Choi matrix** is $\rho_{\mathcal E}=(\mathcal I\otimes\mathcal E)(\Psi_d)$, where $\Psi_d=|\Psi_d\rangle\langle\Psi_d|$ and $|\Psi_d\rangle=d^{-1/2}\sum_{i}|ii\rangle$; the first factor is the untouched reference $R$, the second the channel output $B$.
--
--   The **Shannon entropy** of a weight vector is $H(\mathbf P)=-\sum_m P_m\log_2 P_m$ with $0\log 0=0$. With the von Neumann entropy $S$ in bits, the **coherent information** and the **reverse coherent information** of the channel are (Eqs. (38)–(43))
--
--   $$I_C(\mathcal E)=S(\mathrm{Tr}_R\,\rho_{\mathcal E})-S(\rho_{\mathcal E}),\qquad I_{RC}(\mathcal E)=S(\mathrm{Tr}_B\,\rho_{\mathcal E})-S(\rho_{\mathcal E}).$$
--
--   The **entanglement flux** is the relative entropy of entanglement of the Choi matrix, $\Phi(\mathcal E)=E_R(\rho_{\mathcal E})=\inf_{\sigma\in\mathrm{SEP}}S(\rho_{\mathcal E}\|\sigma)$, the infimum over all separable states for the cut $R:B$, with the relative entropy $S(\rho\|\sigma)=\mathrm{Tr}[\rho(\log_2\rho-\log_2\sigma)]$ equal to $+\infty$ when the support of $\rho$ is not contained in that of $\sigma$.
--
--   Finally, the separable candidate state of Eq. (92) is
--
--   $$\tilde\sigma=\sum_{i=0}^{d-1}\frac1d\,|i\rangle\langle i|\otimes\mathcal P_d(|i\rangle\langle i|).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Qudit indices are `Fin d`; $Z^m$ is a matrix power. The channel is the published `QAlgorithms.krausApply` of the Kraus family above, the Choi matrix is the published `QAlgorithms.idTensorSuperop` applied to the published `maximallyEntangledProjector d` (so it is computed from the channel, never from a closed form), the partial traces are `QAlgorithms.traceLeft` (over the reference) and `QAlgorithms.traceRight` (over the output), the von Neumann entropy is `QAlgorithms.vnEntropy` (bits, via the functional calculus), and $E_R$ is the published `relativeEntanglement` (bits, values in $[0,\infty]$, infimum over `IsSeparableDensity`). Outside $p\in[0,1]$ the real square root clips negative weights to $0$; every statement assumes $0\le p\le 1$.
-- source:
--   Pirandola & Laurenza, General Benchmarks for Quantum Repeaters, arXiv:1512.04945v2, pp. 2, 5–7, 10–11, Eqs. (21), (23), (38)–(43), (67), (89)–(92)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

noncomputable section

open scoped Matrix ENNReal

namespace QRepeaterBench.Dephasing

/-- Eq. (23), p. 6: the primitive `d`-th root of unity `ω = exp(i2π/d)`. -/
def omega (d : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (d : ℂ))

/-- Eq. (23), p. 6: the generalized phase operator `Z|j⟩ = ω^j |j⟩` on a qudit with
computational basis `{|j⟩}`, `j ∈ Z_d = {0, …, d − 1}` (here `Fin d`). -/
def Zop (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun j => omega d ^ (j : ℕ)

/-- Eq. (90), p. 11: the binomial weight `P_m(p, d) = C(d−1, m) p^m (1 − p)^{d−1−m}`,
`m ∈ {0, …, d − 1}`. Lean's `0 ^ 0 = 1` gives the correct weights at `p ∈ {0, 1}`. -/
def weight (d : ℕ) (p : ℝ) (m : Fin d) : ℝ :=
  ((d - 1).choose (m : ℕ) : ℝ) * p ^ (m : ℕ) * (1 - p) ^ (d - 1 - (m : ℕ))

/-- Eq. (89), p. 11: the Kraus operators `E_m = √(P_m(p, d)) Z^m` (matrix power). -/
def krausOp (d : ℕ) (p : ℝ) (m : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  ((Real.sqrt (weight d p m) : ℝ) : ℂ) • Zop d ^ (m : ℕ)

/-- Eq. (89), p. 11: the generalized dephasing channel in Kraus form,
`P_d(ρ) = Σ_{m=0}^{d−1} E_m ρ E_m^†`, through the published `QAlgorithms.krausApply`. -/
def dephasing (d : ℕ) (p : ℝ) : QAlgorithms.Superop (Fin d) (Fin d) :=
  QAlgorithms.krausApply (krausOp d p)

/-- Eq. (21), p. 5 and p. 11: the Choi matrix `ρ_E = (I ⊗ E)(Ψ_d)` of a map `E` on qudit
operators, with `Ψ_d = |Ψ_d⟩⟨Ψ_d|`, `|Ψ_d⟩ = d^{−1/2} Σ_i |ii⟩`. The first factor is the
reference `R` (untouched), the second the channel output `B`. Computed from `E` by the
published `QAlgorithms.idTensorSuperop` applied to the published projector
`maximallyEntangledProjector d` (entries `1/d` on `|ii⟩⟨jj|`). -/
def choi (d : ℕ) (E : QAlgorithms.Superop (Fin d) (Fin d)) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  QAlgorithms.idTensorSuperop (R := Fin d) E
    (QAlgorithms.Papers.Independent.Information100.P54.maximallyEntangledProjector d)

/-- Eq. (91), p. 11 and p. 10: the Shannon entropy in bits,
`H(P) = −Σ_m P_m log₂ P_m`, with `0 log 0 = 0` (`Real.negMulLog 0 = 0`). -/
def shannonEntropy {ι : Type*} [Fintype ι] (P : ι → ℝ) : ℝ :=
  ∑ m, Real.negMulLog (P m) / Real.log 2

/-- Eqs. (38), (42), p. 7: the coherent information of the channel,
`I_C(E) = S(ρ_B) − S(ρ_RB)` evaluated on the Choi matrix `ρ_RB = ρ_E`, where
`ρ_B = Tr_R ρ_E` (partial trace over the first factor, `QAlgorithms.traceLeft`) and `S` is the
published von Neumann entropy in bits `QAlgorithms.vnEntropy`. -/
def coherentInfo (d : ℕ) (E : QAlgorithms.Superop (Fin d) (Fin d)) : ℝ :=
  QAlgorithms.vnEntropy (QAlgorithms.traceLeft (choi d E)) - QAlgorithms.vnEntropy (choi d E)

/-- Eqs. (40), (43), p. 7: the reverse coherent information of the channel,
`I_RC(E) = S(ρ_R) − S(ρ_RB)` on the Choi matrix, `ρ_R = Tr_B ρ_E` (partial trace over the second
factor, `QAlgorithms.traceRight`). -/
def reverseCoherentInfo (d : ℕ) (E : QAlgorithms.Superop (Fin d) (Fin d)) : ℝ :=
  QAlgorithms.vnEntropy (QAlgorithms.traceRight (choi d E)) - QAlgorithms.vnEntropy (choi d E)

/-- p. 2 and Eq. (67), p. 10: the entanglement flux `Φ(E) := E_R(ρ_E)`, the relative entropy of
entanglement (bits, infimum over all separable states for the reference : output cut, `+∞` off
support) of the Choi matrix — the published P54 `relativeEntanglement`. -/
def flux (d : ℕ) [NeZero d] (E : QAlgorithms.Superop (Fin d) (Fin d)) : ℝ≥0∞ :=
  QAlgorithms.Papers.Independent.Information100.P54.relativeEntanglement (choi d E)

/-- Eq. (92), p. 11: the separable state `σ̃ = Σ_{i=0}^{d−1} (1/d) |i⟩⟨i| ⊗ P_d(|i⟩⟨i|)`,
computed from the channel (not from its closed form). -/
def sigmaTilde (d : ℕ) (p : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∑ i : Fin d, ((d : ℂ)⁻¹) •
    Matrix.kronecker (Matrix.single i i (1 : ℂ)) (dephasing d p (Matrix.single i i (1 : ℂ)))

/-! ### Sanity checks -/

example (d : ℕ) : Zop d = Matrix.diagonal fun j : Fin d => omega d ^ (j : ℕ) := rfl

example (p : ℝ) : weight 1 p 0 = 1 := by simp [weight]

example : shannonEntropy (fun _ : Fin 1 => (1 : ℝ)) = 0 := by simp [shannonEntropy]

example (d : ℕ) (E : QAlgorithms.Superop (Fin d) (Fin d)) (i k j l : Fin d) :
    choi d E (i, k) (j, l) =
      E (QAlgorithms.Papers.Independent.Information100.P54.maximallyEntangledProjector d
        |>.submatrix (fun a => (i, a)) (fun b => (j, b))) k l := rfl

end QRepeaterBench.Dephasing


