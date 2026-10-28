-- Prove2me | Definitions.Def_QPurityAmp_Choi_Model
-- name    : QPurityAmp_Choi_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:41.477283+00:00
-- url     : https://prove2.me/theorems/792cc5d1-a49e-4f4c-87ec-cf997d9b653d
-- title:
--   Def. I.1, SDP (1), Eq. (S22), Lemma S2.3, pp. 2–3, 19 — depolarized states, the Haar cost matrices C and C′, Choi feasibility, fidelity, the projection P, the mixed representation
-- statement:
--   This module fixes the quantum purity amplification (QPA) problem of Li, Fu, Isogawa, Silva and Chuang for $n$ depolarized copies of an unknown pure qudit state.
--
--   Let $W=\mathbb C^d$. The **output register** is $W$ and the $n$ **input registers** are $W^{\otimes n}$; an operator on $\mathrm{out}\otimes\mathrm{in}$ is a matrix indexed by pairs $(a,x)$ with $a\in\{0,\dots,d-1\}$ and $x\in\{0,\dots,d-1\}^n$, output first. The partial traces $\mathrm{tr}_{\mathrm{out}}$ and $\mathrm{tr}_{\mathrm{in}}$ are the published ones (Wilde, Definition 4.3.4).
--
--   1. **States.** For $\psi\in W$, $\sigma=|\psi\rangle\langle\psi|$. For $\lambda\in\mathbb R$ the **depolarized state** is
--   $$\mathcal D_\lambda(\sigma)=(1-\lambda)\,\sigma+\lambda\,\frac{\mathbb I_d}{d}.$$
--   2. **Haar averages.** For a matrix-valued function $F$ on the unitary group $U(d)$, $\int F(U)\,dU$ is taken entrywise against the probability Haar measure on $U(d)$. The Haar-random pure state is $\sigma_U=U|0\rangle\langle 0|U^\dagger$ and $\rho_U=\mathcal D_\lambda(\sigma_U)$.
--   3. **Cost matrices.** The cost matrix of p. 2 and the modified cost matrix of Eq. (S22) are
--   $$C=\int \sigma_U^{\top}\otimes\rho_U^{\otimes n}\,dU,\qquad C'=-\int (\rho_U^{\top})^{-1}\otimes\rho_U^{\otimes n}\,dU .$$
--   4. **Feasibility and optimality.** $T$ is **feasible** (the Choi matrix of a channel from the input registers to the output register, SDP (1)) if $T\succeq 0$ and $\mathrm{tr}_{\mathrm{out}}T=\mathbb I_{\mathrm{in}}$. $T_0$ is **optimal for the cost $K$** if it is feasible and $\mathrm{Re}\,\mathrm{tr}(KT)\le\mathrm{Re}\,\mathrm{tr}(KT_0)$ for every feasible $T$. The SDP (1) of the paper, maximize $\mathrm{tr}(C^\top T)$, is optimality for $K=C^\top$.
--   5. **Channel of a Choi matrix and fidelity.** $\Phi_T(X)=\mathrm{tr}_{\mathrm{in}}\big(T(\mathbb I_{\mathrm{out}}\otimes X^\top)\big)$. The fidelity of a protocol $\Phi$ at $\psi$ is
--   $$F_\Phi(\psi)=\mathrm{Re}\,\langle\psi|\,\Phi\big(\mathcal D_\lambda(|\psi\rangle\langle\psi|)^{\otimes n}\big)\,|\psi\rangle .$$
--   6. **The projection of Lemma S2.3.** $P(X)=X-\frac{\mathbb I_d}{d}\otimes\mathrm{tr}_{\mathrm{out}}X$.
--   7. **The mixed representation.** $R(A)=\bar A\otimes A^{\otimes n}$, the covariance group $U^*_{\mathrm{out}}\otimes U_{\mathrm{in}}$ of p. 3.
--
--   These objects state the SDP whose optimum Theorem II.1 identifies, and the cost-matrix replacement $C\to C'$ used in its proof.
--
--   **Formalization Note** The Haar integral is entrywise, so no norm on matrices is chosen; all integrands are continuous on the compact group, hence integrable. $(\rho^\top)^{-1}$ is Mathlib's matrix inverse, which returns $0$ on a singular matrix; $\rho_U$ is invertible whenever $0<\lambda<1$, the paper's range, which every theorem using $C'$ assumes. The ordering $\mathrm{out}\otimes\mathrm{in}$ and the Choi convention $\Phi_T(X)=\mathrm{tr}_{\mathrm{in}}(T(\mathbb I\otimes X^\top))$ make $F_\Phi$ averaged over $\psi$ equal to $\mathrm{tr}(C^\top T_\Phi)$, as on p. 2.
-- source:
--   Li, Fu, Isogawa, Silva and Chuang, Optimal Quantum Purity Amplification, arXiv:2409.18167v4, p. 2, Definition I.1 and the figure of merit; p. 3, Eq. (1); p. 18, Eq. (S16); p. 19, Eq. (S22) and Lemma S2.3

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_Channel
noncomputable section

namespace QPurityAmp.Choi

open scoped Matrix Kronecker ComplexOrder

/-! Li, Fu, Isogawa, Silva and Chuang, *Optimal Quantum Purity Amplification*,
arXiv:2409.18167v4, pp. 2–3 (Definition I.1, the figure of merit, SDP (1)) and pp. 19–20
(Eq. (S22), Lemmas S2.3–S2.4).

Registers: the output register is `Fin d` (W = ℂ^d), the `n` input registers are
`Fin n → Fin d` (W^{⊗n}); a joint operator is indexed by `Fin d × (Fin n → Fin d)`, output
first (the paper's `C_{out,in}`). The partial traces are the published
`WildeQIT.partialTraceLeft` (= tr_out) and `WildeQIT.partialTraceRight` (= tr_in). -/

/-- The pure state σ = |ψ⟩⟨ψ| of a vector ψ ∈ ℂ^d (p. 2). -/
def pureProj {d : ℕ} (psi : EuclideanSpace ℂ (Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec (WithLp.ofLp psi) (star (WithLp.ofLp psi))

/-- The depolarized state D_λ(σ) = (1 − λ)σ + λ I_d / d (p. 2). -/
def depol (d : ℕ) (lam : ℝ) (sigma : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ((1 - lam : ℝ) : ℂ) • sigma + ((lam / d : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)

/-- Entrywise integral of a matrix-valued function of a unitary U ∈ U(d) against the
published probability Haar measure `QAlgorithms.Schur.unitaryHaar d`. -/
def haarInt {d : ℕ} {ι : Type} (F : Matrix.unitaryGroup (Fin d) ℂ → Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  Matrix.of fun i j => ∫ U, F U i j ∂(QAlgorithms.Schur.unitaryHaar d)

/-- The Haar-random pure state σ_U = U|0⟩⟨0|U† (p. 2: "averaging σ over a Haar-random prior
on W"). -/
def haarState {d : ℕ} [NeZero d] (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec ((U : Matrix (Fin d) (Fin d) ℂ) *ᵥ Pi.single 0 1)
    (star ((U : Matrix (Fin d) (Fin d) ℂ) *ᵥ Pi.single 0 1))

/-- The cost matrix C_{out,in} = ∫ σᵀ_out ⊗ ρ^{⊗n}_in with ρ = D_λ(σ) (p. 2). -/
def cost (d n : ℕ) [NeZero d] (lam : ℝ) :
    Matrix (Fin d × (Fin n → Fin d)) (Fin d × (Fin n → Fin d)) ℂ :=
  haarInt fun U => (haarState U)ᵀ ⊗ₖ QAlgorithms.piKron n (depol d lam (haarState U))

/-- The modified cost matrix C′ = −∫ (ρ^{⊤})^{−1} ⊗ ρ^{⊗n} of Eq. (S22), p. 19, with
ρ = D_λ(σ_U). (`⁻¹` is Mathlib's matrix inverse; ρ is invertible for 0 < λ < 1.) -/
def costPrime (d n : ℕ) [NeZero d] (lam : ℝ) :
    Matrix (Fin d × (Fin n → Fin d)) (Fin d × (Fin n → Fin d)) ℂ :=
  -haarInt fun U =>
    ((depol d lam (haarState U))ᵀ)⁻¹ ⊗ₖ QAlgorithms.piKron n (depol d lam (haarState U))

/-- Feasibility in the SDP (1), p. 3: T ⪰ 0 and tr_out T = I_in (T is the Choi matrix of a
channel from the input registers to the output register). -/
def IsChoiFeasible {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : Matrix (Fin d × ι) (Fin d × ι) ℂ) : Prop :=
  T.PosSemidef ∧ WildeQIT.partialTraceLeft T = 1

/-- `T₀` is an optimal solution of the SDP "maximize Re tr(C T) subject to T ⪰ 0,
tr_out T = I". The SDP (1) of p. 3 is `IsOptimal Cᵀ`. -/
def IsOptimal {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (C T₀ : Matrix (Fin d × ι) (Fin d × ι) ℂ) : Prop :=
  IsChoiFeasible T₀ ∧
    ∀ T : Matrix (Fin d × ι) (Fin d × ι) ℂ, IsChoiFeasible T →
      (C * T).trace.re ≤ (C * T₀).trace.re

/-- The channel whose Choi matrix is T: Φ_T(X) = tr_in(T (I_out ⊗ Xᵀ)). -/
def choiChannel {d : ℕ} {ι : Type} [Fintype ι]
    (T : Matrix (Fin d × ι) (Fin d × ι) ℂ) : QAlgorithms.Superop ι (Fin d) :=
  fun X => WildeQIT.partialTraceRight (T * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Xᵀ))

/-- The fidelity tr(σ Φ(ρ^{⊗n})) = ⟨ψ|Φ(D_λ(σ)^{⊗n})|ψ⟩ of a protocol Φ at the pure state
σ = |ψ⟩⟨ψ| (Definition I.1 and the figure of merit, p. 2). -/
def fidelity {d : ℕ} (n : ℕ) (Phi : QAlgorithms.Superop (Fin n → Fin d) (Fin d)) (lam : ℝ)
    (psi : EuclideanSpace ℂ (Fin d)) : ℝ :=
  (star (WithLp.ofLp psi) ⬝ᵥ
    (Phi (QAlgorithms.piKron n (depol d lam (pureProj psi))) *ᵥ WithLp.ofLp psi)).re

/-- The projection P = Id − (I/d) ⊗ tr_out of Lemma S2.3, p. 19, acting on operators on
V_out ⊗ V_in. -/
def projP {d : ℕ} {ι : Type} [Fintype ι]
    (X : Matrix (Fin d × ι) (Fin d × ι) ℂ) : Matrix (Fin d × ι) (Fin d × ι) ℂ :=
  X - ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ WildeQIT.partialTraceLeft X

/-- The mixed representation R(A) = Ā ⊗ A^{⊗n} on out ⊗ in: the covariance group
U*_out ⊗ U_in of p. 3 (Ā is the entrywise complex conjugate). -/
def mixedRep {d : ℕ} (n : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin n → Fin d)) (Fin d × (Fin n → Fin d)) ℂ :=
  A.map star ⊗ₖ QAlgorithms.piKron n A

end QPurityAmp.Choi


