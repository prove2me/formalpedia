-- Prove2me | Definitions.Def_DeFinettiSDP_Hierarchy_Distortion
-- name    : DeFinettiSDP_Hierarchy_Distortion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:39.586779+00:00
-- url     : https://prove2.me/theorems/d4f6948f-efb6-451e-9a77-a161e52bc1ed
-- title:
--   Eqs. (9)–(10), p. 6, and Lemma D.1, p. 29 — state two-designs, f(A,B) and f(B|·)
-- statement:
--   This file defines state two-designs and the two minimal distortions of §2.4.
--
--   1. **Swap and symmetric projector.** $F$ is the swap operator on $B\otimes B$, $F(|i\rangle\otimes|j\rangle)=|j\rangle\otimes|i\rangle$, and $P^{\mathrm{sym}}=\tfrac12(\mathbb 1+F)$ is the projector onto the symmetric subspace of $B\otimes B$.
--   2. **State two-design** (Lemma D.1, p. 29). A family $\{P_z\}_{z=1}^t$ of rank-one projectors $P_z=|\psi_z\rangle\langle\psi_z|$ ($\|\psi_z\|=1$) on a $d$-dimensional system with
--   $$\frac1t\sum_{z=1}^t P_z\otimes P_z=\frac{2P^{\mathrm{sym}}}{d(d+1)}.$$
--   Its measurement $\mathcal M_B$ has effects $\frac{d}{t}P_z$.
--   3. **Distortion with side information** of a measurement $\mathcal M_B$: the supremum, over all finite-dimensional systems $A$ and all Hermitian $\xi_{AB}$ with $\xi_A=\mathrm{Tr}_B\,\xi_{AB}=0$ and $\xi_B=\mathrm{Tr}_A\,\xi_{AB}=0$, of $\|\xi_{AB}\|_1/\|(\mathcal I_A\otimes\mathcal M_B)(\xi_{AB})\|_1$.
--   4. **Minimal distortion with side information** (10):
--   $$f(B|\cdot)=\inf_{\mathcal M_B}\ \sup_{\substack{\xi_{AB}^\dagger=\xi_{AB}\\ \xi_A=0,\ \xi_B=0}}\frac{\|\xi_{AB}\|_1}{\|(\mathcal I_A\otimes\mathcal M_B)(\xi_{AB})\|_1},$$
--   the infimum over all measurements on $B$ (any finite number of outcomes) and the supremum also over all finite-dimensional $A$.
--   5. **Minimal distortion** (9) for the bipartite system $A\otimes B$:
--   $$f(A,B)=\inf_{\mathcal M_A,\mathcal M_B}\ \max_{\substack{\xi_{AB}^\dagger=\xi_{AB}\\ \xi_A=0,\ \xi_B=0}}\frac{\|\xi_{AB}\|_1}{\|(\mathcal M_A\otimes\mathcal M_B)(\xi_{AB})\|_1},$$
--   the infimum over product measurements.
--
--   These quantities measure how much trace-norm distinguishability an informationally complete measurement loses; they are the constants in the de Finetti theorem with linear constraints.
--
--   **Formalization Note** Both distortions take values in $[0,\infty]$ (`ℝ≥0∞`): a ratio with a vanishing denominator and a nonzero numerator is $+\infty$ (a measurement that is not informationally complete), and $0/0=0$ (only for $\xi=0$, which does not affect the supremum). The page's "max" in (9) is written as a supremum. $P^{\mathrm{sym}}$ is given by its standard formula $(\mathbb 1+F)/2$.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, §2.4, p. 6, eqs. (9) and (10); App. D, Lemma D.1, p. 29

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_DeFinettiSDP_Hierarchy_Systems

/-!
Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, §2.4 (p. 6, equations (9) and (10)) and
Appendix D (Lemma D.1, p. 29): state two-designs, their measurement, and the minimal distortions
`f(A,B)` and `f(B|·)`.
-/

namespace DeFinettiSDP.Hierarchy

open Matrix
open scoped Kronecker ComplexOrder

/-- The swap operator `F` on `B ⊗ B` (§2.1): `F (|i⟩ ⊗ |j⟩) = |j⟩ ⊗ |i⟩`. -/
def swapMat (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- The projector onto the symmetric subspace of `B ⊗ B`, by the standard formula
`P^sym = (1 + F)/2`. -/
noncomputable def Psym (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1 / 2 : ℂ) • (1 + swapMat d)

/-- A state two-design on a `d`-dimensional system `B` (Lemma D.1, p. 29): a family
`{P_z}_{z ∈ {1,…,t}}` of rank-one projectors `P_z = |ψ_z⟩⟨ψ_z|` (unit vectors `ψ_z`) with
`(1/t) ∑_z P_z ⊗ P_z = 2 P^sym / (d (d+1))`. -/
def IsStateTwoDesign {d t : ℕ} (P : Fin t → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ z, ∃ ψ : Fin d → ℂ, ∑ i, ‖ψ i‖ ^ 2 = 1 ∧ P z = Matrix.vecMulVec ψ (star ψ)) ∧
    (1 / (t : ℂ)) • ∑ z, P z ⊗ₖ P z = (2 / ((d : ℂ) * ((d : ℂ) + 1))) • Psym d

/-- The measurement of Lemma D.1: `M_B(X) = ∑_z (d_B/t) Tr[P_z X] |z⟩⟨z|`, i.e. the effects
`(d_B/t) P_z`. -/
noncomputable def designMeas {d t : ℕ} (P : Fin t → Matrix (Fin d) (Fin d) ℂ) :
    Fin t → Matrix (Fin d) (Fin d) ℂ :=
  fun z => ((d : ℂ) / (t : ℂ)) • P z

/-- The distortion with side information of a family `M` of operators on `B`: the supremum over
all finite dimensions `dA` and all Hermitian `ξ` on `A ⊗ B` with `ξ_A = Tr_B ξ = 0` and
`ξ_B = Tr_A ξ = 0` of `‖ξ‖₁ / ‖(I_A ⊗ M_B)(ξ)‖₁`. The ratio is computed in `ℝ≥0∞`
(`x / 0 = ⊤` for `x > 0`, and `0 / 0 = 0`). -/
noncomputable def distortion {dB t : ℕ} (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ) : ENNReal :=
  ⨆ (dA : ℕ) (ξ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (_ : ξ.IsHermitian)
    (_ : WildeQIT.partialTraceRight ξ = 0) (_ : WildeQIT.partialTraceLeft ξ = 0),
    ENNReal.ofReal (WildeQIT.traceNorm ξ) / ENNReal.ofReal (WildeQIT.traceNorm (measB M ξ))

/-- The minimal distortion with side information `f(B|·)` of equation (10), p. 6: the infimum
of `distortion M` over all measurements `M` on `B` (any finite number of outcomes). -/
noncomputable def fBside (dB : ℕ) : ENNReal :=
  ⨅ (t : ℕ) (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ) (_ : IsPOVM M), distortion M

/-- The minimal distortion `f(A,B)` of equation (9), p. 6: the infimum over product
measurements `M_A ⊗ M_B` on `A ⊗ B` of the supremum over Hermitian `ξ` on `A ⊗ B` with
`ξ_A = 0`, `ξ_B = 0` of `‖ξ‖₁ / ‖(M_A ⊗ M_B)(ξ)‖₁`, in `ℝ≥0∞`. -/
noncomputable def fAB (dA dB : ℕ) : ENNReal :=
  ⨅ (tA : ℕ) (tB : ℕ) (MA : Fin tA → Matrix (Fin dA) (Fin dA) ℂ)
    (MB : Fin tB → Matrix (Fin dB) (Fin dB) ℂ) (_ : IsPOVM MA) (_ : IsPOVM MB),
    ⨆ (ξ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (_ : ξ.IsHermitian)
      (_ : WildeQIT.partialTraceRight ξ = 0) (_ : WildeQIT.partialTraceLeft ξ = 0),
      ENNReal.ofReal (WildeQIT.traceNorm ξ) /
        ENNReal.ofReal (WildeQIT.traceNorm (measAB MA MB ξ))

end DeFinettiSDP.Hierarchy


