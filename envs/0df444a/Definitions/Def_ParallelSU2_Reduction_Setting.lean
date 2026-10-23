-- Prove2me | Definitions.Def_ParallelSU2_Reduction_Setting
-- name    : ParallelSU2_Reduction_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:34.426889+00:00
-- url     : https://prove2.me/theorems/cb654aee-c61f-44e9-98cf-320ee5f1baed
-- title:
--   SU(2) parallel-estimation model: Weyl characters, the irrep family H_2, …, H_2d, Hayashi's seed, the pointwise error, the corrected (14) and v(x) (pp. 2–9)
-- statement:
--   This file fixes the objects of Hayashi's reference-assisted estimation of an unknown $g\in\mathrm{SU}(2)$ from $n=2d-1$ uses.
--
--   1. **Weyl character.** For $j\in\mathbb N$ and $g\in\mathrm{SU}(2)$ with eigenvalues $e^{\pm i\theta/2}$,
--   $$\chi_j(g)=\sum_{l=1}^{j} e^{i(l-\frac{j+1}{2})\theta}=\frac{\sin(j\theta/2)}{\sin(\theta/2)}=U_{j-1}\!\Big(\tfrac{\operatorname{Re}\operatorname{Tr} g}{2}\Big),$$
--   where $U_m$ is the Chebyshev polynomial of the second kind ($U_{-1}=0$). It is the character of the $j$-dimensional irreducible representation $V^j$ (p. 9).
--   2. **Spin family.** A family $D_0,\dots,D_{d-1}$ of continuous unitary irreducible representations of $\mathrm{SU}(2)$ is a *spin family* if $D_k$ has dimension $2(k+1)$ and $\operatorname{Tr} D_k(g)=\chi_{2(k+1)}(g)$ for all $g$; $D_k$ is the paper's $V^{2(k+1)}$ on $\mathcal H_{2(k+1)}$.
--   3. **Reference-assisted space.** The space is $\bigoplus_{k}\mathcal H_{2k}\otimes\mathcal H_{2k,R}$ with action $U_g=\bigoplus_k V^{2k}_g\otimes I$ (the published `canonicalAction`). The input for a coefficient vector $x\in\mathbb C^d$ is $\bigoplus_k x_k\,x^{2k}_E$ with $x^{2k}_E=\operatorname{vec}(I)/\sqrt{2k}$ maximally entangled (the published `canonicalInput` with identity block unitaries).
--   4. **Seed.** With $e_k=(2k)x^{2k}_E=\sqrt{2k}\operatorname{vec}(I)$ placed in block $k$, Hayashi's seed for a matrix $T=(t_{k,l})$ is
--   $$\Xi_T=\sum_{k,l} t_{k,l}\,|e_k\rangle\langle e_l|,$$
--   and $M^T(d\hat g)=U_{\hat g}\,\Xi_T\,U_{\hat g}^\dagger\,\mu(d\hat g)$ (p. 8).
--   5. **Pointwise error.** For a measurement with operator density $M(\hat g)$ with respect to a reference measure, a cost $c(\hat g,g)$ and a state $\rho$, the error at the true value $g$ is
--   $$\mathcal D_g=\int c(\hat g,g)\,\operatorname{Re}\operatorname{Tr}\big[M(\hat g)\,U_g\rho U_g^\dagger\big]\,d\hat g$$
--   (p. 6). The cost used is $d(g,\hat g)=1-|\operatorname{Tr}(g^{-1}\hat g)/2|^2$ (pp. 2–3, the published `bellCost`).
--   6. **Error formula (14), corrected.**
--   $$E(x,T)=\tfrac12\sum_{k}|x_k|^2\operatorname{Re}t_{k,k}-\tfrac14\sum_{k=1}^{d-1}\operatorname{Re}\big(\overline{x_k}x_{k+1}t_{k,k+1}+\overline{x_{k+1}}x_kt_{k+1,k}\big).$$
--   7. **Method value.** $v(x)=\tfrac12\big(1-\sum_{k=1}^{d-1}|x_k||x_{k+1}|\big)$ (eqs. (10), (14)).
--   8. **Phase-aligned matrix.** $t_{k,l}=\phi(x_k)\overline{\phi(x_l)}$ with $\phi(z)=z/|z|$ and $\phi(0)=1$ (eq. (9), corrected).
--
--   These objects make the reduction of SU(2) estimation to Bužek's phase-estimation problem expressible in a single model.
--
--   **Formalization Note** Irreducible representations are indexed $k=0,\dots,d-1$ for the paper's $\mathcal H_2,\dots,\mathcal H_{2d}$. The character hypothesis is a true property of every such irrep (Weyl's character formula), and is what the paper uses on p. 9. In (14) the paper writes $\overline{x_{k-1}}x_kt_{k,k-1}$; with $\operatorname{Tr}M\rho=\sum t_{k,l}\overline{x_k}x_l$ the correct pairing is $t_{k-1,k}$, which is what $E$ uses (and $x_0:=0$). The sums over adjacent pairs run over $k,l$ with $l=k+1$, avoiding natural-number subtraction.
-- source:
--   Hayashi, Parallel Treatment of Estimation of SU(2) and Phase Estimation, arXiv:quant-ph/0407053v3, pp. 2–3 (cost), p. 5 (eqs. (9), (10)), pp. 6–7 (model, D_g), p. 8 (M^T, eq. (14)), p. 9 (characters)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36
open MeasureTheory
open scoped ComplexConjugate

namespace ParallelSU2.Reduction

/-- The group SU(2) of 2×2 complex unitary matrices of determinant one (Hayashi p. 6). -/
abbrev SU2 : Type := ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)

/-- Hayashi p. 9: the Weyl character of the `j`-dimensional irreducible representation of
SU(2), `Tr V^j_g = ∑_{l=1}^j e^{i(l-(j+1)/2)θ}` where `e^{±iθ/2}` are the eigenvalues of `g`.
Since `Tr g = 2 cos(θ/2)`, this equals `sin(jθ/2)/sin(θ/2) = U_{j-1}(Re Tr g / 2)`, with `U` the
Chebyshev polynomial of the second kind. At `j = 0` it is `U_{-1} = 0`. -/
noncomputable def weylCharacter (j : ℕ) (g : SU2) : ℝ :=
  (Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)).eval
    (((g : Matrix (Fin 2) (Fin 2) ℂ).trace).re / 2)

/-- Hayashi pp. 6–7, 9: `D k` (for `k = 0, …, d-1`) is the paper's irreducible space
`H_{2(k+1)}`: a based continuous unitary irrep of SU(2) of dimension `2(k+1)` whose character is
the Weyl character. -/
def IsSpinFamily {d : ℕ} (D : Fin d → QAlgorithms.Papers.Independent.Next46.P36.BasedIrrep SU2) :
    Prop :=
  ∀ k : Fin d, (D k).dim = 2 * (k.val + 1) ∧
    ∀ g : SU2, ((D k).matrix g).trace = (weylCharacter (2 * (k.val + 1)) g : ℂ)

/-- Hayashi p. 7: the vector `(2k)·x^{2k}_E = √(2k)·vec(I)` in the block `H_{2k} ⊗ H_{2k,R}`
of the reference-assisted space, zero in the other blocks. -/
noncomputable def blockBellVector {d : ℕ}
    (D : Fin d → QAlgorithms.Papers.Independent.Next46.P36.BasedIrrep SU2) (k : Fin d) :
    EuclideanSpace ℂ (QAlgorithms.Papers.Independent.Next46.P36.CanonicalIndex D) :=
  QAlgorithms.Papers.Independent.Next46.P36.componentVector D (fun s => if s = k then 1 else 0)

/-- Hayashi p. 8: the seed `∑_{k,l} t_{k,l} |(2k)x^{2k}_E⟩⟨(2l)x^{2l}_E|` of the covariant
measurement `M^T_{2d-1}`. -/
noncomputable def hayashiSeed {d : ℕ}
    (D : Fin d → QAlgorithms.Papers.Independent.Next46.P36.BasedIrrep SU2)
    (T : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (QAlgorithms.Papers.Independent.Next46.P36.CanonicalIndex D)
      (QAlgorithms.Papers.Independent.Next46.P36.CanonicalIndex D) ℂ :=
  ∑ k : Fin d, ∑ l : Fin d,
    T k l • Matrix.of (fun p q => blockBellVector D k p * conj (blockBellVector D l q))

/-- Hayashi p. 6: the error `D_g(M, x)` at a FIXED true group element `g`,
`∫ d(g, ĝ) Tr M(dĝ) U_g ρ U_g^†`, for a measurement given by its operator density with respect to
its reference measure. `cost ĝ g` takes the estimate first and the true value second. -/
noncomputable def pointwiseRisk {I G : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace G]
    (U : G → Matrix I I ℂ) (cost : G → G → ℝ) (ρ : Matrix I I ℂ)
    (M : QAlgorithms.Measurements.DensityPOVM I G) (g : G) : ℝ :=
  ∫ h, cost h g * QAlgorithms.effectProb (M.density h) (QAlgorithms.conjSuperop (U g) ρ)
    ∂M.reference

/-- Hayashi p. 8, eq. (14), first line, with the conjugation corrected:
`½ ∑_k |x_k|² t_{k,k} − ¼ ∑_{k} (x̄_k x_{k+1} t_{k,k+1} + x̄_{k+1} x_k t_{k+1,k})`
(the sum over adjacent pairs `(k, k+1)` of `Fin d`; the printed `x_0` term is zero). -/
noncomputable def hayashiError {d : ℕ} (x : Fin d → ℂ) (T : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (1 / 2 : ℝ) * ∑ k : Fin d, Complex.normSq (x k) * (T k k).re -
    (1 / 4 : ℝ) * ∑ k : Fin d, ∑ l : Fin d,
      if k.val + 1 = l.val then
        (conj (x k) * x l * T k l + conj (x l) * x k * T l k).re
      else 0

/-- Hayashi p. 8, eq. (14), right-hand side (and eq. (10), p. 5):
`v(x) = ½ (1 − ∑_{k=1}^{d-1} |x_k| |x_{k+1}|)`. -/
noncomputable def methodValue {d : ℕ} (x : Fin d → ℂ) : ℝ :=
  (1 / 2 : ℝ) * (1 - ∑ k : Fin d, ∑ l : Fin d,
    if k.val + 1 = l.val then ‖x k‖ * ‖x l‖ else 0)

/-- Hayashi p. 5, eq. (9) and `T_x`, corrected: `t_{k,l} = (x_k/|x_k|) · conj(x_l/|x_l|)`, with the
phase of a zero coefficient taken to be `1`. -/
noncomputable def phaseAligned {d : ℕ} (x : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun k l =>
    QAlgorithms.Papers.Independent.Next46.P36.coefficientPhase (x k) *
      conj (QAlgorithms.Papers.Independent.Next46.P36.coefficientPhase (x l))

end ParallelSU2.Reduction


