-- Prove2me | Definitions.Def_TwoFoldOPI_qft
-- name    : TwoFoldOPI_qft
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:44.657975+00:00
-- url     : https://prove2.me/theorems/bea0e277-c5c7-425f-ba59-1d0711055715
-- title:
--   The quantum Fourier transform over $\mathbb F_q^M$, Eq. (6)
-- statement:
--   Let $p=\operatorname{char}\mathbb F_q$, $\omega_p=e^{2\pi i/p}$, $\operatorname{Tr}=\operatorname{Tr}_{\mathbb F_q/\mathbb F_p}$ and $\langle x,y\rangle=\sum_jx_jy_j$. The quantum Fourier transform on $\mathbb C^{\mathbb F_q^M}$ is
--   $$\mathrm{QFT}\,|y\rangle=q^{-M/2}\sum_{x\in\mathbb F_q^M}\omega_p^{\operatorname{Tr}(\langle x,y\rangle)}|x\rangle .$$
--   Its adjoint satisfies $\mathrm{QFT}^\dagger|y\rangle=\mathrm{QFT}|-y\rangle$. The decoder inputs of the mission are $X^c\,\mathrm{QFT}^\dagger|\psi\rangle$.
--
--   **Formalization Note** The trace is read as an integer in $\{0,\dots,p-1\}$; the inner product is bilinear, not Hermitian; $\mathrm{QFT}^\dagger$ is the conjugate transpose.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5, Notation, Eq. (6), p. 20

import Mathlib
import Definitions.Def_TwoFoldOPI_elemBits

namespace TwoFoldOPI

/-- **The quantum Fourier transform over `F_q^M`, Eq. (6).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5, Notation, p.20: "Over F_q, write p = char(F_q), ω_p = e^{2πi/p}, and Tr = Tr_{F_q/F_p}
for the field trace … For x, y ∈ F_q^M, put ⟨x, y⟩ = Σ_j x_j y_j and use
QFT |y⟩ = q^{−M/2} Σ_{x∈F_q^M} ω_p^{Tr(⟨x,y⟩)} |x⟩. (6) Thus QFT† |y⟩ = QFT |−y⟩."

The matrix entry in row `x`, column `y` is `q^{−M/2} · exp(2πi · Tr(⟨x, y⟩)/p)`.

**Formalization Note.** `Tr` is `Algebra.trace (ZMod p) K`, read as the integer `0 ≤ Tr < p`
(`ZMod.val`); `⟨x, y⟩ = Σⱼ xⱼyⱼ` is the bilinear (not Hermitian) form. `QFT†` is the conjugate
transpose `(qft F M)ᴴ`. -/
noncomputable def qft (F : AvgCaseTI.FieldPres) (M : ℕ) :
    Matrix (Fin M → F.F) (Fin M → F.F) ℂ :=
  Matrix.of fun x y =>
    ((Real.sqrt (Fintype.card F.F : ℝ) ^ M)⁻¹ : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I *
        ((Algebra.trace (ZMod F.p) F.F (∑ j, x j * y j)).val : ℂ) / (F.p : ℂ))

end TwoFoldOPI


