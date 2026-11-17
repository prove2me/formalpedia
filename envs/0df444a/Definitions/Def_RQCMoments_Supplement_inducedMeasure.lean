-- Prove2me | Definitions.Def_RQCMoments_Supplement_inducedMeasure
-- name    : RQCMoments_Supplement_inducedMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:46:56.079956+00:00
-- url     : https://prove2.me/theorems/e412c158-0a4a-452a-9544-7a7dd5f9397b
-- title:
--   Definition 5.1 — the distribution $\mu(p)$ on $U(D)$ induced by a distribution $p$ on $[0,1]$
-- statement:
--   Fix an integer $D>1$. Let $L,R\sim\mathrm{Haar}(D-1)$ be independent Haar random unitaries of dimension $D-1$, let $\Theta\sim\mathrm{Uniform}(0,2\pi)$ be independent of $(L,R)$, and let $X\sim p$ be independent of $(L,R,\Theta)$, where $p$ is a distribution on $[0,1]$. For $x\in[0,1]$ put
--
--   $$W(x)=\begin{bmatrix}\sqrt{x}\,e^{i\Theta} & \sqrt{1-x}\,e_1^{\top}\\ \sqrt{1-x}\,e_1 & -\sqrt{x}\,e^{-i\Theta}e_1e_1^{\top}+(I-e_1e_1^{\top})\end{bmatrix},\qquad U(x)=\begin{bmatrix}1&0\\0&L\end{bmatrix}W(x)\begin{bmatrix}1&0\\0&R\end{bmatrix},$$
--
--   where $e_1$ is the first standard basis vector of $\mathbb C^{D-1}$. The distribution $\mu(p)$ of $U(X)$ on the unitary group $U(D)$ is the **unitary distribution induced by $p$**.
--
--   The construction places $X$ as the squared magnitude of the top-left entry of a unitary while the random phases and the Haar factors $L,R$ symmetrize the rest. Theorems 5.3 and 5.4 show that a moment-matching $p$ makes $\mu(p)$ an exact or approximate unitary design, which is how the paper builds its lower-bound examples.
--
--   **Formalization Note** $\mu(p)$ is the pushforward of $p\otimes\mathrm{Uniform}(0,2\pi)\otimes\mathrm{Haar}(D-1)\otimes\mathrm{Haar}(D-1)$ under $(x,\theta,L,R)\mapsto U(x)$. Coordinate $0$ of $\mathrm{Fin}\,D$ is the leading one and $e_1$ is coordinate $1$. For $x\in[0,1]$ the matrix $U(x)$ is unitary; outside $[0,1]$, a set the theorems' $p$ gives mass zero, the map returns the identity. Haar is the published `QAlgorithms.Schur.unitaryHaar`.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 5.1, (109)–(110), p.31 (PDF p.33)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- The block matrix `[[1, 0], [0, L]]` (`= [1] ⊕ L`) of size `D`, for a `(D−1) × (D−1)` matrix `L`
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 5.1, (110), p.31, PDF p.33).

**Formalization Note** Index `0 : Fin D` is the leading coordinate; index `i ≥ 1` of `Fin D` is index
`i − 1` of `Fin (D − 1)`. The final `else 0` branch is never reached for indices of `Fin D`. -/
def blockOne (D : ℕ) (L : Matrix (Fin (D - 1)) (Fin (D - 1)) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1
    else if i.val = 0 ∨ j.val = 0 then 0
    else if h : i.val - 1 < D - 1 ∧ j.val - 1 < D - 1 then L ⟨i.val - 1, h.1⟩ ⟨j.val - 1, h.2⟩
    else 0

/-- The matrix `W(x)` of (109) (Hung, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 5.1, (109), p.31, PDF p.33):
`W(x) = [[√x e^{iΘ}, √(1−x) e₁ᵀ], [√(1−x) e₁, −√x e^{−iΘ} e₁e₁ᵀ + (I − e₁e₁ᵀ)]]`,
with `e₁` the first standard basis vector of `ℂ^{D−1}`.

**Formalization Note** In `Fin D` coordinates (`e₁` of the lower block is index `1`): entry `(0,0)` is
`√x e^{iθ}`, entries `(0,1)` and `(1,0)` are `√(1−x)`, entry `(1,1)` is `−√x e^{−iθ}`, the other
diagonal entries are `1` and all other entries are `0`. `Real.sqrt` is used on `x ∈ [0,1]`. -/
noncomputable def Wmat (D : ℕ) (x θ : ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then (Real.sqrt x : ℂ) * Complex.exp (θ * Complex.I)
    else if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) then (Real.sqrt (1 - x) : ℂ)
    else if i.val = 1 ∧ j.val = 1 then -((Real.sqrt x : ℂ) * Complex.exp (-(θ * Complex.I)))
    else if i = j then 1
    else 0

/-- The matrix `U(x) = ([1] ⊕ L) W(x) ([1] ⊕ R)` of (110)
(Hung, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 5.1, (110), p.31, PDF p.33). -/
noncomputable def inducedMatrix (D : ℕ) (x θ : ℝ) (L R : Matrix.unitaryGroup (Fin (D - 1)) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  blockOne D (L : Matrix (Fin (D - 1)) (Fin (D - 1)) ℂ) * Wmat D x θ *
    blockOne D (R : Matrix (Fin (D - 1)) (Fin (D - 1)) ℂ)

open Classical in
/-- `(x, Θ, L, R) ↦ U(x)` as a map into `U(D)`.

**Formalization Note** For `D ≥ 2` and `x ∈ [0,1]` the matrix `U(x)` is unitary (the paper's
Definition 5.1), so the first branch is taken; the fallback value `1` is used only off `[0,1]`, a
set the theorems' distributions `p` give mass `0`. -/
noncomputable def inducedMap (D : ℕ) :
    ℝ × ℝ × Matrix.unitaryGroup (Fin (D - 1)) ℂ × Matrix.unitaryGroup (Fin (D - 1)) ℂ →
      Matrix.unitaryGroup (Fin D) ℂ :=
  fun z =>
    if h : inducedMatrix D z.1 z.2.1 z.2.2.1 z.2.2.2 ∈ Matrix.unitaryGroup (Fin D) ℂ then
      ⟨inducedMatrix D z.1 z.2.1 z.2.2.1 z.2.2.2, h⟩
    else 1

/-- The uniform distribution `Uniform(0, 2π)` on `ℝ`. -/
noncomputable def uniformAngle : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • volume.restrict (Set.Ico 0 (2 * Real.pi))

/-- **Definition 5.1** (unitary distribution induced by a distribution on `[0,1]`)
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 5.1, (109)–(110), p.31, PDF p.33).
For an integer `D > 1`, let `L, R ∼ Haar(D−1)` be independent, `Θ ∼ Uniform(0, 2π)` independent of
`(L, R)`, and `X ∼ p` independent of `(L, R, Θ)`. Then `μ(p)` is the law of
`U(X) = ([1] ⊕ L) W(X) ([1] ⊕ R)`, a distribution on `U(D)`.

**Formalization Note** `μ(p)` is the pushforward of the product measure
`p ⊗ Uniform(0,2π) ⊗ Haar(D−1) ⊗ Haar(D−1)` under `(x, θ, L, R) ↦ U(x)` (`inducedMap`). `p` is a
measure on `ℝ`; the theorems assume it is a probability measure concentrated on `[0,1]`. Haar is
the published `QAlgorithms.Schur.unitaryHaar`. -/
noncomputable def inducedMeasure (D : ℕ) (p : Measure ℝ) : Measure (Matrix.unitaryGroup (Fin D) ℂ) :=
  (p.prod (uniformAngle.prod ((QAlgorithms.Schur.unitaryHaar (D - 1)).prod
    (QAlgorithms.Schur.unitaryHaar (D - 1))))).map (inducedMap D)

end Supplement

end RQCMoments


