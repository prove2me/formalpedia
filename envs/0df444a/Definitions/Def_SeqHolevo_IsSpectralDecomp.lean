-- Prove2me | Definitions.Def_SeqHolevo_IsSpectralDecomp
-- name    : SeqHolevo_IsSpectralDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:22.057795+00:00
-- url     : https://prove2.me/theorems/139d2a9f-e43c-471e-8222-908f0b130e6e
-- title:
--   Countable spectral decomposition $\rho=\sum_x p_X(x)|x\rangle\langle x|$
-- statement:
--   A density operator $\rho$ on $\ell^2(I)$ has the **spectral decomposition** $(p,u)$, with labels $x\in\mathbb N$, when
--
--   $$\rho=\sum_{x}p_X(x)\,|u_x\rangle\langle u_x| ,$$
--
--   where $p_X$ is a probability vector ($p_X(x)\ge0$, $\sum_xp_X(x)=1$), and the eigenvectors $|u_x\rangle$ of positive weight are unit vectors and pairwise orthogonal. The identity holds coefficientwise.
--
--   The weakly typical subspace and the typical projector of Appendix A are built from such a decomposition.
--
--   **Formalization Note** This is the body of the published `HasSpectralLaw` (`Intakenext100.P76`) with the eigenvectors named. Countable labels cover every density operator; finite spectra use zero weights, and vectors of weight zero carry no condition.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix A, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

open QAlgorithms.Papers.Independent.Intakenext100.P76 (IsUnitCoefficientVector coefficientInner meanOutput kernelEntropyBits productPureCQChannel selfInformationMean HasSpectralLaw)

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix A, p.6 (PDF page): "a density operator `ρ` with the following spectral
decomposition: `ρ = Σ_x p_X(x) |x⟩⟨x|`". Here the labels `x` run over `ℕ`, `p` is a
probability vector and `u x` is the eigenvector `|x⟩`: the weights are nonnegative and sum to
one, the eigenvectors of positive weight are unit vectors and mutually orthogonal, and `ρ` is
reconstructed coefficientwise as `ρ_{ab} = Σ_x p_x u_x(a) conj(u_x(b))`.

**Formalization Note.** This is the body of the published `HasSpectralLaw ρ p`
(`Intakenext100.P76`) with the eigenvectors `u` named instead of hidden behind `∃`, because
the typical projector is built from them. Labels with zero weight carry no condition (their
vectors never enter the typical projector). A countable label set covers every density operator
(trace class implies countable spectrum); finite spectra use zero weights. -/
def IsSpectralDecomp {I : Type} (ρ : Matrix I I ℂ) (p : ℕ → ℝ) (u : ℕ → I → ℂ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ Summable p ∧ (∑' j, p j) = 1 ∧
    (∀ j, 0 < p j → IsUnitCoefficientVector (u j)) ∧
    (∀ j k, j ≠ k → 0 < p j → 0 < p k → coefficientInner (u j) (u k) = 0) ∧
    ∀ a b, ρ a b = ∑' j, (p j : ℂ) * Matrix.vecMulVec (u j) (star (u j)) a b

end SeqHolevo


