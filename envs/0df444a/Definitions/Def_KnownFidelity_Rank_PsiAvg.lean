-- Prove2me | Definitions.Def_KnownFidelity_Rank_PsiAvg
-- name    : KnownFidelity_Rank_PsiAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:51:02.226335+00:00
-- url     : https://prove2.me/theorems/c53fe870-90b8-4fe7-b8c2-b9439fe949fe
-- title:
--   The $m$-copy average pure state $\overline\Psi_b^{(m)}$, Eq. (43)
-- statement:
--   For $a\in\mathbb R^r_{\ge0}$ and $m\ge1$,
--
--   $$\overline\Psi^{(m)}=\mathbb E_{G\sim\Pi^{(m)}}\,|\psi_G\rangle\langle\psi_G|^{\otimes m},$$
--
--   a state on $(\mathbb C^r\otimes\mathbb C^r)^{\otimes m}$. With $a=a^{(b)}$ it is $\overline\Psi_b^{(m)}$; Proposition 5.11 and Corollary 5.12 bound the trace distance between the two.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §5.4, Eq. (43), p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_sizeBiasedPrior
import Definitions.Def_KnownFidelity_Rank_psiVec
import Definitions.Def_KnownFidelity_Rank_avgPower

open MeasureTheory

namespace KnownFidelity.Rank

/-- **The `m`-copy average pure state `Ψ̄_b^{(m)}`, Eq. (43).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §5.4, Eq. (43), printed p. 17 (PDF p. 19): "The corresponding m-copy average
pure state is Ψ̄_b^{(m)} = E_{G∼Π_b^{(m)}} |ψ_G⟩⟨ψ_G|^{⊗m}."

`PsiAvg a m = E_{G ∼ Π^{(m)}(a)} (|ψ_G⟩⟨ψ_G|)^{⊗m}`, a matrix on `(ℂ^r ⊗ ℂ^r)^{⊗m}`, with
`Π^{(m)}(a) = sizeBiasedPrior a m` and `ψ_G = psiVec G`.

**Formalization Note.** The average is `avgPower` (entrywise Bochner integrals of the bounded,
continuous-off-zero integrand); `(ℂ^r ⊗ ℂ^r)^{⊗m}` is indexed by `Fin m → Fin r × Fin r`. -/
noncomputable def PsiAvg {r : ℕ} (a : Fin r → ℝ) (m : ℕ) :
    Matrix (Fin m → Fin r × Fin r) (Fin m → Fin r × Fin r) ℂ :=
  avgPower (sizeBiasedPrior a m) (fun G => Matrix.vecMulVec (psiVec G) (star (psiVec G))) m

end KnownFidelity.Rank


