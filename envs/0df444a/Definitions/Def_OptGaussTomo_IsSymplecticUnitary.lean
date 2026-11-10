-- Prove2me | Definitions.Def_OptGaussTomo_IsSymplecticUnitary
-- name    : OptGaussTomo_IsSymplecticUnitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:17.292548+00:00
-- url     : https://prove2.me/theorems/940f3817-4204-463d-a91d-e80f75db921b
-- title:
--   Symplectic matrices and the symplectic Gaussian unitaries $U_S$
-- statement:
--   For modes labelled by a finite set $\mathcal I$ and the interleaved quadratures $(q_j,p_j)_{j\in\mathcal I}$, let $\Omega=\bigoplus_j\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ be the symplectic form ($[q_j,p_j]=i$). A real matrix $S$ is **symplectic** if $S\Omega S^{\mathsf T}=\Omega$. A unitary $U$ on the Fock space **implements** $S$ if
--
--   $$
--   U r_j U^\dagger=\sum_k S_{kj}r_k\quad\text{(D.1)},\qquad\text{equivalently}\qquad U\,W(\xi)\,U^\dagger=W(S\xi)\ \text{ for all }\xi,
--   $$
--
--   with $W(\xi)=e^{i\xi\cdot r}$ the Weyl operators. $U$ is determined by $S$ up to a phase.
--
--   **Formalization Note** The Weyl form is (D.1) exponentiated. Operators are the published Fock-basis kernels; conjugation is the published kernel product `conjugateKernel`.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §D.1 p.42 (pdf p.42), eq. (D.1)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (InterleavedQuadrature OscillatorCovariance oscillatorWeylKernel)
open QAlgorithms.Papers.Independent.Frontier30.P14 (unitaryCoeff conjugateKernel)

namespace OptGaussTomo

/-!
# Symplectic matrices and the symplectic Gaussian unitaries `U_S`

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), §D.1, p.42: "For
`S ∈ Sp(2m)`, there are unitaries `U_S` that map `U_S r_j U_S† = ∑_{k=1}^{2m} S_kj r_k`, (D.1) where
`(r_1, …, r_{2m}) = (q_1, p_1, …, q_m, p_m)` are the quadrature operators. … For `S ∈ Sp(2m)` we
denote the associated symplectic Gaussian unitary by `U_S`."

**Formalization Note.** The modes are labelled by a finite type `I` (`Fin m` for one system,
`Fin m ⊕ Fin m` for two), the quadratures by `I × Fin 2` with `(j, 0) = q_j`, `(j, 1) = p_j`
(published `Support50.P14`, interleaved as in the source). `sympForm I` is the interleaved
symplectic form `Ω = ⊕_j [[0, 1], [−1, 0]]` (`[q_j, p_j] = i`), and `S ∈ Sp(2m)` iff
`S Ω Sᵀ = Ω`. A unitary `U` on `ℓ²(Occupation I)` implements `S` iff
`U W(ξ) U† = W(S ξ)` for every `ξ`, where `W(ξ) = exp(i ξ·r)` is the published Weyl kernel
`oscillatorWeylKernel`; this is (D.1) exponentiated (`U exp(i ∑_j ξ_j r_j) U† =
exp(i ∑_k (∑_j S_kj ξ_j) r_k)`). `U` is determined by `S` up to a phase. Conjugation is the
published kernel product `conjugateKernel` (bounded operators, iterated sums).
-/

/-- The interleaved symplectic form `Ω = ⊕_j [[0, 1], [−1, 0]]` on `I × Fin 2`. -/
def sympForm (I : Type) [DecidableEq I] : OscillatorCovariance I :=
  fun a b => if a.1 = b.1 then
    (if a.2 = 0 ∧ b.2 = 1 then 1 else if a.2 = 1 ∧ b.2 = 0 then -1 else 0) else 0

/-- `S ∈ Sp(2|I|)`: `S Ω Sᵀ = Ω` (interleaved convention). -/
def IsSymplecticMatrix {I : Type} [Fintype I] [DecidableEq I] (S : OscillatorCovariance I) : Prop :=
  S * sympForm I * S.transpose = sympForm I

/-- `U` is a symplectic Gaussian unitary implementing `S` (D.1): `U W(ξ) U† = W(S ξ)`. -/
def IsSymplecticUnitary {I : Type} [Fintype I] [DecidableEq I]
    (U : Hilbert (Occupation I) ≃ₗᵢ[ℂ] Hilbert (Occupation I)) (S : OscillatorCovariance I) : Prop :=
  IsSymplecticMatrix S ∧
  ∀ ξ : InterleavedQuadrature I → ℝ,
    conjugateKernel (unitaryCoeff U) (oscillatorWeylKernel ξ) = oscillatorWeylKernel (S.mulVec ξ)

end OptGaussTomo


