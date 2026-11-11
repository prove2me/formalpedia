-- Prove2me | Definitions.Def_AgnGaussTomo_psi
-- name    : AgnGaussTomo_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:54.986587+00:00
-- url     : https://prove2.me/theorems/5e05e4aa-74c2-417d-9ae8-02a5fbf4f702
-- title:
--   Pure Gaussian state in Bargmann form, $|\psi(b,A)\rangle=Z^{-1/2}|\Phi(b,A)\rangle$
-- statement:
--   For $\theta=(b,A)\in\mathcal P_n$ with $\|A\|_{\mathrm{op}}<1$, the **Bargmann state**
--
--   $$
--   |\psi(b,A)\rangle=\frac{1}{\sqrt{Z(b,A)}}\exp\Big(\sum_i b_i\hat a_i^\dagger+\tfrac12\sum_{i,j}A_{ij}\hat a_i^\dagger\hat a_j^\dagger\Big)|0\rangle,\qquad Z(b,A)=\|\Phi(b,A)\|^2,
--   $$
--
--   is a pure Gaussian state, and every pure Gaussian state is uniquely of this form with the global phase fixed so that the vacuum coefficient is positive (Fact 2.4). These coordinates are used for the gradient-descent refinement near the vacuum.
--
--   **Formalization Note** `psi θ` is the vector $Z^{-1/2}\Phi(\theta)$ of $\ell^2(\mathbb N^n)$ (published `Hilbert (Occupation (Fin n))`), with positive vacuum coefficient. Outside the domain $\|A\|_{\mathrm{op}}<1$ the coefficients are not square-summable and the value is the junk vector $0$; the statements use `psi` only on the domain (balls $\|\theta\|_{\mathcal P}\le1/8$ lie inside it, since $\|A\|_{\mathrm{op}}\le\sqrt2\|\theta\|_{\mathcal P}$).
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Fact 2.4, Eq. (5), printed p. 11 (PDF p. 14); Z(b, A) = ‖Φ(b, A)‖², p. 12 (PDF p. 15)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_AgnGaussTomo_Phi

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

open Classical in
/-- **The pure Gaussian state `|ψ(b, A)⟩ = Z(b, A)^{-1/2} |Φ(b, A)⟩` in Bargmann form.** Arulandu, Chen,
Chen, Li, Ma, *Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov
2026), Fact 2.4 and Eq. (5), printed p. 11 (PDF p. 14): "Every pure Gaussian state |ψ⟩ can be
uniquely written as f_ψ(z) = 1/√Z(b, A) exp(bᵀz + ½ zᵀAz) with θ = (b, A) ∈ P_n … and ‖A‖_op < 1. The
global phase is typically fixed so that the vacuum coefficient is positive", where "Z(b, A) is the
normalization factor that gives |ψ(b, A)⟩ unit norm"; `Z(b, A) = ‖Φ(b, A)‖²` (p. 12, before (10)).

`psi θ` is the unit vector `Z^{-1/2} Φ(θ)` in the Fock space `ℓ²(ℕⁿ)`, with `Z = Σ_m |Φ_m(θ)|²`; its
vacuum coefficient `Z^{-1/2}` is positive (the paper's phase convention).

**Formalization Note.** The Fock space is the published `Hilbert (Occupation (Fin n)) =
ℓ²(Fin n → ℕ)`. For `‖A‖_op < 1` (the paper's domain; e.g. whenever `‖θ‖_P < 1/√2`, since
`‖A‖_op ≤ ‖A‖_F ≤ √2‖θ‖_P`) the vector `Z^{-1/2}Φ` is square-summable and this is the Bargmann
state. Outside that domain the coefficient family is not in `ℓ²` and the value is the junk `0`;
every statement of the mission uses `psi` only on the domain (or on a neighbourhood of a closed
ball inside it). -/
noncomputable def psi {n : ℕ} (θ : Pspace n) : Hilbert (Occupation (Fin n)) :=
  let v : Occupation (Fin n) → ℂ :=
    fun m => ((∑' m', ‖Phi θ m'‖ ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) * Phi θ m
  if h : Memℓp v 2 then ⟨v, h⟩ else 0

end AgnGaussTomo


