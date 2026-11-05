-- Prove2me | Definitions.Def_MosonyiPetz_IsSufficient
-- name    : MosonyiPetz_IsSufficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:50.860891+00:00
-- url     : https://prove2.me/theorems/47d46084-d180-439e-a022-61554ff3f0ac
-- title:
--   Sufficiency of $T$ for $D_1, D_2$ (eq. (1))
-- statement:
--   Let $T:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ be a linear map between the matrix algebras of finite-dimensional Hilbert spaces and let $D_1,D_2\in\mathcal B(\mathcal H)$. **$T$ is sufficient for $D_1$ and $D_2$** if there is a linear map $\beta:\mathcal B(\mathcal K)\to\mathcal B(\mathcal H)$ that is
--
--   1. 2-positive: $\begin{pmatrix}\beta(A)&\beta(B)\\\beta(C)&\beta(D)\end{pmatrix}\ge0$ whenever $\begin{pmatrix}A&B\\C&D\end{pmatrix}\ge0$;
--   2. trace preserving: $\operatorname{Tr}\beta(X)=\operatorname{Tr}X$ for every $X$;
--   3. a recovery map for both densities:
--
--   $$\beta(T(D_1))=D_1,\qquad \beta(T(D_2))=D_2.$$
--
--   This is the paper's notion of a coarse-graining that loses no information about the pair $D_1,D_2$; every result of the mission assumes it.
--
--   **Formalization Note** 2-positivity is the published `IsTwoPositive` (positivity of the $2\times2$ block amplification). The recovery map is not required to be completely positive or unital.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, eq. (1), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

open scoped Matrix
open QAlgorithms.Papers.Independent.Intakethird100.P84 (IsTwoPositive)

namespace MosonyiPetz

/-- **Sufficiency of a coarse-graining for two densities, eq. (1).**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, eq. (1), p.2: "T is sufficient for D1 and D2 if there exists a trace preserving
2-positive mapping β : B(K) → B(H) such that βT(D1) = D1 and βT(D2) = D2."

`IsSufficient T D₁ D₂` holds when some `ℂ`-linear `β : Matrix K K ℂ → Matrix H H ℂ` is
2-positive (`IsTwoPositive`: the 2 × 2 block amplification of `β` maps positive semidefinite
block matrices to positive semidefinite block matrices), preserves the trace, and recovers both
`D₁` and `D₂` from `T D₁` and `T D₂`.

**Formalization Note.** `B(H)` is `Matrix H H ℂ` for a finite index type `H`. The recovery map
is only 2-positive and trace preserving, as in (1): neither complete positivity nor unitality is
required. -/
def IsSufficient {H K : Type*} [Fintype H] [Fintype K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (D₁ D₂ : Matrix H H ℂ) : Prop :=
  ∃ β : Matrix K K ℂ →ₗ[ℂ] Matrix H H ℂ, IsTwoPositive β ∧ (∀ X, (β X).trace = X.trace) ∧
    β (T D₁) = D₁ ∧ β (T D₂) = D₂

end MosonyiPetz


