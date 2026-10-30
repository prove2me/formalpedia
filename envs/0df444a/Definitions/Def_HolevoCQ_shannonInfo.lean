-- Prove2me | Definitions.Def_HolevoCQ_shannonInfo
-- name    : HolevoCQ_shannonInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:13.547989+00:00
-- url     : https://prove2.me/theorems/a8612e68-2024-4f17-986c-82d62b3b48fd
-- title:
--   Shannon information $I_1(\pi,X)$ of a coding and a decoding (eq. 1)
-- statement:
--   Let $i\mapsto S_i$ ($i\in A$) be a classical-quantum channel on $\mathcal H$, let $\pi$ be a distribution on $A$ (the coding) and $X=\{X_j\}$ a resolution of identity in $\mathcal H$ (the decoding), with output $j$ ranging over a finite alphabet. With $P(j\mid i)=\mathrm{Tr}\,S_iX_j$, the Shannon information is
--
--   $$
--   I_1(\pi,X)=\sum_j\sum_i\pi_iP(j\mid i)\log_2\frac{P(j\mid i)}{\sum_k\pi_kP(j\mid k)} ,
--   $$
--
--   with the convention that terms with $\pi_iP(j\mid i)=0$ vanish. Applied to the product channel $u\mapsto S_u$ on $\mathcal H^{\otimes n}$ and a distribution on $A^n$ it is $I_n(\pi,X)$.
--
--   **Formalization Note** Computed as `QAlgorithms.mutualInfoBits` of the joint law $(i,j)\mapsto\pi_i\,\mathrm{Tr}\,S_iX_j$. For a probability vector $\pi$ and a resolution of identity, the marginals of this law are $\pi_i$ and $\sum_k\pi_kP(j\mid k)$, so the sum agrees with the display term by term. The output alphabet is `Fin m`; traces are real parts.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (1), p.1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (1), p.1: the Shannon information
`I₁(π, X) = Σ_j Σ_i π_i P(j|i) log (P(j|i) / Σ_k π_k P(j|k))` between the input `i ~ π` and the
output `j` of the decoding `X = {X_j}`, with `P(j|i) = Tr S_i X_j`, binary logarithm.

**Formalization Note.** Computed as `QAlgorithms.mutualInfoBits` of the joint law
`(i, j) ↦ π_i Tr(S_i X_j)`. For a probability vector `π` and a resolution of identity `X` the
first marginal is `π_i` and the second is `Σ_k π_k P(j|k)`, so the summands agree with (1) term
by term (terms with `π_i P(j|i) = 0` are `0` on both sides). `Tr(S_i X_j)` is taken as the real
part (`effectProb`), which is the trace for positive operators. The output alphabet is `Fin m`.
Applied to `wordState S n` and a law on `Fin n → A` this is `I_n(π, X)` (p.1). -/
noncomputable def shannonInfo {A D : Type} [Fintype A] [Fintype D] (S : A → Matrix D D ℂ)
    (π : A → ℝ) {m : ℕ} (X : Fin m → Matrix D D ℂ) : ℝ :=
  mutualInfoBits (fun p : A × Fin m => π p.1 * effectProb (X p.2) (S p.1))

end HolevoCQ


