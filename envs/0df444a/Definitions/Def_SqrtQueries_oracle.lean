-- Prove2me | Definitions.Def_SqrtQueries_oracle
-- name    : SqrtQueries_oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:30:32.098934+00:00
-- url     : https://prove2.me/theorems/55e52959-7e67-4385-b2fa-218de285cc9c
-- title:
--   Oracle pair $U_0=D$, $U_1=e^{iA/4}De^{-iA/4}$ (Detecting smearing)
-- statement:
--   Let $N\ge1$, let $D$ be the clock operator on $\mathbb C^N$, and let $A=(S+S^\dagger)/2$ with $S$ the shift operator. The promise problem **Detecting smearing** gives an oracle that is promised to be one of
--   $$
--   U_0=D\qquad\text{(DIAG)},\qquad\qquad U_1=e^{iA/4}\,D\,e^{-iA/4}\qquad\text{(NOTDIAG)},
--   $$
--   and asks which case holds. Both are unitary with the same eigenvalues $\omega_N^j$; the eigenvectors of $U_1$ are $e^{iA/4}|j\rangle$.
--
--   This oracle pair is the object of the black-box separation: $U_0$ and $U_1$ are $O(1/N)$-close in operator norm, while any square roots of them are $\Omega(1)$ apart.
--
--   **Formalization Note** The label is the bit $b$ as a Boolean: `oracle N false` is $U_0$ and `oracle N true` is $U_1$. The exponentials are the matrix exponential `NormedSpace.exp`, with $e^{\pm iA/4}$ written `exp ((± I / 4) • A)`.
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Definition 3.2, p.16

import Mathlib
import Definitions.Def_SqrtQueries_clockOp
import Definitions.Def_SqrtQueries_smearA

namespace SqrtQueries

/-- The oracle pair of the promise problem **Detecting smearing** (Ma–Tang, *Square-root queries
can help*, STOC 2027 submission manuscript, sha256 783868e7…c5f15a, Definition 3.2, p.16):
`U₀ = D` (the case DIAG) and `U₁ = e^{iA/4} D e^{−iA/4}` (the case NOTDIAG), where `D` is the clock
operator and `A = (S + S†)/2`.

**Formalization Note.** The label is the paper's bit `b` as a `Bool`: `oracle N false = U₀ = D`
(DIAG) and `oracle N true = U₁` (NOTDIAG). The exponentials are the matrix exponential
`NormedSpace.exp`, with `e^{iA/4} = exp((i/4) • A)` and `e^{−iA/4} = exp((−i/4) • A)`. -/
noncomputable def oracle (N : ℕ) [NeZero N] : Bool → Matrix (Fin N) (Fin N) ℂ
  | false => clockOp N
  | true => NormedSpace.exp ((Complex.I / 4) • smearA N) * clockOp N *
      NormedSpace.exp ((-Complex.I / 4) • smearA N)

end SqrtQueries


