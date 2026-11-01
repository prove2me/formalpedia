-- Prove2me | Definitions.Def_QubitPhaseEst_optValue
-- name    : QubitPhaseEst_optValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:37.547994+00:00
-- url     : https://prove2.me/theorems/3cc0bf56-b22c-4b60-b33b-fa990bc0e0c3
-- title:
--   The optimal averaged cosine, right side of Eq. (21)
-- statement:
--   Let $N\ge1$, $0\le r<1$, $\theta\in\mathbb R$, $r_\pm=\tfrac12(1\pm r)$ and $J=N/2$. For each spin $j$ let $T^{(j)}=e^{i\theta J_y}$ in the spin-$j$ representation. The **value** of Eq. (21) is
--
--   $$
--   V(N,r,\theta)=\sum_{j=\langle\langle N/2\rangle\rangle}^{J}\ \sum_{m=-j}^{j-1} d_j\,(r_+r_-)^J\,\Bigl|\sum_{n=-j}^{j}\Bigl(\frac{r_+}{r_-}\Bigr)^{n}\,T^{(j)}_{m+1,n}\,\overline{T^{(j)}_{m,n}}\Bigr|.
--   $$
--
--   It is the largest averaged cosine a covariant measurement can achieve on $N$ copies of a qubit state with Bloch vector of length $r$ and polar angle $\theta$.
--
--   **Formalization Note** The paper's sum runs to $m=j$, where $T_{j+1,n}$ does not exist; that term is omitted (it is zero). $T^\dagger_{n,m}=\overline{T_{m,n}}$. The half-integer powers $(r_+r_-)^J$ and $(r_+/r_-)^n$ are real powers of positive numbers. The definition is the explicit expression (21), not the sum $\sum|\langle m+1,j\alpha|R|m,j\alpha\rangle|$ it equals.
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eq. (21), p. 3 (r± after Eq. (13), p. 2)

import Mathlib
import Definitions.Def_QubitPhaseEst_SpinIdx

namespace QubitPhaseEst

/-- `r₊ = ½(1 + r)`, arXiv:quant-ph/0411133v3, Sec. II, after Eq. (13), p. 2. -/
noncomputable def rPlus (r : ℝ) : ℝ :=
  (1 + r) / 2

/-- `r₋ = ½(1 − r)`, arXiv:quant-ph/0411133v3, Sec. II, after Eq. (13), p. 2. -/
noncomputable def rMinus (r : ℝ) : ℝ :=
  (1 - r) / 2

/-- **The optimal averaged cosine**, the right side of arXiv:quant-ph/0411133v3, Sec. II, Eq. (21),
p. 3:
`Σ_{j=⟨⟨N/2⟩⟩}^{J} Σ_{m} d_j (r₊r₋)^J |Σ_n (r₊/r₋)^n T^{(j)}_{m+1,n} T^{(j)†}_{n,m}|`, with `J = N/2`
and `T^{(j)} = e^{iθJ_y}` in the spin-`j` representation.

**Formalization Note.** `k` runs over `{0, …, ⌊N/2⌋}` with `j = N/2 − k`. An `i : Fin (N − 2k)` is an
adjacent pair: `m + 1` at index `i` and `m` at index `i + 1`, so the term `m = j`, in which `T_{j+1,n}`
does not exist, is omitted. `T^†_{n,m} = conj T_{m,n}`. The inner index `l` is the paper's `n`, of weight
`j − l`. Half-integer exponents are `Real.rpow`; for `0 ≤ r < 1` the bases `r₊r₋` and `r₊/r₋` are
positive. It is deliberately the explicit expression (21), not `Σ|⟨m+1, jα|R|m, jα⟩|`. -/
noncomputable def optValue (N : ℕ) (r θ : ℝ) : ℝ :=
  ∑ k : Fin (N / 2 + 1), (mult N k : ℝ) * (rPlus r * rMinus r) ^ ((N : ℝ) / 2) *
    ∑ i : Fin (N - 2 * (k : ℕ)),
      ‖∑ l : Fin (N - 2 * (k : ℕ) + 1),
        (((rPlus r / rMinus r) ^ spinM (N - 2 * (k : ℕ)) l : ℝ) : ℂ) *
          spinRotY (N - 2 * (k : ℕ)) θ i.castSucc l *
          star (spinRotY (N - 2 * (k : ℕ)) θ i.succ l)‖

end QubitPhaseEst


