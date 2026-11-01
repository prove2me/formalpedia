-- Prove2me | Definitions.Def_QubitPhaseEst_SpinIdx
-- name    : QubitPhaseEst_SpinIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:40.005737+00:00
-- url     : https://prove2.me/theorems/9a093d19-1b5f-449c-970f-cbdcace0ef4d
-- title:
--   Multiplicities $d_j=\binom{2J}{J-j}-\binom{2J}{J-j-1}$ and labels $(j,m,\alpha)$
-- statement:
--   The $N$-qubit space decomposes into irreducible representations of $\mathrm{SU}(2)$ with spins $j=J,J-1,\dots,\langle\langle N/2\rangle\rangle$, where $J=N/2$ and $\langle\langle N/2\rangle\rangle$ is $0$ for even $N$ and $\tfrac12$ for odd $N$. Spin $j$ occurs with **multiplicity**
--
--   $$
--   d_j=\binom{2J}{J-j}-\binom{2J}{J-j-1},\qquad \binom{2J}{-1}=0.
--   $$
--
--   The basis labels are the triples $(j,m,\alpha)$ with $m\in\{-j,\dots,j\}$ and $\alpha\in\{1,\dots,d_j\}$. There are $2^N$ of them.
--
--   **Formalization Note** The spin is encoded by $k=J-j\in\{0,\dots,\lfloor N/2\rfloor\}$, the weight by the index $i=j-m\in\{0,\dots,2j\}$, and $\alpha$ by `Fin d_j`. The term $\binom{2J}{-1}$ at $k=0$ is handled separately, because natural-number subtraction would give $\binom{N}{0}=1$ there. The module also names, for an adjacent pair $(m+1,m)$ in a block $(j,\alpha)$, the labels of $|m+1,j\alpha\rangle$ and $|m,j\alpha\rangle$.
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eqs. (11)–(14), p. 2

import Mathlib
import Definitions.Def_QubitPhaseEst_spinRotY

namespace QubitPhaseEst

/-- **The multiplicity `d_j` of the spin-`j` representation in `N` qubits**, arXiv:quant-ph/0411133v3,
Sec. II, Eq. (14), p. 2: `d_j = C(2J, J−j) − C(2J, J−j−1)`, with `2J = N` and `k = J − j`.

**Formalization Note.** `C(N, −1) = 0`, so `k = 0` gives `1`; it is guarded explicitly, because the
natural-number subtraction `k - 1` at `k = 0` would give `N.choose 0 = 1`. For `1 ≤ k ≤ N/2` the
binomials increase, so the outer natural-number subtraction does not truncate. -/
def mult (N k : ℕ) : ℕ :=
  if k = 0 then 1 else N.choose k - N.choose (k - 1)

/-- **The labels `(j, m, α)` of the angular-momentum basis** of `N` qubits, arXiv:quant-ph/0411133v3,
Sec. II, Eqs. (11)–(13), p. 2: `k ∈ {0, …, ⌊N/2⌋}` with `j = N/2 − k`, then an index `i` with
`m = j − i` (so `N − 2k + 1 = 2j + 1` values), and the multiplicity index `α` (`d_j` values). -/
abbrev SpinIdx (N : ℕ) :=
  Σ k : Fin (N / 2 + 1), Fin (N - 2 * (k : ℕ) + 1) × Fin (mult N k)

/-- The eigenvalue `m = j − i` of `J_z` at the label `s = (k, i, α)`, where `j = N/2 − k`
(arXiv:quant-ph/0411133v3, Sec. II, p. 2: `m` the eigenvalue of `J_z`). -/
noncomputable def SpinIdx.weight {N : ℕ} (s : SpinIdx N) : ℝ :=
  spinM (N - 2 * (s.1 : ℕ)) s.2.1

/-- The label of `|m + 1, jα⟩` in an adjacent pair (arXiv:quant-ph/0411133v3, Sec. II, Eq. (15), p. 2). An adjacent pair of the block `(k, α)` is given
by `i : Fin (N − 2k)` (there are `2j` of them): `m + 1` is at index `i`, `m` at index `i + 1`. -/
def spinTop {N : ℕ} (k : Fin (N / 2 + 1)) (α : Fin (mult N k)) (i : Fin (N - 2 * (k : ℕ))) :
    SpinIdx N :=
  ⟨k, (i.castSucc, α)⟩

/-- The label of `|m, jα⟩` in the adjacent pair of `spinTop`: index `i + 1` (arXiv:quant-ph/0411133v3, Sec. II, Eq. (15), p. 2). -/
def spinBot {N : ℕ} (k : Fin (N / 2 + 1)) (α : Fin (mult N k)) (i : Fin (N - 2 * (k : ℕ))) :
    SpinIdx N :=
  ⟨k, (i.succ, α)⟩

end QubitPhaseEst


