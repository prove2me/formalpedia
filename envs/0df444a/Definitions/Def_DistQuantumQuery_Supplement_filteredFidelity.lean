-- Prove2me | Definitions.Def_DistQuantumQuery_Supplement_filteredFidelity
-- name    : DistQuantumQuery_Supplement_filteredFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:45:48.634201+00:00
-- url     : https://prove2.me/theorems/fa1d1a7d-8cb7-4532-b0a5-131237802fe7
-- title:
--   Sign filters $S_i$ and filtered fidelity $F_c(A,B\mid\{P_i\})$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$.
--
--   1. The **sign filters** are $S_i(x,y):=(-1)^{x_i+y_i}$ for $x,y\in\Sigma$ and $i\in[n]$, so $S_i=J-2\Delta_i$.
--   2. For a constant $c>1$, Gram filters $\{P_i\}$ with $P_i\circ I=I$, and positive semidefinite $A,B$ on $\Sigma$, the **filtered fidelity with cost $c$** is
--   $$
--   F_c(A,B\mid\{P_i\}):=\inf_{\Gamma\succ0}\sqrt{\langle\Gamma,A\rangle\,\langle\Gamma^{-1},B\rangle}\quad\text{s.t.}\quad \Gamma\circ P_i\preceq c\,\Gamma\ \ \forall i,
--   $$
--   where $\langle X,Y\rangle=\mathrm{Tr}[X^\dagger Y]$.
--
--   The filtered fidelity restricts Alberti's variational formula for the fidelity to adversary matrices that change by at most a factor $c$ under one query; it is the building block of the filtered $\delta_2$ measure and the Alberti adversary measure.
--
--   **Formalization Note** $\Gamma$ ranges over positive definite complex matrices, $\Gamma\circ P_i\preceq c\Gamma$ is $c\Gamma-\Gamma\circ P_i\succeq0$, and the real part of $\langle\cdot,\cdot\rangle$ is taken (it is real and nonnegative here). The infimum is the real infimum of the feasible values: for $c>1$ and sign filters $\Gamma=I$ is feasible and all values are $\ge0$, so it is the paper's infimum. On a position set of $k$-fold inputs the sign filters are the paper's $S_{ij}=J^{\otimes(i-1)}\otimes S_j\otimes J^{\otimes(k-i)}$.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), §2.4.1, p.17 (sign matrix S_i); Definition 8.1, p.68

import Mathlib
import Definitions.Def_DistQuantumQuery_traceNorm

open scoped Matrix ComplexOrder

namespace DistQuantumQuery.Supplement

open DistQuantumQuery

/-- The **sign filters** `S_i(x, y) := (−1)^{x_i + y_i}` on an input set `Σ ⊆ {0,1}^ι`, one per
bit position `i` (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*,
arXiv:2610.06835, held version, sha256 6334ffaf…, §2.4.1, p.17 and §8.1, p.68), so `S_i = J − 2Δ_i`.

**Formalization Note** Applied to the `k`-fold set `Σ^k` (positions `Fin k × ι`) this gives the
filters `S_{ij} = J^{⊗(i−1)} ⊗ S_j ⊗ J^{⊗(k−i)}` of pp.71, 79, 85. -/
def signFilters {ι : Type*} (S : Finset (ι → Bool)) : ι → Matrix S S ℂ :=
  fun i => Matrix.of fun x y => if x.1 i = y.1 i then 1 else -1

/-- The **filtered fidelity** with cost `c` (arXiv:2610.06835, held version, sha256 6334ffaf…,
Definition 8.1, p.68):
`F_c(A, B | {P_i}) := inf_{Γ ≻ 0} √(⟨Γ, A⟩⟨Γ^{−1}, B⟩)` subject to `Γ ∘ P_i ⪯ cΓ` for all `i`.

**Formalization Note** `Γ` ranges over positive definite complex matrices on `Σ`; `Γ ∘ P_i ⪯ cΓ`
is `cΓ − Γ ∘ P_i ⪰ 0`; `⟨Γ, A⟩ = Tr[Γ†A]` is the base mission's `hsInner`, and its real part is
taken (it is real and nonnegative for `Γ ≻ 0`, `A ⪰ 0`); `Γ^{−1}` is the matrix inverse. The
infimum is the real `sInf` of the set of feasible values. In every use (`c > 1`, sign filters,
whose diagonals are `1`) the set is nonempty (`Γ = I` is feasible) and bounded below by `0`, so
`sInf` is the paper's infimum. The hypotheses of Definition 8.1 on the filters and on `A`, `B`
(Gram filters with unit diagonal, `A, B ⪰ 0`, `c > 1`) are not built in. -/
noncomputable def filteredFidelity {X P : Type*} [Fintype X] [DecidableEq X] (c : ℝ)
    (A B : Matrix X X ℂ) (Pf : P → Matrix X X ℂ) : ℝ :=
  sInf {t : ℝ | ∃ Γ : Matrix X X ℂ, Γ.PosDef ∧ (∀ i, ((c : ℂ) • Γ - Γ ⊙ Pf i).PosSemidef) ∧
    t = Real.sqrt ((hsInner Γ A).re * (hsInner Γ⁻¹ B).re)}

end DistQuantumQuery.Supplement


