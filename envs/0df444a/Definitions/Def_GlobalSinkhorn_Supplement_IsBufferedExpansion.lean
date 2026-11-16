-- Prove2me | Definitions.Def_GlobalSinkhorn_Supplement_IsBufferedExpansion
-- name    : GlobalSinkhorn_Supplement_IsBufferedExpansion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:56:02.991043+00:00
-- url     : https://prove2.me/theorems/d10dc018-b192-4325-ab01-654ad7e7ef1f
-- title:
--   Definition 2.3 — $(q,\eta,\phi)$-two-sided buffered robust vertex expansion
-- statement:
--   Let $n\ge2$, $q\in(1/2,1)$, $\eta,\phi>0$ with $q(1+\eta)<1$, and let $A\in\mathbb R^{n\times n}_{\ge0}$ be row-stochastic. For $I,J\subseteq[n]$ write $A(I,J)=\sum_{i\in I,\,j\in J}A_{ij}$. The matrix $A$ satisfies **$(q,\eta,\phi)$-two-sided buffered robust vertex expansion** if
--
--   1. for every nonempty $I\subseteq[n]$ with $|I|\le qn$ and every $J\subseteq[n]$ with $|J|\le(1+\eta)|I|$,
--   $$A(I,[n]\setminus J)\ge\phi|I|;\qquad(18)$$
--   2. for every nonempty $J\subseteq[n]$ with $|J|\le qn$ and every $I\subseteq[n]$ with $|I|\le(1+\eta)|J|$,
--   $$A([n]\setminus I,J)\ge\phi|J|.\qquad(19)$$
--
--   Every small row set sends a fixed fraction of its mass outside any slightly larger column buffer, and symmetrically for columns. It is the structural hypothesis from which the paper derives polynomial bounds on the diagonal scaling factors (Theorem 4.1).
--
--   **Formalization Note** The context of the definition ($n\ge2$, $1/2<q<1$, $\eta>0$, $\phi>0$, $q(1+\eta)<1$, $A$ row-stochastic) is bundled as the first conjuncts of the predicate, so it never holds outside that context. Sets are `Finset (Fin n)`, $[n]\setminus J$ is `Jᶜ`, and sizes are compared as real numbers.
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Definition 2.3, Eqs. (18)–(19), p.14

import Mathlib

open Matrix

namespace GlobalSinkhorn.Supplement

/-- `(q, η, φ)`-two-sided buffered robust vertex expansion. He, Global Sinkhorn Convergence and
Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad),
Definition 2.3, Eqs. (18)–(19), p.14.

The standing data of the definition (`n ≥ 2`, `q ∈ (1/2, 1)`, `η, φ > 0`, `q(1 + η) < 1`, `A`
nonnegative and row-stochastic) are the first conjuncts; then (18): every nonempty row set `I`
with `|I| ≤ qn` sends mass at least `φ|I|` outside every column set `J` with
`|J| ≤ (1 + η)|I|`; and (19): every nonempty column set `J` with `|J| ≤ qn` receives mass at
least `φ|J|` from outside every row set `I` with `|I| ≤ (1 + η)|J|`.

**Formalization Note.** Indices are `Fin n`; sets are `Finset (Fin n)`; `[n] \ J` is `Jᶜ`;
`A(I, J) = ∑_{i ∈ I} ∑_{j ∈ J} A i j`. Set sizes are compared as real numbers. The paper states
the parameter conditions as the context in which the predicate is defined; they are bundled
here so the predicate never holds outside that context. -/
def IsBufferedExpansion {n : ℕ} (q η φ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  2 ≤ n ∧ 1 / 2 < q ∧ q < 1 ∧ 0 < η ∧ 0 < φ ∧ q * (1 + η) < 1 ∧
  A ∈ Matrix.rowStochastic ℝ (Fin n) ∧
  (∀ I J : Finset (Fin n), I.Nonempty → (I.card : ℝ) ≤ q * n →
      (J.card : ℝ) ≤ (1 + η) * I.card →
      φ * I.card ≤ ∑ i ∈ I, ∑ j ∈ Jᶜ, A i j) ∧
  (∀ I J : Finset (Fin n), J.Nonempty → (J.card : ℝ) ≤ q * n →
      (I.card : ℝ) ≤ (1 + η) * J.card →
      φ * J.card ≤ ∑ i ∈ Iᶜ, ∑ j ∈ J, A i j)

end GlobalSinkhorn.Supplement


