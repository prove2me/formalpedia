-- Prove2me | Definitions.Def_ChanTomoNB_Tester
-- name    : ChanTomoNB_Tester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:31:31.871196+00:00
-- url     : https://prove2.me/theorems/763843fe-9d9d-4d8e-8f3a-042ca7af318c
-- title:
--   Quantum combs, channel testers and success of a tomography tester
-- statement:
--   Fix input and output spaces $\mathcal H_A\cong\mathbb C^{d_1}$, $\mathcal H_B\cong\mathbb C^{d_2}$ of one query, and $n$ queries labelled $(\mathcal H_{A,j},\mathcal H_{B,j})_{j=1}^n$.
--
--   1. An operator $S\succeq0$ on $\bigotimes_j(\mathcal H_{A,j}\otimes\mathcal H_{B,j})$ is a **quantum $(n+1)$-comb** on $(\mathcal H_0,\mathcal H_{A,1},\mathcal H_{B,1},\dots,\mathcal H_{A,n},\mathcal H_{B,n},\mathcal H_{n+1})$ with $\mathcal H_0\cong\mathcal H_{n+1}\cong\mathbb C$ if there are operators $X^{(n)},\dots,X^{(1)}$ with
--   $$
--   S=I_{B_n}\otimes X^{(n)},\qquad \operatorname{tr}_{A_k}X^{(k)}=I_{B_{k-1}}\otimes X^{(k-1)}\ (2\le k\le n),\qquad \operatorname{tr}_{A_1}X^{(1)}=1 .
--   $$
--   2. A **tester** with $n$ queries is a family $\{T_i\}_i$ of operators $T_i\succeq0$ whose sum is such a comb.
--   3. Applied to $n$ queries of $\mathcal E$, it yields outcome $i$ with probability $p_i=\operatorname{tr}(T_i^{T}C_{\mathcal E}^{\otimes n})$.
--   4. A tester with estimates $\hat{\mathcal E}_i$ **learns** $\mathbf{QChan}^r_{d_1,d_2}$ to error $\varepsilon$ in a distance $\mathrm{dist}$ if for every $\mathcal E\in\mathbf{QChan}^r_{d_1,d_2}$
--   $$
--   \sum_{i:\ \mathrm{dist}(\hat{\mathcal E}_i,\mathcal E)\le\varepsilon}p_i\ \ge\ \tfrac23 .
--   $$
--
--   Every sequential, adaptive and coherent query algorithm with a reference system and quantum memory is a tester, so lower bounds for testers are lower bounds for all such algorithms.
--
--   **Formalization Note** One query is indexed by (input, output); the identity factors are indicators on the output indices; the intermediate operators need not be positive (Definition 2.1 does not require it). The outcome set is an arbitrary type and $\sum_iT_i$ converges entrywise. $\operatorname{tr}(T^TC)$ is the entrywise pairing $\sum_{x,y}T_{xy}C_{xy}$. Estimates are arbitrary linear maps.
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Definitions 2.1 and 2.3, Eq. (8), pp.11–12; Theorem 6.1, p.33

import Mathlib
import Definitions.Def_ChanTomoNB_QChan
import Definitions.Def_ChanTomoNB_choi

open Matrix
open scoped ComplexOrder

namespace ChanTomoNB

/-- The normalization of a channel tester: `S` is a quantum `(n+1)`-comb on
`(H_0, H_{A,1}, H_{B,1}, …, H_{A,n}, H_{B,n}, H_{n+1})` with `H_0 ≅ H_{n+1} ≅ ℂ`. Chen, Oufkir,
*Quantum channel tomography: optimal bounds in the near-boundary regime*, arXiv:2611.03639v1,
Definition 2.1 (Eq. (8)) and Definition 2.3, pp.11–12.

Written out: `S ⪰ 0` and there are operators `Ξ k = X^{(k+1)}` on
`A_1 B_1 ⋯ A_k B_k A_{k+1}` with
* `S = I_{B_n} ⊗ Ξ (n−1)` (Eq. (8) for `j = n + 1`, `H_{2n+1}` trivial);
* `tr_{A_{k+1}} Ξ k = I_{B_k} ⊗ Ξ (k−1)` for `1 ≤ k < n` (Eq. (8) for `j = k + 1`);
* `tr_{A_1} Ξ 0 = 1` (Eq. (8) for `j = 1`, `X^{(0)} = 1`, `H_0` trivial);
and `S = 1` when `n = 0`.

**Formalization Note.** One query is indexed by `A × B` (input first); `n` queries by
`Fin n → A × B`, so the `k`-th query of `x` is `x k` and `Fin.init` drops the last query.
The intermediate operators `Ξ k` need not be positive (Definition 2.1 does not ask it); `Ξ k`
for `k ≥ n` is unconstrained. The identity factors `I_{B_k}` are the indicators
`[b_k(x) = b_k(y)]`. This is the standard tester normalization of [CDP09]; a different encoding
of the same normalization is the published `QAlgorithms.Papers.Independent.Dependency50.P26`
(newest-output-first), which is not reused. -/
def IsTesterComb {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    {n : ℕ} → Matrix (Fin n → A × B) (Fin n → A × B) ℂ → Prop
  | 0, S => S = 1
  | m + 1, S => S.PosSemidef ∧
      ∃ Ξ : (k : ℕ) → Matrix ((Fin k → A × B) × A) ((Fin k → A × B) × A) ℂ,
        (∀ x y : Fin (m + 1) → A × B,
          S x y = (if (x (Fin.last m)).2 = (y (Fin.last m)).2 then 1 else 0) *
            Ξ m (Fin.init x, (x (Fin.last m)).1) (Fin.init y, (y (Fin.last m)).1)) ∧
        (∀ k : ℕ, k + 1 ≤ m → ∀ v v' : Fin (k + 1) → A × B,
          ∑ a : A, Ξ (k + 1) (v, a) (v', a) =
            (if (v (Fin.last k)).2 = (v' (Fin.last k)).2 then 1 else 0) *
              Ξ k (Fin.init v, (v (Fin.last k)).1) (Fin.init v', (v' (Fin.last k)).1)) ∧
        (∀ v v' : Fin 0 → A × B, ∑ a : A, Ξ 0 (v, a) (v', a) = 1)

/-- A channel tester with `n` queries (arXiv:2611.03639v1, Definition 2.3, p.12): operators
`T_i ⪰ 0` on `⊗_{j=1}^n (H_{A,j} ⊗ H_{B,j})` whose sum is a quantum `(n+1)`-comb.

**Formalization Note.** The outcome set `ι` is an arbitrary type and `∑ᵢ Tᵢ` is an unconditional
sum (`HasSum`, entrywise convergence); finite testers are the case of a finite `ι`. Every
sequential, adaptive, coherent query algorithm is a tester (p.12, [CDP09, BMQ22]). -/
structure Tester (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (n : ℕ) where
  /-- the set of classical outcomes -/
  ι : Type
  /-- the tester operators -/
  T : ι → Matrix (Fin n → A × B) (Fin n → A × B) ℂ
  psd : ∀ i, (T i).PosSemidef
  /-- the sum of the tester operators -/
  S : Matrix (Fin n → A × B) (Fin n → A × B) ℂ
  hasSum : HasSum T S
  comb : IsTesterComb S

/-- `C_E^{⊗n}` written on the tester's space `⊗_j (H_{A,j} ⊗ H_{B,j})`: the entry at `(x, y)` is
`∏_j (C_E)_{(b_j, a_j), (b'_j, a'_j)}` with `x j = (a_j, b_j)`, `y j = (a'_j, b'_j)`
(arXiv:2611.03639v1, §2.2, p.12). -/
noncomputable def choiPow {A B : Type} [DecidableEq A] (E : Superop A B) (n : ℕ) :
    Matrix (Fin n → A × B) (Fin n → A × B) ℂ :=
  Matrix.of fun x y => ∏ j, choi E ((x j).2, (x j).1) ((y j).2, (y j).1)

/-- The probability `p_i = tr(T_iᵀ C_E^{⊗n})` of outcome `i` when the tester is applied to `n`
queries of `E` (arXiv:2611.03639v1, §2.2, p.12).

**Formalization Note.** `tr(Tᵀ C) = ∑_{x,y} T_{xy} C_{xy}` (the entrywise pairing); the factors of
`C_E^{⊗n}` are reordered to the tester's order by `choiPow`. The value is real for a channel;
the real part is taken. -/
noncomputable def Tester.prob {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] {n : ℕ} (T : Tester A B n) (E : Superop A B) (i : T.ι) : ℝ :=
  (∑ x, ∑ y, T.T i x y * choiPow E n x y).re

/-- The tester, with the estimate map `est` (outcome `i` names the estimate `Ê = est i`), learns
every channel in `QChan^r_{d1,d2}` to error `ε` in the distance `dist` with success probability at
least `2/3`: for every `E ∈ QChan^r_{d1,d2}`, the total probability of the outcomes `i` with
`dist(Ê_i, E) ≤ ε` is at least `2/3` (arXiv:2611.03639v1, Theorem 6.1, p.33: "If ‖Ê − E‖ ≤ ε with
probability at least 2/3").

**Formalization Note.** Estimates are arbitrary linear maps. The probability of the event is the
sum `∑'` over outcomes of `p_i` restricted to the event. -/
def Tester.Learns {d1 d2 n : ℕ} (T : Tester (Fin d1) (Fin d2) n)
    (est : T.ι → Superop (Fin d1) (Fin d2))
    (dist : Superop (Fin d1) (Fin d2) → Superop (Fin d1) (Fin d2) → ℝ) (r : ℕ) (ε : ℝ) : Prop :=
  ∀ E ∈ QChan r d1 d2, (2 / 3 : ℝ) ≤ ∑' i, if dist (est i) E ≤ ε then T.prob E i else 0

end ChanTomoNB


