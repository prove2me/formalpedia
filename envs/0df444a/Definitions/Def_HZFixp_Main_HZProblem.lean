-- Prove2me | Definitions.Def_HZFixp_Main_HZProblem
-- name    : HZFixp_Main_HZProblem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:51:24.168232+00:00
-- url     : https://prove2.me/theorems/5ee6391b-1306-4a9c-a610-e5f0ebc4b786
-- title:
--   Definition 3.5 — the search problems HZ Equilibrium and HZ allocation
-- statement:
--   A **one-sided matching market** has $n$ agents and $n$ goods, each good with unit supply, and a utility matrix $v \in [0,1]^{n\times n}$: agent $i$ values a bundle $x \in \mathbb{R}^n_{\ge 0}$ at $v_i \cdot x$. An **allocation** is a matrix $X$ in
--   $$B_n = \Big\{X \in \mathbb{R}^{n\times n}_{\ge 0} : \textstyle\sum_j X_{ij} = 1 \ (i \in [n]),\ \sum_i X_{ij} = 1 \ (j \in [n])\Big\},$$
--   and every agent has budget one and faces the same prices $p \ge 0$. A pair $(X, p)$ with $X \in B_n$, $p \ge 0$ is an **HZ equilibrium** (Definition 2.1) if (i) $p \cdot X_i \le 1$ for every agent $i$ and (ii) $v_i \cdot X_i = \mathrm{OPT}_i(p) = \max\{v_i \cdot y : y \in \Delta_n,\ p \cdot y \le 1\}$.
--
--   **HZ Equilibrium** (Definition 3.5) is the search problem whose instances are the rational matrices $v \in [0,1]^{n\times n}$ (any $n$), written in binary, and whose solutions are the HZ equilibria $(X, p)$, written as the real vector $(X_{11},\dots,X_{1n},\dots,X_{nn},p_1,\dots,p_n)$ of length $n^2+n$. The **allocation-only** version has the same instances; its solutions are the allocations $X$ (length $n^2$, row-major) for which some price vector $p$ makes $(X,p)$ an HZ equilibrium.
--
--   These are the problems of Theorem 1.1: the first is FIXP-complete, and already the second is FIXP-hard.
--
--   **Formalization Note.** Definition 2.1 is the published `CardinalMatching.IsApproxHZ` at $\varepsilon = 0$ (row and column sums exactly one, $p \ge 0$, $p\cdot X_i \le 1$, $v_i \cdot X_i \ge \mathrm{OPT}_i(p)$ with the maximum attained; equality follows because $X_i$ is itself affordable). There is no minimum-cost condition (footnote 2), no price normalization, and the §2 utility normalization ($\min_j v_{ij}=0$, $\max_j v_{ij}=1$) is not imposed on instances. Indices are $0$-based; the instance is the list of rows.
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 7 (PDF 9), Definition 3.5; p. 5 (PDF 7), Definition 2.1; p. 4 (PDF 6), §2

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch
import Definitions.Def_CardinalMatching_IsApproxHZ

namespace HZFixp.Main

open OnlineCRS.Combine FixpReciprocal

/-- The data of an HZ market: the number `n` of agents (and of goods) and the rows of the rational
utility matrix `v`, row `i` listing `v_{i1}, …, v_{in}`. -/
structure HZData where
  /-- the number of agents, which is also the number of goods -/
  n : ℕ
  /-- the utility rows -/
  rows : List (List ℚ)

/-- **An instance of HZ Equilibrium (Definition 3.5):** "A rational utility matrix
`v ∈ [0, 1]^{n×n}`": `n` rows of `n` rationals, each in `[0, 1]`.

Liu, Tao, Yan, *Settling the Complexity of Hylland–Zeckhauser Equilibria*, arXiv:2606.06317 (held
version later than v2, sha256 36e91522…af1c), p. 7, Definition 3.5. -/
def HZData.IsInstance (D : HZData) : Prop :=
  D.rows.length = D.n ∧ ∀ row ∈ D.rows, row.length = D.n ∧ ∀ q ∈ row, 0 ≤ q ∧ q ≤ 1

/-- Instances of HZ Equilibrium. -/
def HZInst : Type := {D : HZData // D.IsInstance}

/-- The utility `v_{ij}` of agent `i` for good `j`, as a real number (indices are `0`-based). -/
noncomputable def HZData.util (D : HZData) (i j : Fin D.n) : ℝ :=
  (((D.rows.getD i.val []).getD j.val 0 : ℚ) : ℝ)

/-- Binary encoding of an HZ market: `n`, then the list of rows, every rational written with binary
numerator and denominator ("encoded in binary", Definition 3.5). -/
def encHZData (D : HZData) : List Sym := fNat D.n ++ fList (fList fRat) D.rows

theorem encHZData_injective : Function.Injective encHZData := by
  rintro ⟨n, r⟩ ⟨n', r'⟩ h
  simp only [encHZData] at h
  obtain ⟨h1, h⟩ := fNat_prefixFree h
  have h2 := fRat_prefixFree.fList.fList.injective h
  simp_all

/-- The allocation entry `X_{ij}` of a solution vector: coordinate `i·n + j` (row-major order). -/
noncomputable def solX {n m : ℕ} (s : Fin m → ℝ) (i j : Fin n) : ℝ :=
  lookup s (i.val * n + j.val)

/-- The price `p_j` of a solution vector of HZ Equilibrium: coordinate `n² + j`, after the `n²`
allocation entries. -/
noncomputable def solP {n m : ℕ} (s : Fin m → ℝ) (j : Fin n) : ℝ :=
  lookup s (n * n + j.val)

/-- **HZ Equilibrium as a search problem (Definition 3.5).** Input: a rational utility matrix
`v ∈ [0, 1]^{n×n}`, encoded in binary. Output: an allocation `X ∈ B_n` and prices `p ≥ 0` such that
`(X, p)` satisfies the HZ equilibrium conditions of Definition 2.1. A solution is the real vector
`(X_{11}, …, X_{1n}, …, X_{nn}, p_1, …, p_n)` of length `n² + n`.

Liu, Tao, Yan, *Settling the Complexity of Hylland–Zeckhauser Equilibria*, arXiv:2606.06317 (held
version later than v2, sha256 36e91522…af1c), p. 7, Definition 3.5; p. 5, Definition 2.1.

**Formalization Note.** Definition 2.1 is the published `CardinalMatching.IsApproxHZ` at `ε = 0`:
`X ≥ 0` with row and column sums exactly one (`X ∈ B_n`), `p ≥ 0`, `p · X_i ≤ 1`, and
`v_i · X_i ≥ OPT_i(p)`, the maximum of `v_i · y` over affordable `y ∈ Δ_n` (attained); since `X_i` is
itself affordable this is `v_i · X_i = OPT_i(p)`. There is no minimum-cost condition (footnote 2)
and no price normalization, and the §2 utility normalization is not imposed on instances. -/
noncomputable def hzProblem : RealSearch where
  Inst := HZInst
  enc := fun I => encHZData I.1
  enc_injective := fun _ _ h => Subtype.ext (encHZData_injective h)
  dim := fun I => I.1.n * I.1.n + I.1.n
  Sol := fun I => {s | CardinalMatching.IsApproxHZ I.1.util 0 (solX s) (solP s)}

/-- **HZ Equilibrium, allocation only (Theorem 3.6: "even when only the equilibrium allocation is
requested").** Same instances; a solution is the allocation `X` alone, the vector
`(X_{11}, …, X_{nn})` of length `n²` in row-major order, such that some prices `p` make `(X, p)` an
HZ equilibrium (Definition 2.1).

Liu, Tao, Yan, *Settling the Complexity of Hylland–Zeckhauser Equilibria*, arXiv:2606.06317 (held
version later than v2, sha256 36e91522…af1c), p. 7, Definition 3.5 and Theorem 3.6; p. 2,
Theorem 1.1. -/
noncomputable def hzAllocProblem : RealSearch where
  Inst := HZInst
  enc := fun I => encHZData I.1
  enc_injective := fun _ _ h => Subtype.ext (encHZData_injective h)
  dim := fun I => I.1.n * I.1.n
  Sol := fun I => {s | ∃ p : Fin I.1.n → ℝ, CardinalMatching.IsApproxHZ I.1.util 0 (solX s) p}

end HZFixp.Main


