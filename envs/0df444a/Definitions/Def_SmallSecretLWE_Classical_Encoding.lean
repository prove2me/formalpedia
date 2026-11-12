-- Prove2me | Definitions.Def_SmallSecretLWE_Classical_Encoding
-- name    : SmallSecretLWE_Classical_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:27:13.978225+00:00
-- url     : https://prove2.me/theorems/b6ea6232-92e2-4a8f-a388-e4ad1fec547d
-- title:
--   Machine inputs and outputs for sparse k-LIN$(\mathbb Z_q)$, the parameter oracle, expected cost and the distinguishing probabilities
-- statement:
--   Algorithms run on the published fair-coin log-cost RAM (`PrefixMixLearn_Proper_Machine`): every instruction is charged one plus the bit lengths of what it touches, and its only randomness is a fair coin.
--
--   **Inputs.** A sparse vector is written as the pairs $(j,a_j)$ over its support in increasing $j$, with $a_j\in\{1,\dots,q-1\}$. The matrix input is $[n,m,q,k,l]$ followed by the sparse rows of $A$; the instance input writes, after each row $a_i$, the value $b_i\in\{0,\dots,q-1\}$. Rows with exactly $k$ nonzeros take $2k$ cells each, giving random access to the rows. A vector $c\in\mathbb Z_q^m$ is output as $[c_1,\dots,c_m]$; PLANTED is the output $[1]$, RANDOM is $[0]$.
--
--   **Real parameters** $x_0,x_1,\dots$ (such as $B,D,\varepsilon$ or $R,\delta$) reach the program only through the deterministic **parameter oracle**: the query $[i,j]$ is answered with $[\lfloor 2^j x_i\rfloor]$, every other query with $[\,]$.
--
--   The **expected cost** is $\sup_t\mathbb E[\text{cost after } t \text{ steps}]$. For a program $P$, $\mathrm{randomAccept}=\sum_b q^{-m}\Pr[P(A,b)=[0]]$ and $\mathrm{plantedAccept}(s,\Psi)=\sum_e\Pr_{\Psi^m}[e]\Pr[P(A,As+e)=[1]]$.
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 15, Lemma 4.1; pp. 22–23, Corollary 4.8; pp. 31–33, §5 and Theorem 5.1

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Machine
import Definitions.Def_SmallSecretLWE_Classical_Basic

set_option autoImplicit false

open scoped Classical

open PrefixMixLearn.Proper (Program Oracle runLaw outProb)

noncomputable section

namespace SmallSecretLWE.Classical

/-!
# Inputs, outputs, the parameter oracle and the distinguishing success probabilities

Agrawal, Bagchi, Kumar, *Algorithms for Sparse LWE and LPN with Small Secrets*, STOC 2027
submission (manuscript sha256 8d93a268…): Lemma 4.1, p. 15 ("random access to the sparse
representations of the rows"); Corollary 4.8, pp. 22–23; §5 and Theorem 5.1, pp. 31–33.

The machine is the published fair-coin log-cost RAM `PrefixMixLearn.Proper` (`Program`,
`runLaw`, `outProb`, `HaltsWithin`); its oracle slot carries the parameter oracle below.

* A sparse vector `a ∈ Z_q^n` is written as the pairs `(j, a_j)` over its support in increasing
  column order, `a_j ∈ {1, …, q−1}` (`sparseCells`). A row with exactly `k` nonzero entries is
  `2k` cells, so row `i` sits at a fixed offset (random access).
* `matrixInput k l A = [n, m, q, k, l] ++ rows of A`; `instanceInput k l A b` writes each row
  followed by `b_i ∈ {0, …, q−1}`. A vertex of the Kikuchi graph is output as its sparse cells; a
  vector `c ∈ Z_q^m` as the list `[c_1, …, c_m]` of values in `{0, …, q−1}` (`vecCells`).
* `paramOracle xs` answers the query `[i, j]` with `[⌊2^j · x_i⌋]` for `i < |xs|` and every other
  query with `[]`: real parameters reach the program only as their binary expansions, to any
  precision the program pays for. `nullOracle` answers every query with `[]`.
* `expCost P O input = sup_t E[cost after t steps]`, the expected total log-cost (the cost after
  `t` steps is nondecreasing in `t`; a run that never halts has infinite cost).
* `randomAccept`: the probability, over `b` uniform on `Z_q^m` and the run, that the output is
  `[0]` (RANDOM); `plantedAccept`: the probability, over `e ∼ Ψ^m` and the run, that the
  output on `b = A s + e` is `[1]` (PLANTED).
-/

/-- The sparse representation of `a ∈ Z_q^n`: the pairs `(j, a_j)` over the support, in
increasing `j`. -/
def sparseCells {n q : ℕ} (a : Fin n → ZMod q) : List ℕ :=
  ((List.finRange n).filter fun j => decide (a j ≠ 0)).flatMap fun j => [j.val, (a j).val]

/-- The input `[n, m, q, k, l]` followed by the sparse rows of `A`. -/
def matrixInput {m n q : ℕ} (k l : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod q)) : List ℕ :=
  [n, m, q, k, l] ++ (List.finRange m).flatMap fun i => sparseCells (A i)

/-- The input `[n, m, q, k, l]` followed, for each `i`, by the sparse row `a_i` and `b_i`. -/
def instanceInput {m n q : ℕ} (k l : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (b : Fin m → ZMod q) : List ℕ :=
  [n, m, q, k, l] ++ (List.finRange m).flatMap fun i => sparseCells (A i) ++ [(b i).val]

/-- A vector of `Z_q^m` as the list of its values in `{0, …, q − 1}`. -/
def vecCells {m q : ℕ} (c : Fin m → ZMod q) : List ℕ := List.ofFn fun i => (c i).val

/-- The deterministic parameter oracle for the real parameters `xs`:
`[i, j] ↦ [⌊2^j · x_i⌋]` (`i < |xs|`), everything else `↦ []`. -/
def paramOracle (xs : List ℝ) : Oracle := fun qry =>
  match qry with
  | [i, j] => if h : i < xs.length then PMF.pure [⌊(2 : ℝ) ^ j * xs[i]⌋₊] else PMF.pure []
  | _ => PMF.pure []

/-- The oracle that answers every query with `[]`. -/
def nullOracle : Oracle := fun _ => PMF.pure []

/-- The expected total log-cost `sup_t E[cost after t steps]`. -/
def expCost (P : Program) (O : Oracle) (input : List ℕ) : ENNReal :=
  ⨆ t, ∑' s, runLaw P O input t s * (s.cost : ENNReal)

/-- `Pr[output RANDOM]` on a random instance: `b` uniform on `Z_q^m`. -/
def randomAccept {m n q : ℕ} [NeZero q] (P : Program) (O : Oracle) (k l : ℕ)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) : ℝ :=
  ∑ b : Fin m → ZMod q, unifProb q m * outProb P O (instanceInput k l A b) (fun o => o = [0])

/-- `Pr[output PLANTED]` on a planted instance: `b = A s + e`, `e ∼ Ψ^m`. -/
def plantedAccept {m n q : ℕ} [NeZero q] (P : Program) (O : Oracle) (k l : ℕ)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Fin n → ZMod q) (Ψ : PMF (ZMod q)) : ℝ :=
  ∑ e : Fin m → ZMod q,
    prodProb Ψ e * outProb P O (instanceInput k l A (plantedRHS A s e)) (fun o => o = [1])

end SmallSecretLWE.Classical


