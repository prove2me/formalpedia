-- Prove2me | Definitions.Def_L22EigEst_Supplement_SpecQueryAlg
-- name    : L22EigEst_Supplement_SpecQueryAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:36:28.4242+00:00
-- url     : https://prove2.me/theorems/6a21d43f-6b99-4704-a44e-56250ddefe4a
-- title:
--   Randomized adaptive spectrum-estimation algorithms in the $\ell_2^2$-sampling model (Definition 5.4)
-- statement:
--   A **deterministic adaptive algorithm** for estimating the spectrum of an $n\times n$ matrix $A$ is a finite decision tree: at each inner node it queries an entry $(j,j')\in[n]\times[n]$ and continues in a subtree chosen by the real answer $A_{jj'}$; each leaf carries the output estimates $\hat\lambda_1,\dots,\hat\lambda_n\in\mathbb R$. A **randomized algorithm** in the $\ell_2^2$-sampling model receives the squared row norms $r=(\|A_1\|_2^2,\dots,\|A_n\|_2^2)$ and draws such a tree from a probability distribution that depends on $r$ only.
--
--   On an input $A$, a tree $T$ follows one path. Along it,
--
--   1. the **query count** is the number of queries made (repeats counted);
--   2. the **touched rows/columns** are the distinct indices $j\in[n]$ that occur in some query, as a row or as a column index;
--   3. $T$ **succeeds** on $A$ if $A$ is symmetric and $|\hat\lambda_j-\lambda_j(A)|\le\varepsilon\|A\|_F$ for every $j$, where $\lambda_1(A)\ge\dots\ge\lambda_n(A)$ are the eigenvalues of $A$ and $\|A\|_F$ its Frobenius norm.
--
--   For a distribution $\mathcal D$ over matrices, the **success probability** of a randomized algorithm is
--
--   $$\sum_A \mathcal D(A)\,\Pr_{T\sim \mathrm{alg}(r(A))}[T \text{ succeeds on } A],$$
--
--   taken jointly over the input and the algorithm's coins. This is the model of the lower bounds, Theorems 8 and 9.
--
--   **Formalization Note** Trees are the published adaptive probe trees `DynOracleConn.ProbeTree` with questions `Fin n × Fin n`, replies `ℝ` and results `Fin n → ℝ`; being inductive, every run is finite. The randomness is a `PMF` (discrete random bits). Definition 5.4 asks the output to be sorted; that requirement is dropped, which only enlarges the class of algorithms. Indices are 0-based.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Definition 5.4, pp.27–28, and the reduction paragraph before it, p.27; §5 standing assumption, p.26

import Definitions.Def_DynOracleConn_ProbeTree
import Definitions.Def_L22EigEst_rowSq
import Definitions.Def_WainwrightHDS_EigPert_gamma

open DynOracleConn WainwrightHDS.EigPert

namespace L22EigEst.Supplement

/-- **Deterministic adaptive spectrum-estimation algorithm** on `n × n` matrices (Definition 5.4,
pp.27–28), for one fixed list of squared row norms: an adaptive probe tree whose questions are
positions `(j, j′) ∈ [n] × [n]`, whose replies are the real entries `A_{jj′}`, and whose leaves carry
the output estimates `λ̂ : Fin n → ℝ`.
Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…), Definition 5.4, p.27: "Alg queries entries (j, j′) ∈ [n] × [n]
of A one at a time, where each query is a function of the row norms and of the answers to the previous
queries … Alg outputs estimates λ̂1 ≥ ⋯ ≥ λ̂n, which are a function of the row norms and of the answers
to all of its queries."

**Formalization Note.** The dependence on the row norms is carried by `RandSpecAlg` (a tree is chosen
as a function of the row norms). The tree type is inductive, so every run is finite. The output is
not required to be sorted (Definition 5.4 asks `λ̂1 ≥ ⋯ ≥ λ̂n`); dropping this enlarges the class of
algorithms. Indices are 0-based. -/
abbrev SpecTree (n : ℕ) : Type := ProbeTree (Fin n × Fin n) ℝ (Fin n → ℝ)

/-- The entry oracle of a matrix: question `(j, j′)` is answered by `A_{jj′}`. -/
def entryOracle {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Fin n × Fin n → ℝ :=
  fun q => A q.1 q.2

/-- **A randomized adaptive spectrum-estimation algorithm** in the ℓ₂²-sampling model (p.27, "a
randomized algorithm … on every input and every choice of its random bits"; p.26, "the algorithm
receives access to the squared row norms ∥A1∥2², …, ∥An∥2² of A"): from the list `r` of squared row
norms, a probability distribution over deterministic adaptive trees.

**Formalization Note.** The randomness is a `PMF` (discrete random bits). The algorithm sees the
matrix only through `r` and the answers to its queries; it is applied to `r = rowSq A`. -/
abbrev RandSpecAlg (n : ℕ) : Type := (Fin n → ℝ) → PMF (SpecTree n)

/-- The number of queries the tree `T` makes on input `A` (repeated queries counted each time). -/
def queryCount {n : ℕ} (T : SpecTree n) (A : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  T.cost (entryOracle A)

/-- The set of distinct rows/columns `j ∈ [n]` that appear in the queries of `T` on input `A`, as a
row index or as a column index (Definition 5.4, "at most t distinct rows/columns j ∈ [n] appear in its
queries"). -/
def touched {n : ℕ} (T : SpecTree n) (A : Matrix (Fin n) (Fin n) ℝ) : Finset (Fin n) :=
  ((T.transcript (entryOracle A)).flatMap fun x => [x.1.1, x.1.2]).toFinset

/-- The tree `T` **succeeds on** `A` (Definition 5.4, p.28): `A` is symmetric and the output is an
additive `ε‖A‖_F`-approximation to its spectrum, `|λ̂_j − λ_j(A)| ≤ ε‖A‖_F` for every `j`, where
`λ_1(A) ≥ ⋯ ≥ λ_n(A)` (`gamma`, 0-based) and `‖A‖_F` is the Frobenius norm. -/
def Succeeds {n : ℕ} (ε : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (T : SpecTree n) : Prop :=
  ∃ hA : A.IsHermitian, ∀ j : Fin n,
    |T.run (entryOracle A) j - gamma A hA j| ≤ ε * L22EigEst.frob A

/-- **Success probability** of a randomized algorithm over `A ∼ D` and its own randomness:
`∑_A D(A) · Pr_T[T succeeds on A]`, with `T ∼ alg (rowSq A)`. -/
noncomputable def successProb {n : ℕ} (ε : ℝ) (D : PMF (Matrix (Fin n) (Fin n) ℝ))
    (alg : RandSpecAlg n) : ENNReal :=
  ∑' A, D A * (alg (fun i => L22EigEst.rowSq A i)).toOuterMeasure {T | Succeeds ε A T}

end L22EigEst.Supplement


