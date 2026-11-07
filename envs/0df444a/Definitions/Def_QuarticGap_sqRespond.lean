-- Prove2me | Definitions.Def_QuarticGap_sqRespond
-- name    : QuarticGap_sqRespond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:39.059354+00:00
-- url     : https://prove2.me/theorems/def2b0e9-1099-4f26-a935-cf595dfbf590
-- title:
--   Sampling and query access $\mathrm{SQ}(A)$, direct queries, families with known magnitudes
-- statement:
--   For a real matrix $A$, the classical input operations $\mathrm{SQ}(A)$ are:
--
--   1. **entry queries**, which return $A_{ij}$;
--   2. **norm queries**, which return $\|A_{i,*}\|$, $\|A_{*,j}\|$ or $\|A\|_F$;
--   3. **row and column sampling**, which return $i$ with probability $\|A_{i,*}\|^2/\|A\|_F^2$, or $j$ with probability $\|A_{*,j}\|^2/\|A\|_F^2$;
--   4. **conditional sampling**, which in a nonzero row $i$ returns $j$ with probability $A_{ij}^2/\|A_{i,*}\|^2$, in a nonzero column $j$ returns $i$ with probability $A_{ij}^2/\|A_{*,j}\|^2$, and in a zero row or column returns a fixed index.
--
--   Each operation is one query. The item also defines the normalized Frobenius norm $\rho(A) = \|A\|_F/\|A\|$, a **direct query** to a Boolean function $f : \{0,1\}^m \to \{-1,1\}$, which returns $f(\sigma)$, and the hypothesis of Lemma 2.7: a family $\{A(f)\}$ has **known magnitudes** if every entry either does not depend on $f$ or equals $\mu_{ij} f(\sigma_{ij})$ for a fixed nonzero real $\mu_{ij}$ and a fixed point $\sigma_{ij}$.
--
--   These are the operations a dequantized algorithm uses, and the known-magnitude hypothesis is what reduces them to direct queries.
--
--   **Formalization Note** The fixed index of conditional sampling is the parameter pair $(i_0, j_0)$. The reversible-circuit hypothesis of Lemma 2.7 is left out of the predicate; it concerns gate counts, and each statement that uses the predicate says how it is handled.
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), §2.1, p.15; Definition 2.1, p.15; §2.5, p.18

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuarticGap_QueryAlg

open QAlgorithms

namespace QuarticGap

section Norms

variable {ρ κ : Type*} [Fintype ρ] [Fintype κ]

/-- Squared Euclidean norm `∥A_{i,∗}∥²` of row `i`. -/
def rowNormSq (A : Matrix ρ κ ℝ) (i : ρ) : ℝ := ∑ j, A i j ^ 2

/-- Squared Euclidean norm `∥A_{∗,j}∥²` of column `j`. -/
def colNormSq (A : Matrix ρ κ ℝ) (j : κ) : ℝ := ∑ i, A i j ^ 2

/-- Squared Frobenius norm `∥A∥²_F` of a real matrix. -/
def frobSq (A : Matrix ρ κ ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- Euclidean norm `∥A_{i,∗}∥` of row `i`. -/
noncomputable def rowNorm (A : Matrix ρ κ ℝ) (i : ρ) : ℝ := Real.sqrt (rowNormSq A i)

/-- Euclidean norm `∥A_{∗,j}∥` of column `j`. -/
noncomputable def colNorm (A : Matrix ρ κ ℝ) (j : κ) : ℝ := Real.sqrt (colNormSq A j)

/-- Frobenius norm `∥A∥_F` of a real matrix. -/
noncomputable def frobR (A : Matrix ρ κ ℝ) : ℝ := Real.sqrt (frobSq A)

/-- Normalized Frobenius norm `ρ(A) = ∥A∥_F / ∥A∥` for a nonzero matrix, with `∥A∥` the operator norm
(arXiv:2610.42069, §2.1, p.15). -/
noncomputable def rho [DecidableEq κ] (A : Matrix ρ κ ℝ) : ℝ := frobR A / specNorm A

end Norms

/-- The classical input operations of `SQ(A)` for a matrix with rows `ρ` and columns `κ`
(arXiv:2610.42069, Definition 2.1, p.15): entry query, row norm, column norm, Frobenius norm, row
sampling, column sampling, and conditional sampling in a given row or column. -/
inductive SQQuery (ρ κ : Type*) where
  | entry (i : ρ) (j : κ)
  | rowNorm (i : ρ)
  | colNorm (j : κ)
  | frob
  | rowSample
  | colSample
  | condRow (i : ρ)
  | condCol (j : κ)

/-- An answer of `SQ(A)`: a real number or a row or column index. -/
inductive SQAns (ρ κ : Type*) where
  | value (x : ℝ)
  | row (i : ρ)
  | col (j : κ)

open Classical in
/-- The law that gives each `i` probability `w i`, when `w` is a probability vector, and the point
mass at the fixed index `i₀` otherwise. -/
noncomputable def weightedPMF {ι : Type*} [Fintype ι] (w : ι → ℝ) (i₀ : ι) : PMF ι :=
  if h : ∑ i, ENNReal.ofReal (w i) = 1 then
    PMF.ofFintype (fun i => ENNReal.ofReal (w i)) h
  else PMF.pure i₀

/-- The answer laws of `SQ(A)` (arXiv:2610.42069, Definition 2.1, p.15). Entry and norm queries are
deterministic. Row and column sampling return an index with probability `∥A_{i,∗}∥²/∥A∥²_F`, resp.
`∥A_{∗,j}∥²/∥A∥²_F`. Conditional sampling in a nonzero row `i` returns `j` with probability
`A²_ij/∥A_{i,∗}∥²`, and in a nonzero column `j` returns `i` with probability `A²_ij/∥A_{∗,j}∥²`.

**Formalization Note** In a zero row or column the weights are all `0`, so `weightedPMF` returns the
source's "fixed index", here the parameters `i₀`, `j₀`. Definition 2.1 is for a nonzero matrix;
row and column sampling of the zero matrix also return the fixed index. -/
noncomputable def sqRespond {ρ κ : Type*} [Fintype ρ] [Fintype κ] (A : Matrix ρ κ ℝ) (i₀ : ρ)
    (j₀ : κ) : SQQuery ρ κ → PMF (SQAns ρ κ)
  | .entry i j => PMF.pure (.value (A i j))
  | .rowNorm i => PMF.pure (.value (rowNorm A i))
  | .colNorm j => PMF.pure (.value (colNorm A j))
  | .frob => PMF.pure (.value (frobR A))
  | .rowSample => (weightedPMF (fun i => rowNormSq A i / frobSq A) i₀).map .row
  | .colSample => (weightedPMF (fun j => colNormSq A j / frobSq A) j₀).map .col
  | .condRow i => (weightedPMF (fun j => A i j ^ 2 / rowNormSq A i) j₀).map .col
  | .condCol j => (weightedPMF (fun i => A i j ^ 2 / colNormSq A j) i₀).map .row

/-- A classical query to a Boolean function `f : {0,1}^m → {−1,1}` returns `f(σ)` for a chosen point
`σ` (arXiv:2610.42069, §2.5, p.18). -/
noncomputable def directRespond {m : ℕ} (f : Qubits m → ℤˣ) (σ : Qubits m) : PMF ℤˣ :=
  PMF.pure (f σ)

/-- The hypothesis of Lemma 2.7 on a family `{A(f)}` of real matrices indexed by Boolean functions
(arXiv:2610.42069, p.18): every entry either does not depend on `f` or equals `µ_ij f(σ_ij)` for a
fixed nonzero real `µ_ij` and a fixed point `σ_ij`.

**Formalization Note** The source's further hypothesis, that `(i, j) ↦ σ_ij` is computed by a fixed
reversible circuit, is not part of this predicate; it concerns gate counts and is discussed at each
statement that uses it. -/
def IsKnownMagnitudeFamily {m : ℕ} {ρ κ : Type*} (A : (Qubits m → ℤˣ) → Matrix ρ κ ℝ) : Prop :=
  ∀ i j, (∀ f g, A f i j = A g i j) ∨ ∃ μ : ℝ, μ ≠ 0 ∧ ∃ σ, ∀ f, A f i j = μ * sgn (f σ)

end QuarticGap


