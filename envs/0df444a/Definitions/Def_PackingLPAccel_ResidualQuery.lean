-- Prove2me | Definitions.Def_PackingLPAccel_ResidualQuery
-- name    : PackingLPAccel_ResidualQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:15.583008+00:00
-- url     : https://prove2.me/theorems/a8bcef90-10dd-4b9a-a4bb-23354e357b54
-- title:
--   The residual queries of Lemma 3.7: explicit forms, allowed class and solver oracle
-- statement:
--   A residual query asks for an approximate solution of an instance of Problem 1.3 in the form the proof of Lemma 3.7 displays, with $\hat A_{ij}=A_{ij}/\|A_{:,j}\|_\infty$, $u_j=1$ and $X_{ij}=\hat A_{ij}x_j$:
--
--   $$\psi_j(s)=g_js+\sum_{i:A_{ij}\ne0}(y_i+\xi)(\hat A_{ij}s+\xi)\log(\hat A_{ij}s+\xi),$$
--
--   $\phi_{ij}(t)=(X_{ij}+|t|)^q-X_{ij}^q$, $c_{ij}(t)=\lambda'pq_i^{p-1}[|X_{ij}+t|^q-X_{ij}^q]$, $v^{(2)}_i=2\lambda'p^2q_i^{p-2}$, $v^{(p)}_i=\lambda'p^p$, with $q=1+1/p$ and $y\in\Delta^m$. A query is allowed if it is quasi-poly-bounded with a constant $b$ and its accuracy is at least $(m+n)^{-c'}$. The solver oracle writes a feasible $\hat\Delta$ with $F(\hat\Delta)\le\kappa^{-1}F(\Delta')+\delta_{\mathrm{res}}$ for all feasible $\Delta'$, and has no answer on any other query.
--
--   This is how evaluation itself carries "every instance the program solves is quasi-poly-bounded".
--
--   **Formalization Note** The columns are rescaled: Definition 3.1 allows it, and without it the $L_j$ would grow with the width. The proof's "$\|A\|_\infty=1$" (p.28) does not follow from $\min_j\|A_{:,j}\|_\infty=1$, and this rescaling is the repair. The extra row and column of $I(\lambda)$ do not move and contribute nothing.
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), proof of Lemma 3.7, pp.27–28 (pdf 28–29); proof of Lemma 5.8, p.34 (pdf 35)

import Mathlib
import Definitions.Def_PackingLPAccel_Residual
import Definitions.Def_PackingLPAccel_CompositeL1Inf

namespace PackingLPAccel

/-!
# The residual queries of Lemma 3.7

Chen, Chen, Graur, Sidford, *Accelerated Parallel Algorithms for Packing Linear Programming*,
STOC 2027 submission (manuscript sha256 1dac7711…), proof of Lemma 3.7 (pp.27–28) and proof of
Lemma 5.8 (p.34).

**Formalization Note.** A query is an instance of Problem 1.3 with the explicit function forms the
proof displays, in the coordinates of Problem 1.3 (`t = Â_ij ∆_j`).
* The query's matrix is `Â_ij = A_ij / ∥A_{:,j}∥_∞`, with `u_j = 1`: Definition 3.1 allows rescaling
  `x_j` by `∥A_{:,j}∥_∞`, and without it the `L_j` would grow with the width. The proof's "`∥A∥_∞ = 1`"
  (p.28) does not follow from `min_j ∥A_{:,j}∥_∞ = 1`, and this rescaling is the repair.
* `ψ_j(s) = g_j s + ∑_{i ∈ N_j} (y_i + ξ)(Â_ij s + ξ) log(Â_ij s + ξ)` is the linear term plus the
  regularizer's term of the proof of Lemma 5.8, with `N_j = {i : A_ij ≠ 0}`.
* `ϕ_ij`, `c_ij`, `v^{(2)}`, `v^{(p)}` are the corrected residual of `Proxy` at
  `X_ij = Â_ij x_j`, with `λ'` the query's coefficient and `q = 1 + 1/p`. The extra row and column of
  `I(λ)` hold the constant `1` and do not move, so they contribute nothing.
* Decomposability and `∥A∥_∞ ≤ poly` are absent: Theorem 4.1's proof uses only the numeric bounds.
* Oracle block: integer cell `0` holds `p`; real cells `0, 1, 2` hold `λ', ξ, δ_res`; then `x` from
  cell `3`, `g` from `3 + n`, `L` from `3 + 2n`, `y` from `3 + 3n`; the answer from `3 + 3n + m`.
* Input layout: `I` as in the goal; `M` holds `ε, δ, κ, λ` and then the values of `A`. Output
  `M (4 + N + j)`.
-/

variable {m n : ℕ}

/-- `Â_ij = A_ij / ∥A_{:,j}∥_∞`. -/
noncomputable def normMatrix (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => A i j / colNorm A j

/-- The data of a residual query. -/
structure ResidualQuery (m n : ℕ) where
  /-- The exponent `p`. -/
  p : ℕ
  /-- The coefficient of `∥X∥_{q,p}^{pq}`. -/
  lam : ℝ
  /-- The regularizer's `ξ`. -/
  ξ : ℝ
  /-- The accuracy asked for. -/
  δres : ℝ
  /-- The current point, in the rescaled coordinates. -/
  x : Fin n → ℝ
  /-- The linear coefficient. -/
  g : Fin n → ℝ
  /-- The Lipschitz bounds. -/
  L : Fin n → ℝ
  /-- The regularizer's `y ∈ ∆^m`. -/
  y : Fin m → ℝ

/-- `q_i(X)` at `X_ij = Â_ij x_j`, with `q = 1 + 1/p`. -/
noncomputable def queryQ (A : Matrix (Fin m) (Fin n) ℝ) (Q : ResidualQuery m n) (i : Fin m) : ℝ :=
  ∑ j, (normMatrix A i j * Q.x j) ^ (1 + (1 : ℝ) / Q.p)

open Classical in
/-- The instance of Problem 1.3 asked by a query. -/
noncomputable def residualOfQuery (A : Matrix (Fin m) (Fin n) ℝ) (Q : ResidualQuery m n) :
    ResidualInstance m n where
  A := normMatrix A
  x := Q.x
  u := fun _ => 1
  ψ := fun j s => Q.g j * s + ∑ i, if A i j ≠ 0 then
    (Q.y i + Q.ξ) * ((normMatrix A i j * s + Q.ξ) * Real.log (normMatrix A i j * s + Q.ξ)) else 0
  p := Q.p
  v₂ := fun i => 2 * Q.lam * (Q.p : ℝ) ^ 2 * queryQ A Q i ^ (Q.p - 2)
  vₚ := fun _ => Q.lam * (Q.p : ℝ) ^ Q.p
  c := fun i j t => Q.lam * Q.p * queryQ A Q i ^ (Q.p - 1) *
    (|normMatrix A i j * Q.x j + t| ^ (1 + (1 : ℝ) / Q.p) -
      (normMatrix A i j * Q.x j) ^ (1 + (1 : ℝ) / Q.p))
  ϕ := fun i j t =>
    (normMatrix A i j * Q.x j + |t|) ^ (1 + (1 : ℝ) / Q.p) -
      (normMatrix A i j * Q.x j) ^ (1 + (1 : ℝ) / Q.p)

/-- The query in the state. -/
noncomputable def readQuery (st : State) : ResidualQuery m n where
  p := (st.I (blockAddr 0)).toNat
  lam := st.M (blockAddr 0)
  ξ := st.M (blockAddr 1)
  δres := st.M (blockAddr 2)
  x := readBlock st.M 3
  g := readBlock st.M (3 + n)
  L := readBlock st.M (3 + 2 * n)
  y := readBlock st.M (3 + 3 * n)

/-- The allowed queries: `x` is in the box, `y ∈ ∆^m`, `0 < ξ`, `λ' > 0`, `p ≥ 2`, the accuracy is at
least `(m+n)^{-c'}`, and the instance is quasi-poly-bounded with constant `b`. -/
def IsAllowedQuery (A : Matrix (Fin m) (Fin n) ℝ) (b c' : ℕ) (Q : ResidualQuery m n) : Prop :=
  2 ≤ Q.p ∧ 0 < Q.lam ∧ 0 < Q.ξ ∧ 0 < Q.δres ∧ (Q.δres)⁻¹ ≤ ((m + n : ℕ) : ℝ) ^ c' ∧
    Q.y ∈ stdSimplex ℝ (Fin m) ∧ (∀ j, 0 ≤ Q.x j ∧ Q.x j ≤ 1) ∧
    (residualOfQuery A Q).IsQuasiPolyBounded Q.L b

/-- The residual solver of Lemma 3.7: on an allowed query it writes a feasible `∆̂` with
`F(∆̂) ≤ (1/κ) F(∆') + δ_res` for all feasible `∆'`, an `(κ, δ_res)` approximation; every other query
has no answer. -/
def IsResidualSolver (A : Matrix (Fin m) (Fin n) ℝ) (b c' : ℕ) (κ : ℝ) (O : OracleModel) : Prop :=
  ∀ st : State,
    let Q : ResidualQuery m n := readQuery st
    (IsAllowedQuery A b c' Q →
      ∃ Δhat : Fin n → ℝ, (residualOfQuery A Q).InBox Δhat ∧
        (∀ Δ', (residualOfQuery A Q).InBox Δ' →
          (residualOfQuery A Q).F Δhat ≤ κ⁻¹ * (residualOfQuery A Q).F Δ' + Q.δres) ∧
        O.answer st = some (writeBlock st.M (3 + 3 * n + m) n
          (fun k => if h : k < n then Δhat ⟨k, h⟩ else 0), st.I)) ∧
    (¬ IsAllowedQuery A b c' Q → O.answer st = none)

/-- The initial state of Lemma 3.7. -/
noncomputable def lemma37Init {N : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ε δ κ lam : ℝ)
    (e : Fin N → Fin m × Fin n) : State :=
  initState ([ε, δ, κ, lam] ++ sparseVals A e) (goalInts m n e)

/-- The output of Lemma 3.7. -/
def lemma37Output {n : ℕ} (N : ℕ) (s : State) : Fin n → ℝ :=
  fun j => s.M (4 + (N : ℤ) + ((j : ℕ) : ℤ))

end PackingLPAccel


