-- Prove2me | Definitions.Def_LogBarrierIPM_Iterations_Supplement_MonomialPolyhedron
-- name    : LogBarrierIPM_Iterations_Supplement_MonomialPolyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:09:15.515234+00:00
-- url     : https://prove2.me/theorems/cb652efd-97a8-41f8-a02e-2e4da49d0209
-- title:
--   Monomial polyhedra, the extended-matrix gap and vertex specialization
-- statement:
--   A monomial series has coefficient $\pm1$ at one real exponent and zero elsewhere, or is the null series with exponent $-\infty$. For monomial exponents $(a,\beta)$ of $(A,b)$, form the exponent matrix of
--
--   $$\begin{pmatrix}A&b&0\\ e^\top&0&1\end{pmatrix}.$$
--
--   Define $\eta_0$ as the minimum of $\eta(M)$ over every order-$d$ square submatrix, with minimum $+\infty$ for an empty family. The threshold is $(d!)^{1/\eta_0}$, interpreted as $1$ at $\eta_0=+\infty$. A vertex of $\mathcal P=\{x\in K^d:Ax\le b\}$ is a feasible point with $d$ independent active rows. Normalized recession generators are the vertices of $\{v:Av\le0,\ e^\top v=1\}$.
--
--   Two predicates are used in the corrected Theorem 12. `VertexCoverAt` says that every point of $\mathcal P(t)$ is a convex combination of evaluated vertices plus a nonnegative combination of evaluated recession generators; an evaluated vertex is not required to lie in $\mathcal P(t)$. `HasNonnegativityRows` says that each inequality $-x_j\le0$ is one of the rows of $Ax\le b$.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 12, def-monomial-eta

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_PuiseuxGeometry
import Definitions.Def_LogBarrierIPM_Iterations_MonomialMatrix

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

/-- A monomial, including the null series (exponent bottom). -/
def IsMonomial (f : Puiseux) (a : WithBot ℝ) (s : ℝ) : Prop :=
  (s = 1 ∨ s = -1) ∧ ∀ β : ℝ, f.coeff β = if a = (β : WithBot ℝ) then s else 0

/-- Exponents of the extended matrix (A b 0; eᵀ 0 1), p. 13. -/
def extendedExponents {p d : ℕ} (a : Matrix (Fin p) (Fin d) (WithBot ℝ))
    (b : Fin p → WithBot ℝ) : Matrix (Fin (p + 1)) (Fin (d + 2)) (WithBot ℝ) :=
  fun i j => if hi : i.val < p then
    if hj : j.val < d then a ⟨i.val, hi⟩ ⟨j.val, hj⟩
    else if j.val = d then b ⟨i.val, hi⟩ else ⊥
  else if j.val < d then 0 else if j.val = d then ⊥ else 0

/-- All order-d square submatrices: injective row and column selections. -/
noncomputable def etaZero {p d : ℕ} (a : Matrix (Fin p) (Fin d) (WithBot ℝ))
    (b : Fin p → WithBot ℝ) : WithTop ℝ :=
  ⨅ rows : Fin d ↪ Fin (p + 1), ⨅ cols : Fin d ↪ Fin (d + 2),
    etaM (fun i j => extendedExponents a b (rows i) (cols j))

/-- 1/(+∞)=0, so (d!)^(1/η0)=1 when all exponent gaps are infinite. -/
noncomputable def monomialThreshold {p d : ℕ}
    (a : Matrix (Fin p) (Fin d) (WithBot ℝ)) (b : Fin p → WithBot ℝ) : ℝ :=
  match etaZero a b with
  | ⊤ => 1
  | (η : ℝ) => (Nat.factorial d : ℝ) ^ (1 / η)

/-- A vertex: d independent active rows, tested over K by eventual evaluation. -/
def kVertices {p d : ℕ} (A : Matrix (Fin p) (Fin d) Puiseux)
    (b : Fin p → Puiseux) : Set (Fin d → Puiseux) :=
  {x | x ∈ kPolyhedron A b ∧ ∃ rows : Fin d ↪ Fin p,
    ∀ᶠ t in atTop, (∀ i, ∑ j, (A (rows i) j).eval t * (x j).eval t =
      (b (rows i)).eval t) ∧ Matrix.det (fun i j => (A (rows i) j).eval t) ≠ 0}

/-- Vertices of {v : Av ≤ 0, Σv=1}. Active normals may include eᵀ from the equality. -/
def kRayVertices {p d : ℕ} (A : Matrix (Fin p) (Fin d) Puiseux) :
    Set (Fin d → Puiseux) :=
  {v | (∀ᶠ t in atTop, (∀ i, ∑ j, (A i j).eval t * (v j).eval t ≤ 0) ∧
      (∑ j, (v j).eval t) = 1) ∧
    ∃ rows : Fin d ↪ Fin (p + 1), ∀ᶠ t in atTop,
      (let B : Matrix (Fin d) (Fin d) ℝ := fun i j =>
        if hi : (rows i).val < p then (A ⟨(rows i).val, hi⟩ j).eval t else 1
       (∀ i, ∑ j, B i j * (v j).eval t = if (rows i).val < p then 0 else 1) ∧
       B.det ≠ 0)}

/-- Generation by arbitrary sets uses finite combinations. Empty U generates the empty set. -/
def realGeneratedSets {d : ℕ} (U V : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {x | ∃ q r : ℕ, ∃ u : Fin q → Fin d → ℝ, ∃ v : Fin r → Fin d → ℝ,
    (∀ i, u i ∈ U) ∧ (∀ j, v j ∈ V) ∧ x ∈ realGenerated u v}

/-- What inequality (16) uses at `t`: P(t) lies in the hull-plus-cone of the evaluated vertices
and normalized ray vertices of P. The reverse inclusion is not needed: an evaluated vertex of P
may fail to lie in P(t). -/
def VertexCoverAt {p d : ℕ} (A : Matrix (Fin p) (Fin d) Puiseux)
    (b : Fin p → Puiseux) (t : ℝ) : Prop :=
  realPolyhedron A b t ⊆ realGeneratedSets
    ((fun x => evalFun x t) '' kVertices A b)
    ((fun v => evalFun v t) '' kRayVertices A)

/-- Every inequality `-x_j ≤ 0` is one of the rows of `A x ≤ b`. -/
def HasNonnegativityRows {p d : ℕ} (A : Matrix (Fin p) (Fin d) Puiseux)
    (b : Fin p → Puiseux) : Prop :=
  ∀ j : Fin d, ∃ i : Fin p, ∀ᶠ t in atTop,
    (∀ k, (A i k).eval t = if k = j then -1 else 0) ∧ (b i).eval t = 0

end LogBarrierIPM.Iterations.Supplement


