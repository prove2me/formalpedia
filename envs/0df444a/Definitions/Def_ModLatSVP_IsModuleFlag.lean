-- Prove2me | Definitions.Def_ModLatSVP_IsModuleFlag
-- name    : ModLatSVP_IsModuleFlag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:54.489116+00:00
-- url     : https://prove2.me/theorems/271c3c8d-8493-40f2-80ed-0064854ce403
-- title:
--   Module flags, prefixes $M_i$, blocks $L_i$, block minima $H_i$, normalized determinants $G_i$, reducedness
-- statement:
--   Let $M$ be a module of rank $r$ over a number field $K$ of degree $d$, with compatible inner product. A **module flag** of $M$ is a chain of $K$-subspaces $0=V_0\subset V_1\subset\cdots\subset V_r=M\otimes_{\mathbb Z}\mathbb Q$ with $\dim_KV_i=i$. For $1\le i\le r$ the $i$-th **prefix** and **block** are
--
--   $$M_i=M\cap V_i,\qquad L_i=\pi_{V_{i-1}^\perp}M_i ,$$
--
--   where $\pi_W$ is orthogonal projection onto $W$. Each block is a rank-one module; $H_i=\lambda_1(L_i)$ is its minimum and $G_i=\det(L_i)^{1/d}$ its normalized determinant. The flag is **reduced at index $i$** if
--
--   $$\lambda_1(L_i)=\lambda_1\big(\pi_{V_{i-1}^\perp}M\big).$$
--
--   Here the module is written in an **adapted basis**: $M=\mathbb Z^{r\times d}$, coordinates $(i,j)$ being the $j$-th basis vector of the $i$-th block, so that $V_i$ is spanned by the first $i$ blocks; $K$-invariance of every $V_i$ means that the action matrices are block upper triangular. Reducedness is also defined for the flag $V_1\subset\cdots\subset V_t$ of a prefix $M_t$, where the right-hand side becomes $\lambda_1(\pi_{V_{i-1}^\perp}M_t)$.
--
--   Reduced module flags are the module analogue of HKZ-reduced bases; they are the object every algorithm of the paper constructs.
--
--   **Formalization Note** Every module flag has an adapted basis, and all quantities are invariant under the change to it, so this loses no flag. $\|\pi_{V_i^\perp}x\|^2$ is computed as the squared distance from $x$ to $V_i\otimes\mathbb R$. $\det(L_i)^2=g_i/g_{i-1}$, where $g_i$ is the principal minor of the Gram matrix on the first $i$ blocks (the Schur-complement formula); hence $G_i=(g_i/g_{i-1})^{1/(2d)}$. Indices are 1-based as in the paper.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Definition 2.2, p.14 (PDF p.14); §2.2, p.12; App. B.2, (43), p.48; App. B.3, p.50

import Mathlib
import Definitions.Def_ModLatSVP_lam1
import Definitions.Def_ModLatSVP_IsCompatible

open NumberField Matrix

namespace ModLatSVP

/-- A rank-`r` module over `K` with a module flag, written in an adapted basis. Kim, Lee, Son, *Exact SVP
and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission
(manuscript sha256 e7151fad…), Definition 2.2, p.14 (PDF p.14): "A module flag of M is a chain of
K-subspaces 0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ V_n = M ⊗_ℤ ℚ, dim_K V_i = i"; "An adapted basis of M is a ℤ-basis whose
first id vectors form a basis of M_i for every i".

The module is `ℤ^{r×d}` (coordinate `(i, j)` = `j`-th vector of the `i`-th block), with Gram matrix `G`
and compatible `K`-action `φ`, where `d = [K : ℚ]`, and `V_i` is spanned by the coordinates of the first
`i` blocks. `IsModuleFlag K τ r d G φ` says: `d = [K : ℚ]`, the module is compatible (`IsCompatible`),
and every `V_i` is a `K`-subspace, i.e. `φ(α)_{pq} ≠ 0` only if block `p` ≤ block `q`.

**Formalization Note.** Every module flag has an adapted basis (§2.2, [KB79]; App. B.2: the
intersections `M ∩ V_i` are saturated), and every quantity of the flag (prefixes, blocks, minima,
determinants) is invariant under the change to an adapted basis, so quantifying over modules in adapted
coordinates is quantifying over all module flags. A `K`-invariant `ℚ`-subspace of dimension `i·d` has
`K`-dimension `i`. -/
def IsModuleFlag (K : Type*) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (r d : ℕ)
    (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (φ : K →+* Matrix (Fin r × Fin d) (Fin r × Fin d) ℚ) :
    Prop :=
  Module.finrank ℚ K = d ∧ IsCompatible K τ G φ ∧
  ∀ (α : K) (p q : Fin r × Fin d), φ α p q ≠ 0 → p.1 ≤ q.1

/-- `x` lies in `V_i ⊗ ℝ`: it is supported on the first `i` blocks. -/
def InPrefix {r d : ℕ} (i : ℕ) (x : Fin r × Fin d → ℝ) : Prop :=
  ∀ p : Fin r × Fin d, i ≤ (p.1 : ℕ) → x p = 0

/-- `x ∈ M_i = M ∩ V_i`: the integer vector `x` is supported on the first `i` blocks. -/
def InPrefixZ {r d : ℕ} (i : ℕ) (x : Fin r × Fin d → ℤ) : Prop :=
  ∀ p : Fin r × Fin d, i ≤ (p.1 : ℕ) → x p = 0

/-- `‖π_{V_i^⊥} x‖²`, the squared length of the orthogonal projection of `x` onto `V_i^⊥`, i.e. its
squared distance to `V_i ⊗ ℝ` in the metric `G` (§2, p.11: "π_W is the orthogonal projection onto W").

**Formalization Note.** For positive definite `G` the infimum is attained (at the orthogonal
projection) and is bounded below by `0`; `V_0 = 0`, so `projSq G 0 x = xᵀ G x`. -/
noncomputable def projSq {r d : ℕ} (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (i : ℕ)
    (x : Fin r × Fin d → ℝ) : ℝ :=
  ⨅ w : {w : Fin r × Fin d → ℝ // InPrefix i w}, qf G (x - w.1)

/-- The block minimum `H_i = λ₁(L_i)` of the `i`-th block `L_i = π_{V_{i−1}^⊥} M_i` (Definition 2.2,
p.14; "We write H_i = λ₁(L_i)"), for `1 ≤ i ≤ r`: the least length of a nonzero projection
`π_{V_{i−1}^⊥} x` with `x ∈ M_i`.

**Formalization Note.** Indices are `1`-based as in the paper; `i − 1` is natural-number subtraction and
is only used for `i ≥ 1`. -/
noncomputable def blockMin {r d : ℕ} (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (i : ℕ) : ℝ :=
  sInf {s : ℝ | ∃ x : Fin r × Fin d → ℤ, InPrefixZ i x ∧ 0 < projSq G (i - 1) (intVec x) ∧
    s = Real.sqrt (projSq G (i - 1) (intVec x))}

/-- `λ₁(π_{V_{i−1}^⊥} M_t)`, the minimum of the projection of the prefix module `M_t` onto
`V_{i−1}^⊥`. For `t = r` this is the paper's `λ₁(π_{V_{i−1}^⊥} M)` of Definition 2.2. -/
noncomputable def suffixMin {r d : ℕ} (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (t i : ℕ) : ℝ :=
  sInf {s : ℝ | ∃ x : Fin r × Fin d → ℤ, InPrefixZ t x ∧ 0 < projSq G (i - 1) (intVec x) ∧
    s = Real.sqrt (projSq G (i - 1) (intVec x))}

/-- The flag of the prefix module `M_t` (with blocks `L_1, …, L_t`) is reduced at index `i` (Definition
2.2, p.14): `λ₁(L_i) = λ₁(π_{V_{i−1}^⊥} M_t)`. For `t = r` this is the paper's "reduced at index i". -/
def ReducedAt {r d : ℕ} (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (t i : ℕ) : Prop :=
  blockMin G i = suffixMin G t i

/-- The Gram determinant `det(M_i)² = g_i` of the prefix `M_i`: the principal minor of `G` on the
coordinates of the first `i` blocks (App. B.3, p.50: "Let g_j be the determinant of the Gram matrix of the
unscaled j-th prefix"). `g_0 = 1`. -/
noncomputable def prefixGramDet {r d : ℕ} (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (i : ℕ) : ℝ :=
  (G.submatrix (fun p : {p : Fin r × Fin d // (p.1 : ℕ) < i} => (p : Fin r × Fin d))
    (fun p : {p : Fin r × Fin d // (p.1 : ℕ) < i} => (p : Fin r × Fin d))).det

/-- The normalized determinant `G_i = det(L_i)^{1/d}` of the `i`-th block (Definition 2.2, p.14),
`1 ≤ i ≤ r`, computed as `det(L_i)² = g_i / g_{i−1}`.

**Formalization Note.** `det(L_i)² = g_i / g_{i−1}` is the Schur-complement formula for the projected
block (App. B.2, (43)): in the adapted basis the Gram matrix of `L_i = π_{V_{i−1}^⊥} M_i` is the Schur
complement of `g_{i−1}`'s block in `g_i`'s, whose determinant is the quotient. -/
noncomputable def normDet {r d : ℕ} (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (i : ℕ) : ℝ :=
  (prefixGramDet G i / prefixGramDet G (i - 1)) ^ ((1 : ℝ) / (2 * d))

end ModLatSVP


