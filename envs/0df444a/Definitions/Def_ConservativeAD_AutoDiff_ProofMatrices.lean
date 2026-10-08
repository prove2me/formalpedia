-- Prove2me | Definitions.Def_ConservativeAD_AutoDiff_ProofMatrices
-- name    : ConservativeAD_AutoDiff_ProofMatrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:41:28.276501+00:00
-- url     : https://prove2.me/theorems/9542fc80-2c48-425f-9860-8027fd9d3666
-- title:
--   Proof of Theorem 8: the maps $G_k$, $L_k$ and the matrices $J_k$, $J_p$, $M_k$
-- statement:
--   Fix an evaluation program with nodes $1,\dots,q$ and inputs $1,\dots,p$, and write $e_k$ for the $k$-th canonical basis vector of $\mathbb R^q$. For a non-input node $k$:
--
--   1. $x_{\mathtt{parents}(k)}=(x_i)_{i\in\mathtt{parents}(k)}$ for any $x\in\mathbb R^q$, and $G_k:\mathbb R^q\to\mathbb R^q$, $G_k(x)=x+e_k\big(g_k(x_{\mathtt{parents}(k)})-x_k\big)$;
--   2. the field $D_k$ lifted to $\mathbb R^q$: $\tilde D_k(x)$ consists of the vectors obtained from $d\in D_k(x_{\mathtt{parents}(k)})$ by placing $d_j$ at coordinate $\mathtt{parents}(k)_j$ and zeros elsewhere;
--   3. $L_k(x)=\{I-e_ke_k^T+e_kd^T : d\in\tilde D_k(x)\}$, as in (10);
--   4. for a choice $(d_k)$, $J_k=I-e_ke_k^T+e_k\tilde d_k^T$, as in (11), where $\tilde d_k$ is $d_k$ lifted to $\mathbb R^q$;
--   5. $J_p\in\mathbb R^{q\times p}$ is the matrix with ones at positions $(i,i)$, $i\le p$, and zeros elsewhere;
--   6. $M_k\in\mathbb R^{q\times p}$ has row $i$ equal to the forward-mode row $\partial x_i/\partial x_{1,\dots,p}$ of Algorithm 2 for $i\le k$ (the identity block $I_p$ for $i\le p$) and $0$ for $i>k$;
--   7. $J_k\times J_{k-1}\times\cdots\times J_{p+1}$ is the product over the non-input nodes up to $k$, largest first.
--
--   These are the objects through which the paper's proof of Theorem 8 reduces automatic differentiation to products of conservative mappings.
--
--   **Formalization Note** Nodes are 0-based (`Fin q`), as in the program definition. The product is a `List.prod` over the non-input nodes $j\le k$ in decreasing order; Lean's `J_p` is `Jp p q`. In the block display of $M_k$ on p. 22, the rows after $I_p$ are labelled starting from "$\partial x_1/\partial x_{1,\dots,p}$"; they are the rows of nodes $p+1,\dots,k$, which is what the definition implements.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), pp. 22–23, §5.2, proof of Theorem 8, eqs. (10)–(11) and the matrices M_k, J_p

import Mathlib
import Definitions.Def_ConservativeAD_AutoDiff_Program

namespace ConservativeAD.AutoDiff

/-- The `k`-th canonical basis vector `e_k` of `ℝ^q`. -/
def e {q : ℕ} (k : Fin q) : Fin q → ℝ := Pi.single k 1

/-- `J_p ∈ ℝ^{q×p}`: the matrix with ones at the diagonal positions `(i, i)`, `i < p`, and zeros
elsewhere (the Jacobian of `G_p`). -/
def Jp (p q : ℕ) : Matrix (Fin q) (Fin p) ℝ := fun i j => if i.val = j.val then 1 else 0

namespace Program

variable {p q : ℕ} (P : Program p q)

/-- `x_{parents(k)} = (x_i)_{i ∈ parents(k)}` for an arbitrary `x ∈ ℝ^q`. -/
noncomputable def proj (k : Fin q) (x : EuclideanSpace ℝ (Fin q)) :
    EuclideanSpace ℝ (Fin (P.parents k).length) :=
  WithLp.toLp 2 (fun i => x ((P.parents k).get i))

/-- Proof of Theorem 8, p. 22: `G_k : ℝ^q → ℝ^q`, `x ↦ x + e_k (g_k(x_{parents(k)}) − x_k)`. -/
noncomputable def G (k : Fin q) (x : EuclideanSpace ℝ (Fin q)) : EuclideanSpace ℝ (Fin q) :=
  x + EuclideanSpace.single k (P.g k (P.proj k x) - x k)

/-- Proof of Theorem 8, p. 22: `D_k : ℝ^q ⇒ ℝ^q`, the field of `g_k` seen as a function of
`x_1, …, x_q`, obtained by adding zeros at the coordinates that are not parents of `k`. -/
def liftD (k : Fin q) (x : EuclideanSpace ℝ (Fin q)) : Set (EuclideanSpace ℝ (Fin q)) :=
  P.lift k '' P.D k (P.proj k x)

/-- (10): `L_k(x) = { I − e_k e_kᵀ + e_k dᵀ : d ∈ D_k(x) }` (with `D_k` lifted to `ℝ^q`). -/
def L (k : Fin q) (x : EuclideanSpace ℝ (Fin q)) : Set (Matrix (Fin q) (Fin q) ℝ) :=
  {M | ∃ dd ∈ P.liftD k x,
    M = 1 - Matrix.vecMulVec (e k) (e k) + Matrix.vecMulVec (e k) (WithLp.ofLp dd)}

/-- (11): `J_k = I − e_k e_kᵀ + e_k d_kᵀ` for the choice `d` (with `d_k` lifted to `ℝ^q`). -/
noncomputable def Jmat (d : P.Choice) (k : Fin q) : Matrix (Fin q) (Fin q) ℝ :=
  1 - Matrix.vecMulVec (e k) (e k) + Matrix.vecMulVec (e k) (WithLp.ofLp (P.lift k (d k)))

/-- The product `J_k × J_{k−1} × ⋯ × J_{p+1}` of the paper (in 0-based nodes: the non-input
nodes `j` with `j ≤ k`, largest first). -/
noncomputable def jprod (d : P.Choice) (k : Fin q) : Matrix (Fin q) (Fin q) ℝ :=
  (((List.finRange q).filter (fun j => p ≤ j.val ∧ j ≤ k)).reverse.map (P.Jmat d)).prod

/-- `M_k ∈ ℝ^{q×p}`: row `i` is the forward-mode row `∂x_i/∂x_{1,…,p}` of Algorithm 2 for
`i ≤ k` (the identity block `I_p` for the input nodes), and `0` for `i > k`. -/
noncomputable def Mmat (d : P.Choice) (k : Fin q) : Matrix (Fin q) (Fin p) ℝ :=
  fun i j => if i ≤ k then P.fwdRow d i j else 0

end Program

end ConservativeAD.AutoDiff


