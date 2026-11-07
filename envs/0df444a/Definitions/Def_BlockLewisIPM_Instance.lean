-- Prove2me | Definitions.Def_BlockLewisIPM_Instance
-- name    : BlockLewisIPM_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:59.419254+00:00
-- url     : https://prove2.me/theorems/86115824-9a01-4dc6-91e2-754824708b38
-- title:
--   Instances of linear optimization over a product of convex sets
-- statement:
--   An instance is the program
--
--   $$\min\ c^\top x\quad\text{subject to}\quad A^\top x=b,\ \ x\in K=K_1\times\dots\times K_m,\qquad K_i\subset\mathbb R^{n_i},\ \ \sum_i n_i=n,$$
--
--   with $A\in\mathbb R^{n\times d}$, $b\in\mathbb R^d$, $c\in\mathbb R^n$, together with a barrier $\phi_i$ for each $K_i$.
--
--   An instance is **admissible** if it has at least one block, $d\ge1$, $n_i\ge1$, each $K_i$ is convex and compact, and each $\phi_i$ is a $1$-self-concordant barrier for $K_i$. The number $\kappa>0$ is a **radius bound** if $\|x\|\le\kappa$ on every $K_i$, $\|c_i\|_2\le\kappa$, $\|A_i\|_{\mathrm{op}}\le\kappa$, and there is a point $z$ with $A^\top z=b$ and $B(z_i,1/\kappa)\subseteq K_i$ for all $i$. The milestones about the method also use the **standing assumptions**: admissibility, $n_i\le N$, $m\ge2$, and $A$ of full column rank.
--
--   These notions state the main theorem and its milestones.
--
--   **Formalization Note** The barrier predicate is the published `IsNuSelfConcordantBarrier K φ 1`. It adds to Definition 2 the blow-up at the boundary that the word "barrier" and Lemma 3 need. The strictly feasible point in the radius bound is correction C1 of the mission, and $d\ge1$ is correction C2. Blocks are indexed by a finite type, so that the extended program of Lemma 49 is an instance on `Option ι`.
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), (1), p.1; (2), p.3; Theorem 54, p.49; Definition 2, p.11

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_BlockLewisIPM_Notation

namespace BlockLewisIPM

/-!
# Instances of the product-domain program

Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization over
Product-Domain* (manuscript, sha256 66072000…), problem (1), p.1, and (2), p.3; the hypotheses of
Theorem 54, p.49; Definition 2, p.11.

**Formalization Note.**
* Blocks are indexed by a finite type `ι`, so that the extended program of Lemma 49 is the instance
  on `Option ι`; the machine and the goal use `ι = Fin m`.
* `A⊤x = b` has `d` equations in `n` variables: `A` has `n` rows and `d` columns.
* The barrier predicate is the published `IsNuSelfConcordantBarrier K φ 1`: the barrier clause, the
  line form of Definition 2 item 1 and item 2 with `ν = 1`, without an inverse (reading R6).
* `IsAdmissible` carries the printed hypotheses and three conditions the printed statement leaves
  implicit. **C2**: `1 ≤ d`, since at `d = 0` the time bound is `0`. Nonempty block list and nonempty
  blocks (reading R8): at `m = 0` the bound vanishes for `k ≥ 1`, since `n_max = 0`.
* `RadiusBound κ` carries **C1**: a point `z` with `A⊤z = b` and `B(z_i, 1/κ) ⊆ K_i`. As printed
  Theorem 54 has no conclusion on an infeasible instance. `κ` is not part of the instance and is not
  given to the algorithm (reading R9).
* `IsAdmissible` has no rank condition on `A` (reading R10). `Standing` adds full column rank for the
  milestones about the method, whose `P(·)` and `(A⊤T⁻¹∇²Φ⁻¹A)⁻¹` need it; it also adds `2 ≤ m`,
  since `θ = 1/(10 log m)` is undefined at `m = 1`, and a bound `n_max` on the block sizes for the
  hidden constants of those milestones (`n_i = O(1)`, p.3, and p.10).
-/

open Matrix

/-- An instance of `min { c⊤x : x ∈ K₁ × ⋯ × K_m, A⊤x = b }`, (1), p.1, with its barriers. -/
structure Instance (ι : Type) where
  /-- The block dimensions `n_i`. -/
  dim : ι → ℕ
  /-- The number `d` of equality constraints. -/
  d : ℕ
  /-- The constraint matrix `A ∈ ℝ^{n×d}`. -/
  A : Matrix (BIdx dim) (Fin d) ℝ
  /-- The right-hand side `b ∈ ℝ^d`. -/
  b : Fin d → ℝ
  /-- The objective `c ∈ ℝⁿ`. -/
  c : BIdx dim → ℝ
  /-- The convex sets `K_i`. -/
  K : ∀ i, Set (Eu (dim i))
  /-- The barriers `ϕ_i`. -/
  φ : ∀ i, Eu (dim i) → ℝ

namespace Instance

variable {ι : Type} (I : Instance ι)

/-- A vector of `ℝⁿ`. -/
abbrev Vec := BIdx I.dim → ℝ

/-- `x_i ∈ K_i` for every block. -/
def InK (x : I.Vec) : Prop := ∀ i, blockPt x i ∈ I.K i

/-- `x_i ∈ int K_i` for every block. -/
def InDomain (x : I.Vec) : Prop := ∀ i, blockPt x i ∈ interior (I.K i)

/-- The row block `A_i ∈ ℝ^{n_i×d}` (p.10). -/
def blockA (i : ι) : Matrix (Fin (I.dim i)) (Fin I.d) ℝ := fun l k => I.A ⟨i, l⟩ k

variable [Fintype ι]

/-- `n = ∑ n_i`. -/
def n : ℕ := ∑ i, I.dim i

/-- `n_max = max_i n_i`. -/
def nmax : ℕ := Finset.univ.sup I.dim

/-- `x` is feasible: `x ∈ K` and `A⊤x = b`. -/
def Feasible (x : I.Vec) : Prop := I.InK x ∧ I.Aᵀ *ᵥ x = I.b

/-- The hypotheses of Theorem 54, p.49, on the instance, with correction C2 and reading R8. -/
structure IsAdmissible : Prop where
  m_pos : 1 ≤ Fintype.card ι
  d_pos : 1 ≤ I.d
  dim_pos : ∀ i, 1 ≤ I.dim i
  compact : ∀ i, IsCompact (I.K i)
  convex : ∀ i, Convex ℝ (I.K i)
  barrier : ∀ i, EntropicBarrier.Universal.IsNuSelfConcordantBarrier (I.K i) (I.φ i) 1

variable [DecidableEq ι]

/-- `κ` bounds the instance (reading R1), with correction C1: it bounds `K_i`, `c_i` and `‖A_i‖_op`,
and `1/κ` bounds the inner radius of a feasible point. -/
structure RadiusBound (κ : ℝ) : Prop where
  κ_pos : 0 < κ
  K_le : ∀ i, ∀ x ∈ I.K i, ‖x‖ ≤ κ
  c_le : ∀ i, eNorm (block I.c i) ≤ κ
  A_le : ∀ i, opNorm (I.blockA i) ≤ κ
  strictly_feasible : ∃ z : I.Vec, I.Aᵀ *ᵥ z = I.b ∧ ∀ i,
    Metric.closedBall (blockPt z i) κ⁻¹ ⊆ I.K i

/-- The standing assumptions of the milestones about the method: the instance is admissible, with
block sizes at most `N`, `m ≥ 2` and `A` of full column rank (reading R10). -/
structure Standing (N : ℕ) : Prop where
  admissible : I.IsAdmissible
  dim_le : ∀ i, I.dim i ≤ N
  two_le : 2 ≤ Fintype.card ι
  rank : FullColRank I.A

end Instance

end BlockLewisIPM


