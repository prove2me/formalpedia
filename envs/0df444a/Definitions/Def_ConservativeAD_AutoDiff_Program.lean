-- Prove2me | Definitions.Def_ConservativeAD_AutoDiff_Program
-- name    : ConservativeAD_AutoDiff_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:44.539062+00:00
-- url     : https://prove2.me/theorems/f9711c8c-8b19-418b-b959-b993dfbedd01
-- title:
--   Algorithms 1–3: evaluation programs, forward and reverse mode automatic differentiation
-- statement:
--   An **evaluation program** consists of integers $p<q$, a map $\mathtt{parents}$ assigning to each non-input node $k\in\{p+1,\dots,q\}$ a tuple without repetition of indices in $\{1,\dots,k-1\}$, elementary functions $g_k:\mathbb R^{|\mathtt{parents}(k)|}\to\mathbb R$, and set-valued maps $D_k:\mathbb R^{|\mathtt{parents}(k)|}\rightrightarrows\mathbb R^{|\mathtt{parents}(k)|}$ (the paper's (a)–(c), and the data of (d)).
--
--   **Algorithm 1** evaluates $f:\mathbb R^p\to\mathbb R$: given $x=(x_1,\dots,x_p)$, for $k=p+1,\dots,q$ set $x_k=g_k(x_{\mathtt{parents}(k)})$ with $x_{\mathtt{parents}(k)}=(x_i)_{i\in\mathtt{parents}(k)}$, and return $f(x)=x_q$.
--
--   A **choice** at $x$ is a family $d_k=(d_{kj})_j\in D_k(x_{\mathtt{parents}(k)})$, $k=p+1,\dots,q$.
--
--   **Algorithm 2 (forward mode)** sets $\partial x_k/\partial x_{1,\dots,p}=e_k$ for $k\le p$ and, for $k=p+1,\dots,q$,
--
--   $$
--   \frac{\partial x_k}{\partial x}=\sum_{j\in\mathtt{parents}(k)}\frac{\partial x_j}{\partial x}\,d_{kj},
--   $$
--
--   and returns $\partial x_q/\partial x_{1,\dots,p}\in\mathbb R^p$.
--
--   **Algorithm 3 (reverse mode)** starts from $v=(0,\dots,0,1)\in\mathbb R^q$; for $t=q,\dots,p+1$ and every $j\in\mathtt{parents}(t)$ it updates $v[j]:=v[j]+v[t]\,d_{tj}$, and returns $(v[1],\dots,v[p])$.
--
--   The **autodiff fields** are $D_{\mathrm{fwd}}(x)=\{\text{output of Algorithm 2 for } d : d \text{ a choice at } x\}$ and $D_{\mathrm{rev}}(x)$, the same with Algorithm 3: the sets of outputs over **all** choices.
--
--   These objects model nonsmooth automatic differentiation of a function given as a closed formula, as in backpropagation for neural networks.
--
--   **Formalization Note** Nodes are `Fin q`, numbered from $0$: node $k$ is the paper's $x_{k+1}$, the inputs are the nodes $k<p$, and the output is node $q-1$. Input nodes have empty parent lists; the fields `g k`, `D k` at input nodes are never used. Parent tuples are `List`s (their order fixes the argument order of $g_k$). Algorithm 2's loop bound, printed "$P$", is read as $q$. **Algorithm 3 is repaired:** the printed update is "$v[j] := v[t]d_{tj}$" (an overwrite), but the paper's proof computes $v_t=(I+d_te_t^T)\cdots(I+d_qe_q^T)e_q$, i.e. the accumulation $v[j]:=v[j]+v[t]d_{tj}$; with the overwrite, reverse and forward mode disagree as soon as a node has two children (as $x_4$ does in Example 1). The inner loop is applied simultaneously, which is the same since $j<t$ leaves $v[t]$ unchanged. Property (d) is a hypothesis of the theorems, not a field of the structure.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 20, §5.1 (a)–(c) and Algorithm 1; p. 21, (d) and Algorithm 2; p. 22, Algorithm 3 and Theorem 8 (i)–(ii)

import Mathlib
import Definitions.Def_ConservativeAD_AutoDiff_ConservativeField

namespace ConservativeAD.AutoDiff

/-- The evaluation program of §5.1 (a)–(c), with the elementary conservative fields of (d) as data.
Nodes are `Fin q`, numbered from `0`: node `k` is the paper's `x_{k+1}`. The first `p` nodes
(`k < p`) are the inputs `x_1, …, x_p`, and the output is the last node `q - 1` (the paper's
`x_q`).
* (a) `p < q`;
* (b) `parents k` is a tuple (a `List`, so its order fixes the argument order of `g k`) without
  repetition of nodes strictly smaller than `k`; input nodes have no parents;
* (c) `g k : ℝ^{|parents k|} → ℝ` is the elementary function of the non-input node `k`;
* `D k : ℝ^{|parents k|} ⇒ ℝ^{|parents k|}` is the set-valued map of (d) attached to `g k`
  (property (d) itself is a hypothesis of the theorems). The values of `g k`, `D k` at input
  nodes are never used. -/
structure Program (p q : ℕ) where
  p_lt_q : p < q
  parents : Fin q → List (Fin q)
  parents_input : ∀ k : Fin q, k.val < p → parents k = []
  parents_nodup : ∀ k : Fin q, (parents k).Nodup
  parents_lt : ∀ k : Fin q, ∀ j ∈ parents k, j < k
  g : (k : Fin q) → EuclideanSpace ℝ (Fin (parents k).length) → ℝ
  D : (k : Fin q) → EuclideanSpace ℝ (Fin (parents k).length) →
    Set (EuclideanSpace ℝ (Fin (parents k).length))

namespace Program

variable {p q : ℕ} (P : Program p q)

/-- The output node `q - 1` (the paper's `x_q`). -/
def output : Fin q := ⟨q - 1, by have := P.p_lt_q; omega⟩

/-- Algorithm 1 (forward evaluation): the value `x_k` of every node at the input `x ∈ ℝ^p`.
Inputs are copied, and `x_k = g_k(x_{parents(k)})` for a non-input node. -/
noncomputable def eval (x : EuclideanSpace ℝ (Fin p)) (k : Fin q) : ℝ :=
  if h : k.val < p then x ⟨k.val, h⟩
  else P.g k (WithLp.toLp 2 (fun i => eval x ((P.parents k).get i)))
termination_by k.val
decreasing_by exact P.parents_lt k _ (List.get_mem _ _)

/-- `x_{parents(k)} = (x_i)_{i ∈ parents(k)} ∈ ℝ^{|parents k|}`, computed by Algorithm 1. -/
noncomputable def parentVals (x : EuclideanSpace ℝ (Fin p)) (k : Fin q) :
    EuclideanSpace ℝ (Fin (P.parents k).length) :=
  WithLp.toLp 2 (fun i => P.eval x ((P.parents k).get i))

/-- The function `f : ℝ^p → ℝ` defined by Algorithm 1: `f(x) = x_q`. -/
noncomputable def fn (x : EuclideanSpace ℝ (Fin p)) : ℝ := P.eval x P.output

/-- A family of vectors `d_k ∈ ℝ^{|parents k|}`, one per node (`d_k = (d_{kj})_{j}`); only the
non-input nodes matter. -/
abbrev Choice := (k : Fin q) → EuclideanSpace ℝ (Fin (P.parents k).length)

/-- `d` is an admissible input of Algorithms 2 and 3 at `x`: `d_k ∈ D_k(x_{parents(k)})` for every
non-input node `k`. -/
def IsChoice (x : EuclideanSpace ℝ (Fin p)) (d : P.Choice) : Prop :=
  ∀ k : Fin q, p ≤ k.val → d k ∈ P.D k (P.parentVals x k)

/-- Algorithm 2 (forward mode): the row `∂x_k/∂x_{1,…,p} ∈ ℝ^p`. It is the `k`-th unit vector
for an input node, and `∑_{j ∈ parents(k)} (∂x_j/∂x_{1,…,p}) d_{kj}` otherwise. -/
noncomputable def fwdRow (d : P.Choice) (k : Fin q) : EuclideanSpace ℝ (Fin p) :=
  if h : k.val < p then EuclideanSpace.single ⟨k.val, h⟩ 1
  else ∑ i : Fin (P.parents k).length, d k i • fwdRow d ((P.parents k).get i)
termination_by k.val
decreasing_by exact P.parents_lt k _ (List.get_mem _ _)

/-- The output `∂x_q/∂x_{1,…,p}` of Algorithm 2 for the choice `d`. -/
noncomputable def forward (d : P.Choice) : EuclideanSpace ℝ (Fin p) := P.fwdRow d P.output

/-- `w ∈ ℝ^{|parents k|}` seen as a vector of `ℝ^q`: coordinate `parents(k)_i` receives `w_i`, all
other coordinates are `0` ("simply add zeros to coordinates which do not correspond to parents
of `k`"). -/
noncomputable def lift (k : Fin q) (w : EuclideanSpace ℝ (Fin (P.parents k).length)) :
    EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 (fun j => ∑ i : Fin (P.parents k).length,
    if (P.parents k).get i = j then w i else 0)

/-- Algorithm 3 (reverse mode), with the accumulating update `v[j] := v[j] + v[t] d_{tj}`:
`revState d n` is the vector `v ∈ ℝ^q` after the outer loop has processed the `n` nodes
`q - 1, q - 2, …, q - n` (0-based; the paper's `t = q, …, q - n + 1`). It starts from
`v = (0, …, 0, 1)`, and only the non-input nodes are processed. -/
noncomputable def revState (d : P.Choice) : ℕ → (Fin q → ℝ)
  | 0 => Pi.single P.output 1
  | n + 1 =>
    if h : n < q - p then
      fun j => revState d n j +
        revState d n ⟨q - 1 - n, by omega⟩ * P.lift ⟨q - 1 - n, by omega⟩ (d ⟨q - 1 - n, by omega⟩) j
    else revState d n

/-- The output `(v[1], …, v[p])` of Algorithm 3 for the choice `d`. -/
noncomputable def reverse (d : P.Choice) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (fun i : Fin p => P.revState d (q - p) ⟨i.val, by have := P.p_lt_q; omega⟩)

/-- Theorem 8 (i): `D(x)` = the set of outputs of Algorithm 2 over all admissible choices at `x`. -/
def Dfwd (x : EuclideanSpace ℝ (Fin p)) : Set (EuclideanSpace ℝ (Fin p)) :=
  {v | ∃ d : P.Choice, P.IsChoice x d ∧ P.forward d = v}

/-- Theorem 8 (ii): the set of outputs of Algorithm 3 over all admissible choices at `x`. -/
def Drev (x : EuclideanSpace ℝ (Fin p)) : Set (EuclideanSpace ℝ (Fin p)) :=
  {v | ∃ d : P.Choice, P.IsChoice x d ∧ P.reverse d = v}

end Program

end ConservativeAD.AutoDiff


