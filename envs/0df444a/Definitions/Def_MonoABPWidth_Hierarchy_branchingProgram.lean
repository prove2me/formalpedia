-- Prove2me | Definitions.Def_MonoABPWidth_Hierarchy_branchingProgram
-- name    : MonoABPWidth_Hierarchy_branchingProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:15:44.033265+00:00
-- url     : https://prove2.me/theorems/b7afcdfa-0899-4e03-a266-ed28a9b71a55
-- title:
--   Finite layered monotone algebraic branching programs and path sums
-- statement:
--   A program $A$ consists of $d+1$ finite layers $V_0,\ldots,V_d$, with singleton source and sink layers, and one nonnegative affine label $\ell_i(u,v)$ for each consecutive-layer pair. Zero labels encode absent edges; interior layers may be empty. There is no restriction on the order of variables. Its depth is $d$ and its width is $\max_{0\le i\le d}|V_i|$. The computed output is
--   $$
--   f^{(A)}=\sum_{(v_0,\ldots,v_d)\in\prod_i V_i}\prod_{i=0}^{d-1}\ell_i(v_i,v_{i+1}).
--   $$
--   The prefix and suffix polynomials are the analogous path sums from the source to a vertex and from that vertex to the sink. The interval path sum enumerates only vertices between its endpoints. A zero-length path contributes $1$ when its endpoints coincide and $0$ otherwise; a depth-zero singleton program computes $1$.
--
--   These definitions compute the program's resources and semantics from its finite graph, independently of all lower bounds. Using finite ordinal vertex sets loses no finite graph up to relabelling. No relevance or simplicity invariant is built into the program type.
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), §2.2, p.4, PDF5

import Definitions.Def_MonoABPWidth_Hierarchy_polynomials

open scoped BigOperators

namespace MonoABPWidth.Hierarchy

/-- §2.2, p.4. The finite layers are numbered 0,...,depth. A zero label represents
an absent edge. No variable order, relevance or simplicity is imposed. -/
structure MABP (σ : Type) where
  depth : ℕ
  layerSize : Fin (depth + 1) → ℕ
  source_singleton : layerSize 0 = 1
  sink_singleton : layerSize (Fin.last depth) = 1
  label : (i : Fin depth) → Fin (layerSize i.castSucc) →
    Fin (layerSize i.succ) → AffineLabel σ

/-- The largest layer cardinality, a maximum over a finite nonempty set. -/
def MABP.width {σ : Type} (A : MABP σ) : ℕ :=
  Finset.univ.sup A.layerSize

/-- Source vertex in the singleton first layer. -/
def MABP.source {σ : Type} (A : MABP σ) : Fin (A.layerSize 0) :=
  ⟨0, by rw [A.source_singleton]; decide⟩

/-- Sink vertex in the singleton last layer. -/
def MABP.sink {σ : Type} (A : MABP σ) : Fin (A.layerSize (Fin.last A.depth)) :=
  ⟨0, by rw [A.sink_singleton]; decide⟩

/-- §2.2: sum of products over all source-to-sink paths. Since both endpoint
layers are singletons, every choice of one vertex per layer has the required endpoints.
Zero labels kill paths through absent edges. A depth-zero program computes 1. -/
noncomputable def MABP.output {σ : Type} (A : MABP σ) : MvPolynomial σ ℝ := by
  classical
  exact ∑ p : (i : Fin (A.depth + 1)) → Fin (A.layerSize i),
    ∏ e : Fin A.depth, (A.label e (p e.castSucc) (p e.succ)).poly

/-- Sum over paths between specified vertices. Only vertices in the interval [a,b]
are enumerated, so choices outside the interval do not multiply the answer.
For a=b this is the Kronecker delta; for a>b it is zero. -/
noncomputable def MABP.segment {σ : Type} (A : MABP σ)
    (a b : Fin (A.depth + 1)) (u : Fin (A.layerSize a))
    (v : Fin (A.layerSize b)) : MvPolynomial σ ℝ := by
  classical
  exact if hab : a ≤ b then
    ∑ p : (i : {i : Fin (A.depth + 1) // a ≤ i ∧ i ≤ b}) → Fin (A.layerSize i.val),
      if p ⟨a, le_rfl, hab⟩ = u ∧ p ⟨b, hab, le_rfl⟩ = v then
        ∏ e : Fin A.depth,
          if he : a.val ≤ e.val ∧ e.val < b.val then
            (A.label e
              (p ⟨e.castSucc, ⟨he.1, Nat.le_of_lt he.2⟩⟩)
              (p ⟨e.succ, ⟨Nat.le_succ_of_le he.1, he.2⟩⟩)).poly
          else 1
      else 0
  else 0

/-- Prefix polynomial f_(s→v). -/
noncomputable def MABP.prefix {σ : Type} (A : MABP σ)
    (i : Fin (A.depth + 1)) (v : Fin (A.layerSize i)) : MvPolynomial σ ℝ :=
  A.segment 0 i A.source v

/-- Suffix polynomial f_(v→t). -/
noncomputable def MABP.suffix {σ : Type} (A : MABP σ)
    (i : Fin (A.depth + 1)) (v : Fin (A.layerSize i)) : MvPolynomial σ ℝ :=
  A.segment i (Fin.last A.depth) v A.sink

end MonoABPWidth.Hierarchy


