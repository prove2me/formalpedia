-- Prove2me | Definitions.Def_PlanarDFVS_SingleExp_Supplement_Exact
-- name    : PlanarDFVS_SingleExp_Supplement_Exact
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:32:27.940356+00:00
-- url     : https://prove2.me/theorems/9e189cb1-8988-46c6-8b65-a3264e620661
-- title:
--   §3.3 — input and guarantee of the positive-vertex enumeration algorithm (Lemma 3.7)
-- statement:
--   Let $D$ be a plane digraph on the vertex set $\{0,\dots,n-1\}$ with a fixed crossing-free drawing $E$, and let $k\in\mathbb N$ be a budget. The **exact input** $\mathrm{exactInput}(E,k)$ is the memory list consisting of $n$, the budget $k$ in binary, the $n\times n$ directed adjacency-support bits of $D$, and the rotation system of $E$ restricted to one representative of each class of parallel arcs (each vertex lists its retained incidences in counterclockwise order). It is the input format of the published protected solver (Lemma 3.6), with the budget $k$ in place of the protected set. It contains no feedback vertex set, optimum or correctness certificate.
--
--   For a program $A$, a coefficient $C$, a degree $d$, a space coefficient $S$ and a space degree $e$, the predicate $\mathrm{ExactGuarantee}(A,C,d,S,e)$ says: $A$ is a deterministic program of the binary instruction fragment, and for every loopless digraph $D$ with drawing $E$ and every $k$, writing $p=|V^+|$ for the number of positive vertices of $E$ (those with $w(v)=b(v)-1>0$), $N=\max(1,n)$, $|k|$ for the bit length of $k$ and $\ell$ for the encoded length of the exact input, the run of $A$ on $\mathrm{exactInput}(E,k)$ halts within some horizon $t$ with
--
--   $$\text{work}\le C\cdot\Bigl(\sum_{h=0}^{\min\{p,k\}}\binom{p}{h}\Bigr)\cdot (N+|k|)^{d},\qquad \text{space at every step}\le S\,\ell^{e},$$
--
--   its output is either Fail or (the binary mask of) a directed feedback vertex set of $D$ of size at most $k$, and it returns a set exactly when $D$ has a directed feedback vertex set of size at most $k$.
--
--   This is the interface of Lemma 3.7, the subroutine Exact called by the $6.75^k$ algorithm of Theorem 4.1. Only the predicate is defined here; the existence of such a program is the theorem item Lemma 3.7.
--
--   **Formalization Note** The binomial sum multiplies the polynomial factor. The count $p$ is taken on the full drawing $E$, parallel arcs included. The polynomial factor is in $N$ and the bit length $|k|$ of the binary budget: the machine charges a load by the bit length of the value read, and every correct program must read $k$, so a factor in $N$ alone cannot be met when $k$ is huge.
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 8 (PDF p. 8), §3.3, Lemma 3.7 (input and guarantee)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Interfaces

namespace PlanarDFVS.SingleExp.Supplement

open PlanarDFVS.SingleExp

/-- Lemma 3.7's input: the vertex count, the binary budget `k`, the directed support
    bits and the compressed rotation system of the given drawing. -/
noncomputable def exactInput {n m : ℕ} {G : Graph n m} (E : Drawing G) (k : ℕ) :
    Configuration :=
  { memory := [n, k] ++ supportList G ++ compressedRotation E }

/-- Lemma 3.7's uniform guarantee: one deterministic binary program whose charged work on
    every loopless plane instance is at most `C · (∑_{h ≤ min(p,k)} C(p,h)) · (max(1,n) + |k|)^d`,
    where `p` is the number of positive vertices of the input drawing and `|k|` is the bit
    length of the binary budget (which every correct program must load), whose live space is
    polynomial in the encoded input length, whose output is a DFVS of size at most `k` or
    Fail, and which succeeds exactly on yes-instances. -/
def ExactGuarantee (A : Program) (C : ℝ) (d : ℕ) (S : ℝ) (e : ℕ) : Prop :=
  BinaryProgram A ∧ Deterministic A ∧
  ∀ (n m : ℕ) (G : Graph n m) (E : Drawing G) (k : ℕ), Loopless G → ∃ t : ℕ,
    BoundedRun A (fun _ => false) (exactInput E k) t
      (C * (∑ h ∈ Finset.range (min (positive E).card k + 1),
          (((positive E).card.choose h : ℕ) : ℝ)) * (max 1 n + Nat.size k : ℕ)^d)
      (S * (inputBits (exactInput E k) : ℝ)^e) ∧
    ValidVertexOutput G k (runBinary A (fun _ => false) (exactInput E k) t) ∧
    ((runBinary A (fun _ => false) (exactInput E k) t).result = some true ↔ Feasible G k)

end PlanarDFVS.SingleExp.Supplement


