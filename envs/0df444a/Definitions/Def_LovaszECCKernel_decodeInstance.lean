-- Prove2me | Definitions.Def_LovaszECCKernel_decodeInstance
-- name    : LovaszECCKernel_decodeInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:55.341567+00:00
-- url     : https://prove2.me/theorems/0bb17997-bc6c-4069-b0d5-1496869d7b62
-- title:
--   The fixed decoding of kernel outputs, bit length, and the kernel predicates
-- statement:
--   A kernel's output is a list of natural numbers, decoded by one fixed rule into an instance $(G',k')$:
--
--   1. $[0,n,m,u_1,v_1,\dots,u_m,v_m,k']$ is the graph on $\{0,\dots,n-1\}$ with edges $u_iv_i$ ($u_i\ne v_i$, both $<n$) and parameter $k'$ (the constant-size yes/no instances and the unchanged input of Algorithm 1);
--   2. $[1,r,t_1,\dots,t_r,q,u_1,v_1,\dots,u_q,v_q,k']$ is $K_{t_1,\dots,t_r}\triangle M$ on $N=t_1+\cdots+t_r$ vertices, part $i$ being the $i$-th consecutive block of indices and $M$ the $q$ listed pairs ($u_i\ne v_i<N$), with parameter $k'$ (the triple $((t_1,\dots,t_r),M,k)$ of Algorithm 1, line 27);
--   3. every other list is not a kernel output.
--
--   The **bit length** of a list $x_1,\dots,x_L$ is $\sum_j(\lfloor\log_2x_j\rfloor+2)$ ($0$ taking one bit), the length of its binary listing with one separator per number. An output is a **kernel output with constant $c$** for the parameter $k$ if it decodes to some $(G',k')$ with
--   $$|V(G')|\le c(k+1),\qquad k'\le c(k+1)(\lfloor\log_2(k+1)\rfloor+1),\qquad \text{bit length}\le c(k+1)(\lfloor\log_2(k+1)\rfloor+1),$$
--   the reading of "$O(k)$ vertices and total size $O(k\log k)$ bits" together with the bound on $k'$ of the definition of a kernel ($|x'|+k'\le f(k)$). It is **equivalent** to $(G,k)$ if $\mathrm{ecc}(G')\le\mathrm{Lb}(G')-k'\iff\mathrm{ecc}(G)\le\mathrm{Lb}(G)-k$.
--
--   **Formalization Note** The decoding is fixed before any algorithm, so that an algorithm cannot hide information in a decoding of its own. The $+1$'s make the bounds positive at $k=0,1$.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 3, p.4, §2, p.16, and Algorithm 1 with the encoding paragraph, p.42 (= PDF pp.4, 16, 42)

import Mathlib
import Definitions.Def_LovaszECCKernel_InLb

set_option autoImplicit false

namespace LovaszECCKernel

/-- Consecutive pairs of a list: `[a₁, b₁, a₂, b₂, …] ↦ [(a₁, b₁), (a₂, b₂), …]` (a trailing odd
entry is dropped). -/
def pairsOf : List ℕ → List (ℕ × ℕ)
  | a :: b :: rest => (a, b) :: pairsOf rest
  | _ => []

/-- The graph on `Fin n` whose edges are the listed pairs (in either orientation). -/
def edgeListGraph (n : ℕ) (ps : List (ℕ × ℕ)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ((u.val, v.val) ∈ ps ∨ (v.val, u.val) ∈ ps)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The index of the block containing `x` when `0, 1, 2, …` is cut into consecutive blocks of the
sizes `t₁, t₂, …, t_r`: the number of blocks that end at or before `x`. -/
def blockOf (sizes : List ℕ) (x : ℕ) : ℕ :=
  ((List.range sizes.length).filter (fun i => (sizes.take (i + 1)).sum ≤ x)).length

/-- The graph `K_{t₁,…,t_r} △ M` on `Fin (t₁ + ⋯ + t_r)`: part `i` is the `i`-th consecutive block
of indices, two vertices of different parts are adjacent in `K_{t₁,…,t_r}`, and the listed pairs
`M` are flipped. -/
def multipartiteFlipGraph (sizes : List ℕ) (ps : List (ℕ × ℕ)) :
    SimpleGraph (Fin sizes.sum) where
  Adj u v := u ≠ v ∧ (blockOf sizes u.val ≠ blockOf sizes v.val ↔
    ¬ ((u.val, v.val) ∈ ps ∨ (v.val, u.val) ∈ ps))
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [ne_comm, or_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The **fixed decoding of kernel outputs** into instances `(G′, k′)` of ECC below the Lovász bound
(Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript sha256
a9d53ab8…), Algorithm 1 and p.42 (= PDF p.42): "return ((t1, t2, . . . , tr), M, k)"; "It is
important that the algorithm's output is encoded as a triple (G△M, M, k) to achieve the bitsize
upper-bound given in the statement. Since G△M is a complete r-partite graph, it is encoded as a
sequence t1, t2, . . . , tr of its parts' sizes"; lines 3, 6, 19, 21, 25 return a constant-size
yes/no instance or the input `(G, k)` itself).

* Tag `0`, `[0, n, m, u₁, v₁, …, u_m, v_m, k′]`: the graph on `Fin n` with edges `u_i v_i`
  (all `u_i, v_i < n`, `u_i ≠ v_i`), and the parameter `k′`.
* Tag `1`, `[1, r, t₁, …, t_r, q, u₁, v₁, …, u_q, v_q, k′]`: the graph `K_{t₁,…,t_r} △ M` on
  `Fin (t₁ + ⋯ + t_r)`, part `i` occupying the `i`-th consecutive block of indices, `M` the `q`
  listed pairs (all `u_i, v_i < t₁ + ⋯ + t_r`, `u_i ≠ v_i`), and the parameter `k′`.
* Every other list (wrong tag, wrong length, a pair out of range or on the diagonal) decodes to
  `none`.

**Formalization Note** The decoding is fixed here, before any algorithm, so that a kernel's bit size
is measured in this code and an algorithm cannot hide information in a decoding of its own. -/
def decodeInstance : List ℕ → Option (Σ n : ℕ, SimpleGraph (Fin n) × ℕ)
  | 0 :: n :: m :: rest =>
      if rest.length = 2 * m + 1 ∧
          (pairsOf (rest.take (2 * m))).all (fun p => decide (p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2))
      then some ⟨n, edgeListGraph n (pairsOf (rest.take (2 * m))), rest.getLastD 0⟩
      else none
  | 1 :: r :: rest =>
      match rest.drop r with
      | q :: rest₂ =>
          if (rest.take r).length = r ∧ rest₂.length = 2 * q + 1 ∧
              (pairsOf (rest₂.take (2 * q))).all (fun p =>
                decide (p.1 < (rest.take r).sum ∧ p.2 < (rest.take r).sum ∧ p.1 ≠ p.2))
          then some ⟨(rest.take r).sum,
            multipartiteFlipGraph (rest.take r) (pairsOf (rest₂.take (2 * q))), rest₂.getLastD 0⟩
          else none
      | [] => none
  | _ => none

/-- The **bit length** of a list of natural numbers: `Σ_x (⌊log₂ x⌋ + 2)` (with `0` taking one
bit), the length of the binary listing of the numbers with one separator per number (Fomin et al.,
STOC 2027 submission (manuscript sha256 a9d53ab8…), p.16 (= PDF p.16): "the bitsize of a kernel,
which is the maximum length of the binary string encoding the obtained instance").

**Formalization Note** `Nat.size x` is the number of binary digits of `x` (`Nat.size 0 = 0`). -/
def bitLength (out : List ℕ) : ℕ := (out.map (fun x => Nat.size x + 1)).sum

/-- The bound `c · (k + 1) · (⌊log₂ (k + 1)⌋ + 1)`, the reading of `O(k log k)`.

**Formalization Note** The `+ 1`s make the bound positive at `k = 0, 1`, where `k log k = 0` but an
instance needs at least one bit. -/
def sizeBound (c k : ℕ) : ℕ := c * (k + 1) * (Nat.log 2 (k + 1) + 1)

/-- `out` is a **kernel output of size `O(k)` vertices and `O(k log k)` bits** for the parameter
`k`, with constant `c` (Fomin et al., STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 3,
p.4, and §2, p.16 (= PDF pp.4, 16): "a kernel with O(k) vertices and total size O(k log k) bits";
"(ii) |x′| + k′ ≤ f(k) … we distinguish between the maximum number of vertices in the graph
obtained by a kernelization algorithm and the bitsize of a kernel"): `out` decodes (by
`decodeInstance`) to an instance `(G′, k′)` with `G′` on at most `c(k + 1)` vertices,
`k′ ≤ c(k + 1)(⌊log₂(k + 1)⌋ + 1)`, and the bit length of `out` at most
`c(k + 1)(⌊log₂(k + 1)⌋ + 1)`. -/
def IsKernelOutput (c k : ℕ) (out : List ℕ) : Prop :=
  ∃ n' : ℕ, ∃ G' : SimpleGraph (Fin n'), ∃ k' : ℕ, decodeInstance out = some ⟨n', G', k'⟩ ∧
    n' ≤ c * (k + 1) ∧ k' ≤ sizeBound c k ∧ bitLength out ≤ sizeBound c k

/-- The output `out` decodes to an instance **equivalent** to `(G, k)` (Fomin et al., STOC 2027
submission (manuscript sha256 a9d53ab8…), §2, p.16 (= PDF p.16): "(i) (x, k) ∈ L if and only if
(x′, k′) ∈ L"): `out` decodes to `(G′, k′)` with `ecc(G′) ≤ Lb(G′) − k′ ⟺ ecc(G) ≤ Lb(G) − k`. -/
def KernelEquiv {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (out : List ℕ) : Prop :=
  ∃ n' : ℕ, ∃ G' : SimpleGraph (Fin n'), ∃ k' : ℕ, decodeInstance out = some ⟨n', G', k'⟩ ∧
    (InLb G' k' ↔ InLb G k)

end LovaszECCKernel


