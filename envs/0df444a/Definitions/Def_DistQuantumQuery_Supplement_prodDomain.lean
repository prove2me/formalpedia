-- Prove2me | Definitions.Def_DistQuantumQuery_Supplement_prodDomain
-- name    : DistQuantumQuery_Supplement_prodDomain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:45:23.988204+00:00
-- url     : https://prove2.me/theorems/8a6e0eef-b910-4bec-9248-9cbfc15066a3
-- title:
--   $k$-fold inputs $\Sigma^k$, product distribution $\mu^{\otimes k}$, $f^{\otimes k}$ and $f^{\oplus k}$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$ and $k\ge1$.
--
--   1. The **$k$-fold input set** $\Sigma^k\subseteq\{0,1\}^{nk}$ consists of the strings $\mathbf x=(x_1,\dots,x_k)$ all of whose blocks $x_i$ lie in $\Sigma$; a $k$-fold input is queried one bit at a time.
--   2. For a distribution $\mu$ on $\Sigma$, the **product distribution** is $\mu^{\otimes k}(x_1,\dots,x_k):=\prod_{j=1}^k\mu(x_j)$.
--   3. For a search problem $f\subseteq\Sigma\times\Omega$, the **$k$-fold problem** $f^{\otimes k}\subseteq\Sigma^k\times\Omega^k$ is $f^{\otimes k}(x_1,\dots,x_k):=f(x_1)\times\cdots\times f(x_k)$: an output $(s_1,\dots,s_k)$ is valid iff $s_i\in f(x_i)$ for every $i$.
--   4. For a decision problem $f:\Sigma\to\{0,1\}$, the **$k$-fold XOR** is $f^{\oplus k}(x_1,\dots,x_k):=f(x_1)\oplus\cdots\oplus f(x_k)$.
--
--   These are the objects of the paper's XOR lemma (Theorem 8.11) and direct-product theorems (Theorems 9.6 and 9.8).
--
--   **Formalization Note** The positions of a $k$-fold input are pairs $(i,j)\in\mathrm{Fin}\,k\times\iota$ (block $i$, bit $j$), and block $i$ is read with the base mission's `blockOf`. A search problem is a relation $R(x,s)$ ("$s\in f(x)$") and $\Omega^k$ is $\mathrm{Fin}\,k\to\Omega$. The XOR is folded over the blocks starting from $0$.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), §2.4.2, p.17 (Σ^k, f^{⊗k}, μ^{⊗k}); Theorem 8.11, p.79 (f^{⊕k})

import Mathlib
import Definitions.Def_DistQuantumQuery_compose

open scoped Matrix

namespace DistQuantumQuery.Supplement

open DistQuantumQuery

/-- The **`k`-fold input set** `Σ^k ⊆ {0,1}^{nk}` of a set `Σ ⊆ {0,1}^n` (Ben-David, Ebtehaj,
*Distributional Quantum Query Complexity*, arXiv:2610.06835, held version, sha256 6334ffaf…,
§2.4.2, p.17): the strings `x = (x_1, …, x_k)` every block `x_i` of which lies in `Σ`.

**Formalization Note** Positions of a `k`-fold input are pairs `(i, j) ∈ Fin k × ι`: block `i`,
bit `j`; block `i` is read by the published `blockOf` of the base mission. The input is queried
bit by bit, so the query oracle of `Σ^k` acts on the `nk` positions, as in the paper. -/
def prodDomain {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (ι → Bool)) (k : ℕ) :
    Finset (Fin k × ι → Bool) :=
  Finset.univ.filter fun x => ∀ i, blockOf x i ∈ S

/-- Membership in `Σ^k`. -/
theorem mem_prodDomain {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset (ι → Bool)} {k : ℕ}
    {x : Fin k × ι → Bool} : x ∈ prodDomain S k ↔ ∀ i, blockOf x i ∈ S := by
  simp [prodDomain]

/-- The `i`-th block `x_i ∈ Σ` of a point `x ∈ Σ^k`. -/
def prodBlock {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset (ι → Bool)} {k : ℕ}
    (x : prodDomain S k) (i : Fin k) : S :=
  ⟨blockOf x.1 i, mem_prodDomain.1 x.2 i⟩

/-- The **product distribution** `μ^{⊗k} : Σ^k → [0,1]`,
`μ^{⊗k}(x_1, …, x_k) := Π_{j=1}^k μ(x_j)` (arXiv:2610.06835, held version, sha256 6334ffaf…,
§2.4.2, p.17). -/
noncomputable def prodDist {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset (ι → Bool)}
    (μ : S → ℝ) (k : ℕ) : prodDomain S k → ℝ :=
  fun x => ∏ j, μ (prodBlock x j)

/-- The **`k`-fold search problem** `f^{⊗k} ⊆ Σ^k × Ω^k`,
`f^{⊗k}(x_1, …, x_k) := f(x_1) × ⋯ × f(x_k)` (arXiv:2610.06835, held version, sha256 6334ffaf…,
§2.4.2, p.17): an output `s = (s_1, …, s_k)` is valid on `x` iff `s_i ∈ f(x_i)` for every `i`.

**Formalization Note** A search problem is a relation `R x s` ("`s ∈ f(x)`"), as in the base
mission; `Ω^k` is `Fin k → Ω`. -/
def prodRel {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {S : Finset (ι → Bool)} {k : ℕ}
    (R : S → Ω → Prop) : prodDomain S k → (Fin k → Ω) → Prop :=
  fun x s => ∀ i, R (prodBlock x i) (s i)

/-- The **`k`-fold XOR** `f^{⊕k} : Σ^k → {0,1}` of a decision problem `f : Σ → {0,1}`,
`f^{⊕k}(x_1, …, x_k) := f(x_1) ⊕ ⋯ ⊕ f(x_k)` (arXiv:2610.06835, held version, sha256 6334ffaf…,
Theorem 8.11, p.79).

**Formalization Note** The XOR is folded over the blocks `0, …, k − 1` starting from `false`
(the XOR of no bits). -/
def xorPow {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset (ι → Bool)} {k : ℕ}
    (f : S → Bool) : prodDomain S k → Bool :=
  fun x => (List.finRange k).foldr (fun i b => xor (f (prodBlock x i)) b) false

end DistQuantumQuery.Supplement


