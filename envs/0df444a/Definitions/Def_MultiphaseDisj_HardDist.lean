-- Prove2me | Definitions.Def_MultiphaseDisj_HardDist
-- name    : MultiphaseDisj_HardDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:25.894944+00:00
-- url     : https://prove2.me/theorems/7301b2c8-521a-44c7-832c-280d8198945b
-- title:
--   The hard distribution $\mathcal D$, the insertion order and Bob's sampling randomness
-- statement:
--   With the parameters of §3.1 ($t=t_uw$, blocks $B_i$, sizes $s_i$):
--
--   1. Under the **hard distribution** $\mathcal D$ of $(\vec S,X)$, independently, each query set $S_j$ ($j\in[m]$) and the inserted set $X$ consist of $s_i$ uniformly random elements of each block $B_i$, and of nothing outside the blocks. We write $S_j^{(i)}=S_j\cap B_i$ and $X^{(i)}=X\cap B_i$.
--   2. The insertions are made in **epochs**, indexed backward in time: epoch $\ell$ comes first and epoch $1$ last, and in epoch $i$ the elements of $X^{(i)}$ are inserted in increasing order.
--   3. The query index $Q$ is uniform on $[m]$ and independent of $(\vec S,X)$; $\Pr_{\mathcal D,Q}$ and $\mathbb E_{\mathcal D,Q}$ refer to this joint law (with $m=n$).
--   4. Bob's private randomness $R_{\mathrm{Bob}}$ consists of an independent bit $R_a$ with $\Pr[R_a=1]=p$ for every cell $a$, where
--   $$
--   p=\frac{\varepsilon}{32\,t_uw},\qquad \varepsilon=\frac1{40},
--   $$
--   and $(\vec S,X)$, $Q$ and $R_{\mathrm{Bob}}$ are mutually independent.
--
--   The module also defines the prefix $S_{<q}=(S_1,\dots,S_{q-1})$ of a tuple.
--
--   **Formalization Note** Because the blocks are disjoint, independent uniform $s_i$-subsets of the blocks form the uniform distribution on the family of sets with exactly $s_i$ elements in every block and none outside; the law of $(\vec S,X)$ is the product of $m+1$ such uniform laws. The law of $((\vec S,X),Q,R_{\mathrm{Bob}})$ is the product of $\mathcal D$, the uniform law on $[m]$ and the law of $R_{\mathrm{Bob}}$, for any law of $R_{\mathrm{Bob}}$ on a finite type. $S_{<q}$ is a tuple whose entries from index $q$ on are empty.
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), §3.1, p.15; §3.2, p.17 (R_Bob, p); §3.3, p.19 (S_<Q)

import Mathlib
import Definitions.Def_MultiphaseDisj_FiniteInfo
import Definitions.Def_MultiphaseDisj_Params

set_option autoImplicit false

noncomputable section

open Classical

namespace MultiphaseDisj

/-- The sets that the hard distribution can produce (Ko, *Unconditional Boolean Dynamic Lower
Bounds from Disjointness*, arXiv:2610.10904, held version sha256 ba26649b…, §3.1, p.15): subsets
of `B₁ ∪ ⋯ ∪ B_ℓ` with exactly `sᵢ` elements in each block `Bᵢ` ("The remaining coordinates
occur in neither the query sets nor X"). -/
def validSets (n t : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun T : Finset (Fin n) =>
    T ⊆ (Finset.Icc 1 (ell n t)).biUnion (block n t) ∧
      ∀ i ∈ Finset.Icc 1 (ell n t), (T ∩ block n t i).card = setSize t i)

/-- The **hard distribution** `D` of `(S⃗, X)` (§3.1, p.15), with `t = tu · w` and `m` query sets:
independently, each query set `S_j` and the inserted set `X` consist of `sᵢ` uniformly random
elements of each block `Bᵢ`, and nothing else.

**Formalization Note** Since the blocks are disjoint, a set is determined by its traces on the
blocks, so "independently uniform `sᵢ`-subsets of each block" is the uniform distribution on
`validSets n t`; the `m + 1` sets are independent (product of masses). -/
def hardLaw (n m t : ℕ) : (Fin m → Finset (Fin n)) × Finset (Fin n) → ℝ :=
  fun p => (∏ j, unif (validSets n t) (p.1 j)) * unif (validSets n t) p.2

/-- The joint law of `((S⃗, X), Q)` with `m = n`: `(S⃗, X) ∼ D` and the query index `Q` uniform on
`[m]`, independent (§3.1, p.15, "PrD,Q and ED,Q"). -/
def dqLaw (n t : ℕ) : ((Fin n → Finset (Fin n)) × Finset (Fin n)) × Fin n → ℝ :=
  fun ω => hardLaw n n t ω.1 * (1 / (n : ℝ))

/-- The insertions of epoch `i`: the elements of `X ∩ Bᵢ` in increasing order (§3.1, p.15). -/
def epochList (n t : ℕ) (X : Finset (Fin n)) (i : ℕ) : List (Fin n) :=
  (X ∩ block n t i).sort (· ≤ ·)

/-- The insertions of epochs `ℓ, ℓ − 1, …, k + 1`, in this order (epochs are indexed backward in
time: epoch `ℓ` comes first and epoch `1` last, §3.1, p.15). -/
def epochsAbove (n t : ℕ) (X : Finset (Fin n)) (k : ℕ) : List (Fin n) :=
  ((List.range (ell n t - k)).map (fun r => ell n t - r)).flatMap (epochList n t X)

/-- The whole insertion sequence of Phase II under the hard distribution: epochs `ℓ, …, 1`. -/
def insertList (n t : ℕ) (X : Finset (Fin n)) : List (Fin n) :=
  epochsAbove n t X 0

/-- The joint law of `((S⃗, X), Q, R_Bob)` (§3.2, p.17: "(⃗S, X), Q and RBob are mutually
independent"), for Bob's private randomness `R_Bob` with law `rlaw` on a finite type `R`. -/
def jointLaw (n t : ℕ) {R : Type*} (rlaw : R → ℝ) :
    ((Fin n → Finset (Fin n)) × Finset (Fin n)) × Fin n × R → ℝ :=
  fun ω => dqLaw n t (ω.1, ω.2.1) * rlaw ω.2.2

/-- Bob's private randomness of §3.2, p.17: an independent bit `R_a` with `Pr[R_a = 1] = p` for
every cell `a` (the law of `R_Bob : Word w → Bool`, with cells the `2 ^ w` words `BitVec w`). -/
def bernLaw (w : ℕ) (p : ℝ) : (BitVec w → Bool) → ℝ :=
  fun r => ∏ a, if r a then p else 1 - p

/-- Bob's sampling probability `p := ε/(32 tu w)` with `ε = 1/40` (§3.2, p.17; `ε` is the constant
of Lemma 4.1). -/
def pSample (tu w : ℕ) : ℝ := (1 / 40) / (32 * (tu : ℝ) * w)

/-- The prefix `S_{<q} := (S₁, …, S_{q−1})` of a tuple, as a tuple that is `none` from index `q`
on (§3.3, p.19). -/
def prefixBefore {m : ℕ} {σ : Type*} (S : Fin m → σ) (q : Fin m) : Fin m → Option σ :=
  fun j => if j < q then some (S j) else none

end MultiphaseDisj


