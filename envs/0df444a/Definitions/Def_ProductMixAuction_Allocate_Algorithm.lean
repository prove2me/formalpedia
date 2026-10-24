-- Prove2me | Definitions.Def_ProductMixAuction_Allocate_Algorithm
-- name    : ProductMixAuction_Allocate_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:54.230415+00:00
-- url     : https://prove2.me/theorems/1bad4125-0ca7-4bb2-bc7d-dd9494f88194
-- title:
--   §4, pp. 14–23, 38 — demand clusters, link goods, multi-bidder cycles, FindParams, NonMarginals, UnambiguousMarginals, ShiftProjectUnshift, the run of Allocate
-- statement:
--   This module formalizes the algorithm ALLOCATE of §4 (Algorithm 1, p. 14) and its parts, on top of the setting module (bids, demand, allocation problems, the edge set of the marginal bids graph $G_{\mathcal A}$).
--
--   **Structure of $G_{\mathcal A}$** (p. 17). $G_{\mathcal A}[j]$ is the subgraph of $j$-labelled edges. A pair $(I,j)$ is a *demand cluster* if $I$ is the vertex set of a connected component of $G_{\mathcal A}[j]$ (so $I$ has at least two goods). A good is a *link good* if its incident edges carry more than one label. A *multi-bidder cycle* is a cycle of $G_{\mathcal A}$ with edges of different labels; a vertex of it is a *cycle-link good* if its two cycle edges are labelled differently. The predicate "$i^*$ is a cycle-link good and $j^*$ the label of one of its cycle edges" is stated with a cycle $v_0=i^*,v_1,\dots,v_{k-1}$ of $k\ge2$ distinct goods whose edges $\{v_t,v_{t+1 \bmod k}\}$ carry labels $\ell_t$, with $\ell_0=j^*\neq\ell_{k-1}$.
--
--   **FindParams** (Definition 7, Algorithm 2, p. 18). The derived graph $D_{\mathcal A}$ is bipartite between link goods and demand clusters, with $i\sim(I,j)$ iff $i\in I$. FindParams returns an isolated demand cluster if there is one; otherwise it walks a maximal path from a link good, takes the last link good $i^*$ and the last cluster $(I,j^*)$, and returns $(I,j^*)$ if the path is open and $(i^*,j^*)$ if it is closed. A path is *closed* when its last vertex is adjacent to a vertex at least two positions earlier (the corrected reading; see Lemma 10). A *selector* is any map from allocation problems to choices; it is *admissible* if, on every problem whose bids are all marginal and which has a non-empty bid list, it returns either a demand cluster with at most one link good or a cycle-link good with the label of one of its cycle edges (Lemma 10's output).
--
--   **NonMarginals** (Algorithm 3). Every non-marginal bid $b$ of bidder $j$, demanding the unique good $i$, is removed; $m^j_i$ increases and $r_i$ decreases by $w(b)$.
--
--   **UnambiguousMarginals** (Algorithm 4). For a demand cluster $(I,j)$: with no link good, $r_i$ is moved to $m^j_i$ for every $i\in I$; with link good $i^*$, $d=\sum_{b\in\mathcal B^j_I}w(b)-\sum_{i\in I\setminus\{i^*\}}r_i$ units of $i^*$ and $r_i$ units of every other $i\in I$ are moved, where $\mathcal B^j_I$ are $j$'s bids marginal on goods in $I$; then $\mathcal B^j_I$ is removed from $\mathcal B^j$.
--
--   **ShiftProjectUnshift** (Algorithm 5, p. 22). With $\varepsilon=\tfrac1{10}$: add $\varepsilon e^{i^*}$ to every bid of $j^*$, giving the aggregate list $\mathcal B'$; with the Lyapunov function (5)
--   $$g(q)=f_{\mathcal B'}(q)+\sum_{i\in[n]}r_iq_i,$$
--   let $h^+(S)=g(p+\varepsilon e^S)-g(p)$ and $h^-(S)=g(p-\varepsilon e^S)-g(p)$ for $S\subseteq[n]$, let $S^\pm$ be returned by the SFM oracle on $h^\pm$, and let $p^\varepsilon$ be whichever of $p+\varepsilon e^{S^+}$, $p-\varepsilon e^{S^-}$ has the smaller $g$ (proof of Proposition 14, p. 38). Then *project* every bid w.r.t. $p^\varepsilon$ — with $I$ its demanded goods, $b'=b-e^{[n]_0\setminus I}$ if $0\in I$ and $b'=b+e^I$ otherwise (p. 21) — subtract $\varepsilon e^{i^*}$ from $j^*$'s bids and keep the price $p$. An *SFM oracle* maps set functions on $[n]$ to subsets; it is *admissible* if it returns a minimiser of every submodular set function, with nothing required on other inputs.
--
--   **The run.** The initial problem for integral bid lists, an integral price $p$ and a target $t\in\mathbb Z^n$ has $m^j=0$ and residual $r=(t_0,t)$ with $t_0=\sum_b w(b)-\sum_i t_i$ (p. 16). One loop iteration (lines 5–10) does nothing if all lists are empty, and otherwise applies UnambiguousMarginals or ShiftProjectUnshift according to the selector, then NonMarginals; `run 0` is the state after line 3 and `run k` the state after $k$ iterations. An iteration's SFM calls are *genuine* if both set functions passed to the oracle are submodular.
--
--   **Formalization Note** FindParams is "not fully specified" (p. 23); it is formalized by its possible outputs (`FindParamsOutput`) and, for the run, by an arbitrary selector meeting Lemma 10's output contract. Submodularity is the published `NonmonotoneSubmod.Shared.Submodular`. ShiftProjectUnshift is read literally when $i^*=0$: the reject entry of $j^*$'s bids is $\tfrac1{10}$ during the shift.
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, pp. 13–23, 38, (5), Definition 7, Algorithms 1–5, proof of Proposition 14

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Setting
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

/-!
Baldwin, Goldberg, Klemperer, Lock, *Solving Strong-Substitutes Product-Mix Auctions*,
arXiv:1909.07313v3, §4 (pp. 14–23): demand clusters, link goods and multi-bidder cycles of the
marginal bids graph `G_A` (p. 17), the derived graph `D_A` (Definition 7) and the output of
FindParams (Algorithm 2, p. 18), the procedures NonMarginals (Algorithm 3), UnambiguousMarginals
(Algorithm 4), the shift, the projection (p. 21), the Lyapunov function (5) and the SFM step of
ShiftProjectUnshift (Algorithm 5, p. 22; proof of Proposition 14, p. 38), and the run of
Allocate (Algorithm 1, p. 14).
-/

namespace ProductMixAuction.Allocate

open Finset

variable {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-! ### The marginal bids graph: clusters, link goods, multi-bidder cycles (p. 17) -/

/-- `G_A[j]` has an edge between `i` and `i'`. -/
def adj (A : AllocProblem n J) (j : J) (i i' : Fin (n + 1)) : Prop :=
  (s(i, i'), j) ∈ edges A

/-- `(I, j)` is a demand cluster: `I` is the vertex set of a connected component of `G_A[j]`, the
subgraph induced by the `j`-labelled edges (so `I` has a vertex with a `j`-edge). -/
def IsCluster (A : AllocProblem n J) (I : Finset (Fin (n + 1))) (j : J) : Prop :=
  ∃ i, (∃ i', adj A j i i') ∧ ∀ k, k ∈ I ↔ Relation.ReflTransGen (adj A j) i k

/-- `i` is a link good: its incident edges in `G_A` carry more than one bidder label. -/
def IsLink (A : AllocProblem n J) (i : Fin (n + 1)) : Prop :=
  ∃ e₁ ∈ edges A, ∃ e₂ ∈ edges A, i ∈ e₁.1 ∧ i ∈ e₂.1 ∧ e₁.2 ≠ e₂.2

/-- `istar` is a cycle-link good of a multi-bidder cycle of `G_A` and `jstar` is the label of one
of its two edges in that cycle: there is a cycle `v 0 = istar, v 1, …, v (k-1)` of `k ≥ 2` distinct
goods whose edge `{v t, v (t+1 mod k)}` carries label `ℓ t`, with `ℓ 0 = jstar` and the other edge
at `istar`, `{v (k-1), v 0}`, carrying a different label `ℓ (k-1) ≠ ℓ 0`. -/
def IsCycleLink (A : AllocProblem n J) (istar : Fin (n + 1)) (jstar : J) : Prop :=
  ∃ k : ℕ, ∃ hk : 2 ≤ k, ∃ v : Fin k → Fin (n + 1), ∃ ℓ : Fin k → J,
    Function.Injective v ∧ (∀ t : Fin k, (s(v t, v (finRotate k t)), ℓ t) ∈ edges A) ∧
    v ⟨0, by omega⟩ = istar ∧ ℓ ⟨0, by omega⟩ = jstar ∧ ℓ ⟨k - 1, by omega⟩ ≠ ℓ ⟨0, by omega⟩

/-! ### Choices of FindParams and the selector contract (Lemma 10) -/

/-- An output of FindParams: a demand cluster `(I, j)` (for UnambiguousMarginals) or a cycle-link
good `istar` with an edge label `jstar` (for ShiftProjectUnshift). -/
inductive Choice (n : ℕ) (J : Type*) where
  | cluster (I : Finset (Fin (n + 1))) (j : J)
  | shift (istar : Fin (n + 1)) (jstar : J)

/-- The outputs Lemma 10 allows: a demand cluster with at most one link good, or a cycle-link good
of a multi-bidder cycle together with the label of one of its edges in that cycle. -/
def AdmissibleChoice (A : AllocProblem n J) : Choice n J → Prop
  | .cluster I j => IsCluster A I j ∧ {i | i ∈ I ∧ IsLink A i}.Subsingleton
  | .shift istar jstar => IsCycleLink A istar jstar

/-- A parameter selector (an implementation of FindParams): a choice for every allocation
problem. -/
abbrev Selector (n : ℕ) (J : Type*) := AllocProblem n J → Choice n J

/-- The selector meets Lemma 10's output contract whenever Allocate calls it: on every problem
whose bids are all marginal and which has a non-empty bid list. -/
def Selector.Admissible (sel : Selector n J) : Prop :=
  ∀ A : AllocProblem n J, (∀ j, ∀ b ∈ A.B j, IsMarginalBid b A.p) → (∃ j, A.B j ≠ []) →
    AdmissibleChoice A (sel A)

/-! ### The derived graph and FindParams (Definition 7, Algorithm 2, p. 18) -/

/-- Vertices of the derived graph `D_A`: link goods and demand clusters. -/
inductive DVert (n : ℕ) (J : Type*) where
  | good (i : Fin (n + 1))
  | cluster (I : Finset (Fin (n + 1))) (j : J)

/-- Adjacency in the derived graph `D_A` (Definition 7): link good `i` and demand cluster `(I, j)`
are adjacent iff `i ∈ I`. -/
def dAdj (A : AllocProblem n J) : DVert n J → DVert n J → Prop
  | .good i, .cluster I j => IsLink A i ∧ IsCluster A I j ∧ i ∈ I
  | .cluster I j, .good i => IsLink A i ∧ IsCluster A I j ∧ i ∈ I
  | _, _ => False

/-- A demand cluster that is isolated in `D_A`, i.e. contains no link good. -/
def IsIsolatedCluster (A : AllocProblem n J) (I : Finset (Fin (n + 1))) (j : J) : Prop :=
  IsCluster A I j ∧ ∀ i ∈ I, ¬ IsLink A i

/-- `π 0, …, π (k-1)` is a maximal path of `D_A` started at a link good: distinct vertices,
consecutive ones adjacent, and every neighbour of the last vertex already on the path. -/
def IsMaximalWalkPath (A : AllocProblem n J) (k : ℕ) (π : Fin k → DVert n J) : Prop :=
  ∃ hk : 0 < k, Function.Injective π ∧
    (∃ i, π ⟨0, hk⟩ = .good i ∧ IsLink A i) ∧
    (∀ t : ℕ, ∀ ht : t + 1 < k, dAdj A (π ⟨t, by omega⟩) (π ⟨t + 1, ht⟩)) ∧
    (∀ u, dAdj A (π ⟨k - 1, by omega⟩) u → u ∈ Set.range π)

/-- Algorithm 2 (FindParams) may return `c` on `A`. If `D_A` has an isolated demand cluster, `c` is
such a cluster. Otherwise `c` is read off a maximal path `π 0, …, π (k-1)` started at a link good,
with `i*` its last link good and `(I, j*)` its last demand cluster: if the path is closed — the last
vertex is adjacent to some `π s` with `s ≤ k - 3` (the corrected reading of p. 18) — then
`c = shift i* j*`, and otherwise `c = cluster I j*`. -/
def FindParamsOutput (A : AllocProblem n J) (c : Choice n J) : Prop :=
  (∃ I j, IsIsolatedCluster A I j ∧ c = .cluster I j) ∨
  ((¬ ∃ I j, IsIsolatedCluster A I j) ∧
    ∃ k : ℕ, ∃ π : Fin k → DVert n J, IsMaximalWalkPath A k π ∧
      ∃ istar : Fin (n + 1), ∃ I : Finset (Fin (n + 1)), ∃ jstar : J,
        -- `istar` is the last link good and `(I, jstar)` the last demand cluster of the path
        (∃ s₁ : Fin k, π s₁ = .good istar ∧
          ∀ t : Fin k, s₁ < t → ∀ i, π t ≠ .good i) ∧
        (∃ s₂ : Fin k, π s₂ = .cluster I jstar ∧
          ∀ t : Fin k, s₂ < t → ∀ I' j', π t ≠ .cluster I' j') ∧
        ((∃ s : Fin k, s.val + 3 ≤ k ∧ ∃ hk : 0 < k, dAdj A (π ⟨k - 1, by omega⟩) (π s)) →
          c = .shift istar jstar) ∧
        ((¬ ∃ s : Fin k, s.val + 3 ≤ k ∧ ∃ hk : 0 < k, dAdj A (π ⟨k - 1, by omega⟩) (π s)) →
          c = .cluster I jstar))

/-! ### NonMarginals (Algorithm 3, p. 19) -/

open scoped Classical in
/-- Algorithm 3 (NonMarginals): every non-marginal bid `b` of bidder `j`, demanding the unique good
`i`, is removed from `Bʲ`, `mʲ_i` is incremented and `r_i` decremented by `w(b)`. -/
noncomputable def nonMarginals (A : AllocProblem n J) : AllocProblem n J where
  p := A.p
  B := fun j => (A.B j).filter (fun b => IsMarginalBid b A.p)
  m := fun j => A.m j + nmBundle ((A.B j).filter (fun b => ¬ IsMarginalBid b A.p)) A.p
  r := A.r - ∑ j, nmBundle ((A.B j).filter (fun b => ¬ IsMarginalBid b A.p)) A.p

/-! ### UnambiguousMarginals (Algorithm 4, p. 20) -/

open scoped Classical in
/-- `Bʲ_I`: the bids of bidder `j` marginal on goods in `I` (p. 19). -/
noncomputable def marginalOn (A : AllocProblem n J) (I : Finset (Fin (n + 1))) (j : J) :
    List (Bid n) :=
  (A.B j).filter (fun b => IsMarginalBid b A.p ∧ ∃ i ∈ I, i ∈ demGoods b A.p)

open scoped Classical in
/-- The bundle Algorithm 4 moves from `r` to `mʲ`: with no link good in `I`, `r_i` for every
`i ∈ I`; with link good `i*` (chosen among the link goods of `I`), `d = Σ_{b ∈ Bʲ_I} w(b) −
Σ_{i ∈ I∖{i*}} r_i` units of `i*` and `r_i` units of every `i ∈ I ∖ {i*}`. -/
noncomputable def unambiguousTransfer (A : AllocProblem n J) (I : Finset (Fin (n + 1))) (j : J) :
    Fin (n + 1) → ℤ :=
  if h : ∃ i ∈ I, IsLink A i then
    fun i => if i = h.choose then
        ((marginalOn A I j).map Bid.w).sum - ∑ i' ∈ I.erase h.choose, A.r i'
      else if i ∈ I then A.r i else 0
  else fun i => if i ∈ I then A.r i else 0

open scoped Classical in
/-- Algorithm 4 (UnambiguousMarginals) on the demand cluster `(I, j)`: transfer as above from `r`
to `mʲ`, and remove all bids marginal on `I` from `Bʲ`. -/
noncomputable def unambiguousMarginals (A : AllocProblem n J) (I : Finset (Fin (n + 1))) (j : J) :
    AllocProblem n J where
  p := A.p
  B := Function.update A.B j
    ((A.B j).filter (fun b => ¬ (IsMarginalBid b A.p ∧ ∃ i ∈ I, i ∈ demGoods b A.p)))
  m := Function.update A.m j (A.m j + unambiguousTransfer A I j)
  r := A.r - unambiguousTransfer A I j

/-! ### Shift, projection, Lyapunov function, SFM (pp. 13, 21–22, 38) -/

/-- Add `c · e^i` to a bid vector. -/
def shiftBid (i : Fin (n + 1)) (c : ℝ) (b : Bid n) : Bid n :=
  ⟨b.v + Pi.single i c, b.w⟩

/-- Replace bidder `jstar`'s list by `{b + c e^i | b ∈ B^{jstar}}`; other lists unchanged. -/
def shiftList (B : J → List (Bid n)) (jstar : J) (i : Fin (n + 1)) (c : ℝ) : J → List (Bid n) :=
  fun j => if j = jstar then (B j).map (shiftBid i c) else B j

open scoped Classical in
/-- The projection of `b` w.r.t. `p` (p. 21): with `I` the goods `b` demands at `p`,
`b' = b − e^{[n]₀∖I}` if `0 ∈ I`, and `b' = b + e^I` otherwise. -/
noncomputable def project (b : Bid n) (p : Fin n → ℝ) : Bid n :=
  if (0 : Fin (n + 1)) ∈ demGoods b p then
    ⟨b.v - fun k => if k ∈ demGoods b p then 0 else 1, b.w⟩
  else
    ⟨b.v + fun k => if k ∈ demGoods b p then 1 else 0, b.w⟩

/-- The Lyapunov function (5), p. 13, for the bid list `B` and residual `r`:
`g(q) = f_B(q) + Σ_{i ∈ [n]} r_i q_i` (the reject coordinate has price `0`). -/
noncomputable def gLyap (B : List (Bid n)) (r : Fin (n + 1) → ℤ) (q : Fin n → ℝ) : ℝ :=
  fB B q + ∑ i, (r i.succ : ℝ) * q i

/-- The indicator vector `e^S ∈ ℝⁿ` of `S ⊆ [n]`. -/
def indicator (S : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ S then 1 else 0

/-- `h⁺(S) = g(p + ε e^S) − g(p)` (proof of Proposition 14, p. 38). -/
noncomputable def hPlus (B : List (Bid n)) (r : Fin (n + 1) → ℤ) (p : Fin n → ℝ) (ε : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  gLyap B r (p + ε • indicator S) - gLyap B r p

/-- `h⁻(S) = g(p − ε e^S) − g(p)` (proof of Proposition 14, p. 38, where the page prints `+`). -/
noncomputable def hMinus (B : List (Bid n)) (r : Fin (n + 1) → ℤ) (p : Fin n → ℝ) (ε : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  gLyap B r (p - ε • indicator S) - gLyap B r p

/-- An SFM oracle: returns a subset of `[n]` for every set function. -/
abbrev SFMOracle (n : ℕ) := (Finset (Fin n) → ℝ) → Finset (Fin n)

/-- The oracle minimises every submodular set function (the black box of cost `T(n)`); nothing is
required on other inputs. -/
def SfmAdmissible (sfm : SFMOracle n) : Prop :=
  ∀ h : Finset (Fin n) → ℝ, NonmonotoneSubmod.Shared.Submodular h → ∀ S, h (sfm h) ≤ h S

/-- The shift step `ε = 1/10` of Algorithm 5. -/
noncomputable def spuEps : ℝ := 1 / 10

/-- Line 3 of Algorithm 5: the aggregate list after adding `(1/10) e^{i*}` to `j*`'s bids. -/
noncomputable def spuShifted (A : AllocProblem n J) (istar : Fin (n + 1)) (jstar : J) :
    List (Bid n) :=
  aggregate (shiftList A.B jstar istar spuEps)

/-- The two set functions minimised by SFM in line 3 of Algorithm 5. -/
noncomputable def spuHPlus (A : AllocProblem n J) (istar : Fin (n + 1)) (jstar : J) :
    Finset (Fin n) → ℝ :=
  hPlus (spuShifted A istar jstar) A.r A.p spuEps

noncomputable def spuHMinus (A : AllocProblem n J) (istar : Fin (n + 1)) (jstar : J) :
    Finset (Fin n) → ℝ :=
  hMinus (spuShifted A istar jstar) A.r A.p spuEps

/-- Line 3 of Algorithm 5: `p^ε`, the better (smaller `g`) of `p + (1/10) e^{S⁺}` and
`p − (1/10) e^{S⁻}`, with `S^±` returned by the oracle on `h^±` (proof of Prop. 14, p. 38). -/
noncomputable def pEps (sfm : SFMOracle n) (A : AllocProblem n J) (istar : Fin (n + 1))
    (jstar : J) : Fin n → ℝ :=
  let g := gLyap (spuShifted A istar jstar) A.r
  let qp := A.p + spuEps • indicator (sfm (spuHPlus A istar jstar))
  let qm := A.p - spuEps • indicator (sfm (spuHMinus A istar jstar))
  if g qp ≤ g qm then qp else qm

/-- Both SFM calls of this ShiftProjectUnshift step are on submodular set functions. -/
def SfmCallsGenuine (A : AllocProblem n J) (istar : Fin (n + 1)) (jstar : J) : Prop :=
  NonmonotoneSubmod.Shared.Submodular (spuHPlus A istar jstar) ∧
    NonmonotoneSubmod.Shared.Submodular (spuHMinus A istar jstar)

/-- Algorithm 5 (ShiftProjectUnshift) with cycle-link good `istar` and edge label `jstar`: shift
`j*`'s bids by `(1/10) e^{i*}`, compute `p^ε`, project every bid list w.r.t. `p^ε`, subtract
`(1/10) e^{i*}` from `j*`'s bids and keep the price `p` (and `m`, `r`). -/
noncomputable def shiftProjectUnshift (sfm : SFMOracle n) (A : AllocProblem n J)
    (istar : Fin (n + 1)) (jstar : J) : AllocProblem n J where
  p := A.p
  B := shiftList
    (fun j => (shiftList A.B jstar istar spuEps j).map (fun b => project b (pEps sfm A istar jstar)))
    jstar istar (-spuEps)
  m := A.m
  r := A.r

/-! ### The run of Allocate (Algorithm 1, p. 14) -/

/-- The initial allocation problem (p. 16) for integral bid lists `B`, integral price `p` and
target `t`: partial allocations `0` and residual supply `t`, with `t₀ = Σ w(b) − Σ_{i ∈ [n]} tᵢ`. -/
noncomputable def initial (B : J → List (IntBid n)) (p t : Fin n → ℤ) : AllocProblem n J where
  p := fun i => (p i : ℝ)
  B := fun j => (B j).map IntBid.toBid
  m := 0
  r := Fin.cons ((∑ j, ((B j).map IntBid.w).sum) - ∑ i, t i) t

open scoped Classical in
/-- One iteration of the while loop of Algorithm 1 (lines 5–10): if some bid list is non-empty,
call the selector, apply UnambiguousMarginals or ShiftProjectUnshift accordingly, then
NonMarginals; once every list is empty the problem is left unchanged. -/
noncomputable def step (sel : Selector n J) (sfm : SFMOracle n) (A : AllocProblem n J) :
    AllocProblem n J :=
  if ∀ j, A.B j = [] then A else
    nonMarginals
      (match sel A with
        | .cluster I j => unambiguousMarginals A I j
        | .shift istar jstar => shiftProjectUnshift sfm A istar jstar)

/-- The state of Algorithm 1 after line 3 (`run 0`) and after `k` iterations of the loop. -/
noncomputable def run (sel : Selector n J) (sfm : SFMOracle n) (A₀ : AllocProblem n J) :
    ℕ → AllocProblem n J
  | 0 => nonMarginals A₀
  | k + 1 => step sel sfm (run sel sfm A₀ k)

/-- The loop iteration from `A` makes only genuine SFM calls: if it runs and the selector picks
ShiftProjectUnshift, both set functions passed to the oracle are submodular. -/
def StepGenuine (sel : Selector n J) (A : AllocProblem n J) : Prop :=
  (∃ j, A.B j ≠ []) →
    match sel A with
    | .cluster _ _ => True
    | .shift istar jstar => SfmCallsGenuine A istar jstar

end ProductMixAuction.Allocate


