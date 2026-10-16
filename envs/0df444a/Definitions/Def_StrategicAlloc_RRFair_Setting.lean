-- Prove2me | Definitions.Def_StrategicAlloc_RRFair_Setting
-- name    : StrategicAlloc_RRFair_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:56:59.884662+00:00
-- url     : https://prove2.me/theorems/8ed4dcc1-19fd-40ff-98a6-9ffb578be74d
-- title:
--   pp. 4–7, 10, 23 — additive valuations, bids, EF/EF1, best response and PNE, Mechanism 1 (Round-Robin) with lexicographic ties, Round-Robin$_\ell$, $M_t(b)$, partial slides, the gap $\varepsilon$
-- statement:
--   The model of §2 and the Round-Robin layer of §3.
--
--   **Instance** (p. 4). There are $n\ge1$ agents $N=[n]$ and $m$ goods $M=\{g_1,\dots,g_m\}$. Agent $i$ has a non-negative value $v_i(g)$ for each good, and her value for a bundle $S\subseteq M$ is additive:
--   $$v_i(S)=\sum_{g\in S}v_i(g).$$
--
--   **Bids** (p. 5). Each agent reports a bid vector $b_i=(b_{i1},\dots,b_{im})$ with $b_{ij}\ge0$; a bid profile is $b=(b_1,\dots,b_n)$, and $(b_i',b_{-i})$ replaces the bid of agent $i$ by $b_i'$. An allocation is a partition $(A_1,\dots,A_n)$ of $M$.
--
--   **Fairness** (Definition 2.1). An allocation is *envy-free* (EF) if $v_i(A_i)\ge v_i(A_j)$ for all $i,j$, and *envy-free up to one good* (EF1) if for all $i,j$ with $A_j\neq\emptyset$ there is $g\in A_j$ with $v_i(A_i)\ge v_i(A_j\setminus\{g\})$. "EF (EF1) from $i$'s perspective" fixes the envying agent $i$ (Lemma 3.1).
--
--   **Equilibria** (Definition 2.7). For a mechanism $\mathcal M$ mapping bid profiles to allocations, $b_i$ is a *best response* to $b_{-i}$ if $v_i(\mathcal M(b_i',b_{-i}))\le v_i(\mathcal M(b))$ for every $b_i'\in\mathbb R^m_{\ge0}$; $b$ is a *pure Nash equilibrium* (PNE) if every $b_i$ is a best response. Fairness and payoffs are measured with the true valuations $v$, while the mechanism reads only the bids.
--
--   **Round-Robin** (Mechanism 1, p. 7). Agents $1,2,\dots,n,1,2,\dots$ take turns; the active agent receives the available good she bids most for, ties broken in favour of the good with the lower index ($g\succ_i h$ iff $b_i(g)>b_i(h)$, or $b_i(g)=b_i(h)$ and $g$ has the lower index). This continues until all goods are allocated ($\lceil m/n\rceil$ rounds, the last one possibly incomplete). More generally, *Round-Robin started at agent $s$ on the goods $G$* runs the same rule on $G$ only, with the turn order $s,s+1,\dots,n,1,\dots,s-1$ repeated; Mechanism 1 is the case $s=1$, $G=M$, and the Round-Robin$_\ell$ of p. 10 is the case $s=\ell$.
--
--   **Available goods** (Definition 3.6). $M_t(b)$ is the set of goods still available right after $t-1$ goods have been allocated.
--
--   **Partial slide** (Definition 3.6). Let $q_1\succ q_2\succ\dots\succ q_m$ be the goods ranked by $\succ$. A ranking $\succ'$ is within a partial slide of $\succ$ if for some $x<y$
--   $$q_1\succ'\dots\succ' q_{x-1}\succ' q_{x+1}\succ'\dots\succ' q_y\succ' q_x\succ' q_{y+1}\succ'\dots\succ' q_m,$$
--   i.e. $\succ'$ is $\succ$ with $q_x$ moved down to just after $q_y$.
--
--   **Gap** (Lemma A.1, p. 23). For a valuation $u$, $\varepsilon(u)=\min\{|u(g)-u(h)|: g,h\in M,\ u(g)\neq u(h)\}$, or $\varepsilon(u)=1$ if all goods have the same value.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Agents are `Fin n` and goods `Fin m`, both 0-based (the paper's agent $i$ is $i-1$, good $g_j$ is $j-1$, and the paper's step $t$ is $t-1$). Valuations and bids are functions `Fin n → Fin m → ℝ`; `val v i S` is the sum over `S`, so additivity holds by construction. `rank c` lists the goods by non-increasing bid with ties in index order (a stable `List.mergeSort` of `List.finRange m`), `top l T` is the first good of `l` in `T`, `agentAt s t` is agent $(s+t) \bmod n$, `allocBefore s G b t` is the set of goods allocated in the first $t$ steps, `pick s G b t` is the good allocated at step $t$, and `rrFrom s G b i` collects agent $i$'s picks over the $|G|$ steps; `roundRobin b = rrFrom 0 univ b`. `avail s G b t` is $M_{t+1}(b)$ in the paper's 1-based indexing. `IsPartialSlide l l'` says that `l'` is `l` with its entry at position $x$ removed and reinserted at position $y$ ($0$-based, $x<y$). `IsBestResponse` quantifies over every non-negative bid vector. `IsAllocation` and `IsEF` are included for the reader; Round-Robin's output is an allocation, which is not assumed anywhere.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, pp. 4–7, 10, 23, §2 (Definitions 2.1, 2.7), Mechanism 1, Definition 3.6, Lemma A.1

import Mathlib

namespace StrategicAlloc.RRFair

variable {n m : ℕ}

/-- Additive valuation (p. 4): the value of agent `i` for a bundle `S` is the sum of her values
for the goods of `S`, `v_i(S) = ∑_{g ∈ S} v_i(g)`. -/
def val (v : Fin n → Fin m → ℝ) (i : Fin n) (S : Finset (Fin m)) : ℝ := ∑ g ∈ S, v i g

/-- A bid profile (p. 5): every agent bids a non-negative value `b_{ij} ≥ 0` for every good. -/
def IsBidProfile (b : Fin n → Fin m → ℝ) : Prop := ∀ i g, 0 ≤ b i g

/-- An allocation (p. 4): pairwise disjoint bundles covering all goods (no free disposal). -/
def IsAllocation (A : Fin n → Finset (Fin m)) : Prop :=
  Pairwise (fun i j => Disjoint (A i) (A j)) ∧ Finset.univ.biUnion A = Finset.univ

/-- Definition 2.1: `A` is envy-free (EF). -/
def IsEF (v : Fin n → Fin m → ℝ) (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ i j, val v i (A j) ≤ val v i (A i)

/-- Definition 2.1: `A` is envy-free up to one good (EF1). -/
def IsEF1 (v : Fin n → Fin m → ℝ) (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ i j, (A j).Nonempty → ∃ g ∈ A j, val v i ((A j).erase g) ≤ val v i (A i)

/-- `A` is EF from agent `i`'s perspective (Lemma 3.1, p. 7). -/
def IsEFFor (v : Fin n → Fin m → ℝ) (A : Fin n → Finset (Fin m)) (i : Fin n) : Prop :=
  ∀ j, val v i (A j) ≤ val v i (A i)

/-- `A` is EF1 from agent `i`'s perspective (Lemma 3.1, p. 7). -/
def IsEF1For (v : Fin n → Fin m → ℝ) (A : Fin n → Finset (Fin m)) (i : Fin n) : Prop :=
  ∀ j, (A j).Nonempty → ∃ g ∈ A j, val v i ((A j).erase g) ≤ val v i (A i)

/-- Definition 2.7: `b_i` is a best response to `b_{-i}` in the mechanism `mech`: no non-negative
bid vector `b'` gives agent `i` a bundle of larger true value `v_i`. -/
def IsBestResponse (mech : (Fin n → Fin m → ℝ) → (Fin n → Finset (Fin m)))
    (v : Fin n → Fin m → ℝ) (b : Fin n → Fin m → ℝ) (i : Fin n) : Prop :=
  ∀ b' : Fin m → ℝ, (∀ g, 0 ≤ b' g) →
    val v i (mech (Function.update b i b') i) ≤ val v i (mech b i)

/-- Definition 2.7: `b` is a pure Nash equilibrium (PNE) of `mech`. -/
def IsPNE (mech : (Fin n → Fin m → ℝ) → (Fin n → Finset (Fin m)))
    (v : Fin n → Fin m → ℝ) (b : Fin n → Fin m → ℝ) : Prop :=
  IsBidProfile b ∧ ∀ i, IsBestResponse mech v b i

/-- The strict ranking `≻` induced by the bid vector `c` (p. 7): goods by non-increasing bid,
equal bids in index order. `List.mergeSort` is stable and `List.finRange m` lists
`g_1, …, g_m` in index order, so ties are broken lexicographically (Mechanism 1, line 4). -/
noncomputable def rank (c : Fin m → ℝ) : List (Fin m) :=
  (List.finRange m).mergeSort (fun g h => decide (c h ≤ c g))

/-- `top l T`: the first good of the list `l` lying in `T`. -/
def top (l : List (Fin m)) (T : Finset (Fin m)) : Option (Fin m) := l.find? (· ∈ T)

/-- The agent moving at step `t` (0-based) when agent `s` moves first: `s, s+1, …, n−1, 0, 1, …`. -/
def agentAt [NeZero n] (s : Fin n) (t : ℕ) : Fin n :=
  ⟨(s.val + t) % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- The goods of `G` allocated in steps `0, …, t − 1` of Round-Robin started at agent `s`
on the goods `G`. -/
noncomputable def allocBefore [NeZero n] (s : Fin n) (G : Finset (Fin m))
    (b : Fin n → Fin m → ℝ) : ℕ → Finset (Fin m)
  | 0 => ∅
  | t + 1 => match top (rank (b (agentAt s t))) (G \ allocBefore s G b t) with
             | some g => insert g (allocBefore s G b t)
             | none => allocBefore s G b t

/-- The good allocated at step `t` (0-based). -/
noncomputable def pick [NeZero n] (s : Fin n) (G : Finset (Fin m)) (b : Fin n → Fin m → ℝ)
    (t : ℕ) : Option (Fin m) :=
  top (rank (b (agentAt s t))) (G \ allocBefore s G b t)

/-- Round-Robin started at agent `s` on the goods `G`: agent `i`'s bundle consists of the goods
picked at her steps among the first `|G|` steps. -/
noncomputable def rrFrom [NeZero n] (s : Fin n) (G : Finset (Fin m)) (b : Fin n → Fin m → ℝ) :
    Fin n → Finset (Fin m) := fun i =>
  ((Finset.range G.card).filter (fun t => agentAt s t = i)).biUnion
    (fun t => (pick s G b t).toFinset)

/-- Mechanism 1 (Round-Robin): agent 1 (= `0`) picks first, all goods are allocated. -/
noncomputable def roundRobin [NeZero n] (b : Fin n → Fin m → ℝ) : Fin n → Finset (Fin m) :=
  rrFrom 0 Finset.univ b

/-- `M_t(b)` (p. 10), 0-based: the goods of `G` still available after `t` goods have been
allocated (the paper's `M_{t+1}(b)`), for `t = 0, …, |G|`. -/
noncomputable def avail [NeZero n] (s : Fin n) (G : Finset (Fin m)) (b : Fin n → Fin m → ℝ)
    (t : ℕ) : Finset (Fin m) :=
  G \ allocBefore s G b t

/-- Definition 3.6 (partial slide): `l'` is `l` with its `x`-th entry moved to just after its
`y`-th entry, `x < y` (0-based positions). -/
def IsPartialSlide (l l' : List (Fin m)) : Prop :=
  ∃ (x y : ℕ) (hx : x < l.length), x < y ∧ y < l.length ∧
    l' = (l.eraseIdx x).insertIdx y (l[x]'hx)

/-- The smallest positive difference between the values of two goods under `u`
(Lemma A.1, p. 23), or `1` if all goods have the same value. -/
noncomputable def goodGap (u : Fin m → ℝ) : ℝ :=
  let D := ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin m × Fin m => u p.1 ≠ u p.2)).image
    (fun p => |u p.1 - u p.2|)
  if h : D.Nonempty then D.min' h else 1

end StrategicAlloc.RRFair


