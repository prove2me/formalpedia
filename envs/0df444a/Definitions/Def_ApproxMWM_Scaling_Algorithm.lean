-- Prove2me | Definitions.Def_ApproxMWM_Scaling_Algorithm
-- name    : ApproxMWM_Scaling_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:06:20.983562+00:00
-- url     : https://prove2.me/theorems/00b921da-e26c-407c-8952-a21ffb950e2d
-- title:
--   The scaling algorithm of Figure 2, parametrized by the eligibility rule (Definitions 3.2 and 3.10)
-- statement:
--   This file encodes the scaling algorithm of Figure 2 as a nondeterministic transition system. A **state** consists of a matching $M$, a set $\Omega$ of blossoms with edge sets $E_B$, duals $y$ on vertices and $z$ on vertex sets, a record $\mathrm{entered}(e)$ of the scale in which $e$ last entered $M\cup\bigcup_{B\in\Omega}E_B$ (the "type" of Property 3.1(4)), and the common $y$-value $y_{\mathrm{free}}$ of the free vertices.
--
--   **Eligibility.** At scale $i$, an edge $e$ of $G$ is eligible under Definition 3.2 if (i) $e\in E_B$ for some $B\in\Omega$, or (ii) $e\notin M$ and $yz(e)=w_i(e)-\delta_i$, or (iii) $e\in M$ and $yz(e)-w_i(e)$ is a nonnegative integer multiple of $\delta_i$. Definition 3.10 adds $\mathrm{scale}(e)\ge i-\gamma$ to (ii) and (iii). $G_{\mathrm{elig}}=(V,E_{\mathrm{elig}})/\Omega$ contracts each root blossom to a vertex. Alternating paths in $G_{\mathrm{elig}}$ are given by the $G$-edges they use and visit no contracted vertex twice; augmenting paths join free vertices.
--
--   **One iteration of scale $i$:**
--
--   1. *Augmentation.* Choose a maximal set $\Psi$ of vertex-disjoint augmenting paths in $G_{\mathrm{elig}}$ (every augmenting path of $G_{\mathrm{elig}}$ meets one of them), lift each through the blossoms to an augmenting path of $G$ using edges of $E_B$ inside each blossom, and set $M\leftarrow M\oplus\bigcup_{P\in\Psi}P$.
--   2. *Blossom Shrinking.* Let $V_{\mathrm{out}}$ ($V_{\mathrm{in}}$) be the contracted vertices reachable from free vertices by even-length (only by odd-length) alternating paths. Add a set $\Omega'$ of new full blossoms on $V_{\mathrm{out}}$, formed by eligible edges, which is maximal: every eligible unmatched edge of $G_{\mathrm{elig}}$ with both ends in $V_{\mathrm{out}}$ has both ends in a common new blossom. Set $z(B)=0$ for $B\in\Omega'$.
--   3. *Dual Adjustment.* $y(u)\mathrel{-}=\delta_i/2$ on $\hat V_{\mathrm{out}}$, $y(u)\mathrel{+}=\delta_i/2$ on $\hat V_{\mathrm{in}}$, $z(B)\mathrel{+}=\delta_i$ for root blossoms $B\subseteq\hat V_{\mathrm{out}}$, $z(B)\mathrel{-}=\delta_i$ for root blossoms $B\subseteq\hat V_{\mathrm{in}}$.
--   4. *Blossom Dissolution.* Remove root blossoms with zero $z$-value as long as they exist.
--
--   The run starts from $M=\emptyset$, $\Omega=\emptyset$, $z=0$, $y\equiv N/2-\delta_0/2$. Scale $i$ repeats iterations while the free vertices' $y$-value exceeds the end-of-scale value; between scales every $y(u)$ increases by $\delta_{i+1}$. After scale $L$ the algorithm returns $M$. `Returns P G elig M` says that some terminating run returns $M$; `Reach P G elig i s` says that $s$ occurs in some run at scale $i$, at the start of the scale or between two iterations.
--
--   **Formalization Note** The algorithm is a relation, not a function: the maximal sets $\Psi$ and $\Omega'$ and the lifts are choices, and every statement about the algorithm quantifies over all runs. The loop test uses the explicit counter $y_{\mathrm{free}}$, which is decreased by $\delta_i/2$ in every Dual Adjustment and increased by $\delta_{i+1}$ between scales; when free vertices exist it equals their common $y$-value. $V_{\mathrm{out}}$ and $V_{\mathrm{in}}$ are computed in $G_{\mathrm{elig}}$ after augmentation and before shrinking, as in the order of step (2). The record $\mathrm{entered}$ is ghost state that no choice of the algorithm reads.
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, p. 1:13 Definition 3.2, p. 1:14 Figure 2 (The scaling algorithm), p. 1:17 (Section 3.3: the algorithm unchanged with a new eligibility), p. 1:18 Definition 3.10; Lemma 2.1(2), p. 1:10, for the lift of augmenting paths

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Matching
import Definitions.Def_ApproxMWM_Scaling_Params

namespace ApproxMWM.Scaling

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The state of the scaling algorithm of Figure 2 (p. 1:14): the matching `M`, the blossom set
`Ω` (vertex sets) with the blossom edge sets `EB B = E_B`, the duals `y` on vertices and `z` on
vertex sets, the ghost record `entered e` = the scale `j` in which `e` last entered
`M ∪ ⋃_{B ∈ Ω} E_B` (so `e` is "type `j`", Property 3.1(4)), and the common `y`-value `yfree` of the
free vertices, which drives the loop test of Figure 2. The algorithm's choices never read
`entered`. -/
structure State (V : Type*) where
  M : Finset (Sym2 V)
  Ω : Finset (Finset V)
  EB : Finset V → Finset (Sym2 V)
  y : V → ℝ
  z : Finset V → ℝ
  entered : Sym2 V → ℕ
  yfree : ℝ

/-- An eligibility rule: `elig i s e` says that edge `e` is eligible at scale `i` in state `s`. -/
abbrev EligRule (V : Type*) := ℕ → State V → Sym2 V → Prop

/-- Eligibility of Definition 3.2 (p. 1:13). `e` is an edge of `G` and (i) `e ∈ E_B` for some
`B ∈ Ω`, or (ii) `e ∉ M` and `yz(e) = w_i(e) - δ_i`, or (iii) `e ∈ M` and `yz(e) - w_i(e)` is a
nonnegative integer multiple of `δ_i`. -/
def elig32 (P : Params) (G : SimpleGraph V) (w : Sym2 V → ℕ) : EligRule V := fun i s e =>
  e ∈ G.edgeSet ∧
    ((∃ B ∈ s.Ω, e ∈ s.EB B) ∨
      (e ∉ s.M ∧ yz s.y s.z e = truncW P w i e - P.δ i) ∨
      (e ∈ s.M ∧ ∃ k : ℕ, yz s.y s.z e - truncW P w i e = k * P.δ i))

/-- Eligibility of Definition 3.10 (p. 1:18): Definition 3.2 with the extra condition
`scale(e) ≥ i - γ` (written `i ≤ scale(e) + γ`, `γ = g = log ε'⁻¹`) in criteria (2) and (3). -/
def elig310 (P : Params) (G : SimpleGraph V) (w : Sym2 V → ℕ) : EligRule V := fun i s e =>
  e ∈ G.edgeSet ∧
    ((∃ B ∈ s.Ω, e ∈ s.EB B) ∨
      (e ∉ s.M ∧ yz s.y s.z e = truncW P w i e - P.δ i ∧ i ≤ scaleOf P w e + P.g) ∨
      (e ∈ s.M ∧ (∃ k : ℕ, yz s.y s.z e - truncW P w i e = k * P.δ i) ∧
        i ≤ scaleOf P w e + P.g))

open Classical in
/-- The vertex of the contracted graph `G/Ω` representing `v`: the root blossom of `Ω` containing
`v`, or `{v}` if `v` lies in no blossom. -/
noncomputable def node (Ω : Finset (Finset V)) (v : V) : Finset V :=
  if h : ∃ B, IsRoot Ω B ∧ v ∈ B then h.choose else {v}

/-- The contracted-graph vertices visited by a contracted path that starts at the vertex of `r`
and uses the `G`-edges `(a_0,b_0), …, (a_{k-1},b_{k-1})`. -/
noncomputable def pathNodes (Ω : Finset (Finset V)) (r : V) (es : List (V × V)) :
    List (Finset V) :=
  node Ω r :: es.map (fun q => node Ω q.2)

/-- The last contracted vertex of such a path. -/
noncomputable def endNode (Ω : Finset (Finset V)) (r : V) (es : List (V × V)) : Finset V :=
  (pathNodes Ω r es).getLast (by simp [pathNodes])

/-- An alternating path of `G_elig = (V, E_elig)/Ω` (p. 1:13) starting at the vertex of `G/Ω`
representing `r`, given by the `G`-edges `(a_j, b_j)` it uses: each is eligible (`E`) and joins
two different contracted vertices, consecutive edges meet in a common contracted vertex and
alternate between `M` and `E \ M`, and no contracted vertex is visited twice. -/
def IsAltPathC (Ω : Finset (Finset V)) (E : Sym2 V → Prop) (M : Finset (Sym2 V)) (r : V)
    (es : List (V × V)) : Prop :=
  (∀ q ∈ es, E s(q.1, q.2) ∧ node Ω q.1 ≠ node Ω q.2) ∧
  (∀ q ∈ es.head?, node Ω q.1 = node Ω r) ∧
  es.IsChain (fun q q' => node Ω q.2 = node Ω q'.1 ∧ (s(q.1, q.2) ∈ M ↔ s(q'.1, q'.2) ∉ M)) ∧
  (pathNodes Ω r es).Nodup

/-- An alternating path of `G_elig` from a free vertex `r` (its first edge, if any, is
unmatched). -/
def IsAltPathFromFree (Ω : Finset (Finset V)) (E : Sym2 V → Prop) (M : Finset (Sym2 V)) (r : V)
    (es : List (V × V)) : Prop :=
  IsFree M r ∧ IsAltPathC Ω E M r es ∧ ∀ q ∈ es.head?, s(q.1, q.2) ∉ M

/-- An augmenting path of `G_elig`: a nonempty alternating path between free vertices. -/
def IsAugPathC (Ω : Finset (Finset V)) (E : Sym2 V → Prop) (M : Finset (Sym2 V)) (r : V)
    (es : List (V × V)) : Prop :=
  IsAltPathFromFree Ω E M r es ∧ es ≠ [] ∧ ∃ t, IsFree M t ∧ node Ω t = endNode Ω r es

/-- `V̂_out`: the original vertices represented by contracted vertices reachable from free
vertices by even-length alternating paths of `G_elig` (Figure 2, steps (2)–(3)). -/
def VoutHat (Ω : Finset (Finset V)) (E : Sym2 V → Prop) (M : Finset (Sym2 V)) : Set V :=
  {v | ∃ r es, IsAltPathFromFree Ω E M r es ∧ Even es.length ∧ endNode Ω r es = node Ω v}

/-- `V̂_in`: the original vertices represented by contracted vertices outside `V_out` that are
reachable from free vertices by odd-length alternating paths of `G_elig`. -/
def VinHat (Ω : Finset (Finset V)) (E : Sym2 V → Prop) (M : Finset (Sym2 V)) : Set V :=
  {v | v ∉ VoutHat Ω E M ∧
    ∃ r es, IsAltPathFromFree Ω E M r es ∧ Odd es.length ∧ endNode Ω r es = node Ω v}

/-- The edges `(p_0,p_1), (p_1,p_2), …` of a vertex sequence. -/
def pathEdges (p : List V) : List (Sym2 V) :=
  List.zipWith (fun a b => s(a, b)) p p.tail

/-- An augmenting path of `G` relative to `M` (p. 1:8): a path of `G` with at least one edge,
whose edges alternate between `M` and `E \ M`, beginning and ending at free vertices. -/
def IsAugPathG (G : SimpleGraph V) (M : Finset (Sym2 V)) (p : List V) : Prop :=
  p.Nodup ∧ p.IsChain G.Adj ∧ (pathEdges p).IsChain (fun e f => (e ∈ M ↔ f ∉ M)) ∧
    2 ≤ p.length ∧ (∀ a ∈ p.head?, IsFree M a) ∧ (∀ b ∈ p.getLast?, IsFree M b)

/-- `p` is the lift through the blossoms (Lemma 2.1(2), p. 1:10) of the contracted path with
`G`-edges `es`: every edge of `p` is one of the edges of `es` or an edge of `E_B` for the root
blossom `B` containing both of its endpoints, and every edge of `es` is an edge of `p`. -/
def IsLift (Ω : Finset (Finset V)) (EB : Finset V → Finset (Sym2 V)) (es : List (V × V))
    (p : List V) : Prop :=
  (∀ e ∈ pathEdges p, (∃ q ∈ es, e = s(q.1, q.2)) ∨
      ∃ x x', e = s(x, x') ∧ node Ω x = node Ω x' ∧ e ∈ EB (node Ω x)) ∧
  ∀ q ∈ es, s(q.1, q.2) ∈ pathEdges p

/-- The matched and blossom edges `M ∪ ⋃_{B ∈ Ω} E_B` of a state. -/
def State.tight (s : State V) : Finset (Sym2 V) :=
  s.M ∪ blossomEdges s.Ω s.EB

open Classical in
/-- Step (1), Augmentation, of scale `i` (Figure 2), with eligibility `E` of the current state.
`Ψ` is a maximal set of vertex-disjoint augmenting paths of `G_elig` (each given by its free start
`r`, its contracted edges `es`, and its lift `p` to `G`); maximal means every augmenting path of
`G_elig` shares a contracted vertex with a path of `Ψ`. Then `M ← M ⊕ ⋃_{P ∈ Ψ} P` with
`M ⊕ P = (M \ P) ∪ (P \ M)`, and edges that newly enter `M ∪ ⋃ E_B` are recorded as type `i`. -/
noncomputable def Augment (G : SimpleGraph V) (E : Sym2 V → Prop) (i : ℕ) (s s' : State V) :
    Prop :=
  ∃ Ψ : List (V × List (V × V) × List V),
    (∀ π ∈ Ψ, IsAugPathC s.Ω E s.M π.1 π.2.1 ∧ IsLift s.Ω s.EB π.2.1 π.2.2 ∧
        IsAugPathG G s.M π.2.2) ∧
    Ψ.Pairwise (fun π π' => ∀ X ∈ pathNodes s.Ω π.1 π.2.1, X ∉ pathNodes s.Ω π'.1 π'.2.1) ∧
    (∀ r es, IsAugPathC s.Ω E s.M r es →
        ∃ π ∈ Ψ, ∃ X ∈ pathNodes s.Ω r es, X ∈ pathNodes s.Ω π.1 π.2.1) ∧
    s' = { s with
      M := (s.M \ (Ψ.flatMap (fun π => pathEdges π.2.2)).toFinset) ∪
        ((Ψ.flatMap (fun π => pathEdges π.2.2)).toFinset \ s.M)
      entered := fun e =>
        if e ∈ (s.M \ (Ψ.flatMap (fun π => pathEdges π.2.2)).toFinset) ∪
            ((Ψ.flatMap (fun π => pathEdges π.2.2)).toFinset \ s.M) ∧ e ∉ s.tight
        then i else s.entered e }

open Classical in
/-- Step (2), Blossom Shrinking, of scale `i` (Figure 2), with eligibility `E` of the current
state. `Ω'` is a set of new (nested) blossoms on `V_out`: each is formed by the blossom rule from
children that are vertices of the current `G_elig` (`node s.Ω v`) or other new blossoms, joined by
eligible cycle edges, lies inside `V̂_out`, and is full with respect to `M`; `Ω ∪ Ω'` stays
laminar. Maximal: every eligible unmatched edge of `G_elig` with both ends in `V_out` has both
ends in a common new blossom. Then `z(B) ← 0` for `B ∈ Ω'`, `Ω ← Ω ∪ Ω'`, and edges that newly
enter `M ∪ ⋃ E_B` are recorded as type `i`. -/
noncomputable def Shrink (G : SimpleGraph V) (E : Sym2 V → Prop) (i : ℕ) (s s' : State V) :
    Prop :=
  ∃ (Ω' : Finset (Finset V)) (EB' : Finset V → Finset (Sym2 V)),
    Disjoint Ω' s.Ω ∧
    (∀ B ∈ s.Ω, EB' B = s.EB B) ∧
    (∀ B ∈ Ω', (↑B : Set V) ⊆ VoutHat s.Ω E s.M ∧
      IsBlossomOver G E (fun A => (∃ v, A = node s.Ω v) ∨ A ∈ Ω') (childEB (s.Ω ∪ Ω') EB')
        B (EB' B) ∧
      2 * (s.M ∩ EB' B).card + 1 = B.card) ∧
    IsLaminar (s.Ω ∪ Ω') ∧
    (∀ u v, E s(u, v) → s(u, v) ∉ s.M → node s.Ω u ≠ node s.Ω v →
        u ∈ VoutHat s.Ω E s.M → v ∈ VoutHat s.Ω E s.M → ∃ B ∈ Ω', u ∈ B ∧ v ∈ B) ∧
    s' = { s with
      Ω := s.Ω ∪ Ω'
      EB := EB'
      z := fun B => if B ∈ Ω' then 0 else s.z B
      entered := fun e =>
        if e ∈ blossomEdges (s.Ω ∪ Ω') EB' ∧ e ∉ s.tight then i else s.entered e }

open Classical in
/-- Step (3), Dual Adjustment, of a scale with granularity `δ` (Figure 2): `y(u) ← y(u) - δ/2` on
`V̂_out`, `y(u) ← y(u) + δ/2` on `V̂_in`, `z(B) ← z(B) + δ` for root blossoms `B ⊆ V̂_out`,
`z(B) ← z(B) - δ` for root blossoms `B ⊆ V̂_in`; the free vertices (all in `V̂_out`) lose `δ/2`. -/
noncomputable def dualAdjust (δ : ℝ) (Vout Vin : Set V) (s : State V) : State V :=
  { s with
    y := fun u => if u ∈ Vout then s.y u - δ / 2 else if u ∈ Vin then s.y u + δ / 2 else s.y u
    z := fun B =>
      if IsRoot s.Ω B ∧ (↑B : Set V) ⊆ Vout then s.z B + δ
      else if IsRoot s.Ω B ∧ (↑B : Set V) ⊆ Vin then s.z B - δ
      else s.z B
    yfree := s.yfree - δ / 2 }

open Classical in
/-- Step (4), Blossom Dissolution (Figure 2): root blossoms with zero `z`-value are removed from
`Ω` as long as they exist. The result keeps exactly the blossoms that have a member of `Ω`
containing them (themselves included) with nonzero `z`-value. -/
noncomputable def dissolve (s : State V) : State V :=
  { s with Ω := s.Ω.filter (fun B => ∃ B' ∈ s.Ω, B ⊆ B' ∧ s.z B' ≠ 0) }

/-- One iteration of scale `i` (Figure 2): Augmentation, Blossom Shrinking, Dual Adjustment (with
`V̂_out`, `V̂_in` taken in `G_elig` after augmentation, before shrinking) and Blossom Dissolution.
Eligibility is re-evaluated on the current state before each step ("Update `G_elig`"). -/
def Iter (P : Params) (G : SimpleGraph V) (elig : EligRule V) (i : ℕ) (s s' : State V) :
    Prop :=
  ∃ s₁ s₂, Augment G (elig i s) i s s₁ ∧ Shrink G (elig i s₁) i s₁ s₂ ∧
    s' = dissolve (dualAdjust (P.δ i) (VoutHat s₁.Ω (elig i s₁) s₁.M)
      (VinHat s₁.Ω (elig i s₁) s₁.M) s₂)

/-- The initial state (Figure 2): `M = ∅`, `Ω = ∅`, `y(u) = N/2 - δ_0/2` for all `u`, `z = 0`. -/
noncomputable def initState (P : Params) : State V where
  M := ∅
  Ω := ∅
  EB := fun _ => ∅
  y := fun _ => P.N / 2 - P.δ 0 / 2
  z := fun _ => 0
  entered := fun _ => 0
  yfree := P.N / 2 - P.δ 0 / 2

/-- Preparation for scale `i + 1` (Figure 2): `δ_{i+1} = δ_i / 2` and `y(u) ← y(u) + δ_{i+1}` for
all `u`. -/
noncomputable def prepare (P : Params) (i : ℕ) (s : State V) : State V :=
  { s with y := fun u => s.y u + P.δ (i + 1), yfree := s.yfree + P.δ (i + 1) }

/-- A complete execution of scale `i` from state `s` to state `s'`: repeat the four steps while
the free vertices' common `y`-value is above the target of scale `i`, and stop when it has
reached it. -/
inductive ScaleRun (P : Params) (G : SimpleGraph V) (elig : EligRule V) (i : ℕ) :
    State V → State V → Prop
  | stop (s : State V) : s.yfree ≤ P.target i → ScaleRun P G elig i s s
  | step (s s₁ s' : State V) : P.target i < s.yfree → Iter P G elig i s s₁ →
      ScaleRun P G elig i s₁ s' → ScaleRun P G elig i s s'

/-- `RunFrom P G elig i s M`: executing scales `i, …, L` from state `s` (at the start of scale
`i`) terminates and returns the matching `M`. -/
inductive RunFrom (P : Params) (G : SimpleGraph V) (elig : EligRule V) :
    ℕ → State V → Finset (Sym2 V) → Prop
  | last (s s' : State V) : ScaleRun P G elig P.L s s' → RunFrom P G elig P.L s s'.M
  | next (i : ℕ) (s s' : State V) (M : Finset (Sym2 V)) : i < P.L →
      ScaleRun P G elig i s s' → RunFrom P G elig (i + 1) (prepare P i s') M →
      RunFrom P G elig i s M

/-- A terminating run of the algorithm of Figure 2 (scales `0, …, L`) with eligibility rule
`elig` returns the matching `M`. -/
def Returns (P : Params) (G : SimpleGraph V) (elig : EligRule V) (M : Finset (Sym2 V)) :
    Prop :=
  RunFrom P G elig 0 (initState P) M

/-- `Reach P G elig i s`: `s` is a state of some execution of the algorithm at scale `i`, at the
start of the scale or between two iterations (after a Blossom Dissolution step). -/
inductive Reach (P : Params) (G : SimpleGraph V) (elig : EligRule V) :
    ℕ → State V → Prop
  | init : Reach P G elig 0 (initState P)
  | iter (i : ℕ) (s s' : State V) : Reach P G elig i s → P.target i < s.yfree →
      Iter P G elig i s s' → Reach P G elig i s'
  | next (i : ℕ) (s : State V) : Reach P G elig i s → i < P.L → s.yfree ≤ P.target i →
      Reach P G elig (i + 1) (prepare P i s)

end ApproxMWM.Scaling


