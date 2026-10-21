-- Prove2me | Definitions.Def_RainbowEFX_Sublinear_Setting
-- name    : RainbowEFX_Sublinear_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:11.56799+00:00
-- url     : https://prove2.me/theorems/a82a57c4-6ef6-4c78-aa8a-135d36c984ac
-- title:
--   pp. 3–4, 9–15 — (1 − ε)-EFX, heavy/strong envy, most envious agents, strong Pareto domination, (*), valuable goods, H_X/L_X, group champion graph, rainbow cycles, R(d)
-- statement:
--   This file fixes the vocabulary of the paper. Agents are $[n]$, goods are $M=\{1,\dots,m\}$, valuations $v_i:2^M\to\mathbb R$ (additivity is a separate hypothesis, `IsAdditive`), and an allocation is $X=\langle X_1,\dots,X_n\rangle$. The envy graph $E_X$ (an edge $i\to j$ when $v_i(X_i)<v_i(X_j)$), its sources, reachability, acyclicity and the pool $P$ of unallocated goods are taken from the published `LittleCharity.EFX.Setting`. Fix $0<\varepsilon<1$.
--
--   1. **$\alpha$-EFX** (p. 3). $X$ is $\alpha$-EFX if $\alpha\cdot v_i(X_j\setminus\{g\})\le v_i(X_i)$ for all agents $i,j$ and all $g\in X_j$.
--   2. **Envy notions** (p. 10). Agent $i$ *heavily envies* a set $S$ if $v_i(X_i)<(1-\varepsilon)v_i(S)$, and *strongly envies* $S$ if it heavily envies a proper subset of $S$. A pair $(t,Z)$ is a *most-envious-agent-witness pair* for $S$ if $Z\subseteq S$, $t$ heavily envies $Z$, and no agent strongly envies $Z$; $t$ is then a *most envious agent* for $S$.
--   3. **Strong Pareto domination** (p. 10). $X'>_{PD}X$ if $v_i(X'_i)\ge v_i(X_i)$ for all $i$ and $(1-\varepsilon)\,v_{i'}(X'_{i'})>v_{i'}(X_{i'})$ for some agent $i'$.
--   4. **Update rules and assumption (\*)** (pp. 11–12). Rule U1 applies if there are a source $s$ of $E_X$ and an unallocated good $g$ such that no agent strongly envies $X_s\cup\{g\}$; rule U2 applies if some agent heavily envies $P$. Assumption (\*) says: $E_X$ is acyclic and neither U1 nor U2 applies.
--   5. **Valuable goods, $H_X$, $L_X$** (p. 12). A good $g$ is *valuable* to $i$ if $v_i(\{g\})>\varepsilon\,v_i(X_i)$; $Q_g$ is the set of agents to whom $g$ is valuable. For an integer $d$, $H_X=\{g\in P: |Q_g|\ge d+1\}$ (high-demand goods) and $L_X=\{g\in P:|Q_g|\le d\}$ (low-demand goods).
--   6. **Group champion graph** (pp. 12–13). A source assignment $s(\cdot)$ maps each agent $a$ to a source $s(a)$ of $E_X$ from which $a$ is reachable. The vertices are the pairs $(g,s(a))$ with $g\in L_X$ and $a\in Q_g$; the part of $(g,s(a))$ is $V_g$. There is an edge from $(g,s(a))$ to $(h,s(b))$ (with $a\in Q_g$, $b\in Q_h$) iff $a$ is a most envious agent (the *champion*) for $X_{s(b)}\cup\{g\}$.
--   7. **Rainbow cycles and $R(d)$** (Definition 2, p. 4). For a digraph whose vertices are labelled by parts, a *rainbow cycle* is a directed cycle of length at least $2$ that visits each part at most once. The *in-edge property* says every vertex has an incoming edge from every part other than its own. $R(d)$ is the largest $k$ such that some digraph with $k$ parts, each of size between $1$ and $d$, has the in-edge property and no rainbow cycle.
--   8. **Representative sets** (p. 15). For a set $D$ of vectors in $\{0,1\}^r$, $B\subseteq D$ is a representative set of $D$ if $\{\ell : a[\ell]=1\text{ for some }a\in D\}=\{\ell: b[\ell]=1\text{ for some }b\in B\}$.
--
--   These are the objects in terms of which the paper reduces the number of unallocated goods in a $(1-\varepsilon)$-EFX allocation to an upper bound on $R(d)$.
--
--   **Formalization Note** Agents are `Fin n` and goods `Fin m` (0-indexed). Three choices differ from the printed text, and each is needed for the paper's later statements to hold. (i) In $>_{PD}$ the page prints the non-strict $(1-\varepsilon)v_{i'}(X'_{i'})\ge v_{i'}(X_{i'})$. That holds at $0=0$ with no improvement, so the strict inequality is used here: it is what the update rules U2 and U3 deliver and what the termination argument on p. 15 relies on. (ii) The "champion" of p. 11 is the output of one run of Observation 7's procedure; here it is read relationally as *any* most envious agent, so statements about champions are stated for every most envious agent. (iii) In Definition 2 every part is required to be nonempty: with empty parts allowed, conditions 1–3 hold for every $k$ and $R(d)$ would be infinite. Cycles are maps $c:\mathrm{Fin}\,r\to V$ with $r\ge 2$, `part ∘ c` injective, and an edge from $c(i)$ to $c(i+1 \bmod r)$; edges inside a part are allowed in the encoding but can never lie on a rainbow cycle. $R(d)$ is `sSup` of a set of naturals, which is $0$ if the set is unbounded; statements about $R(d)$ therefore also assert that the set is bounded above. Group-champion-graph vertices are pairs in `Fin m × Fin n`, and an edge records its witnesses $a\in Q_g$, $b\in Q_h$.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, pp. 3–4, 9–15, Definition 2, §3, §4, §5

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_LittleCharity_MMS_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

/-- p. 3, Approximate-EFX: `X` is `α`-EFX if for every pair of agents `i, j` and every good
`g ∈ X j`, `α · v_i(X_j \ {g}) ≤ v_i(X_i)`. The mission uses `α = 1 − ε`. -/
def IsAlphaEFX {n m : ℕ} (α : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) : Prop :=
  ∀ i j, ∀ g ∈ X j, α * v i ((X j).erase g) ≤ v i (X i)

/-- p. 10: agent `i` heavily envies the set `S` if `v_i(X_i) < (1 − ε) v_i(S)`. -/
def HeavilyEnvies {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (i : Fin n) (S : Finset (Fin m)) : Prop :=
  v i (X i) < (1 - ε) * v i S

/-- p. 10: agent `i` strongly envies `S` if it heavily envies a proper subset of `S`. -/
def StronglyEnvies {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (i : Fin n) (S : Finset (Fin m)) : Prop :=
  ∃ T, T ⊂ S ∧ HeavilyEnvies ε v X i T

/-- p. 10: `(t, Z)` is a most-envious-agent-witness pair for `S`: `Z ⊆ S`, `t` heavily envies
`Z`, and no agent strongly envies `Z`. -/
def IsMEAWitnessPair {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (S : Finset (Fin m)) (t : Fin n) (Z : Finset (Fin m)) : Prop :=
  Z ⊆ S ∧ HeavilyEnvies ε v X t Z ∧ ∀ i, ¬ StronglyEnvies ε v X i Z

/-- p. 10: `t` is a most envious agent for `S` if some `Z ⊆ S` makes `(t, Z)` a
most-envious-agent-witness pair. The paper's "champion" (p. 11) is used relationally: every
statement about a champion is stated for every most envious agent. -/
def IsMostEnviousAgent {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (S : Finset (Fin m)) (t : Fin n) : Prop :=
  ∃ Z, IsMEAWitnessPair ε v X S t Z

/-- p. 10: `X'` strongly Pareto-dominates `X` (`X' >_PD X`): nobody is worse off, and some
agent `i'` improves by the factor `1 − ε`. The page prints `(1 − ε) v_{i'}(X'_{i'}) ≥ v_{i'}(X_{i'})`;
the inequality is taken strict here (it holds at `0 = 0` otherwise, with no improvement), which
is what the update rules deliver and the termination argument (p. 15) uses. -/
def StronglyParetoDominates {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X' X : Fin n → Finset (Fin m)) : Prop :=
  (∀ i, v i (X i) ≤ v i (X' i)) ∧ ∃ i', v i' (X i') < (1 - ε) * v i' (X' i')

/-- Lemma 8, p. 11: rule U1 applies if some source `s` of the envy graph and some unallocated
good `g` are such that no agent strongly envies `X_s ∪ {g}`. -/
def U1Applicable {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) : Prop :=
  ∃ s, IsSource v X s ∧ ∃ g ∈ pool X, ∀ i, ¬ StronglyEnvies ε v X i (insert g (X s))

/-- Lemma 9, p. 11: rule U2 applies if some agent heavily envies the pool `P` of unallocated
goods. -/
def U2Applicable {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) : Prop :=
  ∃ i, HeavilyEnvies ε v X i (pool X)

/-- Assumption (*), p. 12: the envy graph `E_X` is acyclic and neither U1 nor U2 applies. -/
def Star {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) : Prop :=
  EnvyAcyclic v X ∧ ¬ U1Applicable ε v X ∧ ¬ U2Applicable ε v X

/-- p. 12: good `g` is valuable to agent `i` if `v_i(g) > ε · v_i(X_i)`. (Membership of `g` in
the pool is not part of this predicate; `HX`, `LX` filter the pool.) -/
def Valuable {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (g : Fin m) (i : Fin n) : Prop :=
  ε * v i (X i) < v i {g}

open Classical in
/-- The agents to whom `g` is valuable (`Q_g`, p. 12). -/
noncomputable def valuableAgents {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (g : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Valuable ε v X g i)

open Classical in
/-- p. 12: high-demand goods `H_X`: unallocated goods valuable to at least `d + 1` agents. -/
noncomputable def HX {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (d : ℕ) : Finset (Fin m) :=
  (pool X).filter (fun g => d < (valuableAgents ε v X g).card)

open Classical in
/-- p. 12: low-demand goods `L_X`: unallocated goods valuable to at most `d` agents. -/
noncomputable def LX {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (d : ℕ) : Finset (Fin m) :=
  (pool X).filter (fun g => (valuableAgents ε v X g).card ≤ d)

/-- p. 12: a source assignment `s(·)`: each agent `a` is reachable in `E_X` from the source
`src a`. -/
def IsSourceAssignment {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (src : Fin n → Fin n) : Prop :=
  ∀ a, IsSource v X (src a) ∧ Reach v X (src a) a

/-- pp. 12–13: the vertices of the group champion graph `G`. A vertex is a pair `(g, s(a))`
with `g ∈ L_X` and `a ∈ Q_g`; its part is its first coordinate `g`. -/
def GCVertex {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (d : ℕ) (src : Fin n → Fin n) (p : Fin m × Fin n) : Prop :=
  p.1 ∈ LX ε v X d ∧ ∃ a, Valuable ε v X p.1 a ∧ src a = p.2

/-- p. 13: the edges of the group champion graph: for goods `g, h` and agents `a ∈ Q_g`,
`b ∈ Q_h`, an edge from `(g, s(a))` to `(h, s(b))` iff `a` is the champion (a most envious
agent) of `X_{s(b)} ∪ {g}`. -/
def GCAdj {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (src : Fin n → Fin n) (p q : Fin m × Fin n) : Prop :=
  ∃ a b, Valuable ε v X p.1 a ∧ Valuable ε v X q.1 b ∧ src a = p.2 ∧ src b = q.2 ∧
    IsMostEnviousAgent ε v X (insert p.1 (X q.2)) a

/-- Definition 2 / Theorem 3: a cycle `c 0 → c 1 → ⋯ → c (r-1) → c 0` of length `r ≥ 2` that
visits each part at most once (`part ∘ c` injective). -/
def IsRainbowCycle {ι V : Type} (part : V → ι) (adj : V → V → Prop) {r : ℕ}
    (c : Fin r → V) : Prop :=
  2 ≤ r ∧ Function.Injective (part ∘ c) ∧ ∀ i, adj (c i) (c (finRotate r i))

/-- Definition 2 (2) / Theorem 3: every vertex `w` has, from every part other than its own, an
incoming edge. -/
def InEdgeProperty {ι V : Type} (part : V → ι) (adj : V → V → Prop) : Prop :=
  ∀ w : V, ∀ i : ι, i ≠ part w → ∃ u, part u = i ∧ adj u w

/-- Definition 2: there is a directed `k`-partite graph with parts `V_1, …, V_k` of sizes
`1 ≤ |V_i| ≤ d` (vertices `Σ i, Fin (a i)`), in which every vertex has an incoming edge from
every other part, and with no cycle visiting each part at most once. -/
def RainbowFree (d k : ℕ) : Prop :=
  ∃ (a : Fin k → ℕ) (adj : (Σ i, Fin (a i)) → (Σ i, Fin (a i)) → Prop),
    (∀ i, 1 ≤ a i ∧ a i ≤ d) ∧ InEdgeProperty Sigma.fst adj ∧
    ∀ (r : ℕ) (c : Fin r → Σ i, Fin (a i)), ¬ IsRainbowCycle Sigma.fst adj c

/-- Definition 2, p. 4: the rainbow cycle number `R(d)`, the largest `k` admitting a
rainbow-cycle-free `k`-partite graph. (`sSup` in `ℕ`; statements about it also assert that the
set is bounded above.) -/
noncomputable def rainbowCycleNumber (d : ℕ) : ℕ :=
  sSup {k | RainbowFree d k}

/-- p. 15: `B` is a representative set of a set `D` of `r`-dimensional Boolean vectors:
`B ⊆ D` and `{ℓ | a[ℓ] = 1 for some a ∈ D} = {ℓ | b[ℓ] = 1 for some b ∈ B}`. -/
def IsRepresentativeSet {r : ℕ} (D B : Finset (Fin r → Bool)) : Prop :=
  B ⊆ D ∧ {ℓ | ∃ a ∈ D, a ℓ = true} = {ℓ | ∃ b ∈ B, b ℓ = true}

end RainbowEFX.Sublinear


