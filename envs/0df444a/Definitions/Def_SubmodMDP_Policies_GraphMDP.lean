-- Prove2me | Definitions.Def_SubmodMDP_Policies_GraphMDP
-- name    : SubmodMDP_Policies_GraphMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:22.707207+00:00
-- url     : https://prove2.me/theorems/6383729c-153b-4892-8e85-3a9d6b7362a3
-- title:
--   The decision/chance graph MDP of §3, constraint (7), Algorithm 4 and $\mathrm{MDP}(x)$
-- statement:
--   **Layered MDP graphs (§3).** A layered graph $G=(V,A)$ with $V=V_1\cup\dots\cup V_H$ whose vertices are split into chance vertices $C$ and decision vertices $D$, with $V_1=\{s\}$ for a chance vertex $s$, and transition probabilities $p_c(v)\ge0$ for $c\in C$, where $p_c(v)\neq0$ if and only if $(c,v)$ is an arc and $\sum_v p_c(v)=1$ for $c$ outside the last layer. A randomized policy $\pi$ assigns to every walk $v_1,\dots,v_\ell$ with $v_1=s$ ending in a decision vertex a distribution $\pi_{v_{\le\ell}}$ on vertices, with $\pi_{v_{\le\ell}}(v)=0$ unless $(v_\ell,v)$ is an arc. The process sets $v_1=s$ and draws $v_i$ from $p_{v_{i-1}}$ if $v_{i-1}$ is a chance vertex and from $\pi$ otherwise; $\mathbb E[\mathbf 1^{(r)}_{\mathrm{OPT}}]_I$ is the probability that all vertices of $I$ are visited.
--
--   **Constraint (7).**
--   $$x_{I\cup\{u\}}=x_I\cdot p_c(u)\qquad i\in\{1,\dots,H-1\},\ c\in V_i\cap C,\ u\in V_{i+1},\ \{c\}\subseteq I\subseteq V_1\cup\dots\cup V_i,\ |I|\le r.$$
--
--   **Algorithm 4.** On a trajectory $(v_1,\dots,v_\ell)\in V_1\times\dots\times V_\ell$: let
--   $$K=\{\max\{k\cdot d^j: k\in\mathbb Z_{\ge0},\ k d^j\le\ell\}: j\in\mathbb Z_{\ge0}\}\setminus\{0\},\qquad I=\{v_i:i\in K\};$$
--   if $x_I=0$ return "error", else return the weights $(x_{I\cup\{u\}}/x_I)_{u\in V_{\ell+1}}$.
--
--   **$\mathrm{MDP}(x)$.** Starting from the empty trajectory, repeatedly apply Algorithm 4 to the vertices chosen so far and sample the next vertex from its output; $\mathrm{MDP}(x)$ is the law of the resulting $v_1,\dots,v_H$.
--
--   **Formalization Note** "error" is the value *none*. The repeated process also fails (outcome *none*) if Algorithm 4 returns weights that are not a probability vector, so equality with $\mathrm{RRR}(x)$ includes that this never happens. $\max\{k d^j\le\ell\}$ is computed as $\lfloor \ell/d^j\rfloor d^j$, with exponents $j\le \ell$ (all larger exponents give $0$ when $d\ge2$).
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), §3, pp. 17–19 (PDF pp. 18–20): the graph model, (7), Algorithm 4 and MDP(x)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Layered

namespace SubmodMDP.Policies

noncomputable section

open Classical

/-! # The decision/chance graph model of §3 (PDF pp. 17–19), constraint (7) and Algorithm 4 -/

/-- A layered MDP graph: a layered graph, the chance vertices (the others are decision
vertices), transition probabilities `p c v` out of chance vertices, and the start vertex `s`. -/
structure GMDP where
  G : LGraph
  chance : Fin G.N → Bool
  p : Fin G.N → Fin G.N → ℝ
  s : Fin G.N

/-- Well-formedness (PDF pp. 17–18): `G` is layered, `V₁ = {s}` with `s` a chance vertex, and for
every chance vertex `c`, `p_c(v) ≥ 0`, `p_c(v) ≠ 0` iff `(c, v)` is an arc, and `p_c` sums to one
when `c` is not in the last layer. -/
def GMDP.WF (M : GMDP) : Prop :=
  M.G.WF ∧ (∀ v, M.G.layer v = 1 ↔ v = M.s) ∧ M.chance M.s = true ∧
  ∀ c, M.chance c = true →
    (∀ v, 0 ≤ M.p c v) ∧ (∀ v, M.p c v ≠ 0 ↔ M.G.arc c v = true) ∧
    (M.G.layer c < M.G.H → ∑ v, M.p c v = 1)

/-- A walk `(v₁, …, v_ℓ)` in `G` starting at `v₁ = s`. -/
def IsWalkFromS (M : GMDP) (w : List (Fin M.G.N)) : Prop :=
  w.head? = some M.s ∧ ∀ (i : ℕ) (h : i + 1 < w.length), M.G.arc w[i] w[i + 1] = true

/-- A randomized policy: to every trajectory, weights on the next vertex. -/
abbrev GPolicy (M : GMDP) := List (Fin M.G.N) → Fin M.G.N → ℝ

/-- Validity: on every walk from `s` of length `< H` ending in a decision vertex, the policy is a
probability distribution supported on the out-neighbours of the last vertex. -/
def IsGPolicy (M : GMDP) (π : GPolicy M) : Prop :=
  ∀ w : List (Fin M.G.N), IsWalkFromS M w → w.length < M.G.H →
    ∀ vℓ, w.getLast? = some vℓ → M.chance vℓ = false →
      (∀ v, 0 ≤ π w v) ∧ ∑ v, π w v = 1 ∧ ∀ v, π w v ≠ 0 → M.G.arc vℓ v = true

/-- Probability factor of position `j` (0-based) of the vertex sequence `τ`: `[τ₀ = s]` for
`j = 0`; otherwise `p_{τ_{j-1}}(τ_j)` if `τ_{j-1}` is a chance vertex and
`π_{τ_{<j}}(τ_j)` if it is a decision vertex. -/
def gstep (M : GMDP) (π : GPolicy M) (τ : Fin M.G.H → Fin M.G.N) (j : Fin M.G.H) : ℝ :=
  if j.val = 0 then (if τ j = M.s then 1 else 0)
  else
    let u := τ ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
    if M.chance u then M.p u (τ j) else π ((List.ofFn τ).take j.val) (τ j)

/-- The probability that the MDP process with policy `π` visits `τ₀, …, τ_{H-1}`. -/
def gpathProb (M : GMDP) (π : GPolicy M) (τ : Fin M.G.H → Fin M.G.N) : ℝ :=
  ∏ j, gstep M π τ j

/-- `E[1^(r)_OPT]`: the coordinate `I` is the probability that every vertex of `I` is visited. -/
def visitMoment (M : GMDP) (π : GPolicy M) : Finset (Fin M.G.N) → ℝ :=
  fun I => ∑ τ, gpathProb M π τ * liftInd (Finset.univ.image τ) I

/-- Constraint (7) (PDF p. 18): `x_{I∪{u}} = x_I · p_c(u)` for all `i ∈ {1, …, H-1}`,
`c ∈ V_i ∩ C`, `u ∈ V_{i+1}` and `{c} ⊆ I ⊆ V₁ ∪ … ∪ V_i` with `|I| ≤ r`. -/
def Sat7 (M : GMDP) (r : ℕ) (x : Finset (Fin M.G.N) → ℝ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ M.G.H - 1 → ∀ c, M.chance c = true → M.G.layer c = i →
    ∀ u, M.G.layer u = i + 1 → ∀ I : Finset (Fin M.G.N), c ∈ I → (∀ v ∈ I, M.G.layer v ≤ i) →
      I.card ≤ r → x (insert u I) = x I * M.p c u

/-- Line 1 of Algorithm 4: `K = {max{k·d^j | k ∈ ℤ≥0, k·d^j ≤ ℓ} | j ∈ ℤ≥0} ∖ {0}`; the maximum is
`⌊ℓ / d^j⌋ · d^j`, and the exponents `j ≤ ℓ` give every nonzero value when `d ≥ 2`. -/
def alg4K (d ℓ : ℕ) : Finset ℕ :=
  ((Finset.range (ℓ + 1)).image (fun j => (ℓ / d ^ j) * d ^ j)).erase 0

/-- Line 2 of Algorithm 4: `I = {v_i : i ∈ K}` (positions are 1-based). -/
def alg4I {N : ℕ} (d : ℕ) (traj : List (Fin N)) : Finset (Fin N) :=
  (alg4K d traj.length).biUnion (fun i => (traj[i - 1]?).toFinset)

/-- Algorithm 4 (PDF p. 19) on the trajectory `(v₁, …, v_ℓ)`: `none` is the output "error"
(`x_I = 0`); otherwise the weights `x_{I∪{u}} / x_I` on the vertices `u ∈ V_{ℓ+1}` (and `0` on
the other vertices). -/
def alg4 (M : GMDP) (d : ℕ) (x : Finset (Fin M.G.N) → ℝ) (traj : List (Fin M.G.N)) :
    Option (Fin M.G.N → ℝ) :=
  if x (alg4I d traj) = 0 then none
  else some (fun u =>
    if M.G.layer u = traj.length + 1 then x (insert u (alg4I d traj)) / x (alg4I d traj) else 0)

/-- Sampling from a weight vector, if it is a probability vector. -/
def nextDist {N : ℕ} (q : Fin N → ℝ) : Option (PMF (Fin N)) :=
  if h : (∀ u, 0 ≤ q u) ∧ ∑ u, ENNReal.ofReal (q u) = 1 then
    some (PMF.ofFintype (fun u => ENNReal.ofReal (q u)) h.2)
  else none

/-- The law of the trajectory after `k` repeated applications of Algorithm 4 on the previous
vertices and `x`, starting from the empty trajectory; `none` if some application returned
"error" or weights that are not a probability vector. -/
def mdpPrefix (M : GMDP) (d : ℕ) (x : Finset (Fin M.G.N) → ℝ) :
    ℕ → PMF (Option (List (Fin M.G.N)))
  | 0 => PMF.pure (some [])
  | k + 1 => (mdpPrefix M d x k).bind (fun o =>
    match o with
    | none => PMF.pure none
    | some τ =>
      match alg4 M d x τ with
      | none => PMF.pure none
      | some q =>
        match nextDist q with
        | none => PMF.pure none
        | some μ => μ.map (fun u => some (τ ++ [u])))

/-- `MDP(x)`: the law of the path obtained by applying Algorithm 4 `H` times. -/
def MDPlaw (M : GMDP) (d : ℕ) (x : Finset (Fin M.G.N) → ℝ) : PMF (Option (List (Fin M.G.N))) :=
  mdpPrefix M d x M.G.H

end

end SubmodMDP.Policies


