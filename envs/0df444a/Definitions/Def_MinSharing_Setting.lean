-- Prove2me | Definitions.Def_MinSharing_Setting
-- name    : MinSharing_Setting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:04.160177+00:00
-- url     : https://prove2.me/theorems/4e2539ae-aff8-4fad-939f-83325806e8b7
-- title:
--   Fair division with goods and bads: PROP, EF, non-malicious allocations, $\#\mathrm{shar}_z$, consumption graphs, $\mathcal G_v$ and $D_v$
-- statement:
--   There are $n$ agents and $m$ divisible objects; agent $i$ values the whole object $o$ at $v_{i,o}\in\mathbb R$, with no sign restriction (goods, bads and neutral objects are mixed). An **allocation** is a matrix $z=(z_{i,o})$ with $z_{i,o}\ge0$ and $\sum_i z_{i,o}=1$ for every $o$; agent $i$'s utility is $u_i(z_i)=\sum_o v_{i,o}z_{i,o}$. The module defines, for a valuation matrix $v$ and an allocation $z$:
--
--   1. **Envy-freeness** (EF): $u_i(z_i)\ge u_i(z_j)$ for all $i,j$; **proportionality** (PROP): $u_i(z_i)\ge\frac1n\sum_o v_{i,o}$ for all $i$; and a parameter $F\in\{\mathrm{PROP},\mathrm{EF}\}$ selecting one of them.
--   2. **Goods, neutral objects, bads, pure goods**: $o$ is a good if $v_{i,o}>0$ for some $i$; neutral if $v_{i,o}=0$ for some $i$ and $v_{j,o}\le0$ for all $j$; a bad if $v_{i,o}<0$ for all $i$; a pure good if $v_{i,o}>0$ for all $i$.
--   3. **Non-malicious** allocations: every good is consumed only by agents with $v_{i,o}>0$ and every neutral object only by agents with $v_{i,o}=0$.
--   4. The **number of sharings** $\#\mathrm{shar}_z=\sum_{o}\bigl(|\{i: z_{i,o}>0\}|-1\bigr)$ and the **number of shared objects** $|\{o:\ z_{i,o}\in(0,1)\text{ for some }i\}|$.
--   5. The **consumption graph** $\mathcal{CG}_z$: agent $i$ and object $o$ are adjacent iff $z_{i,o}>0$ (as an edge set and as a bipartite simple graph), and the set of **fPO graphs** $\mathcal G_v=\{\mathcal{CG}_z: z\text{ is fPO for }v\}$.
--   6. The **degree of degeneracy**
--   $$D_v=\max_{i\ne j}\ \max_{r>0}\ \bigl|\{o: v_{i,o}=r\cdot v_{j,o}\}\bigr|-1 .$$
--   7. The **sub-instance** $v^k$ of the first $k$ agents, the property that an allocation **minimizes the number of sharings** among fractionally Pareto-optimal $F$-fair allocations, and the input order of Lemma 3.8(b) (objects valued with the same sign by both agents listed by non-increasing ratio $|v_{1,o}|/|v_{2,o}|$).
--
--   Fractional Pareto-optimality (fPO) is the published `IsParetoOptimal`: no allocation gives every agent at least as much and some agent strictly more.
--
--   These are the objects of every statement of the mission: the fairness notions and fPO define the feasible set, $\#\mathrm{shar}$ is the objective, and $D_v$ and $\mathcal G_v$ measure the complexity of the problem.
--
--   **Formalization Note** Agents are `Fin n` and objects `Fin m` (paper index = Lean index + 1). $\#\mathrm{shar}_z$ uses truncated natural subtraction, which never truncates on an allocation (every column has a positive entry). $D_v$ is an integer computed as a supremum in $\mathbb N$ minus one; for $n\ge2$ the supremum is a maximum, and $D_v=-1$ is possible. For $n\le1$, outside the paper's scope, the value is $-1$.
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, §2.1–2.4 pp.7–10 (allocations, EF, PROP, goods/bads, non-malicious p.8, consumption graph p.8, #shar p.10), §3.2 p.13 (D_v), Proposition 3.7 p.15 (G_v), p.17 (v^k), Theorem 3.6 p.14 (sharing minimization), Lemma 3.8(b) p.16 (ratio order)

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting

set_option autoImplicit false

namespace MinSharing

open Finset CompetitiveChores.RichFamily

/-- Envy-freeness (Sandomirskiy, Segal-Halevi, *Efficient Fair Division with Minimal Sharing*,
arXiv:1908.01669v3, §2.2, p.7): "for all i, j ∈ [n]: uᵢ(zᵢ) ≥ uᵢ(zⱼ)".

**Formalization Note** Agents are `Fin n`, objects `Fin m` (paper index = Lean index + 1);
`v i o` is agent `i`'s value of the whole object `o`, any real number (goods, bads and neutral
objects are mixed); `z i o` is the share of `o` given to `i`. `bundleUtility v i x = ∑ₒ v i o * x o`
is the additive utility of the published `CompetitiveChores.RichFamily` setting. -/
def IsEF {n m : ℕ} (v z : Fin n → Fin m → ℝ) : Prop :=
  ∀ i j : Fin n, bundleUtility v i (z j) ≤ bundleUtility v i (z i)

/-- Proportionality (arXiv:1908.01669v3, §2.2, p.7): "∀ i ∈ [n] uᵢ(zᵢ) ≥ 1/n ∑_{o∈[m]} vᵢ,ₒ".

**Formalization Note** `1/n` is the real number `1 / (n : ℝ)`. -/
def IsProp {n m : ℕ} (v z : Fin n → Fin m → ℝ) : Prop :=
  ∀ i : Fin n, (1 / (n : ℝ)) * ∑ o, v i o ≤ utilityProfile v z i

/-- The two fairness notions of Theorem 3.6 (arXiv:1908.01669v3, p.14): proportionality
(`prop`) and envy-freeness (`ef`). -/
inductive Fairness
  | prop
  | ef
  deriving DecidableEq

/-- `IsFair F v z`: the allocation `z` satisfies the fairness notion `F` (PROP or EF, p.7). -/
def IsFair {n m : ℕ} : Fairness → (Fin n → Fin m → ℝ) → (Fin n → Fin m → ℝ) → Prop
  | .prop, v, z => IsProp v z
  | .ef, v, z => IsEF v z

/-- An object `o` is a **good** if `vᵢ,ₒ > 0` for at least one agent (p.7). -/
def IsGood {n m : ℕ} (v : Fin n → Fin m → ℝ) (o : Fin m) : Prop := ∃ i, 0 < v i o

/-- An object `o` is **neutral** if `vᵢ,ₒ = 0` for at least one agent and `vⱼ,ₒ ≤ 0` for all
agents (p.7). -/
def IsNeutral {n m : ℕ} (v : Fin n → Fin m → ℝ) (o : Fin m) : Prop :=
  (∃ i, v i o = 0) ∧ ∀ j, v j o ≤ 0

/-- An object `o` is a **bad** if `vᵢ,ₒ < 0` for all agents (p.7). -/
def IsBad {n m : ℕ} (v : Fin n → Fin m → ℝ) (o : Fin m) : Prop := ∀ i, v i o < 0

/-- An object `o` is a **pure good** if `vᵢ,ₒ > 0` for all agents (p.7). -/
def IsPureGood {n m : ℕ} (v : Fin n → Fin m → ℝ) (o : Fin m) : Prop := ∀ i, 0 < v i o

/-- **Non-malicious** allocation (p.8): "each good o is consumed by agents i with vᵢ,ₒ > 0 and
each neutral object o by agents i with vᵢ,ₒ = 0"; no restriction on bads. -/
def IsNonMalicious {n m : ℕ} (v z : Fin n → Fin m → ℝ) : Prop :=
  (∀ o, IsGood v o → ∀ i, 0 < z i o → 0 < v i o) ∧
  (∀ o, IsNeutral v o → ∀ i, 0 < z i o → v i o = 0)

/-- The **number of sharings** (§2.4, p.10): `#shar_z = ∑_{o∈[m]} (|{i ∈ [n] : zᵢ,ₒ > 0}| − 1)`.

**Formalization Note** The value is a natural number with truncated subtraction. For an
allocation every object has an agent with a positive share (the column sums to `1`), so the
truncation never applies to an allocation. -/
noncomputable def numSharings {n m : ℕ} (z : Fin n → Fin m → ℝ) : ℕ :=
  ∑ o : Fin m, ((univ.filter fun i : Fin n => 0 < z i o).card - 1)

/-- The **number of shared objects** (§2.4, p.10): `|{o ∈ [m] : zᵢ,ₒ ∈ (0,1) for some i}|`. -/
noncomputable def numSharedObjects {n m : ℕ} (z : Fin n → Fin m → ℝ) : ℕ :=
  (univ.filter fun o : Fin m => ∃ i, 0 < z i o ∧ z i o < 1).card

/-- The (undirected) **consumption graph** `CG_z` (§2.3, p.8), as its edge set: agent `i` and
object `o` are joined iff `zᵢ,ₒ > 0`. -/
noncomputable def consumptionGraph {n m : ℕ} (z : Fin n → Fin m → ℝ) : Finset (Fin n × Fin m) :=
  univ.filter fun p => 0 < z p.1 p.2

/-- The consumption graph `CG_z` as a simple graph on the vertex set `agents ⊕ objects`
(agents on the left, objects on the right; p.8), used for "CG_z is acyclic" (Lemma 2.5(b)). -/
def consumptionSimpleGraph {n m : ℕ} (z : Fin n → Fin m → ℝ) : SimpleGraph (Fin n ⊕ Fin m) :=
  SimpleGraph.fromRel fun a b => ∃ i o, a = Sum.inl i ∧ b = Sum.inr o ∧ 0 < z i o

/-- The set of **fPO graphs** (Proposition 3.7, p.15): `G_v := {CG_z : z is fPO for v}`.
fPO is `IsParetoOptimal` of the published setting: `z` is an allocation and no allocation
gives every agent at least as much and some agent strictly more. -/
def fpoGraphs {n m : ℕ} (v : Fin n → Fin m → ℝ) : Set (Finset (Fin n × Fin m)) :=
  {G | ∃ z, IsParetoOptimal v z ∧ consumptionGraph z = G}

/-- The number of objects on which agent `i`'s values are `r` times agent `j`'s:
`|{o ∈ [m] : vᵢ,ₒ = r · vⱼ,ₒ}|` (p.13). -/
noncomputable def proportionalCount {n m : ℕ} (v : Fin n → Fin m → ℝ) (i j : Fin n) (r : ℝ) : ℕ :=
  (univ.filter fun o : Fin m => v i o = r * v j o).card

/-- The **degree of degeneracy** (§3.2, p.13):
`D_v = max_{i,j∈[n], i≠j} max_{r>0} |{o ∈ [m] : vᵢ,ₒ = r · vⱼ,ₒ}| − 1`.

**Formalization Note** The double maximum is the supremum in `ℕ` of the counts
`proportionalCount v i j r` over `i ≠ j` and `r > 0`; for `n ≥ 2` this set is nonempty and
bounded by `m`, so the supremum is attained and is the paper's maximum. `D_v` is an integer and
is **not** truncated at `0`: it equals `−1` when no object satisfies `vᵢ,ₒ = r · vⱼ,ₒ` for any pair
and any `r > 0` (e.g. `n = 2`, `m = 1`, `v = (1; 0)`). For `n ≤ 1` (outside the paper's scope) the
set is empty and the value is `−1`. -/
noncomputable def degeneracy {n m : ℕ} (v : Fin n → Fin m → ℝ) : ℤ :=
  ((sSup {k : ℕ | ∃ i j : Fin n, i ≠ j ∧ ∃ r : ℝ, 0 < r ∧ proportionalCount v i j r = k} : ℕ) : ℤ)
    - 1

/-- The valuation of the first `k` agents (p.17): `vᵏ = (vᵢ,ₒ)_{i∈[k], o∈[m]}`.

**Formalization Note** Used only for `k ≤ n`, where it is the restriction of `v` to the agents
`0, …, k − 1`; rows with index `≥ n` (never used) are set to `0`. -/
def subInstance {n m : ℕ} (v : Fin n → Fin m → ℝ) (k : ℕ) : Fin k → Fin m → ℝ :=
  fun i o => if h : (i : ℕ) < n then v ⟨i, h⟩ o else 0

/-- `z` **minimizes the number of sharings subject to fPO and the fairness notion `F`**
(Theorem 3.6(a), p.14): `z` is fPO and `F`-fair, and `#shar_z ≤ #shar_y` for every fPO,
`F`-fair allocation `y`. -/
def IsMinSharingFair {n m : ℕ} (F : Fairness) (v z : Fin n → Fin m → ℝ) : Prop :=
  IsParetoOptimal v z ∧ IsFair F v z ∧
    ∀ y, IsParetoOptimal v y → IsFair F v y → numSharings z ≤ numSharings y

/-- The precondition of Lemma 3.8(b) (p.16) for a two-agent instance: "all the objects `o` with
`v₁,ₒ · v₂,ₒ > 0` are ordered by the ratio `|v₁,ₒ|/|v₂,ₒ|`", read as: among those objects, the ratio
is monotone in the object index, either non-increasing (the descending order of the proof of
Theorem 3.3, p.13) or non-decreasing; the page does not fix the direction, so both are allowed. -/
def IsRatioSorted {m : ℕ} (v : Fin 2 → Fin m → ℝ) : Prop :=
  (∀ o o' : Fin m, o < o' → 0 < v 0 o * v 1 o → 0 < v 0 o' * v 1 o' →
    |v 0 o'| / |v 1 o'| ≤ |v 0 o| / |v 1 o|) ∨
  (∀ o o' : Fin m, o < o' → 0 < v 0 o * v 1 o → 0 < v 0 o' * v 1 o' →
    |v 0 o| / |v 1 o| ≤ |v 0 o'| / |v 1 o'|)

end MinSharing


