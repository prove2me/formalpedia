-- Prove2me | Definitions.Def_AcycTesting_NearLinear_PermCores
-- name    : AcycTesting_NearLinear_PermCores
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:34:53.385209+00:00
-- url     : https://prove2.me/theorems/cc5cff8d-b9d7-496a-be8f-d16d07a4f06e
-- title:
--   Weak cycles and weak girth of occurrence multigraphs; random permutation cores Γ(Π), cyc≤γ, cut(V₁) and condition (3.1)
-- statement:
--   A directed multigraph is given by a set of edge *occurrences*, each with a tail and a head. *Weak* notions refer to the underlying undirected multigraph, which forgets directions and keeps every occurrence. A *weak cycle of length $j\ge1$* is a set of $j$ distinct occurrences $e_0,\dots,e_{j-1}$ together with distinct vertices $x_0,\dots,x_{j-1}$ such that $e_i$ joins $x_i$ and $x_{i+1 \bmod j}$ in either direction. Thus a loop is a weak cycle of length one, and two occurrences on the same unordered pair form a weak cycle of length two, whatever their directions. The weak girth is *greater than $\gamma$* if every weak cycle has more than $\gamma$ occurrences. A *weak forest* has no weak cycle. A set $F$ of occurrences *destroys all directed cycles* if the occurrences outside $F$ form no directed cycle (loops included).
--
--   A *core* on a vertex set $V$ consists of 32 colour maps $P_1,\dots,P_{32}:V\to V$, with one colour-$a$ occurrence $x\to P_a(x)$ for every vertex $x$ and colour $a$; it is a *permutation core* if every $P_a$ is a bijection.
--
--   For a tuple $\Pi=(\pi_1,\dots,\pi_{32})$ of permutations of $[N]$, the occurrence graph $\Gamma(\Pi)$ is the core with $P_a=\pi_a$. Probabilities and expectations are taken over $\Pi$ uniform on all $(N!)^{32}$ tuples (independent uniform permutations). Further:
--   - $G_\gamma$ is the event that $\Gamma(\Pi)$ has weak girth greater than $\gamma$;
--   - $\mathrm{cyc}_{\le\gamma}(\Pi)$ is the number of weak cycles of length at most $\gamma$ in $\Gamma(\Pi)$;
--   - for $V_1\subseteq[N]$, $\mathrm{cut}(V_1)$ is the number of occurrences $v\xrightarrow{a}\pi_a(v)$ with $v\in V_1$ and $\pi_a(v)\notin V_1$;
--   - $\mathrm{fas}(\Gamma(\Pi))$ is the fas of the digraph with $N^+(v)=\{\pi_a(v): a\in[32]\}$, which on $G_\gamma$ with $\gamma\ge2$ is $\Gamma(\Pi)$ itself.
--
--   A *girth scale* is a function $\gamma=\gamma(N)$ with integer values satisfying condition (3.1):
--   $$\gamma(N)\ge 2\quad\text{and}\quad 64^{\gamma(N)}\log N=o(N)\ \ (N\to\infty),$$
--   with the natural logarithm.
--
--   **Formalization Note.** Colours are `Fin 32` and $[N]$ is `Fin N`. `probU`/`expU` are the uniform probability and expectation on a finite type; on `PermTuple N` the type is nonempty, so there is no division by zero. $o(N)$ is the limit `64^γ(N) · log N / N → 0`.
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), pp. 14–15 (PDF 17–18), §3.1 Conventions and §3.2; pp. 38–39 (PDF 41–42), Lemmas A.1, A.4

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_Digraphs

namespace AcycTesting.NearLinear

open Filter Topology

/-! ### Weak cycles of a directed multigraph

A directed multigraph is given by a type `E` of edge occurrences and the map `ends : E → V × V`
sending an occurrence to its (tail, head). "Weak" notions refer to the underlying undirected
multigraph, which forgets directions and keeps every occurrence. -/

/-- A weak cycle of length `j ≥ 1`, listed cyclically: distinct vertices `x 0, …, x (j-1)` and
distinct occurrences `e 0, …, e (j-1)`, where `e i` joins `x i` and `x (i+1 mod j)` in either
direction. For `j = 1` this is a loop; for `j = 2` two distinct occurrences on one unordered
pair, in any directions. -/
def IsWeakCycleSeq {E V : Type*} (ends : E → V × V) (j : ℕ) (x : Fin j → V)
    (e : Fin j → E) : Prop :=
  1 ≤ j ∧ Function.Injective x ∧ Function.Injective e ∧
    ∀ i : Fin j, ends (e i) = (x i, x (finRotate j i)) ∨
      ends (e i) = (x (finRotate j i), x i)

/-- A weak cycle, as a set of occurrences; its length is the number of occurrences. -/
def IsWeakCycle {E V : Type*} (ends : E → V × V) (S : Finset E) : Prop :=
  ∃ (j : ℕ) (x : Fin j → V) (e : Fin j → E),
    IsWeakCycleSeq ends j x e ∧ (S : Set E) = Set.range e

/-- Weak girth greater than `γ`: every weak cycle has more than `γ` occurrences. -/
def WeakGirthGT {E V : Type*} (ends : E → V × V) (γ : ℕ) : Prop :=
  ∀ S : Finset E, IsWeakCycle ends S → γ < S.card

/-- A weak forest: no weak cycle at all (no loops, no opposite occurrences, no repeated
occurrences on one pair, no longer undirected cycles). -/
def IsWeakForest {E V : Type*} (ends : E → V × V) : Prop :=
  ∀ S : Finset E, ¬ IsWeakCycle ends S

/-- A set `F` of occurrences whose deletion destroys every directed cycle (loops included). -/
def IsOccFeedbackSet {E V : Type*} (ends : E → V × V) (F : Finset E) : Prop :=
  ∀ v : V, ¬ Relation.TransGen (fun u w => ∃ o, o ∉ F ∧ ends o = (u, w)) v v

/-! ### Permutation cores -/

/-- Thirty-two colour maps `P a : V → V`, `a ∈ [32]` (colours `0, …, 31`). -/
abbrev CoreMaps (V : Type*) := Fin 32 → V → V

/-- A permutation core: every colour map is a bijection. -/
def IsPermCore {V : Type*} (P : CoreMaps V) : Prop := ∀ a, Function.Bijective (P a)

/-- The occurrences of a core: one occurrence `x → P a x` per vertex `x` and colour `a`. -/
def coreEnds {V : Type*} (P : CoreMaps V) : V × Fin 32 → V × V :=
  fun o => (o.1, P o.2 o.1)

/-- Weak girth of the occurrence multigraph of a core greater than `γ`. -/
def CoreGirthGT {V : Type*} (P : CoreMaps V) (γ : ℕ) : Prop := WeakGirthGT (coreEnds P) γ

/-! ### Random permutation tuples `Π = (π₁, …, π₃₂)` of `[N]` -/

/-- A tuple of 32 permutations of `[N]` (here `Fin N`). -/
abbrev PermTuple (N : ℕ) := Fin 32 → Equiv.Perm (Fin N)

/-- The occurrence graph `Γ(Π)` as core maps. -/
def occMaps {N : ℕ} (πs : PermTuple N) : CoreMaps (Fin N) := fun a v => πs a v

/-- Probability of an event under the uniform distribution on a finite nonempty type. -/
noncomputable def probU {α : Type*} [Fintype α] (p : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter p).card : ℝ) / (Fintype.card α : ℝ)

/-- Expectation under the uniform distribution on a finite nonempty type. -/
noncomputable def expU {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

/-- `cyc≤γ(Π)`: the number of weak cycles (as occurrence sets) of length at most `γ` in
`Γ(Π)`. -/
noncomputable def cycLe {N : ℕ} (πs : PermTuple N) (γ : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun S : Finset (Fin N × Fin 32) => IsWeakCycle (coreEnds (occMaps πs)) S ∧
      S.card ≤ γ)).card

/-- `cut(V₁)`: the number of occurrences of `Γ(Π)` from `V₁` to its complement. -/
noncomputable def cut {N : ℕ} (πs : PermTuple N) (V₁ : Finset (Fin N)) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun o : Fin N × Fin 32 => o.1 ∈ V₁ ∧ πs o.2 o.1 ∉ V₁)).card

/-- `Γ(Π)` as a digraph without parallel edges (its set of distinct outneighbours); on the
girth event `G_γ` with `γ ≥ 2` it is exactly `Γ(Π)`, which is then simple. -/
noncomputable def coreGraph {N : ℕ} (πs : PermTuple N) : OutGraph (Fin N) := by
  classical
  exact fun v => Finset.univ.image (fun a => πs a v)

/-- Condition (3.1) on a girth scale `γ = γ(N)`: `γ(N) ≥ 2` and `64^γ log N = o(N)`
(natural logarithm). -/
def GirthScale (γ : ℕ → ℕ) : Prop :=
  (∀ N, 2 ≤ γ N) ∧
    Tendsto (fun N : ℕ => (64 : ℝ) ^ (γ N) * Real.log N / N) atTop (𝓝 0)

end AcycTesting.NearLinear


