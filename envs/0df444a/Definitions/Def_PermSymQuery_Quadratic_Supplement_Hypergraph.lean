-- Prove2me | Definitions.Def_PermSymQuery_Quadratic_Supplement_Hypergraph
-- name    : PermSymQuery_Quadratic_Supplement_Hypergraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:38:47.624397+00:00
-- url     : https://prove2.me/theorems/da82fb9a-38a4-4e1b-a1ce-1942bac644fb
-- title:
--   Hypergraph query models: relabeling, invariance, $Q_\varepsilon$, $R_\varepsilon$, vertex sampling
-- statement:
--   Fix an integer $k$ and a finite vertex set $V$. A **simple uncolored $k$-uniform hypergraph** on $V$ is a function $H:\binom Vk\to\{0,1\}$; $H(e)=1$ exactly when the $k$-set $e$ is a hyperedge. For a permutation $\pi$ of $V$, write $\pi(e)=\{\pi(v):v\in e\}$ and $H^\pi(e)=H(\pi(e))$. For $V=[N]$, a pair $(D,f)$ with $D\subseteq\{0,1\}^{\binom{[N]}k}$ is a **$k$-uniform hypergraph property** when $H^\pi\in D$ and $f(H^\pi)=f(H)$ for every $H\in D$ and every $\pi\in S_N$ (Definition 2.2). Promises are allowed.
--
--   **Query models.** The quantum oracle acts on ordered vertex tuples: $H(v_1,\dots,v_k)=H(\{v_1,\dots,v_k\})$ if the $v_i$ are distinct and $0$ otherwise, and
--   $$O_H|v_1,\dots,v_k,z\rangle=|v_1,\dots,v_k,z\oplus H(v_1,\dots,v_k)\rangle .$$
--   There is no dummy address. $Q_\varepsilon(f)$ is the least $T$ for which a $T$-query quantum algorithm, with any finite workspace and a final computational-basis measurement, outputs $f(H)$ with probability at least $1-\varepsilon$ on every $H\in D$. A classical query reads one hyperedge-membership bit $H(e)$. $R_\varepsilon(f)$ is the least worst-case number of such queries of a randomized decision tree (a probability distribution over decision trees) with error at most $\varepsilon$ on every $H\in D$. Both infima take values in $\mathbb N\cup\{\infty\}$, with $\infty$ for an empty feasible set. A randomized algorithm is **nonadaptive** when every tree in its support makes the same query list on every input.
--
--   **Signed outputs and sampling.** For a quantum algorithm $\mathcal A$ with output map, $h_{\mathcal A}(H)=\Pr[1]-\Pr[0]$, and $\bar h_{\mathcal A}(H)=\mathbb E_{\pi\in S_N}h_{\mathcal A}(H^\pi)$ with $\pi$ uniform. For an $s$-element vertex set $S\subseteq[N]$, the **induced hypergraph** $H[S]$ is the restriction of $H$ to $\binom Sk$. A postprocessing rule $a(S,Z)$ takes a sample $S$ and a hypergraph $Z$ on $S$; it is bounded when all its values lie in $[-1,1]$, and its sample average is
--   $$\mathbb E_S\,a(S,H[S])=\binom Ns^{-1}\sum_{|S|=s}a(S,H[S]).$$
--   The sample size of (19) is $s=K(2kT)^2$ with $K=10^8$.
--
--   **Structure.** The incidence graph of $H$ has one node per vertex and per hyperedge and joins a vertex to the hyperedges containing it; $H$ is **connected** when its incidence graph is connected. The degree $\deg(v)$ is the number of hyperedges containing $v$. Two hypergraphs are isomorphic, $H\cong H'$, when some vertex bijection $\sigma$ satisfies $H'(\sigma(e))=H(e)$ for every $k$-set $e$.
--
--   These definitions carry the §2.3 and §5 hypergraph model shared by Lemma 5.3, Proposition 5.4, Theorems 1.2 and 1.3 and Lemma 6.1.
--
--   **Formalization Note** The answer bit is `ZMod 2`, and the algorithm and decision-tree types are the published `QAlgorithms` definitions; `K`, `Sample` and `queryList` are reused from the base mission's `PermSymQuery_Quadratic_Model`.
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), §2.1, §2.3 and Definition 2.2 (PDF pp. 7–9, printed pp. 5–7); §5.1–5.3 and (19), PDF p. 22–23 (printed p. 20–21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_PermSymQuery_Quadratic_Model

namespace PermSymQuery.Quadratic.Supplement

open QAlgorithms

/-- §2.3, PDF p.8: the k-element subsets of a finite vertex set `V`. -/
abbrev KSet (V : Type) [DecidableEq V] (k : ℕ) := {e : Finset V // e.card = k}

/-- §2.3, PDF p.8: a simple uncolored k-uniform hypergraph `H : (V choose k) → {0,1}`;
`H e = true` exactly when `e` is a hyperedge. -/
abbrev Hypergraph (V : Type) [DecidableEq V] (k : ℕ) := KSet V k → Bool

variable {V : Type} [DecidableEq V] {k : ℕ}

/-- The image `π(e) = {π(v) : v ∈ e}` of a k-set under a vertex bijection. -/
def KSet.map {V' : Type} [DecidableEq V'] (π : V ≃ V') (e : KSet V k) : KSet V' k :=
  ⟨e.1.map π.toEmbedding, by simp [e.2]⟩

/-- §2.3, PDF p.8: the relabeled hypergraph `H^π(e) = H(π(e))`. -/
def relabel (H : Hypergraph V k) (π : Equiv.Perm V) : Hypergraph V k :=
  fun e => H (KSet.map π e)

/-- Definition 2.2, PDF p.8: `f` is a k-uniform hypergraph property on the promise `D`:
for every `H ∈ D` and every vertex permutation `π`, `H^π ∈ D` and `f(H^π) = f(H)`.
Values of `f` outside `D` are never used; promises are allowed, `D` may be empty. -/
def HypPermInvariant {N : ℕ} (D : Set (Hypergraph (Fin N) k))
    (f : Hypergraph (Fin N) k → Bool) : Prop :=
  ∀ H ∈ D, ∀ π : Equiv.Perm (Fin N), relabel H π ∈ D ∧ f (relabel H π) = f H

/-- §2.3, PDF p.9: the extension of `H` to ordered vertex tuples,
`H(v_1,…,v_k) = H({v_1,…,v_k})` when the vertices are distinct and `0` otherwise,
as an element of the answer register `ZMod 2`. -/
noncomputable def orderedValue (H : Hypergraph V k) (v : Fin k → V) : ZMod 2 :=
  if h : Function.Injective v then
    (if H ⟨Finset.univ.image v, by rw [Finset.card_image_of_injective _ h]; simp⟩
      then 1 else 0)
  else 0

/-- §2.3, PDF p.9 (and §5.1, PDF p.22): the hypergraph oracle
`O_H |v_1,…,v_k, z⟩ = |v_1,…,v_k, z ⊕ H(v_1,…,v_k)⟩`. There is no dummy address. -/
noncomputable def hypOracle {N : ℕ} (H : Hypergraph (Fin N) k) :=
  xorOracle (orderedValue H)

/-- Basis labels of a hypergraph-query algorithm: an ordered vertex tuple, one answer bit and
the workspace. -/
abbrev HStateIndex (N k : ℕ) (W : Type) := ((Fin k → Fin N) × ZMod 2) × W

/-- A quantum algorithm with exactly `T` hypergraph queries, some finite workspace and a
Boolean computational-basis output map computes `f` with error at most `ε` on every `H ∈ D`. -/
def HQuantumComputes {N : ℕ} (D : Set (Hypergraph (Fin N) k))
    (f : Hypergraph (Fin N) k → Bool) (ε : ℝ) (T : ℕ) : Prop :=
  ∃ (m : ℕ) (alg : QueryAlg (Fin k → Fin N) (ZMod 2) (Fin m) T)
    (out : HStateIndex N k (Fin m) → Bool),
    ∀ H ∈ D, 1 - ε ≤ alg.outputProb (hypOracle H) out (f H)

/-- `Q_ε(f)` for hypergraph properties (§2.1, §2.3): the least feasible worst-case number of
hypergraph queries, in `ℕ∞` (an empty feasible set gives `⊤`). -/
noncomputable def HQeps {N : ℕ} (D : Set (Hypergraph (Fin N) k))
    (f : Hypergraph (Fin N) k → Bool) (ε : ℝ) : ℕ∞ :=
  ⨅ (T : ℕ) (_ : HQuantumComputes D f ε T), (T : ℕ∞)

/-- A randomized decision tree reading one hyperedge-membership bit `H e` per query, with at
most `d` queries on every supported tree and every input, computes `f` with error at most `ε`
on every `H ∈ D`. -/
def HRandomComputes {N : ℕ} (D : Set (Hypergraph (Fin N) k))
    (f : Hypergraph (Fin N) k → Bool) (ε : ℝ) (d : ℕ) : Prop :=
  ∃ R : RandDecisionTree (KSet (Fin N) k) Bool Bool,
    RandMakesAtMost R d ∧ ∀ H ∈ D, 1 - ε ≤ successProb R H (f H)

/-- `R_ε(f)` for hypergraph properties: least feasible worst-case number of
hyperedge-membership queries, in `ℕ∞`. -/
noncomputable def HReps {N : ℕ} (D : Set (Hypergraph (Fin N) k))
    (f : Hypergraph (Fin N) k → Bool) (ε : ℝ) : ℕ∞ :=
  ⨅ (d : ℕ) (_ : HRandomComputes D f ε d), (d : ℕ∞)

/-- §2.1: a randomized hyperedge-query algorithm is nonadaptive when every supported tree
makes the same list of queries on every input. -/
def HNonadaptive {N : ℕ} (R : RandDecisionTree (KSet (Fin N) k) Bool Bool) : Prop :=
  ∀ t ∈ R.support, ∀ H H' : Hypergraph (Fin N) k,
    PermSymQuery.Quadratic.queryList t H = PermSymQuery.Quadratic.queryList t H'

variable {N T : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- §2.1: the signed output expectation `h_A(H) = Pr[1] − Pr[0]` with the hypergraph oracle. -/
noncomputable def hSigned (alg : QueryAlg (Fin k → Fin N) (ZMod 2) W T)
    (out : HStateIndex N k W → Bool) (H : Hypergraph (Fin N) k) : ℝ :=
  alg.outputProb (hypOracle H) out true - alg.outputProb (hypOracle H) out false

/-- §5.3, PDF p.23: `h̄_A(H) = E_{π ∈ S_N} h_A(H^π)`, uniform over vertex permutations. -/
noncomputable def hSymSigned (alg : QueryAlg (Fin k → Fin N) (ZMod 2) W T)
    (out : HStateIndex N k W → Bool) (H : Hypergraph (Fin N) k) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
    ∑ π : Equiv.Perm (Fin N), hSigned alg out (relabel H π)

/-- §5.2, PDF p.22: the induced hypergraph `H[S]`, the restriction of `H` to the k-subsets of
`S`, as a hypergraph on the vertex type `S`. -/
def induced (H : Hypergraph (Fin N) k) (S : Finset (Fin N)) : Hypergraph S k :=
  fun e => H ⟨e.1.map (Function.Embedding.subtype _), by simp [e.2]⟩

/-- A postprocessing rule for vertex samples of size `s` sees only the sample `S` and a
hypergraph `Z` on `S`; it cannot read any hyperedge outside `S`. -/
abbrev HPostprocess (N s k : ℕ) :=
  (S : PermSymQuery.Quadratic.Sample N s) → Hypergraph S.val k → ℝ

/-- The rule is bounded: `a(S, Z) ∈ [−1, 1]` for every sample and every hypergraph on it. -/
def HBounded {s : ℕ} (a : HPostprocess N s k) : Prop :=
  ∀ S Z, a S Z ∈ Set.Icc (-1 : ℝ) 1

/-- `E_S a(S, H[S])` with `S` uniform among the s-element vertex subsets (used for `s ≤ N`). -/
noncomputable def hSampleAverage {s : ℕ} (a : HPostprocess N s k)
    (H : Hypergraph (Fin N) k) : ℝ :=
  (Nat.choose N s : ℝ)⁻¹ * ∑ S : PermSymQuery.Quadratic.Sample N s, a S (induced H S.val)

/-- (19), PDF p.22: `s = ⌈K q²⌉` with `q = 2kT` and `K = 10^8`; over `ℕ` the ceiling is the
integer itself. -/
def hSampleSize (k T : ℕ) : ℕ := PermSymQuery.Quadratic.K * (2 * k * T) ^ 2

/-- §2.3, PDF p.9: the incidence graph, with one node per vertex and per hyperedge, joining a
vertex to the hyperedges containing it. -/
def incidenceGraph (H : Hypergraph V k) : SimpleGraph (V ⊕ {e : KSet V k // H e = true}) :=
  SimpleGraph.fromRel fun p q => ∃ v e, p = Sum.inl v ∧ q = Sum.inr e ∧ v ∈ e.1.1

/-- §2.3, PDF p.9: a hypergraph is connected if its incidence graph is connected. -/
def HConnected (H : Hypergraph V k) : Prop := (incidenceGraph H).Connected

/-- The degree of a vertex: the number of hyperedges containing it. -/
def hdeg [Fintype V] (H : Hypergraph V k) (v : V) : ℕ :=
  (Finset.univ.filter fun e : KSet V k => v ∈ e.1 ∧ H e = true).card

/-- `H ≅ H'`: some vertex bijection `σ` satisfies `H'(σ(e)) = H(e)` for every k-set `e`. -/
def HIso (H H' : Hypergraph V k) : Prop :=
  ∃ σ : Equiv.Perm V, ∀ e : KSet V k, H' (KSet.map σ e) = H e

end PermSymQuery.Quadratic.Supplement


