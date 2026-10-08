-- Prove2me | Definitions.Def_LittleCharity_EFX_Setting
-- name    : LittleCharity_EFX_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:37:59.258983+00:00
-- url     : https://prove2.me/theorems/1929fcbd-5e64-4802-8060-a536e272f8a9
-- title:
--   Finite allocations, pool, EFX, envy graph, and minimal envied sets
-- statement:
--   This file fixes the model of §1.1.1 (p. 3) and the objects of Definitions 1 and 3 and Algorithm 2 (pp. 8–9).
--
--   There are $n$ agents $N=[n]$ and a set $M$ of $m$ indivisible goods. Each agent $i$ has a valuation $v_i$ assigning a real number $v_i(S)$ to every bundle $S\subseteq M$. The valuation profile is
--
--   1. **normalized** if $v_i(\varnothing)=0$ for every $i$;
--   2. **monotone** if $S\subseteq T$ implies $v_i(S)\le v_i(T)$ for every $i$.
--
--   An **allocation** $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles; allocations are partial, and the **pool** of unallocated goods is
--   $$
--   P(X)=M\setminus\bigcup_{i=1}^n X_i .
--   $$
--   $X$ is **EFX** if $v_i(X_j\setminus\{g\})\le v_i(X_i)$ for any two agents $i,j$ and every $g\in X_j$.
--
--   The **envy graph** $G_X$ has the agents as vertices and an edge $i\to j$ if and only if $v_i(X_i)<v_i(X_j)$. A **source** is a vertex of indegree zero (an agent nobody envies). The **reachability component** $C(s)$ is the set of agents reachable from $s$ by a directed path, including $s$ itself. $G_X$ is **acyclic** if no agent reaches itself by a nonempty path. The **social welfare** is $\phi(X)=\sum_{i} v_i(X_i)$.
--
--   A set $S\subseteq M$ is **envied** if some agent $i$ has $v_i(X_i)<v_i(S)$. A set $Z$ is an **inclusion-wise minimal envied subset** of $S$ if $Z\subseteq S$, $Z$ is envied, and every agent $j$ satisfies $v_j(Z')\le v_j(X_j)$ for every strict subset $Z'\subsetneq Z$. An agent $i$ is a **most envious agent** of $S$ if $v_i(X_i)<v_i(Z)$ for some inclusion-wise minimal envied subset $Z$ of $S$ (ties broken arbitrarily, so this is a relation, not a function).
--
--   Rule $U_0$ is **applicable** if some good $g\in P(X)$ and some agent $i$ exist such that giving $g$ to $i$ yields an EFX allocation.
--
--   Rule $U_2$'s output allocation (Algorithm 2, lines 14–17) is defined from listed envy paths $u^a_0\to\cdots\to u^a_{m_a}$, terminal agents $t_a$ and sets $Z_a$: the terminal agent $t_{a+1}$ (indices modulo $\ell$) receives $Z_a$; every other agent $u^a_k$ with $k<m_a$ receives $X_{u^a_{k+1}}$, the bundle of the next agent on its path; all remaining agents keep their bundles.
--
--   **Formalization Note** Agents are `Fin n` and goods `Fin m`, both indexed from $0$; $M$ is the whole of `Fin m`. Valuations are real-valued; nonnegativity is not part of the definitions and follows from normalized plus monotone where needed. The pool is always computed from the allocation, never an independent variable. Reachability is the reflexive–transitive closure of the envy relation, so $s\in C(s)$. In the $U_2$ allocation, cases are resolved by a fixed choice; under the hypotheses of Lemma 7 (distinct terminal agents, vertex-disjoint paths) the choice is unique.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, pp. 3, 8–9, §1.1.1, Definitions 1 and 3, Algorithm 2

import Mathlib

namespace LittleCharity.EFX

def IsNormalized {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) : Prop :=
  ∀ i, v i ∅ = 0

def IsMonotoneVal {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) : Prop :=
  ∀ i S T, S ⊆ T → v i S ≤ v i T

def IsPartialAllocation {n m : ℕ} (X : Fin n → Finset (Fin m)) : Prop :=
  Pairwise (fun i j => Disjoint (X i) (X j))

def pool {n m : ℕ} (X : Fin n → Finset (Fin m)) : Finset (Fin m) :=
  Finset.univ \ Finset.univ.biUnion X

def IsEFX {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) : Prop :=
  ∀ i j, ∀ g ∈ X j, v i ((X j).erase g) ≤ v i (X i)

def Envies {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (i j : Fin n) : Prop :=
  v i (X i) < v i (X j)

def IsSource {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (j : Fin n) : Prop :=
  ∀ i, ¬ Envies v X i j

noncomputable def sources {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => IsSource v X j)

def welfare {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) : ℝ :=
  ∑ i, v i (X i)

def Reach {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (s t : Fin n) : Prop :=
  Relation.ReflTransGen (Envies v X) s t

def EnvyAcyclic {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) : Prop :=
  ∀ i, ¬ Relation.TransGen (Envies v X) i i

def IsEnvied {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (S : Finset (Fin m)) : Prop :=
  ∃ i, v i (X i) < v i S

def IsMinimalEnviedSubset {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (S Z : Finset (Fin m)) : Prop :=
  Z ⊆ S ∧ IsEnvied v X Z ∧ ∀ Z' ⊂ Z, ∀ j, v j Z' ≤ v j (X j)

def IsMostEnviousAgent {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (S : Finset (Fin m)) (i : Fin n) : Prop :=
  ∃ Z, IsMinimalEnviedSubset v X S Z ∧ v i (X i) < v i Z

def U0Applicable {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) : Prop :=
  ∃ g ∈ pool X, ∃ i, IsEFX v (Function.update X i (insert g (X i)))

/-- The successor of a vertex on a listed envy path, if the vertex is not last. -/
def pathNext? {n : ℕ} (p : List (Fin n)) (j : Fin n) : Option (Fin n) :=
  (p.zip p.tail).lookup j

/-- Rule U2's allocation after rotating bundles along its paths and assigning minimal envied
subsets to the terminal agents. The hypotheses of Lemma 7 make the cases unambiguous. -/
noncomputable def u2Allocation {n m ℓ : ℕ} (X : Fin n → Finset (Fin m))
    (t : Fin ℓ → Fin n) (Z : Fin ℓ → Finset (Fin m))
    (p : Fin ℓ → List (Fin n)) : Fin n → Finset (Fin m) := by
  classical
  exact fun j =>
    if h : ∃ a : Fin ℓ, t (finRotate ℓ a) = j then
      Z (Classical.choose h)
    else if h : ∃ a : Fin ℓ, (pathNext? (p a) j).isSome then
      X ((pathNext? (p (Classical.choose h)) j).getD j)
    else X j

end LittleCharity.EFX


