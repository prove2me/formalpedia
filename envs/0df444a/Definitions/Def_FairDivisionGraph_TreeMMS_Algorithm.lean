-- Prove2me | Definitions.Def_FairDivisionGraph_TreeMMS_Algorithm
-- name    : FairDivisionGraph_TreeMMS_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:30.547014+00:00
-- url     : https://prove2.me/theorems/9bea9a95-f0e6-44e4-8989-70beaa1ed275
-- title:
--   Algorithm 1: residual states, legal transitions and failure semantics
-- statement:
--   A residual state records remaining original vertex labels $V'$ and agent labels $N'$. Its utilities are the original table restricted to those vertices, without renormalization. For a chosen root $r$, $D(v)$ is the set of vertices whose simple path from $r$ passes through $v$, including $v$ itself. Children are adjacent strict descendants.
--
--   The procedure fails if some remaining agent values $V'$ below her original rational threshold. With one agent it assigns all of $V'$ to her. Otherwise it may choose any root and any agent $i$ and vertex $v$ with $u_i(D(v))\ge q_i$, provided $u_j(D(w))<q_j$ for every child $w$ of $v$ and every remaining agent $j$. It removes $D(v)$ and $i$ and recurses. Missing choices and zero-agent inputs are explicit failures; recursive failure propagates. A successful recursive result is used once to extend the allocation with $i$'s bundle. Inactive agents have no role in the residual problem.
--
--   Reached states are finite prefixes of these local recursive-call transitions starting from all vertices and agents. A prefix need not return successfully, and its definition does not assume the residual MMS invariant. This relational encoding permits every legal root and tie break. Reusing one recursive result implements the informal description's reading of the two identical printed calls.
-- source:
--   Bouveret, Cechlárová, Elkind, Igarashi and Peters (2017), Fair Division of a Graph, IJCAI-17, https://doi.org/10.24963/ijcai.2017/20, Algorithm 1 and context of Lemma 5.2, printed p. 139 (PDF p. 5)

import Definitions.Def_FairDivisionGraph_TreeMMS_MMS

set_option autoImplicit false

noncomputable section

namespace FairDivisionGraph.TreeMMS

/-- Residual labels retain their original names and original utilities. -/
structure Residual (m n : ℕ) where
  vertices : Finset (Fin m)
  agents : Finset (Fin n)

/-- The initial recursive state. -/
def initial (m n : ℕ) : Residual m n := ⟨Finset.univ, Finset.univ⟩

/-- Descendants include `v`: the simple root-to-vertex path passes through `v`.
On a tree the simple path is unique. -/
def descendants {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (r v : Fin m) : Finset (Fin m) := by
  classical
  exact V.filter fun x => ∃ (hr : r ∈ V) (hx : x ∈ V),
    ∃ p : (G.induce (V : Set (Fin m))).Walk ⟨r, hr⟩ ⟨x, hx⟩,
      p.IsPath ∧ v ∈ p.support.map Subtype.val

/-- A child is an adjacent strict descendant, in the induced residual tree. -/
def Child {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (r v w : Fin m) : Prop :=
  G.Adj v w ∧ w ∈ descendants G V r v ∧ w ≠ v

/-- The explicit line 1 failure test. -/
def Shortfall {m n : ℕ} (u : Fin n → Fin m → ℝ) (q : Fin n → ℚ)
    (s : Residual m n) : Prop :=
  ∃ i ∈ s.agents, value (u i) s.vertices < (q i : ℝ)

/-- Exactly the local root and line-7 choice guards, universal over remaining players. -/
def Eligible {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) (r v : Fin m) (i : Fin n) : Prop :=
  r ∈ s.vertices ∧ v ∈ s.vertices ∧ i ∈ s.agents ∧
  (q i : ℝ) ≤ value (u i) (descendants G s.vertices r v) ∧
  ∀ w, Child G s.vertices r v w →
    ∀ j ∈ s.agents, value (u j) (descendants G s.vertices r w) < (q j : ℝ)

/-- Delete the selected bundle and player; utilities are never rescaled. -/
def remove {m n : ℕ} (G : SimpleGraph (Fin m)) (s : Residual m n)
    (r v : Fin m) (i : Fin n) : Residual m n :=
  ⟨s.vertices \ descendants G s.vertices r v, s.agents.erase i⟩

/-- A recursive call is made precisely when these local guards hold. -/
def Recurses {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s t : Residual m n) : Prop :=
  ¬ Shortfall u q s ∧ 1 < s.agents.card ∧
  ∃ r v i, Eligible G u q s r v i ∧ t = remove G s r v i

/-- All states actually reached by finite prefixes, including states that subsequently fail.
No successful return or residual MMS invariant is assumed. -/
def Reached {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) : Prop :=
  Relation.ReflTransGen (Recurses G u q) (initial m n) s

/-- Failure also represents an absent choice or the undefined zero-player input. -/
def FailsHere {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) : Prop :=
  Shortfall u q s ∨ s.agents.card = 0 ∨
    (1 < s.agents.card ∧ ¬ ∃ r v i, Eligible G u q s r v i)

/-- Relational execution of Algorithm 1, allowing every legal root and tie break.
The recursive result is evaluated once and reused; `none` propagates failure. -/
inductive Execution {m n : ℕ} (G : SimpleGraph (Fin m))
    (u : Fin n → Fin m → ℝ) (q : Fin n → ℚ) :
    Residual m n → Option (Fin n → Finset (Fin m)) → Prop
  | fail (s) : FailsHere G u q s → Execution G u q s none
  | single (s) : ¬ Shortfall u q s → s.agents.card = 1 →
      Execution G u q s (some (fun i => if i ∈ s.agents then s.vertices else ∅))
  | recurse (s) (r v) (i) (out) : ¬ Shortfall u q s → 1 < s.agents.card →
      Eligible G u q s r v i → Execution G u q (remove G s r v i) out →
      Execution G u q s (out.map (fun π => Function.update π i (descendants G s.vertices r v)))

end FairDivisionGraph.TreeMMS

/-
BEGIN IMPORTED DEPENDENCY SOURCE

MODULE: Model
SHA256: 296ea53e433168aed88ae50d3345cd5d66705c6f11d264712fdc401f7adc3ca0

import Mathlib

set_option autoImplicit false

namespace FairDivisionGraph.TreeMMS

/-- Additive value; no normalization is built into this raw operation. -/
def value {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) : ℝ := ∑ v ∈ S, u v

/-- Initial CFD utility assumptions, including the standing cardinality convention. -/
def IsCFD {m n : ℕ} (u : Fin n → Fin m → ℝ) : Prop :=
  0 < n ∧ n ≤ m ∧ (∀ i v, 0 ≤ u i v) ∧ (∀ i, value (u i) Finset.univ = 1)

/-- Empty bundles are permitted; every nonempty bundle induces a connected graph. -/
def BundleConnected {m : ℕ} (G : SimpleGraph (Fin m)) (S : Finset (Fin m)) : Prop :=
  S = ∅ ∨ (G.induce (S : Set (Fin m))).Connected

/-- General valid allocations need not cover all vertices. -/
def Valid {m n : ℕ} (G : SimpleGraph (Fin m)) (π : Fin n → Finset (Fin m)) : Prop :=
  (∀ i, BundleConnected G (π i)) ∧ (∀ i j, i ≠ j → Disjoint (π i) (π j))

/-- Completeness is separate from validity. -/
def Complete {m n : ℕ} (π : Fin n → Finset (Fin m)) : Prop :=
  ∀ v, ∃ i, v ∈ π i

/-- A labelled partition of a residual vertex set into nonempty connected parts. -/
def ConnectedPartition {m k : ℕ} (G : SimpleGraph (Fin m))
    (V : Finset (Fin m)) (P : Fin k → Finset (Fin m)) : Prop :=
  (∀ j, P j ⊆ V ∧ (P j).Nonempty ∧ (G.induce (P j : Set (Fin m))).Connected) ∧
  (∀ j l, j ≠ l → Disjoint (P j) (P l)) ∧
  (∀ v, v ∈ V ↔ ∃ j, v ∈ P j)

end FairDivisionGraph.TreeMMS

MODULE: MMS
SHA256: f7f8b22e61ead3997c54b67d98fb97869f03e7868d26dbf463d813bc3c3351d8

import Definitions.Def_FairDivisionGraph_TreeMMS_Model

set_option autoImplicit false

noncomputable section

namespace FairDivisionGraph.TreeMMS

/-- Least part value. The artificial zero-player case is totalized by zero. -/
def partitionValue {m k : ℕ} (u : Fin m → ℝ) (P : Fin k → Finset (Fin m)) : ℝ := by
  classical
  let vals := Finset.univ.image (fun j => value u (P j))
  exact if h : vals.Nonempty then vals.min' h else 0

/-- The actual finite family of connected partitions, not a supplied optimum. -/
def partitions {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (k : ℕ) : Finset (Fin k → Finset (Fin m)) := by
  classical
  exact Finset.univ.filter (ConnectedPartition G V)

/-- Maximum of the finite family of least-part values. Zero when no partition exists.
For a tree with `1 ≤ k ≤ |V|`, the connected family is nonempty; this fact is not an input. -/
def mms {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (k : ℕ) (u : Fin m → ℝ) : ℝ := by
  classical
  let vals := (partitions G V k).image (partitionValue u)
  exact if h : vals.Nonempty then vals.max' h else 0

/-- The connected-partition MMS guarantee, with factor exactly one. -/
def IsMMS {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (π : Fin n → Finset (Fin m)) : Prop :=
  Valid G π ∧ ∀ i, mms G Finset.univ n (u i) ≤ value (u i) (π i)

end FairDivisionGraph.TreeMMS

END IMPORTED DEPENDENCY SOURCE
-/


