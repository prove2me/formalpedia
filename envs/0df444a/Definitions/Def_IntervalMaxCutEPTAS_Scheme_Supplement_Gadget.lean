-- Prove2me | Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Gadget
-- name    : IntervalMaxCutEPTAS_Scheme_Supplement_Gadget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:30:15.862648+00:00
-- url     : https://prove2.me/theorems/70355c35-b3dc-41f1-8172-6dc6df433ab0
-- title:
--   The complete two-copy attachment graph and its cut statistics
-- statement:
--   For a simple source graph $Q$ and integer $p$, the target has core vertices $c_v^i$ for both copies $i\in\{1,2\}$, one middle $a_v^{i,j}$ for every repetition $1\le j\le p$, and exactly $\deg_Q(v)+1$ private vertices for each attachment. All cores form one clique. Each middle is joined to its own core and its same-copy source-neighbor cores. Each private vertex is joined only to its own core and middle. No other edges are added, so
--
--   $$|V(T_p(Q))|=2n_Q+4p(m_Q+n_Q).$$
--
--   The dependent private indices avoid padding vertices. The source set $S^i$ is read from core copy $i$, and $\rho_v^i$ counts its cut incident source edges. The attachment cut is counted from actual target edges incident with that attachment; core-core edges are excluded. Fixed lexicographic lists name all vertices, and the polynomial PEO program receives $n,p$ and the adjacency matrix of $Q$. It returns a permutation in these names with the actual PEO property. These objects are shared by Lemmas 7.3–7.5.
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), §7.2, including (5), PDF p. 26 (printed p. 25)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Machine
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Classes

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

/-- Indices (i,v,j): Fin 2 means the two copies, Fin p means all p repetitions. -/
structure Attachment (n p : ℕ) where
  copy : Fin 2
  vertex : Fin n
  repetition : Fin p
  deriving DecidableEq, Fintype

variable {n : ℕ} (Q : SimpleGraph (Fin n)) [DecidableRel Q.Adj] (p : ℕ)

/-- No padding vertices: private vertices are indexed by exactly degree(v)+1. -/
abbrev TargetVertex :=
  (Fin 2 × Fin n) ⊕ (Attachment n p ⊕ (Σ a : Attachment n p, Fin (Q.degree a.vertex + 1)))

def core (i : Fin 2) (v : Fin n) : TargetVertex Q p := .inl (i, v)
def middle (a : Attachment n p) : TargetVertex Q p := .inr (.inl a)
def privateVertex (a : Attachment n p) (t : Fin (Q.degree a.vertex + 1)) : TargetVertex Q p :=
  .inr (.inr ⟨a, t⟩)

/-- The complete core, the indicated middle-core edges, and exactly two edges at each private
vertex. fromRel symmetrizes these cases and removes loops. There are no other edges. -/
def targetRule : TargetVertex Q p → TargetVertex Q p → Bool
  | .inl c, .inl d => decide (c ≠ d)
  | .inr (.inl a), .inl (i, u) => decide (i = a.copy ∧ (u = a.vertex ∨ Q.Adj a.vertex u))
  | .inr (.inr ⟨a, _⟩), .inl c => decide (c = (a.copy, a.vertex))
  | .inr (.inr ⟨a, _⟩), .inr (.inl b) => decide (a = b)
  | _, _ => false

def target : SimpleGraph (TargetVertex Q p) :=
  SimpleGraph.fromRel (fun x y => targetRule Q p x y = true)

instance : DecidableRel (target Q p).Adj := inferInstanceAs
  (DecidableRel (SimpleGraph.fromRel (fun x y => targetRule Q p x y = true)).Adj)

/-- The attachment's own edges exclude all core-core edges. -/
def inAttachment (a : Attachment n p) (x : TargetVertex Q p) : Prop :=
  x = middle Q p a ∨ ∃ t, x = privateVertex Q p a t

def attachmentGraph (a : Attachment n p) : SimpleGraph (TargetVertex Q p) :=
  (target Q p) ⊓ SimpleGraph.fromRel (fun x y => inAttachment Q p a x ∨ inAttachment Q p a y)

noncomputable instance (a : Attachment n p) : DecidableRel (attachmentGraph Q p a).Adj := Classical.decRel _

noncomputable def attachmentCut (a : Attachment n p) (S : Finset (TargetVertex Q p)) : ℕ :=
  cutCount (attachmentGraph Q p a) S

def sourceSide (i : Fin 2) (S : Finset (TargetVertex Q p)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => core Q p i v ∈ S)

def crossingDegree (i : Fin 2) (v : Fin n) (S : Finset (TargetVertex Q p)) : ℕ :=
  ((Q.neighborFinset v).filter (fun u =>
    decide (core Q p i u ∈ S) ≠ decide (core Q p i v ∈ S))).card

def allAttachments (n p : ℕ) : List (Attachment n p) :=
  (List.ofFn fun i : Fin 2 => (List.ofFn fun v : Fin n =>
    List.ofFn fun j : Fin p => (⟨i, v, j⟩ : Attachment n p)).flatten).flatten

/-- Fixed names: all cores, then all middles, then private vertices, lexicographically. -/
def targetVertices : List (TargetVertex Q p) :=
  (List.ofFn fun i : Fin 2 => List.ofFn fun v : Fin n => core Q p i v).flatten ++
  (allAttachments n p).map (middle Q p) ++
  (allAttachments n p).flatMap (fun a => List.ofFn (privateVertex Q p a))

def targetName (x : TargetVertex Q p) : ℕ := (targetVertices Q p).idxOf x

noncomputable def privateSet : Finset (TargetVertex Q p) :=
  Finset.univ.filter (fun x => ∃ a t, x = privateVertex Q p a t)

/-- Ordinary source input for computing a PEO: n,p followed by the adjacency bitmap of Q. -/
def encodePEO : List ℤ := [(n : ℤ), (p : ℤ)] ++
  (List.ofFn fun u : Fin n => List.ofFn fun v : Fin n =>
    if Q.Adj u v then (1 : ℤ) else 0).flatten

/-- A permutation in the fixed target names, with the actual PEO property. -/
def ReportsPEO (S : ℕ) (s : Light.State) : Prop :=
  ∃ xs : List (TargetVertex Q p), IsPEO (target Q p) xs ∧
    WritesList S s (xs.map (fun x => (targetName Q p x : ℤ)))

end IntervalMaxCutEPTAS.Scheme.Supplement


