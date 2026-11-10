-- Prove2me | Definitions.Def_MerkleROM_VerifierLowerBound_oracle
-- name    : MerkleROM_VerifierLowerBound_oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T22:29:45.427265+00:00
-- url     : https://prove2.me/theorems/dfbfdbfb-3628-40a7-83f0-c8145db7442c
-- title:
--   Consistent adaptive random-oracle execution
-- statement:
--   Let $X$ be an arbitrary set of oracle inputs and let $Y$ be its answer set. Adaptive algorithms use the published probe-tree interface: each internal node selects a query using previous replies, and each leaf returns a result. Randomized algorithms are probability distributions over these trees, chosen independently of the oracle. A query bound counts every call on every execution, including repeated calls.
--
--   For $\lambda$-bit answers, a previously unseen input receives a uniform answer and a repeated input receives its cached answer. Thus
--
--   $$R:X\longrightarrow\{0,1\}^{\lambda}$$
--
--   has the uniform finite-query cylinder law, with no finiteness assumption on $X$. For the vector-commitment domain $X=\{0,1\}^{\theta}$, a full uniform oracle is also defined, together with its uniform law conditioned on any consistent partial table. Event probabilities are computed from normalized probability mass functions. The fixed selector uses a well-order chosen independently of the oracle.
--
--   This layer supplies execution, query tables, sequential composition and actual event probabilities to both the security games and the disjoint product theorem. It contains no security estimate or lower bound.
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, pp. 14–15, §4 and Fact 1; p.24, §6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Mathlib
import Definitions.Def_DynOracleConn_ProbeTree

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev StringBits := List Bool
abbrev Tree (X Y A : Type) := DynOracleConn.ProbeTree X Y A
abbrev Table (X Y : Type) := List (X × Y)

variable {X Y A B : Type}

/-- All oracle calls count, including repetitions and calls on dishonest inputs. -/
def Bounded (q : ℕ) (a : Tree X Y A) : Prop :=
  ∀ R : X → Y, a.cost R ≤ q

def RandomBounded (q : ℕ) (a : PMF (Tree X Y A)) : Prop :=
  ∀ t ∈ a.support, Bounded q t

def treeMap (f : A → B) : Tree X Y A → Tree X Y B
  | .done a => .done (f a)
  | .probe x next => .probe x (fun y => treeMap f (next y))

def treeBind (a : Tree X Y A) (f : A → Tree X Y B) : Tree X Y B :=
  match a with
  | .done v => f v
  | .probe x next => .probe x (fun y => treeBind (next y) f)

def readQueries : List X → Tree X Y (Table X Y)
  | [] => .done []
  | x :: xs => .probe x (fun y => treeMap (fun t => (x,y) :: t) (readQueries xs))

def Consistent (T : Table X Y) : Prop :=
  ∃ R : X → Y, ∀ z ∈ T, R z.1 = z.2

def Extends (R : X → Y) (T : Table X Y) : Prop :=
  ∀ z ∈ T, R z.1 = z.2

def tableDomain (T : Table X Y) : Finset X := by
  classical
  exact (T.map Prod.fst).toFinset

/-- Probability of a predicate in a normalized PMF, with no integral default. -/
def probability (μ : PMF A) (P : A → Prop) : ℝ := by
  classical
  exact ((μ.map (fun a => decide (P a))) true).toReal

/-- Lazy uniform oracle execution; cached answers make repeated calls consistent.
There is no finiteness assumption on the input set X. -/
def lazyRun {lam : ℕ} : Tree X (Bits lam) A → Table X (Bits lam) →
    PMF (A × Table X (Bits lam))
  | .done a, T => pure (a,T)
  | .probe x next, T => by
    classical
    exact match T.lookup x with
    | some y => lazyRun (next y) T
    | none => (PMF.uniformOfFintype (Bits lam)).bind fun y => lazyRun (next y) ((x,y)::T)

def randomRun {lam : ℕ} (a : PMF (Tree X (Bits lam) A)) :
    PMF (A × Table X (Bits lam)) := a.bind (fun t => lazyRun t [])

def uniformOracle (theta lam : ℕ) : PMF (Bits theta → Bits lam) :=
  PMF.uniformOfFintype (Bits theta → Bits lam)

/-- Uniform extension exists precisely for a consistent table. -/
def extendingOracle {theta lam : ℕ} (T : Table (Bits theta) (Bits lam)) (hT : Consistent T) :
    PMF (Bits theta → Bits lam) := by
  classical
  exact (uniformOracle theta lam).filter {R | Extends R T} (by
    obtain ⟨R,hR⟩ := hT
    exact ⟨R,hR,by simp [uniformOracle]⟩)

/-- A fixed tie-breaking choice, made independently of the oracle. -/
def fixedChoice {α : Type} (P : α → Prop) (h : ∃ a, P a) : α :=
  (IsWellFounded.wf (r := @WellOrderingRel α)).min {a | P a} h

end MerkleROM.VerifierLowerBound


