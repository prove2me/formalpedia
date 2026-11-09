-- Prove2me | Definitions.Def_TestingEstimation_Dense_GraphModel
-- name    : TestingEstimation_Dense_GraphModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:02.086105+00:00
-- url     : https://prove2.me/theorems/633591c6-4419-4121-9346-93c654a5685d
-- title:
--   Dense graphs, edit distance, and adaptive oracle procedures
-- statement:
--   For each finite order $n$, an ordinary graph assigns a bit to each unordered pair of distinct vertices, and a weighted graph assigns an arbitrary real weight in $[0,1]$. A property $P$ is a family $P_n$ closed under every permutation of the vertices. The normalized edit distance is
--
--   $$d(G,H)=\binom n2^{-1}\sum_e |G(e)-H(e)|.$$
--
--   The distance to $P$ is the minimum over $P_n$ when this set is nonempty and $n\ge2$, is zero for a nonempty property at order below two, and is one when $P_n$ is empty. The empty-property case takes precedence.
--
--   An oracle procedure is a finite uniform random choice of a finite adaptive query tree. Each internal node asks for one input adjacency bit, and its next node depends on that answer; each leaf contains an output. The query count is the number of visited query nodes. A family of procedures has bound $B$ if every execution on every graph at every order uses at most $B$ queries. Boolean true means acceptance. A tester accepts members and rejects graphs with distance at least $\varepsilon$, each with probability at least $2/3$. An estimator succeeds when its real output differs from the distance by at most $\varepsilon$, again with probability at least $2/3$.
--
--   A canonical rejection rule on $s$ vertices is a rational-valued table $f$ with values between zero and one. Its graph rejection probability is the uniform average of $f(G[v])$ over ordered injective $s$-tuples $v$. Symmetry and the two canonical accuracy guarantees are separate predicates; they are not assertions installed in the algorithm data. The logarithm used throughout is $\log_2$.
--
--   **Formalization Note** Vertices are `Fin n`, and a pair is represented once by its increasing endpoints. Finite uniform seeds express every rational finite random law, including uniform subset sampling. All procedures are selected before the unknown graph. Empty finite averages are defined as zero; no algorithm has an empty seed set.
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), §§1.1–1.2 and 3, pp. 2–3, 7–8 (PDF pages equal printed pages)

import Mathlib

noncomputable section

namespace TestingEstimation.Dense
attribute [local instance] Classical.propDecidable

/-- An unordered pair, represented once using the order on the labelled vertices. -/
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Graph (n : ℕ) := Edge n → Bool
abbrev UnitWeight := Set.Icc (0 : ℝ) 1
abbrev WGraph (n : ℕ) := Edge n → UnitWeight
abbrev PairFunction (n : ℕ) := Edge n → ℝ

def bit (b : Bool) : ℝ := if b then 1 else 0

def weighted {n : ℕ} (G : Graph n) : WGraph n := fun e =>
  if G e then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩

def values {n : ℕ} (W : WGraph n) : PairFunction n := fun e => W e

def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

def mkEdge {n : ℕ} (u v : Fin n) (h : u ≠ v) : Edge n :=
  if huv : u < v then ⟨(u,v), huv⟩ else ⟨(v,u), by change v < u; exact lt_of_le_of_ne (le_of_not_gt huv) (Ne.symm h)⟩

def mapEdge {s n : ℕ} (v : Fin s ↪ Fin n) (e : Edge s) : Edge n :=
  mkEdge (v e.val.1) (v e.val.2) (fun h => (ne_of_lt e.property) (v.injective h))

def induced {s n : ℕ} (G : Graph n) (v : Fin s ↪ Fin n) : Graph s :=
  fun e => G (mapEdge v e)

def inducedW {s n : ℕ} (W : WGraph n) (v : Fin s ↪ Fin n) : WGraph s :=
  fun e => W (mapEdge v e)

/-- All finite orders; permutation closure is the definition of a graph property. -/
structure Property where
  graphs : (n : ℕ) → Set (Graph n)
  iso : ∀ n (G : Graph n) (σ : Equiv.Perm (Fin n)),
    G ∈ graphs n ↔ induced G σ.toEmbedding ∈ graphs n

def editDistance {n : ℕ} (G H : Graph n) : ℝ :=
  mean (fun e => |bit (G e) - bit (H e)|)

/-- Empty-property branch precedes the small-order branch. -/
def distance {n : ℕ} (P : Property) (G : Graph n) : ℝ :=
  if (P.graphs n).Nonempty then
    if n < 2 then 0 else sInf {r | ∃ H ∈ P.graphs n, editDistance G H = r}
  else 1

/-- Finite adaptive query trees. A leaf sees only the answers on its path. -/
inductive QueryTree (n : ℕ) (α : Type) where
  | leaf : α → QueryTree n α
  | query : Edge n → (Bool → QueryTree n α) → QueryTree n α

def QueryTree.run {n : ℕ} {α : Type} (G : Graph n) : QueryTree n α → α
  | .leaf a => a
  | .query e next => (next (G e)).run G

def QueryTree.queries {n : ℕ} {α : Type} (G : Graph n) : QueryTree n α → ℕ
  | .leaf _ => 0
  | .query e next => 1 + (next (G e)).queries G

/-- Uniform finite seeds encode every finite rational random law. -/
structure Procedure (n : ℕ) (α : Type) where
  seeds : ℕ
  positive : 0 < seeds
  tree : Fin seeds → QueryTree n α

def probability {n : ℕ} {α : Type} (A : Procedure n α) (G : Graph n)
    (event : α → Prop) : ℝ :=
  mean (fun r => if event ((A.tree r).run G) then 1 else 0)

def HasQueryBound {α : Type} (A : (n : ℕ) → Procedure n α) (B : ℝ) : Prop :=
  ∀ n (G : Graph n) r, ((A n).tree r).queries G ≤ B

/-- Boolean true means accept. -/
def IsTester (P : Property) (ε : ℝ) (A : (n : ℕ) → Procedure n Bool) : Prop :=
  ∀ n (G : Graph n),
    (G ∈ P.graphs n → (2:ℝ)/3 ≤ probability (A n) G (fun b => b = true)) ∧
    (ε ≤ distance P G → (2:ℝ)/3 ≤ probability (A n) G (fun b => b = false))

def IsEstimator (P : Property) (ε : ℝ) (A : (n : ℕ) → Procedure n ℝ) : Prop :=
  ∀ n (G : Graph n),
    (2:ℝ)/3 ≤ probability (A n) G (fun x => |x - distance P G| ≤ ε)

/-- Exact rational conditional rejection probabilities. -/
structure Rule (s : ℕ) where
  reject : Graph s → ℚ
  bounds : ∀ J, 0 ≤ reject J ∧ reject J ≤ 1

def ruleValue {s : ℕ} (f : Rule s) (J : Graph s) : ℝ := f.reject J

def SymmetricRule {s : ℕ} (f : Rule s) : Prop :=
  ∀ J (σ : Equiv.Perm (Fin s)), f.reject (induced J σ.toEmbedding) = f.reject J

def graphRej {s n : ℕ} (f : Rule s) (G : Graph n) : ℝ :=
  mean (fun v : Fin s ↪ Fin n => ruleValue f (induced G v))

/-- Condition N2 for the fixed original order n. -/
def CanonicalGuarantees {s : ℕ} (P : Property) (τ : ℝ) (n : ℕ) (f : Rule s) : Prop :=
  ∀ G : Graph n,
    (G ∈ P.graphs n → graphRej f G ≤ τ) ∧
    (τ ≤ distance P G → (2:ℝ)/3 ≤ graphRej f G)

def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

end TestingEstimation.Dense


