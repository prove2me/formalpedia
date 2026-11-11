-- Prove2me | Definitions.Def_SubspaceEvasion312_Explicit_effective
-- name    : SubspaceEvasion312_Explicit_effective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:47.2352+00:00
-- url     : https://prove2.me/theorems/6f27d072-08aa-4487-b781-16330d55191d
-- title:
--   Operational encoders, graph construction and membership
-- statement:
--   For $x\in F^k$, let $\operatorname{data}(x)$ be its ordered coordinate list; blocks are serialized in block order. For a linear encoder $E$, the basis data are the concatenated images of the $k$ standard basis vectors.
--
--   A code family has fixed programs that, on block length $m$, generate that basis and its dimension, and evaluate $E_m$ on every message. Both programs start from empty work memory and satisfy their stated time and register bounds for every $m\ge m_0$. The encoder's image and dimension are asserted separately in the theorem conclusions.
--
--   For $g:F^k\to(F^b)^m$, the three graph programs respectively evaluate $g$, output the indexed graph point $(x,g(x))$, and output the true membership indicator on every $(x,y)$:
--
--   $$\mathbf 1_{G^g}(x,y)=\mathbf 1[y=g(x)].$$
--
--   The $k$ field symbols of a message are the usual base-$q$ index digits in a fixed ordering of the field. The canonical graph bijection makes this an indexed construction, rather than exponential enumeration of the set. All setup is charged on each query. Local conditional-probability bookkeeping is restricted to a finite word bound $q^{(s+b+r+d+1)^3}$. These interfaces preserve the three separate effectiveness clauses in Theorem 8.
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), complexity conventions, Theorem 8 and proof; Theorem 9 and proof, printed p. 7 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc; printed pp. 8–9 (PDF pp. 9–10)

import Definitions.Def_SubspaceEvasion312_Explicit_algebra
import Definitions.Def_SubspaceEvasion312_Explicit_machine

noncomputable section

namespace SubspaceEvasion312.Explicit
open scoped BigOperators ENNReal

def vectorData {F : Type} {n : ℕ} (x : Vec F n) : List F := List.ofFn x

def blockData {F : Type} {s m : ℕ} (x : Blocks F s m) : List F :=
  (List.ofFn (fun i => vectorData (x i))).flatten

def basisData {F : Type} [Field F] {s m k : ℕ}
    (E : Vec F k →ₗ[F] Blocks F s m) : List F :=
  (List.ofFn (fun j : Fin k => blockData (E (Pi.single j 1)))).flatten

/-- A family is computed by two fixed programs, including its basis and encoder.
B bounds every natural register, so B polynomial in m gives logarithmic words. -/
def CodeAlgorithms {F : Type} [Field F] {s : ℕ} (k : ℕ → ℕ)
    (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m)
    (gen enc : Program F) (T B : ℕ → ℕ) (m₀ : ℕ) : Prop :=
  ∀ m ≥ m₀,
    RunsWithin gen [m] [] (T m) (B m) (basisData (E m)) [k m] ∧
    ∀ x, RunsWithin enc [m] (vectorData x) (T m) (B m) (blockData (E m x))

/-- An evaluator includes all setup on every invocation. -/
def Evaluates {F : Type} [Field F] {a b : ℕ} (P : Program F)
    (f : Vec F a → Vec F b) (T B : ℕ) : Prop :=
  ∀ x, RunsWithin P [] (vectorData x) T B (vectorData (f x))

def EvaluatesBlocks {F : Type} [Field F] {a b m : ℕ} (P : Program F)
    (f : Vec F a → Blocks F b m) (T B : ℕ) : Prop :=
  ∀ x, RunsWithin P [] (vectorData x) T B (blockData (f x))

/-- The standard base-q input digits are field symbols. An alphabet ordering
identifies these k digits with the integers 0,...,q^k−1 (or 1,...,q^k).
The graph equivalence establishes the indexed bijection; its evaluation is charged. -/
def GraphAlgorithms {F : Type} [Field F] {k b m : ℕ}
    (g : Vec F k → Blocks F b m) (eval index member : Program F)
    (T B : ℕ) : Prop := by
  classical
  exact EvaluatesBlocks eval g T B ∧
  (∀ x, RunsWithin index [] (vectorData x) T B (vectorData x ++ blockData (g x))) ∧
  (∀ x y, RunsWithin member [] (vectorData x ++ blockData y) T B
    [if y = g x then 1 else 0])

/-- The rational local-score computation in Theorem 9 may use counters with
O((s+b+r+d)^3 log q) bits. This is a word-RAM bound, not an oracle. -/
def localWordBound (q s b r d : ℕ) : ℕ := q ^ ((s + b + r + d + 1) ^ 3)

end SubspaceEvasion312.Explicit


