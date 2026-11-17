-- Prove2me | Definitions.Def_HypRecov_Supplement_QuerySketchGuarantee
-- name    : HypRecov_Supplement_QuerySketchGuarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:23:34.058132+00:00
-- url     : https://prove2.me/theorems/a7f6b33f-18fc-4e8b-ad43-de07fdefb990
-- title:
--   Deterministic per-vertex additive sketches with simultaneous adaptive queries
-- statement:
--   A **deterministic query sketch** consists of initialization, additive update, state subtraction and query machines. Its state is assembled from one measurement block per occurrence of a vertex in a supplied finite family of sampled sets. The state depends only on the terminal projection vector, and one state must answer every promised query.
--
--   The resource predicate charges every machine stack, including its input and output, to an explicit $\widetilde O(w)$ bit budget and gives uniform polynomial step bounds. It is shared by Theorems A.4 and A.6. A companion predicate gives the deterministic signed-integer sketch interface of Theorem 9.1.
--
--   **Formalization Note** Integer increments are binary encoded. The update-time bound includes their bit length; this only makes explicit the cost of reading the supplied input.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 9.1, p.22 (PDF p.23); Theorems A.4 and A.6, pp.32-34 (PDF pp.33-35)

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_HypRecov_SpaceWithin
import Definitions.Def_HypRecov_encInit
import Definitions.Def_HypRecov_encOut
import Definitions.Def_HypRecov_SketchGuarantee
import Definitions.Def_HypRecov_Supplement_IsCutDegenerate

set_option autoImplicit false

namespace HypRecov.Supplement

open Classical

/-- The budget `C w (1 + ceil(log₂(w+1)))^c`, used for every `O-tilde(w)` statement in
the supplement.  `C,c` are quantified before every problem parameter. -/
def polylogBudget (C c w : ℕ) : ℕ := C * w * (1 + Nat.clog 2 (w + 1)) ^ c

/-- A uniform polynomial time bound.  `ell` is the binary length of an integer increment. -/
def deterministicTimeBudget (C c n r K W ell : ℕ) : ℕ :=
  C * (1 + n * r * K * (1 + Nat.clog 2 (W + 1)) * (1 + ell)) ^ c

/-- A correct complete-edge output: every edge is returned once with all of its vertices. -/
def FullEdgeOutput {n : ℕ} (E : Finset (Finset (Fin n))) (out : List Bool) : Prop :=
  ∃ L : List (Finset (Fin n)), out = HypRecov.encEdges L ∧ L.Nodup ∧ L.toFinset = E

/-- The sampled boundary `D_{R,S}`: original edges meeting both `S` and `R \ S`. -/
def sampledBoundary {n : ℕ} (E : Finset (Finset (Fin n))) (R S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  E.filter (fun e => (e ∩ S).Nonempty ∧ (e ∩ (R \ S)).Nonempty)

/-- The sum `N_R = sum_{R in family} |R|` of vertex occurrences in a finite family. -/
def familySize {n : ℕ} (family : Finset (Finset (Fin n))) : ℕ :=
  ∑ R ∈ family, R.card

/-- Four deterministic machines for a one-pass additive sketch with supplied queries. -/
structure QuerySketch where
  init : Turing.TM2ComputableAux Bool Bool
  upd : Turing.TM2ComputableAux Bool Bool
  sub : Turing.TM2ComputableAux Bool Bool
  query : Turing.TM2ComputableAux Bool Bool

/-- Encode a finite family of vertex subsets. -/
noncomputable def encFamily {n : ℕ} (family : Finset (Finset (Fin n))) : List Bool :=
  HypRecov.encEdges ((List.ofFn fun i =>
    (Fintype.equivFin (Finset (Fin n))).symm i).filter (fun R => R ∈ family))

/-- Inputs for deterministic query-sketch machines. -/
noncomputable def encQueryInit {n : ℕ} (r K : ℕ) (family : Finset (Finset (Fin n))) : List Bool :=
  HypRecov.encParams n r K 0 ++ encFamily family

def encQueryUpd {n : ℕ} (r K : ℕ) (state : List Bool) (A : Finset (Fin n))
    (Delta : ℤ) : List Bool :=
  HypRecov.encParams n r K 0 ++ HypRecov.encBits state ++ HypRecov.encSet A ++ HypRecov.encInt Delta

def encQuerySub (n r K : ℕ) (state state' : List Bool) : List Bool :=
  HypRecov.encParams n r K 0 ++ HypRecov.encBits state ++ HypRecov.encBits state'

def encQuery {n : ℕ} (r K : ℕ) (state : List Bool) (R S : Finset (Fin n)) : List Bool :=
  HypRecov.encParams n r K 0 ++ HypRecov.encBits state ++ HypRecov.encSet R ++ HypRecov.encSet S

/-- Concatenation of one measurement block for every vertex occurrence `v in R` in the supplied
finite family. -/
noncomputable def encPerVertexState {n : ℕ} (family : Finset (Finset (Fin n)))
    (cell : Finset (Fin n) → Fin n → List Bool) : List Bool :=
  ((List.ofFn fun i => (Fintype.equivFin (Finset (Fin n))).symm i).filter
      (fun R => R ∈ family)).flatMap (fun R =>
    (R.sort (· ≤ ·)).flatMap (fun v => true :: HypRecov.encBits (cell R v))) ++ [false]

/-- A deterministic additive sketch whose single terminal state answers every promised query.
The state is a function of the terminal projection vector, so the guarantee is simultaneous and
continues to hold for adaptively selected queries.  All stacks, including input and output, count
toward the displayed space budget. -/
def QuerySketchGuarantee (A : QuerySketch) (C c n r K q spaceWeight : ℕ)
    (family : Finset (Finset (Fin n)))
    (Promised : Finset (Finset (Fin n)) → Finset (Fin n) → Finset (Fin n) → Prop)
    (Answer : Finset (Finset (Fin n)) → Finset (Fin n) → Finset (Fin n) → List Bool → Prop) : Prop :=
  ∃ (sk : (Finset (Fin n) → ℤ) → List Bool)
      (cell : (Finset (Fin n) → ℤ) → Finset (Fin n) → Fin n → List Bool),
    (∀ y, sk y = encPerVertexState family (cell y)) ∧
    (∀ y, (sk y).length ≤ polylogBudget C c spaceWeight) ∧
    SpikyCVP.RunsWithin A.init (encQueryInit r K family) (sk 0)
      (polylogBudget C c spaceWeight) ∧
    HypRecov.SpaceWithin A.init (encQueryInit r K family) (polylogBudget C c spaceWeight) ∧
    (∀ (y : Finset (Fin n) → ℤ) (B : Finset (Fin n)) (Delta : ℤ), B.card = q →
      SpikyCVP.RunsWithin A.upd (encQueryUpd r K (sk y) B Delta)
          (sk (y + Pi.single B Delta))
          (deterministicTimeBudget C c n r K 1 (Nat.size Delta.natAbs)) ∧
      HypRecov.SpaceWithin A.upd (encQueryUpd r K (sk y) B Delta)
          (polylogBudget C c spaceWeight + (encQueryUpd r K (sk y) B Delta).length)) ∧
    (∀ y y' : Finset (Fin n) → ℤ,
      SpikyCVP.RunsWithin A.sub (encQuerySub n r K (sk y) (sk y')) (sk (y - y'))
          (deterministicTimeBudget C c n r K 1 0) ∧
      HypRecov.SpaceWithin A.sub (encQuerySub n r K (sk y) (sk y'))
          (polylogBudget C c spaceWeight + (encQuerySub n r K (sk y) (sk y')).length)) ∧
    ∀ (E : Finset (Finset (Fin n))), IsUniform r E →
      ∀ sigma : List (Finset (Fin n) × ℤ), HypRecov.IsValidStream E q sigma →
      ∀ R S : Finset (Fin n), Promised E R S → ∃ out : List Bool,
        SpikyCVP.RunsWithin A.query (encQuery r K (sk (HypRecov.net sigma)) R S) out
            (deterministicTimeBudget C c n r K 1 0) ∧
        HypRecov.SpaceWithin A.query (encQuery r K (sk (HypRecov.net sigma)) R S)
            (polylogBudget C c spaceWeight) ∧ Answer E R S out

/-- A deterministic additive sketch for arbitrary signed integer vectors on the `r`-uniform slice.
The decoder returns the entire vector by its nonzero coordinates and signed values. -/
def VectorSketchGuarantee (A : HypRecov.LinearSketch) (C c n r K W q a L : ℕ) : Prop :=
  ∃ sk : (Finset (Fin n) → ℤ) → List Bool,
    let S := C * K * r * Nat.clog 2 (n + 1) * (a + L)
    (∀ y, (sk y).length ≤ S) ∧
    SpikyCVP.RunsWithin A.init (HypRecov.encInit n r K W []) (sk 0)
      (deterministicTimeBudget C c n r K W 0) ∧
    HypRecov.SpaceWithin A.init (HypRecov.encInit n r K W []) S ∧
    (∀ (y : Finset (Fin n) → ℤ) (B : Finset (Fin n)) (Delta : ℤ), B.card = q →
      SpikyCVP.RunsWithin A.upd (HypRecov.encUpd r K W (sk y) B Delta)
          (sk (y + Pi.single B Delta))
          (deterministicTimeBudget C c n r K W (Nat.size Delta.natAbs)) ∧
      HypRecov.SpaceWithin A.upd (HypRecov.encUpd r K W (sk y) B Delta)
          (S + (HypRecov.encUpd r K W (sk y) B Delta).length)) ∧
    (∀ y y' : Finset (Fin n) → ℤ,
      SpikyCVP.RunsWithin A.sub (HypRecov.encSub n r K W (sk y) (sk y')) (sk (y - y'))
          (deterministicTimeBudget C c n r K W 0) ∧
      HypRecov.SpaceWithin A.sub (HypRecov.encSub n r K W (sk y) (sk y'))
          (S + (HypRecov.encSub n r K W (sk y) (sk y')).length)) ∧
    ∀ z : Finset (Fin n) → ℤ, IsSparseBounded r K W z →
      ∀ sigma : List (Finset (Fin n) × ℤ), IsValidVectorStream r q z sigma →
      SpikyCVP.RunsWithin A.dec (HypRecov.encDec n r K W (sk (HypRecov.net sigma)))
          (encIntegerVector r z) (deterministicTimeBudget C c n r K W 0) ∧
      HypRecov.SpaceWithin A.dec (HypRecov.encDec n r K W (sk (HypRecov.net sigma))) S

end HypRecov.Supplement


