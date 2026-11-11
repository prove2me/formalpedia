-- Prove2me | Definitions.Def_NuclearTensor_Membership_Covers
-- name    : NuclearTensor_Membership_Covers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:16:33.163992+00:00
-- url     : https://prove2.me/theorems/6de8386c-52ee-4919-8b80-95e4f6c9b109
-- title:
--   Reachable messages, stored witnesses, and terminal enumeration
-- statement:
--   Starting with $R_0=\{1\}$, reachable messages satisfy $R_{j+1}=\{U_{j+1}^{\dagger}(p\otimes x):p\in R_j,\ x\in K_{j+1}\}$. A layerwise $\delta$-cover starts at $S_0=\{1\}$; each retained point is reachable from the preceding retained layer, stores an actual predecessor and feasible local vector, and covers every next reachable point within $\delta$.
--
--   The set-valued definition permits infinite covers, as does Lemma 4.2. Algorithm 2 uses an additional finite, duplicate-free enumeration with predecessor indices. It enumerates retained final messages, computes both the maximum terminal value and an actual feasible maximizer, selects a largest value, and traces the stored witnesses backward. Its terminal objective is
--   $$G(p)=\sup_{x\in K_m}\langle\widetilde M,p\otimes x\rangle.$$
--   Under the compact, nonempty hypotheses used for the exact terminal routine, this supremum is an attained maximum. These data keep reachability and feasible witnesses separate from approximation theorems.
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), pp.15–17, Definition 4.1, Algorithm 2, and Claim 4.4

import Definitions.Def_NuclearTensor_Membership_Compression

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NuclearTensor.Membership

def reachable {ds : List ℕ} (C : PrefixData ds)
    (K : (j : ℕ) → Set (Vec (ds.getD j 0))) : (j : ℕ) → Set (Vec (C.rank j))
  | 0 => {WithLp.toLp 2 (fun _ => 1)}
  | j + 1 => {q | ∃ p ∈ reachable C K j, ∃ x ∈ K j,
      q = mtv (C.embedding j) (outer p x)}

/-- Witness data from Definition 4.1; no approximation property is built into this data. -/
structure CoverData {ds : List ℕ} (C : PrefixData ds) where
  points : (j : ℕ) → Set (Vec (C.rank j))
  previous : (j : ℕ) → {p // p ∈ points (j + 1)} → Vec (C.rank j)
  strategy : (j : ℕ) → {p // p ∈ points (j + 1)} → Vec (ds.getD j 0)

/-- The source layerwise definition. This allows infinite covers for Lemma 4.2;
Algorithm 2 additionally uses finite explicit enumerations. -/
def isCover {ds : List ℕ} (C : PrefixData ds)
    (K : (j : ℕ) → Set (Vec (ds.getD j 0))) (δ : ℝ) (S : CoverData C) : Prop :=
  S.points 0 = {WithLp.toLp 2 (fun _ => 1)} ∧
  ∀ j, j + 1 < ds.length →
    (∀ p : {p // p ∈ S.points (j + 1)},
      S.previous j p ∈ S.points j ∧ S.strategy j p ∈ K j ∧
      p.val = mtv (C.embedding j) (outer (S.previous j p) (S.strategy j p))) ∧
    (∀ p ∈ S.points j, ∀ x ∈ K j, ∃ z ∈ S.points (j + 1),
      ‖z - mtv (C.embedding j) (outer p x)‖ ≤ δ)

/-- An explicit, duplicate-free enumeration, storing each predecessor by its array index. -/
structure FiniteCover {ds : List ℕ} (C : PrefixData ds) where
  count : ℕ → ℕ
  node : (j : ℕ) → Fin (count j) → Vec (C.rank j)
  parent : (j : ℕ) → Fin (count (j + 1)) → ℕ
  factor : (j : ℕ) → Fin (count (j + 1)) → Vec (ds.getD j 0)

def finiteCoverSets {ds : List ℕ} {C : PrefixData ds} (S : FiniteCover C) (j : ℕ) :
    Set (Vec (C.rank j)) := Set.range (S.node j)

def finiteCoverProperty {ds : List ℕ} (C : PrefixData ds)
    (K : (j : ℕ) → Set (Vec (ds.getD j 0))) (δ : ℝ) (S : FiniteCover C) : Prop :=
  S.count 0 = 1 ∧ (∀ t, S.node 0 t = WithLp.toLp 2 (fun _ => 1)) ∧
  (∀ j < ds.length, Function.Injective (S.node j)) ∧
  ∀ j, j + 1 < ds.length →
    (∀ t, S.parent j t < S.count j ∧ S.factor j t ∈ K j ∧
      S.node (j + 1) t = mtv (C.embedding j)
        (outer (WithLp.toLp 2 (fun a =>
          if h : S.parent j t < S.count j then S.node j ⟨S.parent j t, h⟩ a else 0))
          (S.factor j t))) ∧
    (∀ p ∈ finiteCoverSets S j, ∀ x ∈ K j,
      ∃ z ∈ finiteCoverSets S (j + 1), ‖z - mtv (C.embedding j) (outer p x)‖ ≤ δ)

/-- G(p), on any real p, with norm-one terminal tensor and nonempty compact terminal set. -/
def terminalObjective {a b : ℕ} (T : Vec (a * b)) (K : Set (Vec b)) (p : Vec a) : ℝ :=
  sSup ((fun x => inner ℝ T (outer p x)) '' K)

def encodeCoverIntegers {ds : List ℕ} {C : PrefixData ds} (S : FiniteCover C) : List ℤ :=
  ((List.range ds.length).map fun j => (S.count j : ℤ)) ++
  ((List.range (ds.length - 1)).map fun j =>
    List.ofFn (fun t : Fin (S.count (j + 1)) => (S.parent j t : ℤ))).flatten

def encodeCoverReals {ds : List ℕ} {C : PrefixData ds} (S : FiniteCover C) : List ℝ :=
  ((List.range ds.length).map fun j =>
    (List.ofFn (fun t : Fin (S.count j) => encodeVec (S.node j t))).flatten).flatten ++
  ((List.range (ds.length - 1)).map fun j =>
    (List.ofFn (fun t : Fin (S.count (j + 1)) => encodeVec (S.factor j t))).flatten).flatten

def outputsCover {ds : List ℕ} {C : PrefixData ds} (s : Configuration) (S : FiniteCover C) : Prop :=
  outputIntegers s = encodeCoverIntegers S ∧ outputReals s = encodeCoverReals S

def encodeTuple {ds : List ℕ} (x : Tuple ds) : List ℝ :=
  ((List.range ds.length).map fun j => encodeVec (x j)).flatten

def outputsTuple {ds : List ℕ} (s : Configuration) (x : Tuple ds) : Prop :=
  (outputReals s).take ds.sum = encodeTuple x

/-- Witness traceback of Algorithm 2, starting from one retained final-message index. -/
def traceback {ds : List ℕ} {C : PrefixData ds} (S : FiniteCover C)
    (last : ℕ) (x : Tuple ds) : Prop :=
  ∃ path : ℕ → ℕ, path (ds.length - 1) = last ∧
    (∀ j < ds.length, path j < S.count j) ∧
    ∀ j (_h : j + 1 < ds.length), ∃ t : Fin (S.count (j + 1)),
      t.val = path (j + 1) ∧ path j = S.parent j t ∧ x j = S.factor j t

/-- Algorithm 2 terminal enumeration and witness traceback. No guarantee about the
original global objective occurs in this operational output relation. -/
def algorithm2Output {ds : List ℕ} (C : PrefixData ds)
    (K : (j : ℕ) → Set (Vec (ds.getD j 0))) (S : FiniteCover C) (x : Tuple ds) : Prop :=
  ∃ t : Fin (S.count (ds.length - 1)),
    traceback S t.val x ∧ x (ds.length - 1) ∈ K (ds.length - 1) ∧
    (∀ y ∈ K (ds.length - 1),
      inner ℝ (C.tensor (ds.length - 1)) (terminalProduct C x) ≥
        inner ℝ (C.tensor (ds.length - 1))
          (WithLp.toLp 2 (fun i =>
            entry (S.node (ds.length - 1) t)
              (i.val / (ds.drop (ds.length - 1)).prod) *
            entry y (i.val % (ds.drop (ds.length - 1)).prod)))) ∧
    (∀ u : Fin (S.count (ds.length - 1)),
      terminalObjective (C.tensor (ds.length - 1))
        {y : Vec ((ds.drop (ds.length - 1)).prod) |
          ∃ z ∈ K (ds.length - 1), encodeVec y = encodeVec z}
        (S.node (ds.length - 1) u) ≤
      inner ℝ (C.tensor (ds.length - 1)) (terminalProduct C x))

end NuclearTensor.Membership


