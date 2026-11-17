-- Prove2me | Definitions.Def_HypRecov_Supplement_LinkRecord
-- name    : HypRecov_Supplement_LinkRecord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:25:11.214808+00:00
-- url     : https://prove2.me/theorems/da8b1948-03dc-4cdb-a719-011a812eb703
-- title:
--   Complete low-codegree link records with globally distinct edge tags
-- statement:
--   For an unordered pair $f$, its **link** is $L_f=\{e\in E:f\subseteq e\}$ and its codegree is $w_f=|L_f|$. A complete link record stores $f$, the exact integer $w_f$, and one short tag for each original edge in $L_f$.
--
--   A valid low-link output contains at most one record per pair, every returned record has $1\le w_f<M$, and its tag list is exactly the tagged original link. All represented tags are nonzero and distinct globally. The coverage predicate requires a record for every low-codegree two-section pair crossing every hypergraph cut of value at most $K$.
--
--   **Formalization Note** Pairs are two-element `Finset`s. Field tags are stored through injective nonzero natural-number codes, so their complete binary representations are charged to the state and output budget.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Appendix F, p.41 (PDF p.42), Theorem F.1

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_encNat
import Definitions.Def_HypRecov_Supplement_QuerySketchGuarantee
import Definitions.Def_PunctSketch_coinProb

set_option autoImplicit false

namespace HypRecov.Supplement

/-- The original link `L_f` of an unordered vertex pair represented as a two-element `Finset`. -/
def link {n : ℕ} (E : Finset (Finset (Fin n))) (f : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  E.filter (fun e => f ⊆ e)

/-- A complete low-link record: the pair, its exact integer codegree, and the short tags of all
original edges in its link. -/
structure LinkRecord (n : ℕ) where
  pair : Finset (Fin n)
  codegree : ℕ
  tags : List ℕ
  deriving DecidableEq

/-- Binary encoding of a family of link records. -/
def encLinkRecords {n : ℕ} (records : List (LinkRecord n)) : List Bool :=
  records.flatMap (fun R => true ::
    (HypRecov.encSet R.pair ++ HypRecov.encNat R.codegree ++
      R.tags.flatMap (fun t => true :: HypRecov.encNat t) ++ [false])) ++ [false]

/-- Every returned link record is valid, the tags identify exactly its original link, all tags are
nonzero and globally distinct on every original edge appearing in a returned record, and every
low-codegree pair crossing every cut of value at most `K` is returned. -/
def CorrectLowLinks {n : ℕ} (E : Finset (Finset (Fin n))) (K M tagCap : ℕ)
    (out : List Bool) : Prop :=
  ∃ (records : List (LinkRecord n)) (tag : Finset (Fin n) → ℕ),
    out = encLinkRecords records ∧ (records.map LinkRecord.pair).Nodup ∧
    (∀ R ∈ records,
      R.pair.card = 2 ∧
      R.codegree = (link E R.pair).card ∧ 1 ≤ R.codegree ∧ R.codegree < M ∧
      R.tags.Nodup ∧ R.tags.toFinset = (link E R.pair).image tag) ∧
    (∀ e ∈ records.toFinset.biUnion (fun R => link E R.pair), tag e ≠ 0) ∧
    Set.InjOn tag ↑(records.toFinset.biUnion (fun R => link E R.pair)) ∧
    (∀ S : Finset (Fin n), HypRecov.cut E S ≤ K →
      ∀ f : Finset (Fin n), f.card = 2 → (f ∩ S).Nonempty → (f \ S).Nonempty →
        1 ≤ (link E f).card → (link E f).card < M → ∃ R ∈ records, R.pair = f) ∧
    (records.map (fun R => R.tags.length)).sum ≤ tagCap

/-- Every successfully parsed decoder output obeys the deterministic stored-tag cap. -/
def BoundedLinkOutput {n : ℕ} (out : List Bool) (tagCap : ℕ) : Prop :=
  ∀ records : List (LinkRecord n), out = encLinkRecords records →
    (records.map (fun R => R.tags.length)).sum ≤ tagCap

/-- The randomized linear-sketch interface for Theorem F.1, including the off-good-event cap on
the total number of stored tags in every non-aborted decoder output. -/
def LowLinkSketchGuarantee (A : HypRecov.LinearSketch) (C c n r K M q : ℕ) (eta : ℝ) : Prop :=
  1 ≤ A.M n r K ⌈1 / eta⌉₊ ∧
  ∃ sk : (Fin (A.N n r K ⌈1 / eta⌉₊) → Fin (A.M n r K ⌈1 / eta⌉₊)) →
      (Finset (Fin n) → ℤ) → List Bool,
    (∀ omega,
      (∀ y, (sk omega y).length ≤ HypRecov.spaceBudget C c (n * r * K) eta) ∧
      SpikyCVP.RunsWithin A.init
        (HypRecov.encInit n r K ⌈1 / eta⌉₊ (HypRecov.coinList omega)) (sk omega 0)
        (HypRecov.timeBudget C c (n * r * K) eta 0) ∧
      HypRecov.SpaceWithin A.init
        (HypRecov.encInit n r K ⌈1 / eta⌉₊ (HypRecov.coinList omega))
        (HypRecov.spaceBudget C c (n * r * K) eta) ∧
      (∀ (y : Finset (Fin n) → ℤ) (B : Finset (Fin n)) (Delta : ℤ), B.card = q →
        SpikyCVP.RunsWithin A.upd (HypRecov.encUpd r K ⌈1 / eta⌉₊ (sk omega y) B Delta)
          (sk omega (y + Pi.single B Delta))
          (HypRecov.timeBudget C c (n * r * K) eta (Nat.size Delta.natAbs)) ∧
        HypRecov.SpaceWithin A.upd (HypRecov.encUpd r K ⌈1 / eta⌉₊ (sk omega y) B Delta)
          (HypRecov.spaceBudget C c (n * r * K) eta +
            (HypRecov.encUpd r K ⌈1 / eta⌉₊ (sk omega y) B Delta).length)) ∧
      (∀ y y' : Finset (Fin n) → ℤ,
        SpikyCVP.RunsWithin A.sub
          (HypRecov.encSub n r K ⌈1 / eta⌉₊ (sk omega y) (sk omega y'))
          (sk omega (y - y')) (HypRecov.timeBudget C c (n * r * K) eta 0) ∧
        HypRecov.SpaceWithin A.sub
          (HypRecov.encSub n r K ⌈1 / eta⌉₊ (sk omega y) (sk omega y'))
          (HypRecov.spaceBudget C c (n * r * K) eta +
            (HypRecov.encSub n r K ⌈1 / eta⌉₊ (sk omega y) (sk omega y')).length)) ∧
      (∀ y : Finset (Fin n) → ℤ, ∃ out : List Bool,
        SpikyCVP.RunsWithin A.dec (HypRecov.encDec n r K ⌈1 / eta⌉₊ (sk omega y)) out
          (HypRecov.timeBudget C c (n * r * K) eta 0) ∧
        HypRecov.SpaceWithin A.dec (HypRecov.encDec n r K ⌈1 / eta⌉₊ (sk omega y))
          (HypRecov.spaceBudget C c (n * r * K) eta) ∧
        BoundedLinkOutput (n := n) out (HypRecov.spaceBudget C c (n * r * K) eta))) ∧
    ∀ E : Finset (Finset (Fin n)), IsUniform r E →
      ∀ sigma : List (Finset (Fin n) × ℤ), HypRecov.IsValidStream E q sigma →
      PunctSketch.coinProb (fun omega : Fin (A.N n r K ⌈1 / eta⌉₊) → Fin (A.M n r K ⌈1 / eta⌉₊) =>
        ¬ ∃ out : List Bool,
          SpikyCVP.RunsWithin A.dec (HypRecov.encDec n r K ⌈1 / eta⌉₊
            (sk omega (HypRecov.net sigma))) out (HypRecov.timeBudget C c (n * r * K) eta 0) ∧
          CorrectLowLinks E K M (HypRecov.spaceBudget C c (n * r * K) eta) out) ≤ eta

end HypRecov.Supplement


