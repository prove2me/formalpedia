-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_limitedCache
-- name    : NonuniformCompetitive_Snoopy_Supplement_limitedCache
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:58:42.327951+00:00
-- url     : https://prove2.me/theorems/279b4b82-0355-48bb-9147-20b77311b53f
-- title:
--   Direct-mapped limited snoopy-cache hardware and operational costs
-- statement:
--   For a block-address type $B$ and $n$ processors, processor $i$ has a positive finite number $m_i$ of lines and a fixed hash $h_i:B\to\{0,\ldots,m_i-1\}$. A state records each resident and last-resident tag, every private owner and each dirty block. Validity enforces hash placement, exclusive private ownership and dirty-private coherence. Empty initial caches and all other valid finite initial cache contents are represented.
--
--   A fetch costs $p$ plus any dirty collision writeback; a dirty eviction costs $p$; sharing broadcasts cost $p$; invalidating other copies to privatize a present block costs zero. A broadcast permits any subset of snoopers, but each recipient must have an empty matching line whose last resident was that block. A private write costs zero and marks dirty; a shared write costs one. A read must find a valid resident, so a missing read requires a fetch. Before-request controls use only the preceding history; moment controls on a write are empty. All processors and blocks share the full input history, permitting arbitrary interleavings.
--
--   Offline cost is the infimum of the costs of all full-information control schedules respecting the same hashes and write timing. It is taken in $[0,\infty]$ and is finite on admissible finite inputs: the policy that fetches on each read and keeps blocks shared supplies a finite comparison schedule. For a mixed causal policy,
--   $$\mathbb E C_A(\sigma)\le c\,C_{\rm opt}(\sigma)+a$$
--   uses fixed-input cost measurability and one real additive constant. The address type remains unrestricted here; Theorem 6 requires only that it be nonempty, so finite and infinite address spaces are both covered. Preparatory reads remain in force until another processor accesses the block or the processor accesses a colliding block, the two write-run termination cases on p.555.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, §3.3, pp.554–556

import Mathlib

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory
open scoped NNReal ENNReal

/-- Direct-mapped hardware. The address type is not truncated to a finite set.
Each processor has its own fixed positive finite number of lines and hash. -/
structure LimitedHardware (B : Type) (n : ℕ) where
  lines : Fin n → ℕ
  positive : ∀ i, 0 < lines i
  hash : ∀ i, B → Fin (lines i)

/-- Invalidating or evicting a block empties its line but retains its last tag.
A clean exclusive copy need not be written back on eviction. A private write
sets dirty; a block broadcast updates memory and clears dirty. -/
structure LimitedState {B : Type} {n : ℕ} (H : LimitedHardware B n) where
  resident : ∀ i, Fin (H.lines i) → Option B
  last : ∀ i, Fin (H.lines i) → Option B
  privateOwner : B → Option (Fin n)
  dirty : B → Bool

def LimitedState.Valid {B : Type} {n : ℕ} (H : LimitedHardware B n)
    (q : LimitedState H) : Prop :=
  (∀ i l b, q.resident i l = some b → H.hash i b = l ∧ q.last i l = some b) ∧
  (∀ i l b, q.last i l = some b → H.hash i b = l) ∧
  (∀ b i, q.privateOwner b = some i →
    q.resident i (H.hash i b) = some b ∧
      ∀ j, j ≠ i → q.resident j (H.hash j b) ≠ some b) ∧
  (∀ b, q.dirty b = true → (q.privateOwner b).isSome)

/-- Ordinary empty initial caches, with current main-memory copies. Arbitrary
valid initial contents are allowed in the theorem as well. -/
def limitedEmpty {B : Type} {n : ℕ} (H : LimitedHardware B n) : LimitedState H where
  resident := fun _ _ => none
  last := fun _ _ => none
  privateOwner := fun _ => none
  dirty := fun _ => false

inductive LimitedRequest (B : Type) (n : ℕ) where
  | read (processor : Fin n) (block : B)
  | write (processor : Fin n) (block : B)
  deriving DecidableEq

/-- Controls may be issued before or after any request, and at the moment of a
read. `fetch` pays a block-transfer cost and any dirty collision cost; `share`
broadcasts; `privatize` invalidates other copies at zero bus cost. The Boolean
mask allows any subset of eligible snoopers, including all of them. -/
inductive LimitedControl {B : Type} {n : ℕ} (H : LimitedHardware B n) where
  | fetch (processor : Fin n) (block : B) (snoop : Fin n → Bool)
  | share (block : B) (snoop : Fin n → Bool)
  | privatize (processor : Fin n) (block : B)
  | evict (processor : Fin n) (line : Fin (H.lines processor)) (snoop : Fin n → Bool)

noncomputable def limitedBroadcast {B : Type} [DecidableEq B] {n : ℕ}
    {H : LimitedHardware B n} (q : LimitedState H) (b : B) (mask : Fin n → Bool) :
    LimitedState H :=
  { q with
    resident := fun i l =>
      if l = H.hash i b ∧ q.resident i l = none ∧ q.last i l = some b ∧ mask i = true
      then some b else q.resident i l
    privateOwner := Function.update q.privateOwner b none
    dirty := Function.update q.dirty b false }

noncomputable def limitedEvict {B : Type} [DecidableEq B] {n : ℕ}
    {H : LimitedHardware B n} (p : ℕ) (q : LimitedState H) (i : Fin n)
    (l : Fin (H.lines i)) (mask : Fin n → Bool) : LimitedState H × ℝ≥0∞ :=
  match q.resident i l with
  | none => (q, 0)
  | some b =>
      let writeback := q.privateOwner b = some i ∧ q.dirty b = true
      let q' := if writeback then limitedBroadcast q b mask else q
      ({ q' with
          resident := fun j k => if h : j = i then
            if h ▸ k = l then none else q'.resident j k else q'.resident j k
          privateOwner := if q.privateOwner b = some i then
            Function.update q'.privateOwner b none else q'.privateOwner },
        if writeback then (p : ℝ≥0∞) else 0)

noncomputable def limitedControl {B : Type} [DecidableEq B] {n : ℕ}
    {H : LimitedHardware B n} (p : ℕ) (q : LimitedState H) :
    LimitedControl H → LimitedState H × ℝ≥0∞
  | .evict i l mask => limitedEvict p q i l mask
  | .share b mask => (limitedBroadcast q b mask, p)
  | .privatize i b =>
      if q.resident i (H.hash i b) = some b then
        ({ q with
          resident := fun j l => if j ≠ i ∧ q.resident j l = some b then none else q.resident j l
          privateOwner := Function.update q.privateOwner b (some i) }, 0)
      else (q, ⊤)
  | .fetch i b mask =>
      if q.resident i (H.hash i b) = some b then (q, 0) else
        let e := limitedEvict p q i (H.hash i b) mask
        let v := limitedBroadcast e.1 b mask
        ({ v with
            resident := fun j k => if h : j = i then
              if h ▸ k = H.hash i b then some b else v.resident j k else v.resident j k
            last := fun j k => if h : j = i then
              if h ▸ k = H.hash i b then some b else v.last j k else v.last j k }, e.2 + p)

noncomputable def limitedControls {B : Type} [DecidableEq B] {n : ℕ}
    {H : LimitedHardware B n} (p : ℕ) (q : LimitedState H)
    (cs : List (LimitedControl H)) : LimitedState H × ℝ≥0∞ :=
  cs.foldl (fun v c => let w := limitedControl p v.1 c; (w.1, v.2 + w.2)) (q, 0)

/-- A write cannot acquire a missing block: the source requires its preparatory
read. Shared writes update memory for one cycle; private writes mark dirty for
zero bus cycles. Service itself changes no placement or coherence mode. -/
noncomputable def limitedService {B : Type} [DecidableEq B] {n : ℕ}
    {H : LimitedHardware B n} (q : LimitedState H) :
    LimitedRequest B n → LimitedState H × ℝ≥0∞
  | .read i b => (q, if q.resident i (H.hash i b) = some b then 0 else ⊤)
  | .write i b =>
      if q.resident i (H.hash i b) ≠ some b then (q, ⊤) else
        if q.privateOwner b = some i then
          ({q with dirty := Function.update q.dirty b true}, 0) else (q, 1)

/-- Before-request controls cannot see the new request. Moment controls on a
write are empty. Distinct blocks and all processors share this one history. -/
structure LimitedOnline {B : Type} {n : ℕ} (H : LimitedHardware B n) where
  before : List (LimitedRequest B n) → List (LimitedControl H)
  moment : List (LimitedRequest B n) → List (LimitedControl H)
  after : List (LimitedRequest B n) → List (LimitedControl H)
  zero : ∀ h i b, moment (h ++ [.write i b]) = []

noncomputable def limitedStep {B : Type} [DecidableEq B] {n : ℕ}
    {H : LimitedHardware B n} (p : ℕ) (q : LimitedState H) (r : LimitedRequest B n)
    (before moment after : List (LimitedControl H)) : LimitedState H × ℝ≥0∞ :=
  let u := limitedControls p q before
  let v := limitedControls p u.1 moment
  let w := limitedService v.1 r
  let z := limitedControls p w.1 after
  (z.1, u.2 + v.2 + w.2 + z.2)

noncomputable def LimitedOnline.run {B : Type} [DecidableEq B] {n : ℕ}
    {H : LimitedHardware B n} (A : LimitedOnline H) (p : ℕ) (q₀ : LimitedState H)
    (σ : List (LimitedRequest B n)) : LimitedState H × ℝ≥0∞ :=
  ((List.range σ.length).foldl (fun v j =>
    match σ[j]? with
    | none => v
    | some r =>
        let w := limitedStep p v.1 r (A.before (σ.take j))
          (A.moment (σ.take (j + 1))) (A.after (σ.take (j + 1)))
        (w.1, v.2 + w.2)) (q₀, 0))

/-- Preparatory reads remain in force until another processor accesses the
same block, or this processor accesses a colliding block. This is the source's
read-before-write convention, including collision-terminated write runs. -/
def LimitedAdmissible {B : Type} [DecidableEq B] {n : ℕ}
    (H : LimitedHardware B n) (σ : List (LimitedRequest B n)) : Prop :=
  ∀ (j : ℕ) (i : Fin n) (b : B), σ[j]? = some (LimitedRequest.write i b) →
    ∃ k : ℕ, k < j ∧ σ[k]? = some (LimitedRequest.read i b) ∧
      ∀ l : ℕ, k < l → l < j →
        (∀ t : Fin n, t ≠ i →
          σ[l]? ≠ some (LimitedRequest.read t b) ∧
          σ[l]? ≠ some (LimitedRequest.write t b)) ∧
        (∀ d : B, H.hash i d = H.hash i b → d ≠ b →
          σ[l]? ≠ some (LimitedRequest.read i d) ∧
          σ[l]? ≠ some (LimitedRequest.write i d))

/-- Offline schedules can use the entire word when choosing their controls.
The write timing rule is still enforced. Infimum is in [0,∞], including empty
words; a fetch-on-read shared schedule proves finiteness on admissible words. -/
noncomputable def limitedOpt {B : Type} [DecidableEq B] {n : ℕ}
    {H : LimitedHardware B n} (p : ℕ) (q₀ : LimitedState H)
    (σ : List (LimitedRequest B n)) : ℝ≥0∞ :=
  ⨅ (u : ℕ → List (LimitedControl H)) (v : ℕ → List (LimitedControl H))
    (w : ℕ → List (LimitedControl H))
    (_ : ∀ (j : ℕ) (i : Fin n) (b : B), σ[j]? = some (LimitedRequest.write i b) → v j = []),
    (((List.range σ.length).foldl (fun z j =>
      match σ[j]? with
      | none => z
      | some r =>
          let z' := limitedStep p z.1 r (u j) (v j) (w j)
          (z'.1, z.2 + z'.2)) (q₀, 0)).2)

structure LimitedRandomized {B : Type} [DecidableEq B] {n : ℕ}
    (H : LimitedHardware B n) (p : ℕ) (q₀ : LimitedState H) where
  ι : Type
  [ms : MeasurableSpace ι]
  μ : Measure ι
  prob : IsProbabilityMeasure μ
  alg : ι → LimitedOnline H
  meas : ∀ σ, Measurable fun i => ((alg i).run p q₀ σ).2

noncomputable def LimitedRandomized.expCost {B : Type} [DecidableEq B] {n : ℕ}
    {H : LimitedHardware B n} {p : ℕ} {q₀ : LimitedState H}
    (A : LimitedRandomized H p q₀) (σ : List (LimitedRequest B n)) : ℝ≥0∞ :=
  ∫⁻ i, ((A.alg i).run p q₀ σ).2 ∂A.μ

def LimitedRandomized.Competitive {B : Type} [DecidableEq B] {n : ℕ}
    {H : LimitedHardware B n} {p : ℕ} {q₀ : LimitedState H}
    (A : LimitedRandomized H p q₀) (c : ℝ) : Prop :=
  ∃ a : ℝ, ∀ σ : List (LimitedRequest B n), LimitedAdmissible H σ →
    A.expCost σ ≤ ENNReal.ofReal (c * (limitedOpt p q₀ σ).toReal + a)

end NonuniformCompetitive.Snoopy.Supplement


