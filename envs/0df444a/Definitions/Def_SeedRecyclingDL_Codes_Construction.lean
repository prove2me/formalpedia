-- Prove2me | Definitions.Def_SeedRecyclingDL_Codes_Construction
-- name    : SeedRecyclingDL_Codes_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:43.801739+00:00
-- url     : https://prove2.me/theorems/ae8a3302-6e02-4777-b1e8-15c862b85e03
-- title:
--   The actual encoders, greedy and bootstrap suffixes, and Procedure B.2
-- statement:
--   The encoder concatenates the systematic payload with the protected recycled tag. The greedy suffix table scans words lexicographically, selects unmarked words, and marks their DL neighbors. The bootstrap suffix uses the least inner length in $\{h+1,\ldots,2h\}$ with enough message bits, pads with zeros, and applies the already defined greedy family. Its inverse checks padding and re-encodes.
--
--   Procedure B.2 enumerates length-$n$ preimages, splits each candidate at $m$, tests tag membership and its hash, then recovers both ranks. The payload can be returned before rank recovery. Both variants use the exact parameters $D_t=(2t+1)10^{2t}$, $L=D_tn^{2t}$, $b=\lceil\log_2(2Ln)\rceil$, and $r=\lceil\log_2(2L)\rceil$.
--
--   These are constructed functions, not free code tables assumed to be correct.
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), §§3.1–3.3 and 4.3, PDF pp. 10–12, 14 (printed pp. 8–10, 12); Appendix B, PDF pp. 18–19 (printed pp. 16–17); Appendix D, PDF pp. 24–25 (printed pp. 22–23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Tag

set_option autoImplicit false

noncomputable section

namespace SeedRecyclingDL.Codes

def listCompetitors (t m : ℕ) (x : Word) : List Word :=
  (enumerateBall (2 * t) x).filter fun x' => x'.length = m ∧ x' ≠ x

def competitorSet (t m : ℕ) (x : Word) : Finset Word := (listCompetitors t m x).toFinset

def listPreimages (t n : ℕ) (y : Word) : List Word :=
  if n ≤ y.length + t ∧ y.length ≤ n + t then
    (enumerateBall t y).filter fun z => z.length = n else []

/-- The actual marked-word greedy scan of §3.3. -/
def greedyTable (N : ℕ) (neighbors : Word → List Word) : List Word :=
  ((allWords N).foldl (fun state s =>
    if s ∈ state.2 then state else (state.1 ++ [s], state.2 ++ neighbors s))
    (([] : List Word), ([] : List Word))).1

def dlGreedyTable (t N : ℕ) : List Word :=
  greedyTable N (fun s => (enumerateBall (2 * t) s).filter fun u => u.length = N)

def tableEncode (table : List Word) (T : Word) : Word := (table[value T]?).getD []

def tableInverse (h : ℕ) (table : List Word) (u : Word) : Option Word := do
  let i ← table.idxOf? u
  if i < 2 ^ h then some (binary h i) else none

def D (t : ℕ) : ℕ := (2 * t + 1) * 10 ^ (2 * t)
def L (t n : ℕ) : ℕ := D t * n ^ (2 * t)
def fieldWidth (t n : ℕ) : ℕ := EditMulticoloring.Code.ceilLog 2 (2 * L t n * n)
def hashWidth (t n : ℕ) : ℕ := EditMulticoloring.Code.ceilLog 2 (2 * L t n)
def tagWidth (t n : ℕ) : ℕ := 2 * fieldWidth t n + hashWidth t n

def greedySuffix (t n : ℕ) : ℕ :=
  tagWidth t n + ⌈(2 * t : ℕ) * log₂ (20 * tagWidth t n) + log₂ (2 * t + 1)⌉₊

def greedyMessageLength (t n : ℕ) : ℕ := n - greedySuffix t n + 2 * fieldWidth t n - 2

/-- The search interval is finite. Zero is a failure sentinel; D.1 proves
that it is not used for any source input. -/
def bootstrapLength (M : ℕ → ℕ) (h : ℕ) : ℕ :=
  (((List.range h).map fun i => h + 1 + i).find? fun ell => h ≤ M ell).getD 0

def paddedTag (M h : ℕ) (T : Word) : Word := T ++ List.replicate (M - h) 0

def bootstrapTag (M : ℕ → ℕ) (Enc : ℕ → Word → Word) (h : ℕ) (T : Word) : Word :=
  let N := bootstrapLength M h
  Enc N (paddedTag (M N) h T)

/-- Padding check and re-encoding are both necessary, including on invalid inputs. -/
def bootstrapInverse (M : ℕ → ℕ) (Enc : ℕ → Word → Word)
    (Dec : ℕ → Word → Option Word) (h : ℕ) (u : Word) : Option Word := do
  let N := bootstrapLength M h
  let mu ← Dec N u
  if mu.length = M N ∧ h ≤ M N ∧
      mu.drop h = List.replicate (M N - h) 0 ∧ Enc N mu = u then
    some (mu.take h) else none

def passesCandidate {F : Type} [Field F] [Fintype F] (P : FieldPresentation F)
    (m N r : ℕ) (inverse : Word → Option Word) (z : Word) : Bool :=
  if z.length ≠ m + N then false else
  match inverse (z.drop m) with
  | none => false
  | some T => if T.length ≠ 2 * P.k + r then false else
    let a := fromBits P (T.take P.k)
    let lam := fromBits P ((T.drop P.k).take P.k)
    decide (project P r (lam * (payloadPolynomial P m (z.take m)).eval a) = T.drop (2 * P.k))

def firstCandidate {F : Type} [Field F] [Fintype F] (P : FieldPresentation F)
    (m N r : ℕ) (preimages : Word → List Word) (inverse : Word → Option Word)
    (y : Word) : Option Word :=
  (preimages y).find? (passesCandidate P m N r inverse)

/-- The payload is available before either bad-seed computation. -/
def decodePayload {F : Type} [Field F] [Fintype F] (P : FieldPresentation F)
    (m N r : ℕ) (preimages : Word → List Word) (inverse : Word → Option Word)
    (y : Word) : Option Word :=
  (firstCandidate P m N r preimages inverse y).map (List.take m)

def procedureB2 {F : Type} [Field F] [Fintype F] (P : FieldPresentation F)
    (m N r : ℕ) (Γ : Competitors) (preimages : Word → List Word)
    (inverse : Word → Option Word) (y : Word) : Option Word := do
  let z ← firstCandidate P m N r preimages inverse y
  let T ← inverse (z.drop m)
  let ranks ← recoverRanks P m r Γ (z.take m) T
  some (z.take m ++ ranks.1 ++ ranks.2)

/-- Number of invocations of the two bad-list computations in B.2. -/
def badListCalls {F : Type} [Field F] [Fintype F] (P : FieldPresentation F)
    (m N r : ℕ) (Γ : Competitors) (preimages : Word → List Word)
    (inverse : Word → Option Word) (y : Word) : ℕ × ℕ := by
  classical
  exact match firstCandidate P m N r preimages inverse y with
  | none => (0, 0)
  | some z => match inverse (z.drop m) with
    | none => (0, 0)
    | some T =>
      let report := rankRecovery P m r Γ (z.take m) T
      (report.firstCalls, report.secondCalls)

structure FieldData where
  Carrier : Type
  field : Field Carrier
  fintype : Fintype Carrier
  presentation : @FieldPresentation Carrier field fintype

attribute [instance] FieldData.field FieldData.fintype

def greedyEncode (data : ℕ → FieldData) (t n : ℕ) (mu : Word) : Word :=
  let P := (data n).presentation
  let N := greedySuffix t n
  let m := n - N
  let A := tableEncode (dlGreedyTable t N)
  encode P m (hashWidth t n) (competitorSet t m) A
    (mu.take m) ((mu.drop m).take (P.k - 1)) ((mu.drop (m + P.k - 1)).take (P.k - 1))

def greedyDecode (data : ℕ → FieldData) (t n : ℕ) (y : Word) : Option Word :=
  let P := (data n).presentation
  let N := greedySuffix t n
  let m := n - N
  procedureB2 P m N (hashWidth t n) (competitorSet t m) (listPreimages t n)
    (tableInverse (tagWidth t n) (dlGreedyTable t N)) y

inductive Variant where
  | bootstrapped | greedy
  deriving DecidableEq

def suffixLength (t n : ℕ) : Variant → ℕ
  | .greedy => greedySuffix t n
  | .bootstrapped => bootstrapLength (greedyMessageLength t) (tagWidth t n)

def suffixEncode (data : ℕ → FieldData) (t n : ℕ) : Variant → Word → Word
  | .greedy => tableEncode (dlGreedyTable t (greedySuffix t n))
  | .bootstrapped => bootstrapTag (greedyMessageLength t) (greedyEncode data t) (tagWidth t n)

def suffixInverse (data : ℕ → FieldData) (t n : ℕ) : Variant → Word → Option Word
  | .greedy => tableInverse (tagWidth t n) (dlGreedyTable t (greedySuffix t n))
  | .bootstrapped => bootstrapInverse (greedyMessageLength t)
      (greedyEncode data t) (greedyDecode data t) (tagWidth t n)

def messageLength (v : Variant) (t n : ℕ) : ℕ :=
  n - suffixLength t n v + 2 * fieldWidth t n - 2

def finalEncode (data : ℕ → FieldData) (v : Variant) (t n : ℕ) (mu : Word) : Word :=
  let P := (data n).presentation
  let m := n - suffixLength t n v
  encode P m (hashWidth t n) (competitorSet t m) (suffixEncode data t n v)
    (mu.take m) ((mu.drop m).take (P.k - 1)) ((mu.drop (m + P.k - 1)).take (P.k - 1))

def finalDecode (data : ℕ → FieldData) (v : Variant) (t n : ℕ) (y : Word) : Option Word :=
  let P := (data n).presentation
  let N := suffixLength t n v
  let m := n - N
  procedureB2 P m N (hashWidth t n) (competitorSet t m)
    (listPreimages t n) (suffixInverse data t n v) y

def finalPayload (data : ℕ → FieldData) (v : Variant) (t n : ℕ) (y : Word) : Option Word :=
  let P := (data n).presentation
  let N := suffixLength t n v
  decodePayload P (n - N) N (hashWidth t n) (listPreimages t n) (suffixInverse data t n v) y

end SeedRecyclingDL.Codes


