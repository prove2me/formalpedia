-- Prove2me | Definitions.Def_RWCuckoo_Threshold_Insertion
-- name    : RWCuckoo_Threshold_Insertion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:30:30.715283+00:00
-- url     : https://prove2.me/theorems/d9a732ee-5c49-4638-a69d-c8a936c71ca5
-- title:
--   Random hashes, the probe stream, random-walk insertion, the sequential process from an empty table, T^insertion : ℕ∪{∞}, E[T^insertion | H], fresh probes left, and the nonbacktracking insertion
-- statement:
--   A hash table has $n$ cells $[n]$. Each of $K$ keys $x$ has $d$ hashes $h_1(x),\dots,h_d(x)\in[n]$, independent and uniform; a **probe** is a pair $(x,i)$. A table stores in each cell at most one key, together with the index by which that key sits there.
--
--   **Random-walk insertion** (§2, p. 4) of a key $x$: choose a uniformly random probe $i\in[d]$ and place $x$ in $v=h_i(x)$. If $v$ was empty the insertion stops; otherwise the key $y$ previously in $v$ is evicted and the procedure is repeated to reinsert $y$. The **cost** of an insertion is the number of evictions plus one, i.e. the number of placements; it is $\infty$ if the insertion never ends.
--
--   The keys $1,\dots,m+1$ are inserted in this order into an initially empty table with no deletions, every placement using a fresh independent uniform probe choice, independent of the hashes. **$T^{\mathrm{insertion}}$** is the cost of the $(m+1)$-th insertion, with $T^{\mathrm{insertion}}=\infty$ when an earlier insertion never ends (p. 5: "the final insertion either never occurs or never ends"). An event is **hash-only** if it depends only on the hash values; for such an event $H$,
--   $$\mathbb E[T^{\mathrm{insertion}}\mid H]=\frac{1}{\Pr(H)}\int_H T^{\mathrm{insertion}}\,d\Pr\in[0,\infty].$$
--
--   A probe is **examined** when an insertion uses it; after the first $m$ insertions, the probes of the first $m$ keys never examined are **fresh** (§5.1, p. 17).
--
--   In the **nonbacktracking insertion** (App. B, p. 41) the new key chooses uniformly among its $d$ indices, but an evicted key chooses uniformly among its $d-1$ indices other than the one at which it was just evicted. Its number of probes is its number of placements.
--
--   **Formalization Note** Hashes are functions `Fin K → Fin d → Fin n` with the uniform measure; probe choices are one stream `ℕ → Fin d` with the product of uniform measures (`Measure.infinitePi`), consumed in order by all insertions. Tables are `Fin n → Option (Fin K × Fin d)`. The cost is `ℕ∞` (`⊤` on non-termination), expectations are lintegrals in `ℝ≥0∞`, and $\mathbb E[\cdot\mid H]$ uses `ProbabilityTheory.cond` on the event `Prod.fst ⁻¹' H`. The new key is `Fin.last m`. The nonbacktracking insertion draws its first index from a uniform `Fin d` and later ones from a stream in `Fin (d − 1)`, the $u$-th other index of $j$ being $(j+1+u)\bmod d$.
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 4 (§2), p. 5, p. 17 (§5.1), p. 41 (App. B)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Hash values of `K` keys: key `x : Fin K` has the `d` hashes `h x 0, …, h x (d-1)` in the
`n` cells `Fin n` (Hu–Kuszmaul–Liang, §2, p. 4). A probe is a pair `(x, i)`. -/
abbrev Hashes (K d n : ℕ) : Type := Fin K → Fin d → Fin n

/-- The hashes are independent and uniform: the uniform probability measure on all hash
assignments (all subsets are measurable, the space is finite). -/
noncomputable def hashMeasure (K d n : ℕ) : Measure (Hashes K d n) :=
  uniformOn Set.univ

/-- An i.i.d. stream of uniformly random probe indices in `Fin d`, consumed in order. -/
noncomputable def streamMeasure (d : ℕ) : Measure (ℕ → Fin d) :=
  Measure.infinitePi (fun _ : ℕ => (uniformOn Set.univ : Measure (Fin d)))

/-- A table: each cell is empty (`none`) or holds a key together with the index of the hash by
which that key sits there. -/
abbrev Table (K d n : ℕ) : Type := Fin n → Option (Fin K × Fin d)

/-- The empty table. -/
def emptyTable (K d n : ℕ) : Table K d n := fun _ => none

/-- The state of an eviction chain: the table and the key currently held (being placed), if any. -/
structure ChainState (K d n : ℕ) where
  table : Table K d n
  held : Option (Fin K)

/-- One move of the random-walk insertion (§2, p. 4): the held key `x` is placed in its cell
`v = h x i` by probe `i`; the key previously in `v`, if any, is evicted and becomes held. With no
held key the state does not change. -/
def ChainState.step {K d n : ℕ} (h : Hashes K d n) (s : ChainState K d n) (i : Fin d) :
    ChainState K d n :=
  match s.held with
  | none => s
  | some x =>
      { table := Function.update s.table (h x i) (some (x, i)),
        held := (s.table (h x i)).map Prod.fst }

/-- The eviction chain of inserting key `x` into table `τ`, the `t`-th move using probe `ω t`. -/
def chain {K d n : ℕ} (h : Hashes K d n) (τ : Table K d n) (x : Fin K) (ω : ℕ → Fin d) :
    ℕ → ChainState K d n
  | 0 => ⟨τ, some x⟩
  | t + 1 => (chain h τ x ω t).step h (ω t)

open Classical in
/-- The cost of inserting `x` into `τ` with probe choices `ω`: the number of evictions plus one,
i.e. the number of moves until no key is held (§2, p. 4); `⊤` if the insertion never ends. -/
noncomputable def insertionCost {K d n : ℕ} (h : Hashes K d n) (τ : Table K d n) (x : Fin K)
    (ω : ℕ → Fin d) : ℕ∞ :=
  if hx : ∃ t, (chain h τ x ω t).held = none then (Nat.find hx : ℕ∞) else ⊤

open Classical in
/-- The probes `(key, index)` examined (used) during the first `N` moves of an eviction chain. -/
noncomputable def chainProbes {K d n : ℕ} (h : Hashes K d n) (τ : Table K d n) (x : Fin K)
    (ω : ℕ → Fin d) (N : ℕ) : Finset (Fin K × Fin d) :=
  (Finset.range N).biUnion fun t =>
    match (chain h τ x ω t).held with
    | none => ∅
    | some y => {(y, ω t)}

/-- The state of the sequential insertion process after some insertions: the table, the number
of probe choices consumed so far, and the set of probes examined so far. -/
structure ProcessState (K d n : ℕ) where
  table : Table K d n
  used : ℕ
  examined : Finset (Fin K × Fin d)

open Classical in
/-- The process that inserts keys `0, 1, …, K − 1` in order by random-walk insertion into an
initially empty table, without deletions, every insertion consuming the next probe choices of the
single stream `ω`. `afterInsertions h ω j` is the state after the first `j` insertions, or `none`
if one of them never ends (or `j > K`). -/
noncomputable def afterInsertions {K d n : ℕ} (h : Hashes K d n) (ω : ℕ → Fin d) :
    ℕ → Option (ProcessState K d n)
  | 0 => some ⟨emptyTable K d n, 0, ∅⟩
  | j + 1 =>
      match afterInsertions h ω j with
      | none => none
      | some st =>
          if hj : j < K then
            if hx : ∃ t, (chain h st.table ⟨j, hj⟩ (fun t => ω (st.used + t)) t).held = none then
              some ⟨(chain h st.table ⟨j, hj⟩ (fun t => ω (st.used + t)) (Nat.find hx)).table,
                st.used + Nat.find hx,
                st.examined ∪ chainProbes h st.table ⟨j, hj⟩ (fun t => ω (st.used + t))
                  (Nat.find hx)⟩
            else none
          else none

/-- `T^insertion` (§2, p. 4): the cost of the `(m + 1)`-th insertion (key `Fin.last m`) in the
process that inserts the `m + 1` keys in order from an empty table. It is `⊤` if an earlier
insertion never ends or if this one never ends (p. 5). -/
noncomputable def insertionTime {m d n : ℕ} (h : Hashes (m + 1) d n) (ω : ℕ → Fin d) : ℕ∞ :=
  match afterInsertions h ω m with
  | none => ⊤
  | some st => insertionCost h st.table (Fin.last m) (fun t => ω (st.used + t))

/-- The probability space of the process: independent uniform hashes and an independent i.i.d.
uniform probe stream. -/
noncomputable def processMeasure (K d n : ℕ) : Measure (Hashes K d n × (ℕ → Fin d)) :=
  (hashMeasure K d n).prod (streamMeasure d)

/-- `E[T^insertion | H]` for a hash-only event `H` (a set of hash assignments of the `m + 1`
keys), an element of `ℝ≥0∞` (p. 5). -/
noncomputable def condExpInsertionTime (m d n : ℕ) (H : Set (Hashes (m + 1) d n)) : ℝ≥0∞ :=
  ∫⁻ p, ((insertionTime p.1 p.2 : ℕ∞) : ℝ≥0∞) ∂((processMeasure (m + 1) d n)[|Prod.fst ⁻¹' H])

/-- The first insertions all finish: the state after the first `m` insertions exists. -/
def firstInsertionsFinish {m d n : ℕ} (h : Hashes (m + 1) d n) (ω : ℕ → Fin d) : Prop :=
  (afterInsertions h ω m).isSome

/-- The number of fresh probes left by the first `m` insertions (§5.1, p. 17): probes `(x, i)`
of the first `m` keys whose value was not examined by those insertions (`0` if they do not all
finish). -/
noncomputable def freshLeft {m d n : ℕ} (h : Hashes (m + 1) d n) (ω : ℕ → Fin d) : ℕ :=
  match afterInsertions h ω m with
  | none => 0
  | some st => m * d - st.examined.card

/-- The state of the nonbacktracking insertion (App. B, p. 41): the table and the held key
together with the index at which it was just evicted. -/
structure NBState (K d n : ℕ) where
  table : Table K d n
  held : Option (Fin K × Fin d)

/-- The `u`-th of the `d − 1` indices other than `j` (`u : Fin (d − 1)`). -/
def otherIndex {d : ℕ} (j : Fin d) (u : Fin (d - 1)) : Fin d :=
  ⟨(j.val + 1 + u.val) % d, Nat.mod_lt _ (Fin.pos j)⟩

/-- The nonbacktracking insertion of key `x` into `τ` (App. B, p. 41): the new key chooses among
its `d` indices (`i0`); an evicted key, evicted at index `j`, chooses among its `d − 1` other
indices (`otherIndex j (ρ t)`). State after `t + 1` moves. -/
def nbChain {K d n : ℕ} (h : Hashes K d n) (τ : Table K d n) (x : Fin K) (i0 : Fin d)
    (ρ : ℕ → Fin (d - 1)) : ℕ → NBState K d n
  | 0 => ⟨Function.update τ (h x i0) (some (x, i0)), τ (h x i0)⟩
  | t + 1 =>
      let s := nbChain h τ x i0 ρ t
      match s.held with
      | none => s
      | some (y, j) =>
          let i := otherIndex j (ρ t)
          ⟨Function.update s.table (h y i) (some (y, i)), s.table (h y i)⟩

open Classical in
/-- The number of probes (moves) of the nonbacktracking insertion; `⊤` if it never ends. -/
noncomputable def nbCost {K d n : ℕ} (h : Hashes K d n) (τ : Table K d n) (x : Fin K)
    (i0 : Fin d) (ρ : ℕ → Fin (d - 1)) : ℕ∞ :=
  if hx : ∃ t, (nbChain h τ x i0 ρ t).held = none then ((Nat.find hx + 1 : ℕ) : ℕ∞) else ⊤

/-- Expected number of probes of the ordinary insertion of `x` into `τ` (fixed hashes and table;
expectation over the probe choices). -/
noncomputable def expInsertionCost {K d n : ℕ} (h : Hashes K d n) (τ : Table K d n) (x : Fin K) :
    ℝ≥0∞ :=
  ∫⁻ ω, ((insertionCost h τ x ω : ℕ∞) : ℝ≥0∞) ∂(streamMeasure d)

/-- Expected number of probes of the nonbacktracking insertion of `x` into `τ`. -/
noncomputable def expNBCost {K d n : ℕ} (h : Hashes K d n) (τ : Table K d n) (x : Fin K) :
    ℝ≥0∞ :=
  ∫⁻ p, ((nbCost h τ x p.1 p.2 : ℕ∞) : ℝ≥0∞)
    ∂((uniformOn Set.univ : Measure (Fin d)).prod (streamMeasure (d - 1)))

end RWCuckoo.Threshold


