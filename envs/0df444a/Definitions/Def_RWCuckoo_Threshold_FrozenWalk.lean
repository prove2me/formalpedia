-- Prove2me | Definitions.Def_RWCuckoo_Threshold_FrozenWalk
-- name    : RWCuckoo_Threshold_FrozenWalk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:31:22.952595+00:00
-- url     : https://prove2.me/theorems/692d845f-60b2-41e8-8221-88a73b28bf75
-- title:
--   Matchings, the frozen-matching random walk (Definition 2.1), T^frozen and N_G; admissible configurations (Definition 5.2) and the fresh-stopped walk (Definition 5.3)
-- statement:
--   Let $h$ be the hashes of the first $m$ keys. A **matching** (p. 5) is an injective map $M:[m]\to[n]$ with $M(x)\in\{h_1(x),\dots,h_d(x)\}$; the cells $M([m])$ are **occupied**, the others form the set $E$ of **empty** cells. A matching index of $x$ is an $i$ with $M(x)=h_i(x)$.
--
--   **Definition 2.1 (frozen-matching random walk).** The walk starts at a uniformly random cell $X_0$. If $X_t$ is empty it stops; otherwise, with $x=M^{-1}(X_t)$, it chooses $i\in[d]$ uniformly at random and moves to $X_{t+1}=h_i(x)$. The matching never changes. $T^{\mathrm{frozen}}$ is the number of cells, with repetition, that it visits until it stops (the final empty cell included), and for a set $G$ of cells
--   $$N_G=\bigl|\{t:0\le t<T^{\mathrm{frozen}},\ X_t\in G\}\bigr| .$$
--
--   **Definition 5.2 (admissible configuration).** An adversary examines the hashes one probe at a time, adaptively, and finally outputs a matching that uses only examined probes; the unexamined probes form the set $F$ of **fresh** probes, and $(M,F)$ is an admissible configuration. For given hashes, the pairs that some adversary can output are exactly those in which no matching probe $(x,\mathrm{idx}(x))$ is fresh.
--
--   **Definition 5.3 (fresh-stopped walk).** For an admissible $(M,F)$, the fresh-stopped walk is the frozen-matching walk that also stops at once when, at the cell of $x$, it chooses a probe $(x,i)\in F$; the target of that probe is not visited. $T^{\mathrm{fresh}}$ is the number of cells it visits and $N_G$ its number of visits to $G$ before it stops.
--
--   The expectations $\mathbb E\,T^{\mathrm{frozen}}$, $\mathbb E\,N_G$, $\mathbb E\,T^{\mathrm{fresh}}$ are over the walk only (uniform first cell and probe choices), for fixed hashes and $(M,F)$.
--
--   **Formalization Note** A matching is a choice of matching index per key whose cells are pairwise distinct (with repeated hash values this fixes which index the key uses). Walk times are in `ℕ∞` (`⊤` if the walk never stops); positions use the probe stream `ℕ → Fin d`. `Matching.table` places the first $m$ keys at their matching indices in a table of $m+1$ keys, and `withNewKey h g` appends the new key's hashes `g`.
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 5 (§2, Definition 2.1), p. 13 (§4), p. 17 (§5.1, Definitions 5.2 and 5.3)

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_Insertion

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- A matching of the `m` keys (§2, p. 5): each key `x` sits at the cell `h x (idx x)` of its
matching index `idx x`, and distinct keys sit at distinct cells. (A key whose hashes repeat may
have several indices pointing at its cell; the matching records the one it uses.) -/
structure Matching {m d n : ℕ} (h : Hashes m d n) where
  idx : Fin m → Fin d
  injective : Function.Injective fun x => h x (idx x)

variable {m d n : ℕ} {h : Hashes m d n}

/-- The matched cell `M(x)` of key `x`. -/
def Matching.cell (M : Matching h) (x : Fin m) : Fin n := h x (M.idx x)

/-- The occupied cells `M([m])`. -/
def Matching.occupied (M : Matching h) : Finset (Fin n) := Finset.univ.image M.cell

/-- The empty cells `E = [n] \ M([m])`. -/
def Matching.empty (M : Matching h) : Finset (Fin n) := Finset.univ \ M.occupied

open Classical in
/-- The positions `X_0, X_1, …` of the frozen-matching random walk (Definition 2.1, p. 5) from
the cell `v = X_0`: from an occupied cell `X_t = M(x)` it moves to `h x (ω t)`, the probe index
`ω t` being uniform in `Fin d`; an empty cell is absorbing (the walk has stopped there). -/
noncomputable def frozenPos (M : Matching h) (v : Fin n) (ω : ℕ → Fin d) : ℕ → Fin n
  | 0 => v
  | t + 1 =>
      let u := frozenPos M v ω t
      if hx : ∃ x, M.cell x = u then h (Classical.choose hx) (ω t) else u

open Classical in
/-- `T^frozen` (Definition 2.1): the number of cells (with repetition) that the frozen-matching
walk visits until it stops at an empty cell, counting that empty cell; `⊤` if it never stops. -/
noncomputable def frozenTime (M : Matching h) (v : Fin n) (ω : ℕ → Fin d) : ℕ∞ :=
  if hx : ∃ t, frozenPos M v ω t ∈ M.empty then ((Nat.find hx + 1 : ℕ) : ℕ∞) else ⊤

/-- `N_G = |{t : 0 ≤ t < T^frozen, X_t ∈ G}|` (p. 13), the number of visits to `G` before the walk
stops, counted with multiplicity. -/
noncomputable def frozenVisits (M : Matching h) (G : Finset (Fin n)) (v : Fin n)
    (ω : ℕ → Fin d) : ℕ∞ :=
  {t : ℕ | (t : ℕ∞) < frozenTime M v ω ∧ frozenPos M v ω t ∈ G}.encard

/-- The law of the walk's randomness: a uniformly random first cell and the probe stream. -/
noncomputable def walkMeasure (d n : ℕ) : Measure (Fin n × (ℕ → Fin d)) :=
  (uniformOn Set.univ : Measure (Fin n)).prod (streamMeasure d)

/-- `E T^frozen` for fixed hashes and matching (expectation over the walk only). -/
noncomputable def expFrozenTime (M : Matching h) : ℝ≥0∞ :=
  ∫⁻ p, ((frozenTime M p.1 p.2 : ℕ∞) : ℝ≥0∞) ∂(walkMeasure d n)

/-- `E N_G` for the frozen-matching walk. -/
noncomputable def expFrozenVisits (M : Matching h) (G : Finset (Fin n)) : ℝ≥0∞ :=
  ∫⁻ p, ((frozenVisits M G p.1 p.2 : ℕ∞) : ℝ≥0∞) ∂(walkMeasure d n)

/-- Admissible configuration (Definition 5.2, p. 17). An adversary examines probes one at a time
and outputs a matching that uses only examined (spoiled) probes; `F` is the set of probes it
has not examined (fresh). For given hashes the pairs `(M, F)` that some adversary can output are
exactly those in which no matching probe `(x, idx x)` is fresh: examining the complement of `F`
in a fixed order and then outputting `M` is such an adversary. -/
def IsAdmissible (M : Matching h) (F : Finset (Fin m × Fin d)) : Prop :=
  ∀ x, (x, M.idx x) ∉ F

open Classical in
/-- `T^fresh` (Definition 5.3, p. 17): the fresh-stopped walk is the frozen-matching walk that
also stops, at once and without moving, when at an occupied cell `M(x)` it chooses a probe
`(x, ω t) ∈ F`; `T^fresh` is the number of cells it visits (the target of the fresh probe is not
counted); `⊤` if it never stops. -/
noncomputable def freshTime (M : Matching h) (F : Finset (Fin m × Fin d)) (v : Fin n)
    (ω : ℕ → Fin d) : ℕ∞ :=
  if hx : ∃ t, frozenPos M v ω t ∈ M.empty ∨ ∃ x, M.cell x = frozenPos M v ω t ∧ (x, ω t) ∈ F
  then ((Nat.find hx + 1 : ℕ) : ℕ∞) else ⊤

/-- `N_G` for the fresh-stopped walk: its number of visits to `G` before it stops. -/
noncomputable def freshVisits (M : Matching h) (F : Finset (Fin m × Fin d)) (G : Finset (Fin n))
    (v : Fin n) (ω : ℕ → Fin d) : ℕ∞ :=
  {t : ℕ | (t : ℕ∞) < freshTime M F v ω ∧ frozenPos M v ω t ∈ G}.encard

/-- `E T^fresh` (expectation over the walk: uniform first cell, uniform probe choices). -/
noncomputable def expFreshTime (M : Matching h) (F : Finset (Fin m × Fin d)) : ℝ≥0∞ :=
  ∫⁻ p, ((freshTime M F p.1 p.2 : ℕ∞) : ℝ≥0∞) ∂(walkMeasure d n)

/-- `E N_G` for the fresh-stopped walk. -/
noncomputable def expFreshVisits (M : Matching h) (F : Finset (Fin m × Fin d))
    (G : Finset (Fin n)) : ℝ≥0∞ :=
  ∫⁻ p, ((freshVisits M F G p.1 p.2 : ℕ∞) : ℝ≥0∞) ∂(walkMeasure d n)

/-- The hashes of all `m + 1` keys, from the hashes `h` of the first `m` keys and the hashes `g`
of the new key `Fin.last m`. -/
def withNewKey (h : Hashes m d n) (g : Fin d → Fin n) : Hashes (m + 1) d n :=
  Fin.snoc (α := fun _ => Fin d → Fin n) h g

open Classical in
/-- The table of `m + 1` keys in which the first `m` keys are placed by the matching `M` (each
at its matching index) and the new key is not placed. -/
noncomputable def Matching.table (M : Matching h) : Table (m + 1) d n := fun v =>
  if hx : ∃ x, M.cell x = v then some ((Classical.choose hx).castSucc, M.idx (Classical.choose hx))
  else none

end RWCuckoo.Threshold


