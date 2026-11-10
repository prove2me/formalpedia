-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_Word
-- name    : RealPinwheel_FiveSixths_Word
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:35:14.46445+00:00
-- url     : https://prove2.me/theorems/023f3c79-a524-47fa-94a1-cc641b2d0768
-- title:
--   Periodic words, operational dominance intervals and cyclic gaps
-- statement:
--   An $n$-word $w$ has positive length $L$, one of the $n$ task labels at every position, and at least one occurrence of each task. Repeating $w$ gives the schedule $S_w$. Let $m_i$ count task $i$ in one copy. For a starting occurrence of $i$, its $k$-th subsequent occurrence is the first day by which $k$ further executions have happened; $G_i(k)$ is the largest of these distances over every starting occurrence in one period, including spans across boundaries.
--
--   Define the admissible-density interval directly from window validity, independently of any endpoint calculation:
--
--   $$I_i(w)=\{d>0:\ \forall\ell\ge1,\ \forall m\ge0,\ C_i(S_w;m,\lceil\ell/d\rceil)\ge\ell\},\qquad B(w)=\prod_i I_i(w).$$
--
--   A word dominates a period vector exactly when its repeated schedule is valid for that vector. Its candidate endpoint $u_i$ is the minimum of the mean term $m_i/L$ and the finitely many quotients $k/(G_i(k)-1)$ for $1\le k\le m_i$ and $G_i(k)>1$. The endpoint is marked closed precisely when no retained gap quotient equals that minimum. The endpoint theorem, rather than a definition, establishes that these computed values describe $I_i(w)$.
--
--   The density domain $D_n$ consists of decreasing positive real vectors with total sum at most $5/6$. The potential domain $P_n$ bounds only the first $n-1$ coordinates by $5/6$. The mission uses $D_1,\ldots,D_8$ and $P_9$.
--
--   **Formalization Note** The occurrence distance is the least natural length containing the next $k$ executions. The defining set is nonempty because every $kL$ consecutive days contain at least $k$ occurrences. Cyclic gaps use a finite maximum; the endpoint uses a nonempty finite minimum containing the mean term. Gap subtraction takes place in the reals after coercion, and terms with zero denominator are omitted.
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Section 1, printed pp. 2–3 (PDF pp. 3–4); Section 3, equation (2) and endpoint rule, printed pp. 7–9 (PDF pp. 8–10)

import Definitions.Def_RealPinwheel_FiveSixths_Instance

namespace RealPinwheel.FiveSixths

/-- A nonempty finite word containing every task, with positions starting at zero. -/
structure Word (n : ℕ) where
  length : ℕ
  positive_length : 0 < length
  letter : Fin length → Fin n
  covers : ∀ i : Fin n, ∃ t : Fin length, letter t = i

def wordSchedule {n : ℕ} (w : Word n) (t : ℕ) : Fin n :=
  w.letter ⟨t % w.length, Nat.mod_lt _ w.positive_length⟩

def occurrences {n : ℕ} (w : Word n) (i : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin w.length)).filter fun t => w.letter t = i).card

/-- Distance from day t to its k-th subsequent execution of i.
The searched set is nonempty: every block of length k*|w| contains at least k
executions, since covers supplies an occurrence of i in each period. At k=0 the infimum is 0.
This is an infimum of NATURALS (a least element), not a conditional real infimum. -/
noncomputable def occurrenceDistance {n : ℕ} (w : Word n) (i : Fin n) (t k : ℕ) : ℕ :=
  sInf {d : ℕ | k ≤ windowCount (wordSchedule w) i (t + 1) d}

/-- Maximum over ALL cyclic starting occurrences in one period. Non-occurrences
contribute zero and do not change this maximum of nonnegative distances. -/
noncomputable def cyclicGap {n : ℕ} (w : Word n) (i : Fin n) (k : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin w.length)).sup fun t =>
    if w.letter t = i then occurrenceDistance w i t.val k else 0

/-- Operational interval, defined by all windows, before the endpoint theorem. -/
def admissibleDensities {n : ℕ} (w : Word n) (i : Fin n) : Set ℝ :=
  {d | 0 < d ∧ ∀ ell : ℕ, 0 < ell → ∀ m : ℕ,
    ell ≤ windowCount (wordSchedule w) i m ⌈(ell : ℝ) * (1 / d)⌉₊}

def dominanceBox {n : ℕ} (w : Word n) : Set (Fin n → ℝ) :=
  {d | ∀ i, d i ∈ admissibleDensities w i}

def Dominates {n : ℕ} (w : Word n) (a : Fin n → ℝ) : Prop :=
  Valid a (wordSchedule w)

/-- The finite set includes the mean term even if there are no gap terms. -/
noncomputable def endpointBounds {n : ℕ} (w : Word n) (i : Fin n) : Finset ℝ :=
  insert ((occurrences w i : ℝ) / (w.length : ℝ))
    (((Finset.Icc 1 (occurrences w i)).filter fun k => 1 < cyclicGap w i k).image
      fun k : ℕ => (k : ℝ) / ((cyclicGap w i k : ℝ) - 1))

noncomputable def endpoint {n : ℕ} (w : Word n) (i : Fin n) : ℝ :=
  (endpointBounds w i).min' (by simp [endpointBounds])

/-- The endpoint is closed exactly when no retained gap term attains the minimum. -/
noncomputable def closedEndpoint {n : ℕ} (w : Word n) (i : Fin n) : Prop :=
  ∀ k ∈ Finset.Icc 1 (occurrences w i), 1 < cyclicGap w i k →
    (k : ℝ) / ((cyclicGap w i k : ℝ) - 1) ≠ endpoint w i

/-- Density and potential domains impose ordering; dominance boxes do not. -/
def densityDomain (n : ℕ) : Set (Fin n → ℝ) :=
  {d | Antitone d ∧ (∀ i, 0 < d i) ∧ ∑ i, d i ≤ (5 : ℝ) / 6}

def potentialDomain (n : ℕ) : Set (Fin n → ℝ) :=
  {d | Antitone d ∧ (∀ i, 0 < d i) ∧
    (∑ i : Fin n, if i.val + 1 < n then d i else 0) ≤ (5 : ℝ) / 6}

end RealPinwheel.FiveSixths


