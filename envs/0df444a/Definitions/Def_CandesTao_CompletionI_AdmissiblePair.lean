-- Prove2me | Definitions.Def_CandesTao_CompletionI_AdmissiblePair
-- name    : CandesTao_CompletionI_AdmissiblePair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:41:27.802985+00:00
-- url     : https://prove2.me/theorems/86a7445b-2d05-414a-80f6-ad95f993a5e9
-- title:
--   Admissible and strongly admissible pairs $(s,t)$, and the sets $J, K, \Omega, Q, Q'$ (Sections IV-B, V)
-- statement:
--   Fix integers $j, k \ge 0$ and order the $2j(k+1)$ triples $(i,\mu,l) \in [j]\times\{0,1\}\times\{0,\dots,k\}$ lexicographically: $(i,\mu,l) < (i',\mu',l')$ if $i < i'$, or $i = i'$ and $\mu < \mu'$, or $i = i'$, $\mu = \mu'$ and $l < l'$. A pair $(s,t)$ of sequences $s_{i,\mu,l}, t_{i,\mu,l} \in \{1,2,3,\dots\}$ indexed by these triples is **admissible** if
--
--   1. (IV.6) for all $i \in [j]$, with the cyclic convention $s_{j+1,0,0} = s_{1,0,0}$,
--   $$s_{i,1,0} = s_{i+1,0,0}, \qquad t_{i,1,0} = t_{i,0,0};$$
--   2. (IV.7) for every triple $(i,\mu,l)$ the sets $\{s_{i',\mu',l'} : (i',\mu',l') \le (i,\mu,l)\}$ and $\{t_{i',\mu',l'} : (i',\mu',l') \le (i,\mu,l)\}$ are initial segments $[m] = \{1,\dots,m\}$.
--
--   For an admissible pair define $J := \{s_{i,\mu,l}\}$ and $K := \{t_{i,\mu,l}\}$ (IV.8), and the set of visited pairs $\Omega := \{(s_{i,\mu,l}, t_{i,\mu,l})\} \subset J\times K$ (IV.9). The pair is **strongly admissible** if every element of $\Omega$ is visited at least twice by the sequence $(s_{i,\mu,l}, t_{i,\mu,l})$.
--
--   Let $Q$ be the set of triples $(i,\mu,l) \in [j]\times\{0,1\}\times[k]$ (so $l \ge 1$) with $s_{i,\mu,l-1} \neq s_{i,\mu,l}$ and $t_{i,\mu,l-1} \neq t_{i,\mu,l}$ (the "non-rook moves"). A triple $(i,\mu,l)$ is **recycled** if $s_{i',\mu',l'} = s_{i,\mu,l}$ or $t_{i',\mu',l'} = t_{i,\mu,l}$ for some $(i',\mu',l') < (i,\mu,l)$, and $Q' \subset Q$ is the set of recycled elements of $Q$.
--
--   Finally, for $q \ge 0$ let $N(j,k,q)$ be the number of strongly admissible pairs with $|Q'| = q$.
--
--   Admissible pairs encode which vertices of the "spider" paths in the expansion (IV.4) of $\mathbb E\operatorname{trace}(A^*A)^j$ share a row or a column; the moment bound of Section V is reduced to the exponent bound and the count of these pairs.
--
--   **Formalization Note** The index $i$ is 0-based (`Fin j`), and the cyclic successor $i \mapsto i+1$ is `finRotate j`. The lexicographic order is compared through the position $(2i+\mu)(k+1)+l$. Condition (IV.7) forces every value into $\{1,\dots,2j(k+1)\}$, so $N(j,k,q)$ (`strongPairCount`) counts pairs of functions with values in `Fin (2j(k+1)+1)`; this counts exactly the paper's pairs and is finite.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, pp. 2066–2068, Eqs. (IV.6)–(IV.9), definitions of admissible, strongly admissible, Q, recycled, Q'

import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Set.Defs
import Mathlib.SetTheory.Cardinal.Finite

namespace CandesTao.CompletionI

/-- The index set `[j] × {0,1} × {0,…,k}` of Section IV-B of Candès–Tao.  The first
coordinate is 0-based: the paper's `i ∈ {1,…,j}` is `i - 1 : Fin j`. -/
abbrev PathIndex (j k : ℕ) := Fin j × Fin 2 × Fin (k + 1)

/-- Position of `(i, μ, l)` in the lexicographic order of Section IV-B
(`(i,μ,l) < (i',μ',l')` iff `i < i'`, or `i = i'` and `μ < μ'`, or `i = i'`, `μ = μ'`
and `l < l'`).  The map is injective, so comparing positions is exactly the
lexicographic comparison. -/
def PathIndex.pos {j k : ℕ} (x : PathIndex j k) : ℕ :=
  (x.1.val * 2 + x.2.1.val) * (k + 1) + x.2.2.val

/-- The predecessor `(i, μ, l - 1)` of `(i, μ, l)` along a leg; it is only used when
`l ≥ 1`. -/
def PathIndex.prev {j k : ℕ} (x : PathIndex j k) : PathIndex j k :=
  (x.1, x.2.1, ⟨x.2.2.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.2.2.isLt⟩)

/-- A set of positive integers is an initial segment `[m] = {1, …, m}` for some
integer `m ≥ 0`. -/
def IsInitialSegment (A : Set ℕ) : Prop :=
  ∃ m : ℕ, A = Set.Icc 1 m

/-- Admissible pair `(s, t)` (Candès–Tao, Section IV-B, p. 2066): two sequences indexed
by `[j] × {0,1} × {0,…,k}` with
1. the cyclic condition (IV.6): `s_{i,1,0} = s_{i+1,0,0}` and `t_{i,1,0} = t_{i,0,0}`
   for all `i ∈ [j]`, with `s_{j+1,0,0} = s_{1,0,0}` (`finRotate j` is `i ↦ i + 1 mod j`);
2. the initial-segment condition (IV.7): for every `(i,μ,l)` the sets
   `{s(i',μ',l') : (i',μ',l') ≤ (i,μ,l)}` and `{t(i',μ',l') : (i',μ',l') ≤ (i,μ,l)}`
   are of the form `[m]`.
Condition 2 forces all values to lie in `{1, 2, 3, …}`. -/
def IsAdmissible (j k : ℕ) (s t : PathIndex j k → ℕ) : Prop :=
  (∀ i : Fin j, s (i, 1, 0) = s (finRotate j i, 0, 0) ∧ t (i, 1, 0) = t (i, 0, 0)) ∧
  (∀ x : PathIndex j k,
    IsInitialSegment {v | ∃ y : PathIndex j k, y.pos ≤ x.pos ∧ s y = v} ∧
    IsInitialSegment {v | ∃ y : PathIndex j k, y.pos ≤ x.pos ∧ t y = v})

/-- `J := {s_{i,μ,l}}`, the set of values of `s` (Eq. (IV.8)). -/
def rowValues {j k : ℕ} (s : PathIndex j k → ℕ) : Finset ℕ :=
  Finset.univ.image s

/-- `K := {t_{i,μ,l}}`, the set of values of `t` (Eq. (IV.8)). -/
def colValues {j k : ℕ} (t : PathIndex j k → ℕ) : Finset ℕ :=
  Finset.univ.image t

/-- `Ω := {(s_{i,μ,l}, t_{i,μ,l})} ⊂ J × K`, the set of visited pairs (Eq. (IV.9)). -/
def visitedPairs {j k : ℕ} (s t : PathIndex j k → ℕ) : Finset (ℕ × ℕ) :=
  Finset.univ.image (fun x => (s x, t x))

/-- Strongly admissible pair (Candès–Tao, p. 2067): an admissible pair such that every
element of `Ω` is visited at least twice by the sequence `(s_{i,μ,l}, t_{i,μ,l})`. -/
def IsStronglyAdmissible (j k : ℕ) (s t : PathIndex j k → ℕ) : Prop :=
  IsAdmissible j k s t ∧
    ∀ ω ∈ visitedPairs s t,
      2 ≤ (Finset.univ.filter (fun x : PathIndex j k => (s x, t x) = ω)).card

/-- `Q` (Candès–Tao, Section V, p. 2067): the triples `(i,μ,l) ∈ [j] × {0,1} × [k]`
(so `l ≥ 1`) with `s_{i,μ,l-1} ≠ s_{i,μ,l}` and `t_{i,μ,l-1} ≠ t_{i,μ,l}`, i.e. the
non-rook moves of the legs. -/
def nonRookMoves {j k : ℕ} (s t : PathIndex j k → ℕ) : Finset (PathIndex j k) :=
  Finset.univ.filter (fun x =>
    0 < x.2.2.val ∧ s x.prev ≠ s x ∧ t x.prev ≠ t x)

/-- `Q'` (Candès–Tao, p. 2068): the elements of `Q` that are *recycled*, i.e. triples
`(i,μ,l)` for which `s_{i',μ',l'} = s_{i,μ,l}` or `t_{i',μ',l'} = t_{i,μ,l}` for some
`(i',μ',l') < (i,μ,l)`. -/
def recycledNonRookMoves {j k : ℕ} (s t : PathIndex j k → ℕ) : Finset (PathIndex j k) :=
  (nonRookMoves s t).filter (fun x =>
    ∃ y : PathIndex j k, y.pos < x.pos ∧ (s y = s x ∨ t y = t x))

/-- The number of strongly admissible pairs `(s, t)` with `|Q'| = q` (the quantity
bounded in Lemma 5.2 of Candès–Tao).  Every value of an admissible pair lies in
`{1, …, 2j(k+1)}` (by (IV.7), each prefix value set is an initial segment `[m]` with at
most `2j(k+1)` elements), so counting pairs with values in `Fin (2j(k+1)+1)` counts
all admissible pairs of positive-integer sequences, and the count is finite. -/
noncomputable def strongPairCount (j k q : ℕ) : ℕ :=
  Nat.card {st : (PathIndex j k → Fin (2 * j * (k + 1) + 1)) ×
      (PathIndex j k → Fin (2 * j * (k + 1) + 1)) //
    IsStronglyAdmissible j k (fun x => (st.1 x : ℕ)) (fun x => (st.2 x : ℕ)) ∧
      (recycledNonRookMoves (fun x => (st.1 x : ℕ)) (fun x => (st.2 x : ℕ))).card = q}

end CandesTao.CompletionI


