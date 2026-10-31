-- Prove2me | Definitions.Def_PopularMixed_Model
-- name    : PopularMixed_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:39.116126+00:00
-- url     : https://prove2.me/theorems/27b5791d-a9eb-4fc4-adf8-3e037789515a
-- title:
--   Instances with strict preferences, matchings, popularity (Definition 1), stable matchings, mixed matchings and popular mixed matchings (Definition 2)
-- statement:
--   An **instance** $G=(A\cup B,E)$ of the stable marriage problem with strict and possibly incomplete preference lists consists of a finite set $A$ of applicants, a finite set $B$ of jobs, an edge set $E\subseteq A\times B$, and for every vertex $u$ a strict ranking of its neighbours $\mathrm{Nbr}(u)$. A **matching** $M$ is a set of edges no two of which share a vertex; $M(u)$ is $u$'s partner. A vertex $u$ **prefers** $M$ to $M'$ if $u$ is matched in $M$ and unmatched in $M'$, or $u$ is matched in both and ranks $M(u)$ above $M'(u)$.
--
--   1. $\phi(M,M')$ is the number of vertices of $A\cup B$ that prefer $M$ to $M'$, and $\Delta(M,M')=\phi(M,M')-\phi(M',M)$.
--   2. (Definition 1) $M$ is **popular** if $\Delta(M,M')\ge 0$ for every matching $M'$ of $G$.
--   3. An edge $(a,b)\in E$ **blocks** $M$ if $a$ and $b$ prefer each other to their assignments in $M$ (being unmatched is worse than any neighbour); $M$ is **stable** if no edge blocks it; a **perfect stable matching** is a stable matching in which no vertex is unmatched.
--   4. A **mixed matching** $\Pi=\{(M_0,p_0),\dots,(M_k,p_k)\}$ is a probability distribution over matchings; its utility for $w:E\to\mathbb Q$ is $\sum_i p_i\,w(M_i)$ with $w(M)=\sum_{e\in M}w(e)$.
--   5. (Definition 2) With $\phi(\Pi,M')=\sum_i p_i\,\phi(M_i,M')$ and $\phi(M',\Pi)=\sum_i p_i\,\phi(M',M_i)$, $\Pi$ is **popular** if
--   $$\Delta(\Pi,M')=\phi(\Pi,M')-\phi(M',\Pi)\ \ge\ 0\qquad\text{for all matchings }M'\text{ of }G.$$
--
--   The lotteries $\{(M_0,\tfrac12),(M_1,\tfrac12)\}$ and $\{(M,1)\}$ of Theorem 1.1 are `half M₀ M₁` and `pure M`. These are the objects of the goal theorem and of every milestone.
--
--   **Formalization Note** $A$, $B$ are finite types and $E$ a `Finset (A × B)`. Preferences are rank functions `rankA a : B → ℕ`, `rankB b : A → ℕ` (smaller = preferred), injective on neighbours; ranks of non-neighbours are never read. A mixed matching is a weight function `Λ : Finset (A × B) → ℝ` that is nonnegative, sums to $1$ and vanishes off matchings (repeated matchings merged). Utilities are real-valued `w : A → B → ℝ`. `half M M` is `pure M`.
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Section 1, PDF pp.1–2 (instance, matchings, φ, Δ, Definition 1, blocking edges, stability, mixed matchings and utility, Definition 2); "perfect stable matching": Theorem 1.1, PDF p.2. The PDF has no printed page numbers.

import Mathlib

namespace PopularMixed

/-!
Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017),
Section 1, PDF pp.1–2 (the PDF has no printed page numbers; "PDF p." is the 1-based PDF page):
instances of the stable marriage problem with strict and possibly incomplete preference lists,
matchings, φ and Δ, popular matchings (Definition 1), stability, perfect stable
matchings, mixed matchings, their utility, and popular mixed matchings (Definition 2).

**Formalization Note.**
* The applicants `A` and the jobs `B` are finite types; the edge set `E` is a `Finset (A × B)`.
* Preferences are rank functions `rankA a : B → ℕ`, `rankB b : A → ℕ` (smaller rank = more
  preferred), injective on the neighbours of each vertex, i.e. strict orders on `Nbr(u)`. Ranks
  of non-neighbours are never read by any definition below.
* A matching is a `Finset (A × B)` of edges, no two sharing an applicant or a job. "Unmatched" is
  the worst option of every vertex.
* A mixed matching `{(M₀,p₀),…,(M_k,p_k)}` is a weight function `Λ : Finset (A × B) → ℝ`,
  nonnegative, summing to `1`, and supported on matchings (repeated matchings are merged).
* Utilities are real-valued `w : A → B → ℝ`; values off `E` are never read on a matching.
-/

open Finset

/-- An instance `G = (A ∪ B, E)` of the stable marriage problem with strict and possibly
incomplete preference lists (PDF p.1): a bipartite graph with edge set `E ⊆ A × B`, and for each
vertex a strict ranking of its neighbours. `rankA a b < rankA a b'` means that `a` prefers `b` to
`b'`; `rankB b a < rankB b a'` means that `b` prefers `a` to `a'`. -/
structure Instance (A B : Type*) [Fintype A] [Fintype B] where
  /-- The edge set `E`. -/
  E : Finset (A × B)
  /-- The rank of `b` in `a`'s preference list (smaller = more preferred). -/
  rankA : A → B → ℕ
  /-- The rank of `a` in `b`'s preference list (smaller = more preferred). -/
  rankB : B → A → ℕ
  /-- `a`'s preference list over its neighbours is strict. -/
  rankA_inj : ∀ a b b', (a, b) ∈ E → (a, b') ∈ E → rankA a b = rankA a b' → b = b'
  /-- `b`'s preference list over its neighbours is strict. -/
  rankB_inj : ∀ b a a', (a, b) ∈ E → (a', b) ∈ E → rankB b a = rankB b a' → a = a'

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- `M` matches every vertex of `A ∪ B` (PDF p.2: "no vertex is unmatched"). -/
def IsPerfect (M : Finset (A × B)) : Prop :=
  (∀ a, ∃ b, (a, b) ∈ M) ∧ ∀ b, ∃ a, (a, b) ∈ M

namespace Instance

variable (G : Instance A B)

/-- A matching of `G` (PDF p.1): a set of edges of `G`, no two of which share a vertex. -/
def IsMatching (M : Finset (A × B)) : Prop :=
  M ⊆ G.E ∧ (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧ (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q)

/-- Applicant `a` prefers matching `M` to matching `M'` (PDF p.1): `a` is matched in `M`, to `b`
say, and either `a` is unmatched in `M'` or `a` is matched in `M'` to some `b'` ranked worse
than `b`. -/
def PrefersA (a : A) (M M' : Finset (A × B)) : Prop :=
  ∃ b, (a, b) ∈ M ∧ ∀ b', (a, b') ∈ M' → G.rankA a b < G.rankA a b'

/-- Job `b` prefers matching `M` to matching `M'` (PDF p.1), as in `PrefersA`. -/
def PrefersB (b : B) (M M' : Finset (A × B)) : Prop :=
  ∃ a, (a, b) ∈ M ∧ ∀ a', (a', b) ∈ M' → G.rankB b a < G.rankB b a'

instance (a : A) (M M' : Finset (A × B)) : Decidable (G.PrefersA a M M') := by
  unfold PrefersA; infer_instance

instance (b : B) (M M' : Finset (A × B)) : Decidable (G.PrefersB b M M') := by
  unfold PrefersB; infer_instance

/-- `φ(M, M')` (PDF p.1): the number of vertices `u ∈ A ∪ B` that prefer `M` to `M'`. -/
def phi (M M' : Finset (A × B)) : ℕ :=
  (univ.filter fun a => G.PrefersA a M M').card + (univ.filter fun b => G.PrefersB b M M').card

/-- `Δ(M, M') = φ(M, M') − φ(M', M)` (PDF p.1, Definition 1), an integer. -/
def delta (M M' : Finset (A × B)) : ℤ :=
  (G.phi M M' : ℤ) - (G.phi M' M : ℤ)

/-- Definition 1 (PDF p.1): a matching `M` is popular if `Δ(M, M') ≥ 0` for every matching `M'`
of `G`. -/
def IsPopular (M : Finset (A × B)) : Prop :=
  G.IsMatching M ∧ ∀ M', G.IsMatching M' → 0 ≤ G.delta M M'

/-- The edge `(a, b) ∈ E` blocks `M` (PDF p.1): `a` and `b` both prefer each other to their
respective assignments in `M` (being unmatched is worse than every neighbour). -/
def Blocks (M : Finset (A × B)) (a : A) (b : B) : Prop :=
  (a, b) ∈ G.E ∧ (∀ b', (a, b') ∈ M → G.rankA a b < G.rankA a b') ∧
    (∀ a', (a', b) ∈ M → G.rankB b a < G.rankB b a')

/-- A stable matching (PDF p.1): a matching with no blocking edge. -/
def IsStable (M : Finset (A × B)) : Prop :=
  G.IsMatching M ∧ ∀ a b, ¬ G.Blocks M a b

/-- `G` admits a perfect stable matching (PDF p.2): "a stable matching where no vertex is
unmatched". -/
def HasPerfectStableMatching : Prop :=
  ∃ S, G.IsStable S ∧ IsPerfect S
instance (M : Finset (A × B)) : Decidable (G.IsMatching M) :=
  have h1 : Decidable (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) := inferInstance
  have h2 : Decidable (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q) := inferInstance
  @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ h1 h2)

instance (M : Finset (A × B)) : Decidable (G.IsPopular M) := by
  unfold IsPopular; infer_instance

instance (M : Finset (A × B)) (a : A) (b : B) : Decidable (G.Blocks M a b) := by
  unfold Blocks; infer_instance

instance (M : Finset (A × B)) : Decidable (G.IsStable M) := by
  unfold IsStable; infer_instance

/-- A mixed matching (PDF p.1): a probability distribution over matchings of `G`, encoded as
nonnegative weights on `Finset (A × B)` that sum to `1` and vanish off the matchings of `G`. -/
def IsMixed (Λ : Finset (A × B) → ℝ) : Prop :=
  (∀ M, 0 ≤ Λ M) ∧ ∑ M, Λ M = 1 ∧ ∀ M, Λ M ≠ 0 → G.IsMatching M

/-- `φ(Π, M') = Σᵢ pᵢ · φ(Mᵢ, M')` (PDF p.2). -/
noncomputable def phiMixedLeft (Λ : Finset (A × B) → ℝ) (M' : Finset (A × B)) : ℝ :=
  ∑ M, Λ M * (G.phi M M' : ℝ)

/-- `φ(M', Π) = Σᵢ pᵢ · φ(M', Mᵢ)` (PDF p.2, "the definition of φ(M′, Π) is analogous"). -/
noncomputable def phiMixedRight (M' : Finset (A × B)) (Λ : Finset (A × B) → ℝ) : ℝ :=
  ∑ M, Λ M * (G.phi M' M : ℝ)

/-- `Δ(Π, M') = φ(Π, M') − φ(M', Π)` (PDF p.2, Definition 2). -/
noncomputable def deltaMixed (Λ : Finset (A × B) → ℝ) (M' : Finset (A × B)) : ℝ :=
  G.phiMixedLeft Λ M' - G.phiMixedRight M' Λ

/-- Definition 2 (PDF p.2): a mixed matching `Π` is popular if `Δ(Π, M') ≥ 0` for all matchings
`M'` of `G`. -/
def IsPopularMixed (Λ : Finset (A × B) → ℝ) : Prop :=
  G.IsMixed Λ ∧ ∀ M', G.IsMatching M' → 0 ≤ G.deltaMixed Λ M'

end Instance

/-- The utility `w(M) = Σ_{e ∈ M} w(e)` of a matching (PDF p.1). -/
def matchingUtility (w : A → B → ℝ) (M : Finset (A × B)) : ℝ :=
  ∑ e ∈ M, w e.1 e.2

/-- The utility `Σᵢ pᵢ · w(Mᵢ)` of a mixed matching (PDF p.1). -/
noncomputable def utility (w : A → B → ℝ) (Λ : Finset (A × B) → ℝ) : ℝ :=
  ∑ M, Λ M * matchingUtility w M

/-- The mixed matching `{(M₀, 1/2), (M₁, 1/2)}` (PDF p.2, Theorem 1.1). When `M₀ = M₁` it puts
weight `1` on `M₀`. -/
noncomputable def half (M₀ M₁ : Finset (A × B)) : Finset (A × B) → ℝ :=
  fun M => (if M = M₀ then 1 / 2 else 0) + (if M = M₁ then 1 / 2 else 0)

/-- The pure mixed matching `{(M, 1)}` (PDF p.2, Theorem 1.1). -/
def pure (M : Finset (A × B)) : Finset (A × B) → ℝ :=
  fun N => if N = M then 1 else 0

end PopularMixed


