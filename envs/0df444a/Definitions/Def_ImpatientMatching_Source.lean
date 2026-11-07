-- Prove2me | Definitions.Def_ImpatientMatching_Source
-- name    : ImpatientMatching_Source
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:22.942492+00:00
-- url     : https://prove2.me/theorems/c876255d-3a8c-4c7c-80ec-244b1777c789
-- title:
--   The cubic vertex-cover source: $\tau(H)$, $\Phi(P)$, Theorem 4.1 and disjoint copies
-- statement:
--   For a finite simple graph $H$ on $n$ vertices, $\tau(H)$ is the minimum vertex-cover size, and for a vertex set $P$,
--   $$u(P)=|\{e\in E_H:e\cap P=\emptyset\}|,\qquad \Phi(P)=|P|+u(P).$$
--   The **source range** requires $H$ cubic and $n/2\le K<n$.
--
--   With $\varepsilon=1/100$, the proposition **CubicVCGap** is the statement of Theorem 4.1 of the source: it is NP-hard to distinguish $\tau(H)\le K$ from $\tau(H)\ge(1+\varepsilon)K$ on such pairs $(H,K)$, in the Karp form of the published `GapNPHard` over the binary encoding of $(H,K)$.
--
--   The module also defines $r$ disjoint copies of a graph, the padding step that brings the source to size at least $n_0$.
--
--   **Formalization Note** The source cites Theorem 4.1 from Chlebík–Chlebíková and does not prove it, so it is a named proposition, not a claim of this module. $\tau$ is Mathlib's `vertexCoverNum` as a natural number, finite on a finite graph.
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), §4.1, pp.10–11; §4.3, p.13; §C.1, pp.28–29

import Definitions.Def_ImpatientMatching_Input
import Definitions.Def_SetCoverThreshold_SetCover_Complexity

open NSWApxHard.Reduction

namespace ImpatientMatching

/-- `ε = 1/100` of Theorem 4.1, Yan–Varma, manuscript (sha256 7b1051b6…), p.10. -/
def eps : ℚ := 1 / 100

/-- `τ(H)`, the minimum vertex-cover size (p.10), by Mathlib's `vertexCoverNum`.

**Formalization Note.** `vertexCoverNum` lives in `ℕ∞` and is finite on a finite graph, since the
whole vertex set is a cover, so `toNat` loses nothing. -/
noncomputable def tau (H : GraphInput) : ℕ := H.G.vertexCoverNum.toNat

/-- `u(P) := |{e ∈ E_H : e ∩ P = ∅}|` of p.13, the number of edges uncovered by `P`. -/
noncomputable def uncovered (H : GraphInput) (P : Finset (Fin H.N)) : ℕ :=
  Set.ncard {e | e ∈ H.G.edgeSet ∧ ∀ v ∈ e, v ∉ P}

/-- `Φ(P) := |P| + u(P)` of p.13. -/
noncomputable def Phi (H : GraphInput) (P : Finset (Fin H.N)) : ℕ := P.card + uncovered H P

/-- The source range clauses (6), p.10, and (36), p.28: `H` is cubic and `n/2 ≤ K < n`. -/
def IsSourceRange (H : GraphInput) (K : ℕ) : Prop :=
  IsCubic H.G ∧ H.N ≤ 2 * K ∧ K < H.N

/-- The binary encoding of a source instance `(H, K)`. -/
noncomputable def encVC (p : GraphInput × ℕ) : List Bool := natBits p.2 ++ encGraph p.1

/-- The YES case of (5), p.10: `τ(H) ≤ K` on the source range. -/
def vcGapYes (p : GraphInput × ℕ) : Prop := IsSourceRange p.1 p.2 ∧ tau p.1 ≤ p.2

/-- The NO case of (5), p.10: `τ(H) ≥ (1 + ε)K` on the source range. -/
def vcGapNo (p : GraphInput × ℕ) : Prop :=
  IsSourceRange p.1 p.2 ∧ (1 + (eps : ℝ)) * (p.2 : ℝ) ≤ (tau p.1 : ℝ)

/-- **Theorem 4.1 (cubic vertex-cover gap)**, Yan–Varma, manuscript (sha256 7b1051b6…), p.10, as a
proposition: for `ε = 1/100` it is NP-hard to distinguish `τ(H) ≤ K` from `τ(H) ≥ (1 + ε)K` on finite
simple cubic graphs with `n` vertices and an integer threshold with `n/2 ≤ K < n`.

**Formalization Note.** The source cites this result ("the cubic 100/99 inapproximability theorem
[CC06]") and does not prove it, so it is a named proposition for the statements that use it, in the
Karp form of the published `GapNPHard`. -/
def CubicVCGap : Prop :=
  SetCoverThreshold.SetCover.GapNPHard encVC vcGapYes vcGapNo

/-- `r` disjoint copies of `H` on `Fin (r * H.N)` (§4.1, p.11; (38), p.29): two vertices are adjacent
when they lie in one copy and their projections are adjacent. -/
def copies (r : ℕ) (H : GraphInput) : GraphInput where
  N := r * H.N
  G :=
    { Adj := fun a b => (finProdFinEquiv.symm a).1 = (finProdFinEquiv.symm b).1 ∧
        H.G.Adj (finProdFinEquiv.symm a).2 (finProdFinEquiv.symm b).2
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
      loopless := ⟨fun _ h => H.G.irrefl h.2⟩ }

end ImpatientMatching


