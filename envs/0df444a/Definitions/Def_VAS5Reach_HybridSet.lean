-- Prove2me | Definitions.Def_VAS5Reach_HybridSet
-- name    : VAS5Reach_HybridSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:29:32.143224+00:00
-- url     : https://prove2.me/theorems/d9883e90-4bde-4bce-8e4d-3b734a1fd4a3
-- title:
--   Hybrid sets $b + P^{\langle c,\cdot\rangle \le K}$, $\mathrm{NORM}(H)$, augmented VASS
-- statement:
--   Given a base $b \in \mathbb N^d$, periods $P = \{p_1, \dots, p_m\} \subseteq \mathbb N^d \setminus \{0\}$, costs $c \in \mathbb N^m$ and $K \in \mathbb N$, the **hybrid set** is
--   $$
--   H = b + P^{\langle c, \cdot\rangle \le K}, \qquad P^{\langle c, \cdot\rangle \le K} = \Bigl\{ \sum_{i=1}^m \lambda_i p_i : \lambda \in \mathbb N^m,\ \langle c, \lambda\rangle \le K \Bigr\}
--   $$
--   (membership `Mem`). A period of cost $0$ is **free** (`freePeriods`). The representation norm is $\mathrm{NORM}(H) := \max\{\|b\|, \|P\|, \|c\|\}$, excluding $K$ (`norm`).
--
--   For a VASS $U = (Q, T)$ with source and target states $p, q$ and period sets $P_1, P_2 \subseteq \mathbb N^d$, the **augmented system** is $U[P_1, P_2] := (Q, T \cup \{(p, a, p) : a \in P_1\} \cup \{(q, -a, q) : a \in P_2\})$ (`augment`). By Definition 6.15, a hybrid set $H$ at state $p$ with free periods $P_0$ is forward $C$-coverable in $U$ if $p(b)$ is forward $C$-coverable in $U[P_0]$ (`HybFwdCoverable`), and $H$ at target state $q$ is backward $C$-coverable if $q(b)$ is backward $C$-coverable in $U[\emptyset, P_0]$ (`HybBwdCoverable`).
--
--   **Formalization Note** A hybrid set is its representation $(b, P, c, K)$, since $\mathrm{NORM}$ depends on it; periods are listed without repetition. The augmented system adds $p$ (resp. $q$) to $Q$ only if it carries an added loop and is not already a state.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 'Linear Set and Hybrid Set', p.13 (PDF p.15); §6.3 and Definition 6.15, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_VAS5Reach_supNorm
import Definitions.Def_VAS5Reach_VASS_FwdCoverable

namespace VAS5Reach

/-- A hybrid set `H = b + P^{⟨c,·⟩≤K}`, given by its representation: a base `b ∈ ℕ^d`, a finite set
of periods `P = {p₁, …, p_m} ⊆ ℕ^d ∖ {0}` (enumerated without repetition), costs `c ∈ ℕ^m` (`c(i)`
is the cost of `pᵢ`) and a budget `K ∈ ℕ`. Its members are the vectors
`b + Σᵢ λᵢ·pᵢ` with `λ ∈ ℕ^m` and `⟨c, λ⟩ ≤ K` (`HybridSet.Mem`).

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 "Linear Set and Hybrid
Set", printed p. 13 (PDF p. 15): "For a finite set P = {p1, . . . , pm} ⊆ N^d \ {0}, write P∗ := […]
A linear set is a set b + P∗, where b ∈ N^d is its base and the vectors in P are its periods. […]
Given c ∈ N^m and K ∈ N, the associated hybrid set is H = b + P^{⟨c,·⟩≤K}, where
P^{⟨c,·⟩≤K} = {Σ_{i=1}^m λi · pi : λ ∈ N^m, ⟨c, λ⟩ ≤ K}. We call c(i) the cost of pi. A period is free
if its cost is zero and restricted if its cost is positive. The representation norm is
NORM(H) := max{∥b∥, ∥P∥, ∥c∥}, where K is excluded from the norm."

**Formalization Note** A hybrid set is its representation `(b, P, c, K)`, because `NORM(H)`
depends on the representation, not only on the set. -/
structure HybridSet (ι : Type) where
  /-- the number `m` of periods -/
  m : ℕ
  /-- the base `b ∈ ℕ^d` -/
  base : ι → ℕ
  /-- the periods `p₁, …, p_m ∈ ℕ^d` -/
  per : Fin m → ι → ℕ
  /-- the costs `c(1), …, c(m) ∈ ℕ` -/
  cost : Fin m → ℕ
  /-- the budget `K ∈ ℕ` -/
  K : ℕ
  /-- periods are nonzero -/
  per_ne_zero : ∀ i, per i ≠ 0
  /-- `P = {p₁, …, p_m}` is enumerated without repetition -/
  per_inj : Function.Injective per

namespace HybridSet

variable {ι : Type}

/-- `x ∈ H`: `x = b + Σᵢ λᵢ·pᵢ` for some `λ ∈ ℕ^m` with `⟨c, λ⟩ ≤ K`. -/
def Mem (H : HybridSet ι) (x : ι → ℕ) : Prop :=
  ∃ l : Fin H.m → ℕ, ∑ i, H.cost i * l i ≤ H.K ∧ x = H.base + ∑ i, l i • H.per i

/-- The representation norm `NORM(H) := max{∥b∥, ∥P∥, ∥c∥}` (max norms; `K` is excluded). -/
def norm [Fintype ι] (H : HybridSet ι) : ℕ :=
  max (supNormN H.base) (max (Finset.univ.sup fun i => supNormN (H.per i))
    (Finset.univ.sup H.cost))

open Classical in
/-- The free periods `P₀ := {pᵢ : c(i) = 0}` of `H`. -/
noncomputable def freePeriods (H : HybridSet ι) : Finset (ι → ℕ) :=
  (Finset.univ.filter fun i => H.cost i = 0).image H.per

end HybridSet

namespace VASS

variable {S ι : Type}

open Classical in
/-- The augmented system `U[P₁, P₂] := (Q, T ∪ {(p, a, p) : a ∈ P₁} ∪ {(q, −a, q) : a ∈ P₂})` for a
VASS `U = (Q, T)` with specified source and target states `p`, `q` and period sets
`P₁, P₂ ⊆ ℕ^d`; `U[P] := U[P, ∅]`.

Source: arXiv:2610.40012 (held version, sha256 a74d76f9…), §6.3, printed p. 30 (PDF p. 32):
"Formally, for a VASS U = (Q, T) with specified source and target states p, q and period sets
P1, P2 ⊆ N^d, define the augmented system: U[P1, P2] := (Q, T ∪ {(p, a, p) : a ∈ P1} ∪
{(q, −a, q) : a ∈ P2}), and abbreviate U[P, ∅] to U[P]."

**Formalization Note** The state set is `Q`, enlarged by `p` (resp. `q`) only when `P₁` (resp.
`P₂`) is nonempty, so that every transition connects states; when `p, q ∈ Q`, as in every use, it
is exactly `Q`. -/
noncomputable def augment (U : VASS S ι) (p q : S) (P₁ P₂ : Finset (ι → ℕ)) : VASS S ι where
  states := U.states ∪ P₁.image (fun _ => p) ∪ P₂.image (fun _ => q)
  trans := U.trans ∪ P₁.image (fun a => (p, fun i => (a i : ℤ), p)) ∪
    P₂.image (fun a => (q, fun i => -(a i : ℤ), q))
  trans_mem := by
    intro τ h
    simp only [Finset.mem_union, Finset.mem_image] at h ⊢
    rcases h with (h | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
    · exact ⟨Or.inl (Or.inl (U.trans_mem τ h).1), Or.inl (Or.inl (U.trans_mem τ h).2)⟩
    · exact ⟨Or.inl (Or.inr ⟨a, ha, rfl⟩), Or.inl (Or.inr ⟨a, ha, rfl⟩)⟩
    · exact ⟨Or.inr ⟨a, ha, rfl⟩, Or.inr ⟨a, ha, rfl⟩⟩

/-- Definition 6.15 (forward): the hybrid set `H = b + P^{⟨c,·⟩≤K}` at state `p` of `U`, with free
periods `P₀`, is forward `C`-coverable in `U` if `p(b)` is forward `C`-coverable in `U[P₀]`.

Source: arXiv:2610.40012 (held version, sha256 a74d76f9…), Definition 6.15, printed p. 30
(PDF p. 32): "Definition 6.15. Let H = b + P^{⟨c,·⟩≤K} be a hybrid set at state p of a VASS U, and
let P0 be its free periods. We say that H is forward C-coverable in U if p(b) is forward
C-coverable in U[P0]. Similarly, H at target state q is backward C-coverable in U if q(b) is
backward C-coverable in U[∅, P0]." -/
def HybFwdCoverable (U : VASS S ι) (C : ℕ) (p : S) (H : HybridSet ι) : Prop :=
  FwdCoverable (augment U p p H.freePeriods ∅) C p H.base

/-- Definition 6.15 (backward): the hybrid set `H` at target state `q` of `U` is backward
`C`-coverable in `U` if `q(b)` is backward `C`-coverable in `U[∅, P₀]`. -/
def HybBwdCoverable (U : VASS S ι) (C : ℕ) (q : S) (H : HybridSet ι) : Prop :=
  BwdCoverable (augment U q q ∅ H.freePeriods) C q H.base

end VASS

end VAS5Reach


