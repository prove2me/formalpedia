-- Prove2me | Definitions.Def_StableCount_Rotation
-- name    : StableCount_Rotation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:02.879682+00:00
-- url     : https://prove2.me/theorems/7dd61e5b-19f8-40a2-8368-24407d72d158
-- title:
--   Rotations (Definition 2.1), the full rotation order, maximal chains and the normalization $\hat I$
-- statement:
--   Fix an instance $I$. On stable matchings, $\mu\le\nu$ when every man prefers his partner in $\mu$ to his partner in $\nu$ or has the same partner in both, and $\nu$ covers $\mu$ if $\mu<\nu$ with no stable matching strictly between. The man-optimal matching $\mu_M$ gives every man his most preferred stable partner, and the woman-optimal matching $\mu_W$ gives every woman her most preferred stable partner.
--
--   For a stable matching $\mu$ and a man $v$, $s_\mu(v)$ is the first woman below $\mu(v)$ on $v$'s list who prefers $v$ to her partner under $\mu$, if any. An ordered list of distinct pairs of $\mu$,
--   $$
--   \rho=\big((v_0,w_0),\dots,(v_{k-1},w_{k-1})\big),\qquad k\ge 2,
--   $$
--   is a **rotation exposed in** $\mu$ if $s_\mu(v_i)=w_{i+1}$ for every $i$, indices modulo $k$. Its elimination replaces $v_iw_i$ by $v_iw_{i+1}$ and leaves all other pairs unchanged, giving $\mu/\rho$. The set $\Pi(I)$ consists of all rotations exposed in at least one stable matching, a rotation being the same under a change of starting pair.
--
--   For distinct rotations, $\rho\prec_f\sigma$ if every rotation elimination sequence from $\mu_M$ containing $\sigma$ eliminates $\rho$ before $\sigma$. A **maximal chain** is $\mu_0=\mu_M<\mu_1<\dots<\mu_R=\mu_W$ in which each matching covers its predecessor. An instance is **normalized** if each person ranks all their stable partners before all their other partners, and $\hat I$ is obtained from $I$ by moving each person's stable partners to the beginning of their list, preserving their relative order, with the remaining partners afterwards in their original relative order.
--
--   This module is the structural vocabulary of stable matchings on which the rotation poset of the paper is built.
--
--   **Formalization Note** A rotation is a `Cycle` of pairs, so the choice of starting pair is quotiented out. The elimination $\mu/\rho$ is a relation between matchings, which determines the result. `IsManOptimal` records the men's clause only; the women's clause on p.7 is its consequence. `normalize` is a function of $I$, built by sorting with `Tuple.sort`.
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), §2.1, pp.7–8; Definition 2.1, p.8; Remark, p.10; §2.2, p.9

import Mathlib
import Definitions.Def_StableCount_Count

namespace StableCount

open StableMatching

variable {n : ℕ}

/-- The relation `μ ≤ ν` on matchings: every man prefers his partner in `μ` to his partner in `ν`,
or has the same partner in both (arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.1, p.8). It is the
order of `StableMatching.stable_matchings_distribLattice`. -/
def MatchingLE (I : Instance n) (μ ν : Matching n) : Prop :=
  ∀ m, I.manRank m (μ m) ≤ I.manRank m (ν m)

instance (I : Instance n) (μ ν : Matching n) : Decidable (MatchingLE I μ ν) := by
  unfold MatchingLE; infer_instance

/-- The strict relation `μ < ν` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.1, p.8). -/
def MatchingLT (I : Instance n) (μ ν : Matching n) : Prop := MatchingLE I μ ν ∧ μ ≠ ν

instance (I : Instance n) (μ ν : Matching n) : Decidable (MatchingLT I μ ν) := by
  unfold MatchingLT; infer_instance

/-- The stable matching `ν` covers the stable matching `μ`: `μ < ν` and no stable matching lies
strictly between (arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.1, p.8). -/
def Covers (I : Instance n) (μ ν : Matching n) : Prop :=
  I.IsStable μ ∧ I.IsStable ν ∧ MatchingLT I μ ν ∧
    ∀ η, I.IsStable η → ¬ (MatchingLT I μ η ∧ MatchingLT I η ν)

instance (I : Instance n) (μ ν : Matching n) : Decidable (Covers I μ ν) := by
  unfold Covers; infer_instance

/-- `μ` is the man-optimal stable matching `µ_M`: every man receives his most preferred stable
partner (arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.1, p.7).

**Formalization Note** The page also says every woman receives her least preferred stable partner.
That is a consequence (the optimality theorem of Gale and Shapley) and is not part of the
predicate, which already determines `μ`. -/
def IsManOptimal (I : Instance n) (μ : Matching n) : Prop :=
  I.IsStable μ ∧ ∀ ν, I.IsStable ν → ∀ m, I.manRank m (μ m) ≤ I.manRank m (ν m)

instance (I : Instance n) (μ : Matching n) : Decidable (IsManOptimal I μ) := by
  unfold IsManOptimal; infer_instance

/-- `μ` is the woman-optimal stable matching `µ_W`: every woman receives her most preferred stable
partner (arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.1, p.7). -/
def IsWomanOptimal (I : Instance n) (μ : Matching n) : Prop :=
  I.IsStable μ ∧ ∀ ν, I.IsStable ν → ∀ w, I.womanRank w (μ.symm w) ≤ I.womanRank w (ν.symm w)

instance (I : Instance n) (μ : Matching n) : Decidable (IsWomanOptimal I μ) := by
  unfold IsWomanOptimal; infer_instance

/-- The women below `μ(v)` on `v`'s list who prefer `v` to their partner under `μ`
(arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.1, p.8). -/
def sCandidates (I : Instance n) (μ : Matching n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun w => I.manPrefers v (μ v) w ∧ I.womanPrefers w v (μ.symm w)

/-- `s_µ(v)`: scan `v`'s list below `µ(v)` and take the first woman who prefers `v` to her partner
under `µ`; `none` if there is no such woman (arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.1,
p.8). -/
def sMu (I : Instance n) (μ : Matching n) (v : Fin n) : Option (Fin n) :=
  if h : (sCandidates I μ v).Nonempty then
    some ((I.manRank v).symm (((sCandidates I μ v).image (I.manRank v)).min' (h.image _)))
  else none

/-- A rotation, up to the choice of starting pair: a cyclic list of (man, woman) pairs
(arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.1, p.8: "starting the list at another pair and
keeping the same cyclic order describes the same rotation"). -/
abbrev Rot (n : ℕ) := Cycle (Fin n × Fin n)

/-- Definition 2.1 for an ordered list: `l = ((v₀,w₀),…,(v_{k−1},w_{k−1}))`, `k ≥ 2`, is a list of
distinct pairs of the stable matching `µ` with `s_µ(vᵢ) = w_{i+1}` for every `i`, indices modulo `k`
(arXiv:2611.06494, held PDF sha256 9445f6a8…, Definition 2.1, p.8). -/
def IsExposedList (I : Instance n) (μ : Matching n) (l : List (Fin n × Fin n)) : Prop :=
  I.IsStable μ ∧ 2 ≤ l.length ∧ l.Nodup ∧ (∀ p ∈ l, μ p.1 = p.2) ∧
    ∀ (i : ℕ) (hi : i < l.length),
      sMu I μ (l[i]).1 = some (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))).2

/-- The rotation `ρ` is exposed in `μ` (arXiv:2611.06494, held PDF sha256 9445f6a8…, Definition 2.1,
p.8): some list describing it satisfies Definition 2.1. -/
def IsExposed (I : Instance n) (μ : Matching n) (ρ : Rot n) : Prop :=
  ∃ l : List (Fin n × Fin n), (l : Cycle (Fin n × Fin n)) = ρ ∧ IsExposedList I μ l

/-- `ν` is the matching obtained from `μ` by replacing `vᵢwᵢ` by `vᵢw_{i+1}`, indices modulo the
length, and leaving all other pairs unchanged (arXiv:2611.06494, held PDF sha256 9445f6a8…,
Definition 2.1, p.8). -/
def IsElimList (μ : Matching n) (l : List (Fin n × Fin n)) (ν : Matching n) : Prop :=
  (∀ (i : ℕ) (hi : i < l.length),
      ν (l[i]).1 = (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))).2) ∧
    ∀ v, v ∉ l.map Prod.fst → ν v = μ v

/-- `ν = µ/ρ`, the result of eliminating `ρ` from `µ` (arXiv:2611.06494, held PDF sha256 9445f6a8…,
Definition 2.1, p.8).

**Formalization Note** A relation between matchings rather than a function: it determines `ν`. -/
def IsElim (μ : Matching n) (ρ : Rot n) (ν : Matching n) : Prop :=
  ∃ l : List (Fin n × Fin n), (l : Cycle (Fin n × Fin n)) = ρ ∧ IsElimList μ l ν

/-- `Π(I)`: the set of all rotations exposed in at least one stable matching of `I`
(arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.1, p.8). -/
def Pi (I : Instance n) : Set (Rot n) := {ρ | ∃ μ, IsExposed I μ ρ}

/-- `l` is a rotation elimination sequence from `μ`, ending in `ν`: each rotation is exposed in the
current matching and is then eliminated (arXiv:2611.06494, held PDF sha256 9445f6a8…, Remark, p.10). -/
def IsElimSeq (I : Instance n) : Matching n → List (Rot n) → Matching n → Prop
  | μ, [], ν => ν = μ
  | μ, ρ :: l, ν => IsExposed I μ ρ ∧ ∃ μ', IsElim μ ρ μ' ∧ IsElimSeq I μ' l ν

/-- The full rotation order: for distinct rotations `ρ, σ`, `ρ ≺f σ` if every rotation elimination
sequence starting from `µ_M` and containing `σ` eliminates `ρ` before `σ` (arXiv:2611.06494, held
PDF sha256 9445f6a8…, Remark, p.10). -/
def FullLT (I : Instance n) (ρ σ : Rot n) : Prop :=
  ρ ≠ σ ∧ ∀ μM l ν, IsManOptimal I μM → IsElimSeq I μM l ν → σ ∈ l →
    ∃ l₁ l₂, l = l₁ ++ σ :: l₂ ∧ ρ ∈ l₁

/-- `D` is a downset of the full rotation poset `Q_f = (Π, ≺f)` (arXiv:2611.06494, held PDF sha256
9445f6a8…, §1.2, p.4; Lemma 3.1, p.10). -/
def IsFullDownset (I : Instance n) (D : Set (Rot n)) : Prop :=
  D ⊆ Pi I ∧ ∀ σ ∈ D, ∀ ρ ∈ Pi I, FullLT I ρ σ → ρ ∈ D

/-- `l` lists the rotations of `D` once each, in an order consistent with `Q_f`
(arXiv:2611.06494, held PDF sha256 9445f6a8…, Lemma 3.1, p.10). -/
def IsConsistentOrder (I : Instance n) (D : Set (Rot n)) (l : List (Rot n)) : Prop :=
  l.Nodup ∧ (∀ ρ, ρ ∈ l ↔ ρ ∈ D) ∧ l.Pairwise fun ρ σ => ¬ FullLT I σ ρ

/-- `µ₀ = µ_M < µ₁ < ⋯ < µ_R = µ_W` is a maximal chain of stable matchings: display (MC)
(arXiv:2611.06494, held PDF sha256 9445f6a8…, (MC), p.8). Maximality means each matching covers its
predecessor. -/
def IsMaximalChain (I : Instance n) {R : ℕ} (μ : Fin (R + 1) → Matching n) : Prop :=
  IsManOptimal I (μ 0) ∧ IsWomanOptimal I (μ (Fin.last R)) ∧
    ∀ i : Fin R, Covers I (μ i.castSucc) (μ i.succ)

/-- `I` is normalized: each person ranks all their stable partners before all their other partners
(arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.2, p.9). -/
def IsNormalized (I : Instance n) : Prop :=
  (∀ v w w', w ∈ manPartners I v → w' ∉ manPartners I v → I.manPrefers v w w') ∧
    ∀ w v v', v ∈ womanPartners I w → v' ∉ womanPartners I w → I.womanPrefers w v v'

/-- The sort key of the normalized list: the members of `S` come first, each block in the original
order of `r` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.2, p.9). -/
def reorderKey (r : Fin n ≃ Fin n) (S : Finset (Fin n)) (x : Fin n) : ℕ :=
  if x ∈ S then (r x : ℕ) else n + (r x : ℕ)

/-- The rank bijection of the list obtained from the list of `r` by moving the members of `S` to the
beginning, preserving their relative order, and placing all others afterwards in their original
relative order (arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.2, p.9).

**Formalization Note** `Tuple.sort f` sends a position to the element in that position of the sorted
list, so its inverse sends an element to its new position; `reorderKey` is injective, so the sort
is unique. -/
noncomputable def reorder (r : Fin n ≃ Fin n) (S : Finset (Fin n)) : Fin n ≃ Fin n :=
  (Tuple.sort (reorderKey r S)).symm

/-- The normalization `Î` of `I`: each person's stable partners are moved to the beginning of their
preference list, preserving their relative order, and all remaining partners follow in their
original relative order (arXiv:2611.06494, held PDF sha256 9445f6a8…, §2.2, p.9). -/
noncomputable def normalize (I : Instance n) : Instance n where
  manRank v := reorder (I.manRank v) (manPartners I v)
  womanRank w := reorder (I.womanRank w) (womanPartners I w)

end StableCount


