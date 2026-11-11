-- Prove2me | Definitions.Def_SwitchingStable_Universal_Model
-- name    : SwitchingStable_Universal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:42.079395+00:00
-- url     : https://prove2.me/theorems/f0c67db4-bcb7-40e4-9a81-c39226d93ce8
-- title:
--   Stable lists, promotion, signed movement, witnesses and occurrence classes
-- statement:
--   Let $I$ be a complete strict market with $n$ agents on each side and let $\mu$ be a stable perfect matching. The ordered list of man $u$ contains exactly his stable partners, ordered from best to worst. Its size is $d_u$ and his current zero-based position is $q_u=\operatorname{idx}_u(\mu)$. For $\varepsilon\in\{-1,1\}$, a witness $h\ne u$ at distance $j$ satisfies
--   $$\nu(h)=\mu(h)\Longrightarrow\varepsilon(\operatorname{idx}_u(\nu)-q_u)<j\qquad(\nu\in\mathrm{Stab}(I)).$$
--   An additional witness lies outside the first $j$ directional owners. The file constructs stable-partner promotion, the next-owner map, all occurrence classes, the actual one-, two- and three-cycle swaps, the Appendix B exceptional case and the third-boundary failures. Counts range over every pair $(\mu,u)$ with $\mu\in\mathrm{Stab}(I)$.
--
--   These definitions provide the finite structural model used by the universal counting argument. Promotion is reconstructed from its exact strict comparison order; Lemma 6 establishes that reconstruction and its stable-pair properties.
--
--   The witness domain is explicitly $1\le j\le b_u^\varepsilon$, as in Definition 1. A separate boundary-implication predicate gives the logical formula without treating nonexistent boundaries as witnesses.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), pp. 2–7, 19, PDF pp. 3–8, 20, Sections 2–3 and Appendix B

import Mathlib
import Definitions.Def_StableMatching_GaleShapley
import Definitions.Def_StableCount_Count

namespace SwitchingStable.Universal

open StableMatching
variable {n : ℕ}

/-- Section 2: exactly the whole stable set. -/
abbrev StableSet (I : Instance n) := {μ : Matching n // I.IsStable μ}
noncomputable def partners (I : Instance n) (u : Fin n) : List (Fin n) :=
  (((StableCount.manPartners I u).image (I.manRank u)).sort (· ≤ ·)).map (I.manRank u).symm
/-- Index is the number of strictly better stable partners; valid on stable edges. -/
def idx (I : Instance n) (μ : Matching n) (u : Fin n) : ℕ :=
  ((StableCount.manPartners I u).filter fun v => I.manPrefers u v (μ u)).card
def degree (I : Instance n) (u : Fin n) : ℕ := (StableCount.manPartners I u).card
/-- Fallback is read only off the valid stable-list domain. -/
noncomputable def atPartner (I : Instance n) (μ : Matching n) (u : Fin n) (r : ℤ) : Fin n :=
  (partners I u)[r.toNat]?.getD (μ u)
inductive Direction where | right | left deriving DecidableEq

def Direction.sign : Direction → ℤ | .right => 1 | .left => -1
def Direction.reverse : Direction → Direction | .right => .left | .left => .right

def distance (I : Instance n) (μ : Matching n) (u : Fin n) (ε : Direction) : ℕ :=
  match ε with | .right => degree I u - 1 - idx I μ u | .left => idx I μ u
noncomputable def owner (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) (j : ℕ) : Fin n :=
  μ.symm (atPartner I μ u ((idx I μ u : ℤ) + ε.sign * (j : ℤ)))
def Active (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  0 < distance I μ u ε
noncomputable def next (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Fin n :=
  by
    classical
    exact if Active I μ ε u then owner I μ ε u 1 else u

def BoundaryImplication (I : Instance n) (μ : Matching n) (ε : Direction) (u h : Fin n) (j : ℕ) : Prop :=
  h ≠ u ∧ ∀ ν : Matching n, I.IsStable ν → ν h = μ h →
    ε.sign * ((idx I ν u : ℤ) - (idx I μ u : ℤ)) < (j : ℤ)
/-- Definition 1: a witness is only named at an existing positive directional boundary. -/
def Witness (I : Instance n) (μ : Matching n) (ε : Direction) (u h : Fin n) (j : ℕ) : Prop :=
  1 ≤ j ∧ j ≤ distance I μ u ε ∧ BoundaryImplication I μ ε u h j
noncomputable def Additional (I : Instance n) (μ : Matching n) (ε : Direction)
    (u h : Fin n) (j : ℕ) : Prop :=
  Witness I μ ε u h j ∧ ∀ k : ℕ, 1 ≤ k → k ≤ j → owner I μ ε u k ≠ h

/-- Literal stable-partner promotion comparison, preserving both internal orders. -/
def PromotedBefore (S : Finset (Fin n)) (rank : Fin n ≃ Fin n) (v w : Fin n) : Prop :=
  (v ∈ S ∧ w ∉ S) ∨ ((v ∈ S ↔ w ∈ S) ∧ rank v < rank w)
noncomputable def promotedRank (S : Finset (Fin n)) (rank : Fin n ≃ Fin n) : Fin n ≃ Fin n :=
  by
    classical
    exact if h : ∃ r : Fin n ≃ Fin n, ∀ v w, r v < r w ↔ PromotedBefore S rank v w
      then Classical.choose h else rank
/-- Finite order reconstruction; Lemma 6 asserts the reconstruction property as well. -/
noncomputable def promote (I : Instance n) : Instance n where
  manRank u := promotedRank (StableCount.manPartners I u) (I.manRank u)
  womanRank v := promotedRank (StableCount.womanPartners I v) (I.womanRank v)
def HasPromotedOrders (I : Instance n) : Prop :=
  (∀ u v w, (promote I).manPrefers u v w ↔
    PromotedBefore (StableCount.manPartners I u) (I.manRank u) v w) ∧
  (∀ v u h, (promote I).womanPrefers v u h ↔
    PromotedBefore (StableCount.womanPartners I v) (I.womanRank v) u h)
def StablePartnersFirst (I : Instance n) : Prop :=
  (∀ u v w, v ∈ StableCount.manPartners I u → w ∉ StableCount.manPartners I u → I.manPrefers u v w) ∧
  (∀ v u h, u ∈ StableCount.womanPartners I v → h ∉ StableCount.womanPartners I v → I.womanPrefers v u h)

/-- Section 3 occurrence classes, evaluated at the supplied stable matching. -/
noncomputable def R (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  Active I μ ε u ∧ next I μ ε (next I μ ε u) ≠ u
noncomputable def S (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  ¬ Active I μ ε u ∨ (next I μ ε (next I μ ε u) = u ∧ distance I μ u ε = 1)
noncomputable def E (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  2 ≤ distance I μ u ε ∧ next I μ ε (next I μ ε u) = u ∧
    next I μ ε (owner I μ ε u 2) ∉ ({u, next I μ ε u} : Finset (Fin n))
noncomputable def Fa (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  2 ≤ distance I μ u ε ∧ next I μ ε (next I μ ε u) = u ∧ next I μ ε (owner I μ ε u 2) = u
noncomputable def Fb (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  2 ≤ distance I μ u ε ∧ next I μ ε (next I μ ε u) = u ∧
    next I μ ε (owner I μ ε u 2) = next I μ ε u
noncomputable def Opposite (I : Instance n) (μ : Matching n) (ε : Direction) (u h : Fin n) : Prop :=
  0 < distance I μ u ε.reverse ∧ owner I μ ε.reverse u 1 = h
noncomputable def R1 (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  R I μ ε u ∧ Opposite I μ ε u (next I μ ε (next I μ ε u))
noncomputable def R0 (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  R I μ ε u ∧ ¬ R1 I μ ε u
noncomputable def D (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  R I μ ε u ∧ next I μ ε (next I μ ε (next I μ ε u)) ∉
    ({u, next I μ ε u, next I μ ε (next I μ ε u)} : Finset (Fin n))
noncomputable def Eadj (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  E I μ ε u ∧ Opposite I μ ε u (next I μ ε (owner I μ ε u 2))
noncomputable def W (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  Fb I μ ε u ∧ 3 ≤ distance I μ u ε ∧ next I μ ε (owner I μ ε u 3) ∉
    ({u, next I μ ε u, owner I μ ε u 2} : Finset (Fin n))
noncomputable def B (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  Fb I μ ε u ∧ ¬ W I μ ε u
noncomputable def T0 (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  R0 I μ ε u ∧ next I μ ε (next I μ ε (next I μ ε u)) = next I μ ε u
noncomputable def D0 (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  D I μ ε u ∧ R0 I μ ε u
noncomputable def D1 (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  D I μ ε u ∧ ¬ D0 I μ ε u
noncomputable def C0 (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  R0 I μ ε u ∧ ¬ T0 I μ ε u ∧ ¬ D0 I μ ε u
noncomputable def swap (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Matching n :=
  (Equiv.swap u (next I μ ε u)).trans μ
noncomputable def swapTwice (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Matching n :=
  swap I (swap I μ ε u) ε u
noncomputable def swapThree (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Matching n :=
  let p := next I μ ε u
  let h := next I μ ε p
  ((Equiv.swap u p).trans (Equiv.swap u h)).trans μ
/-- The actual exceptional case v = w0 in Appendix B, proof of Lemma 11. -/
noncomputable def Exceptional (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  C0 I μ ε u ∧ 2 ≤ distance I μ u ε ∧
  owner I μ ε u 2 = next I μ ε (next I μ ε u) ∧
  let ν := swapThree I μ ε u
  let p := next I μ ε u
  Active I ν ε p ∧ ν (next I ν ε p) = μ u
noncomputable def Failure (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  T0 I μ ε u ∧ 3 ≤ distance I μ u ε ∧
  ∀ z : Fin n, z ∉ ({u, owner I μ ε u 1, owner I μ ε u 2, owner I μ ε u 3} : Finset (Fin n)) →
    ∃ ν : Matching n, I.IsStable ν ∧ ν z = μ z ∧
      (3 : ℤ) ≤ ε.sign * ((idx I ν u : ℤ) - (idx I μ u : ℤ))
abbrev Occurrence (I : Instance n) := StableSet I × Fin n
noncomputable def count (I : Instance n) (P : Matching n → Fin n → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter fun o : Occurrence I => P o.1.val o.2).card
noncomputable def badE (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  E I μ ε u ∧ ¬ Eadj I μ ε u ∧ ¬ T0 I (swap I μ ε u) ε u
noncomputable def badW (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  W I μ ε u ∧ ¬ T0 I (swapTwice I μ ε u) ε u

end SwitchingStable.Universal


