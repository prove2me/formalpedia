-- Prove2me | Definitions.Def_KikuchiMoore_Moore_Paired
-- name    : KikuchiMoore_Moore_Paired
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:42:57.55956+00:00
-- url     : https://prove2.me/theorems/a0562ab3-2cf7-4964-9589-3ff0fce77c54
-- title:
--   Balanced paired transitions, exact weights, and tagged parity lift
-- statement:
--   At a selected residual size $q$, let $a=\lfloor q/2\rfloor$ and $b=\lceil q/2\rceil$. Every residual-disjoint label pair $F,J$ within one selected bundle gives every transition $S\leftrightarrow S\triangle R_F\triangle R_J$ whose two intersections have sizes $a,b$ in either order. An instance stores an unordered endpoint pair and unordered label pair, retaining parallel edges. Its four ports are the Cartesian product of those pairs. If $c(z)$ counts incident instances, set $\delta_e=1+\sum_{z\in P(e)}(c(z)-1)$ and $w_e=1/\delta_e$. The adjacency sums these exact weights and the excess is $\sum_z c(z)(c(z)-1)$. The lift toggles both labels, truncates memory at $2s$, keeps empty-memory components, and inherits normalization. Windows use residuals. Augment each residual with a distinct formal bundle tag and choose a representative system when one exists. Equal-window edges use the least genuine representative among the two labels; unequal-window edges select an endpoint with a nonempty support difference, breaking two-sided ties by its least vertex. Capacity and norm bounds are not assumed.
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Definitions and constructions, Sections 3–5, printed p. 17 = PDF p. 17, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Bundles
import Definitions.Def_KikuchiMoore_Moore_Even

noncomputable section
open scoped BigOperators symmDiff

namespace KikuchiMoore.Moore

/-- Unordered endpoint pair and unordered label pair; different labels stay parallel. -/
abbrev PairInstance (n l : ℕ) := Finset (Row n l) × Finset (Finset (Fin n))
abbrev Port (n l : ℕ) := Row n l × Finset (Fin n)

def Balanced {n : ℕ} (q : ℕ) (S R T : Finset (Fin n)) : Prop :=
  ((S ∩ R).card = q / 2 ∧ (S ∩ T).card = (q + 1) / 2) ∨
  ((S ∩ R).card = (q + 1) / 2 ∧ (S ∩ T).card = q / 2)

def pairInstances {n l : ℕ} (k q : ℕ) (P : Finset (Bundle n)) :
    Finset (PairInstance n l) := by
  classical
  exact Finset.univ.filter fun e => ∃ B ∈ P, B.center.card = k - q ∧
    ∃ F ∈ B.members, ∃ J ∈ B.members, F ≠ J ∧
    Disjoint (residual B F) (residual B J) ∧
    ∃ S T : Row n l, S ≠ T ∧ e = ({S, T}, {F, J}) ∧
      T.val = (S.val ∆ residual B F) ∆ residual B J ∧
      Balanced q S.val (residual B F) (residual B J)

def ports {n l : ℕ} (e : PairInstance n l) : Finset (Port n l) := e.1.product e.2

def contention {n l : ℕ} (E : Finset (PairInstance n l)) (z : Port n l) : ℕ :=
  (E.filter (fun e => z ∈ ports e)).card

def excess {n l : ℕ} (E : Finset (PairInstance n l)) : ℝ :=
  ∑ z : Port n l, (contention E z : ℝ) * ((contention E z : ℝ) - 1)

def instanceWeight {n l : ℕ} (E : Finset (PairInstance n l)) (e : PairInstance n l) : ℝ :=
  (1 + ∑ z ∈ ports e, ((contention E z : ℝ) - 1))⁻¹

def pairedAdj {n l : ℕ} (k q : ℕ) (P : Finset (Bundle n)) :
    Matrix (Row n l) (Row n l) ℝ := by
  classical
  let E : Finset (PairInstance n l) := pairInstances k q P
  exact fun S T => ∑ e ∈ E, if S ≠ T ∧ S ∈ e.1 ∧ T ∈ e.1 then instanceWeight E e else 0

def xi (n k l q : ℕ) : ℝ :=
  8 * (Nat.choose q (q / 2) : ℝ) * (2.031 : ℝ) ^ (q / 2) *
    Real.rpow ((n : ℝ) / l) (((q + 1) / 2 : ℕ) - (k : ℝ) / 2)

def pairedStep {n l : ℕ} (H : Hypergraph n) (k q s : ℕ)
    (P : Finset (Bundle n)) (x y : State n l) : Prop :=
  permitted H (2 * s) x ∧ permitted H (2 * s) y ∧
  ∃ e ∈ (pairInstances k q P : Finset (PairInstance n l)),
    x.1 ≠ y.1 ∧ x.1 ∈ e.1 ∧ y.1 ∈ e.1 ∧ y.2 = x.2 ∆ e.2

def pairedReachable {n l : ℕ} (H : Hypergraph n) (k q s : ℕ)
    (P : Finset (Bundle n)) (x : State n l) : Prop :=
  ∃ S : Row n l, Relation.ReflTransGen (pairedStep H k q s P) (S, ∅) x

def pairedLiftRaw {n l : ℕ} (H : Hypergraph n) (k q s : ℕ)
    (P : Finset (Bundle n)) : Matrix (State n l) (State n l) ℝ := by
  classical
  let E : Finset (PairInstance n l) := pairInstances k q P
  exact fun x y => if pairedReachable H k q s P x ∧ pairedReachable H k q s P y ∧
      permitted H (2*s) x ∧ permitted H (2*s) y then
    ∑ e ∈ E, if x.1 ≠ y.1 ∧ x.1 ∈ e.1 ∧ y.1 ∈ e.1 ∧ y.2 = x.2 ∆ e.2
      then instanceWeight E e else 0
    else 0

def pairedLift {n l : ℕ} (H : Hypergraph n) (k q s : ℕ)
    (P : Finset (Bundle n)) : Matrix (State n l) (State n l) ℝ :=
  normalizedLift (pairedAdj k q P) Prod.fst (pairedLiftRaw H k q s P)

def packedResidual {n : ℕ} (P : Finset (Bundle n)) (F : Finset (Fin n)) : Finset (Fin n) :=
  (P.filter (fun B => F ∈ B.members)).biUnion (fun B => residual B F)

def pairedWindow {n l : ℕ} (P : Finset (Bundle n)) (x : State n l) : Finset (Fin n) :=
  x.1.val ∪ x.2.biUnion (packedResidual P)

/-- Bundle tags are distinct from all genuine vertices. -/
def augmented {n : ℕ} (B : Bundle n) (F : Finset (Fin n)) : Finset (Fin n ⊕ Bundle n) :=
  (residual B F).image Sum.inl ∪ {Sum.inr B}

def TaggedRepSystem {n : ℕ} (P : Finset (Bundle n)) (W : Finset (Fin n))
    (rho : Finset (Fin n) → Option (Fin n ⊕ Bundle n)) : Prop :=
  (∀ B ∈ P, ∀ F ∈ B.members, residual B F ⊆ W →
    ∃ v ∈ augmented B F, rho F = some v) ∧
  ∀ F ∈ packed P, packedResidual P F ⊆ W →
    ∀ J ∈ packed P, packedResidual P J ⊆ W → rho F = rho J → F = J

def taggedRepresentative {n : ℕ} (P : Finset (Bundle n)) (W : Finset (Fin n)) :
    Finset (Fin n) → Option (Fin n ⊕ Bundle n) := by
  classical
  exact if h : ∃ rho, TaggedRepSystem P W rho then Classical.choose h else fun _ => none

/-- A fixed total order supplies the source's arbitrary deterministic tie breaks. -/
def pairedToward {n l : ℕ} (P : Finset (Bundle n))
    (x y : State n l) (labels : Finset (Finset (Fin n))) : Prop := by
  classical
  let W := pairedWindow P x
  let V := pairedWindow P y
  let candidates := Finset.univ.filter fun v : Fin n =>
    ∃ F ∈ labels, taggedRepresentative P W F = some (Sum.inl v)
  exact if W = V then
    ∃ h : candidates.Nonempty, candidates.min' h ∈ y.1.val
  else if (W \ V).Nonempty ∧ (V \ W).Nonempty then
    (W \ V).min < (V \ W).min
  else (V \ W).Nonempty

end KikuchiMoore.Moore


