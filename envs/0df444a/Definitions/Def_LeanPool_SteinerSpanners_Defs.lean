-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_Defs
-- name    : LeanPool_SteinerSpanners_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:45:52.121528+00:00
-- url     : https://prove2.me/theorems/3d0f5c9a-6d8a-46cf-8bd1-3382a68e0d5c
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Defs.lean

module
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
namespace HighDimSteinerSpanners
noncomputable def lpDist (p : ℝ) {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  (∑ i : Fin d, |x i - y i| ^ p) ^ (1 / p)
noncomputable def maxPairwiseDist (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) : ℝ :=
  if hn : 0 < n then
    haveI : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
    Finset.univ.sup' Finset.univ_nonempty (fun ij : Fin n × Fin n => lpDist p (P ij.1) (P ij.2))
  else 0
noncomputable def minDistinctPairwiseDist (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) : ℝ :=
  let offDiag := Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
  if hne : offDiag.Nonempty then
    offDiag.inf' hne (fun ij => lpDist p (P ij.1) (P ij.2))
  else 0
noncomputable def aspectRatio (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) : ℝ :=
  maxPairwiseDist p P / minDistinctPairwiseDist p P
def walkWeight {V : Type} {H : SimpleGraph V} (w : Sym2 V → ℝ) :
    ∀ {u v : V}, H.Walk u v → ℝ
  | _, _, .nil => 0
  | u, _, @SimpleGraph.Walk.cons _ _ _ b _ _ q => w s(u, b) + walkWeight w q
noncomputable def graphDist {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) (u v : V) : ℝ≥0∞ :=
  ⨅ p : H.Walk u v, ENNReal.ofReal (walkWeight w p)
structure IsNonMetricSteinerSpanner (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) (C : ℝ)
    {S : Type} [Fintype S] (H : SimpleGraph (Fin n ⊕ S)) (w : Sym2 (Fin n ⊕ S) → ℝ) : Prop where
  weight_nonneg : ∀ e ∈ H.edgeSet, 0 ≤ w e
  noncontracting : ∀ i j : Fin n,
    ENNReal.ofReal (lpDist p (P i) (P j)) ≤ graphDist H w (.inl i) (.inl j)
  stretch : ∀ i j : Fin n,
    graphDist H w (.inl i) (.inl j) ≤ ENNReal.ofReal (C * lpDist p (P i) (P j))
def IsGeometricSpanner (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) (C : ℝ)
    (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i j : Fin n,
    graphDist G
      (Sym2.lift ⟨fun u v => lpDist p (P u) (P v), fun u v => by
        simp only [lpDist, abs_sub_comm]⟩)
      i j ≤ ENNReal.ofReal (C * lpDist p (P i) (P j))
structure IsGeneralNonMetricSteinerSpanner {P : Type} [MetricSpace P] [Fintype P]
    (C : ℝ) {S : Type} [Fintype S] (H : SimpleGraph (P ⊕ S)) (w : Sym2 (P ⊕ S) → ℝ) : Prop where
  weight_nonneg : ∀ e ∈ H.edgeSet, 0 ≤ w e
  noncontracting : ∀ x y : P,
    ENNReal.ofReal (dist x y) ≤ graphDist H w (.inl x) (.inl y)
  stretch : ∀ x y : P,
    graphDist H w (.inl x) (.inl y) ≤ ENNReal.ofReal (C * dist x y)
def oneHotEmbed {N q : ℕ} (x : Fin N → Fin q) : Fin (N * q) → ℝ :=
  fun k =>
    let vc := finProdFinEquiv.symm k
    if x vc.1 = vc.2 then 1 else 0
def disagreeSet {N q : ℕ} (x y : Fin N → Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun v => x v ≠ y v)
def exactDistPairs {N q : ℕ} (X : Finset (Fin N → Fin q)) (rStar : ℕ) :
    Finset ((Fin N → Fin q) × (Fin N → Fin q)) :=
  (X ×ˢ X).filter (fun xy => hammingDist xy.1 xy.2 = rStar)
def ListSizeCond {N q : ℕ} (C₁ rStar K : ℕ) (X : Finset (Fin N → Fin q))
    (L : ↥X → ↥X → Finset ↥X) : Prop :=
  ∀ a b : ↥X,
    0 < hammingDist a.val b.val →
    hammingDist a.val b.val ≤ C₁ * rStar →
    (L a b).card < K
noncomputable def OverlapCond {N q : ℕ} (C₁ rStar K : ℕ) (X : Finset (Fin N → Fin q)) : Prop :=
  ∀ x w₀ : ↥X,
    0 < hammingDist x.val w₀.val →
    hammingDist x.val w₀.val ≤ C₁ * rStar →
    (Finset.univ.filter (fun y : ↥X =>
      y ≠ x ∧ y ≠ w₀ ∧
      hammingDist x.val y.val = rStar ∧
      (rStar : ℝ) / 4 < ((disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card : ℝ))).card < K
def ListHitCond {N q : ℕ} (C₁ rStar : ℕ) (X : Finset (Fin N → Fin q))
    (L : ↥X → ↥X → Finset ↥X) : Prop :=
  ∀ (x : ↥X) (ℓ : ℕ), 1 ≤ ℓ →
    ∀ (w : Fin (ℓ + 1) → ↥X),
      (∀ t : Fin (ℓ + 1), w t ≠ x ∧ hammingDist x.val (w t).val ≤ C₁ * rStar) →
      (∀ s : Fin ℓ,
        0 < hammingDist (w s.castSucc).val (w s.succ).val ∧
        hammingDist (w s.castSucc).val (w s.succ).val ≤ C₁ * rStar) →
      hammingDist x.val (w (Fin.last ℓ)).val = rStar →
      ((disagreeSet x.val (w 0).val ∩ disagreeSet x.val (w (Fin.last ℓ)).val).card : ℝ) ≤
        (rStar : ℝ) / 4 →
      ∃ s : Fin ℓ, x ∈ L (w s.castSucc) (w s.succ)
noncomputable def bucketDiam {P : Type} [MetricSpace P] (B : Finset P) : ℝ :=
  if hne : B.Nonempty then
    B.sup' hne (fun u => B.sup' hne (fun v => dist u v))
  else 0
def bucketingGraph {P I : Type} (B : I → Finset P) : SimpleGraph (P ⊕ I) where
  Adj u v :=
    match u, v with
    | .inl x, .inr i => x ∈ B i
    | .inr i, .inl x => x ∈ B i
    | _, _ => False
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> exact h⟩
  loopless := ⟨by
    intro u h
    cases u <;> exact h⟩
noncomputable def bucketingWeight {P I : Type} [MetricSpace P] (B : I → Finset P) :
    Sym2 (P ⊕ I) → ℝ :=
  Sym2.lift ⟨fun u v =>
    match u, v with
    | .inl _, .inr i => bucketDiam (B i) / 2
    | .inr i, .inl _ => bucketDiam (B i) / 2
    | _, _ => 0,
    fun u v => by cases u <;> cases v <;> rfl⟩
def stdBasis (n : ℕ) : Fin n → (Fin n → ℝ) :=
  fun i j => if i = j then 1 else 0
def boolVecToReal {d : ℕ} (x : Fin d → Bool) : Fin d → ℝ :=
  fun i => if x i then 1 else 0
noncomputable def cubeLpDist (p : ℝ) {d : ℕ} (x y : Fin d → Bool) : ℝ :=
  lpDist p (boolVecToReal x) (boolVecToReal y)
noncomputable def cubeSubgraphWeight (p : ℝ) {d : ℕ} (V : Finset (Fin d → Bool)) :
    Sym2 ↥V → ℝ :=
  Sym2.lift ⟨fun u v => cubeLpDist p u.val v.val, fun u v => by
    simp only [cubeLpDist, lpDist, abs_sub_comm]⟩
def Symmetric2CSP {N q : ℕ} (R : Fin N → Fin N → Fin q → Fin q → Prop) : Prop :=
  ∀ u v : Fin N, ∀ c₁ c₂ : Fin q, R u v c₁ c₂ ↔ R v u c₂ c₁
noncomputable def satisfyingSet {N q : ℕ} (R : Fin N → Fin N → Fin q → Fin q → Prop) :
    Finset (Fin N → Fin q) := by
  classical
  exact
    Finset.univ.filter (fun x => ∀ u v : Fin N, u < v → R u v (x u) (x v))
def threeWayDisagree {N q : ℕ} (x y z : Fin N → Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun v => x v ≠ y v ∧ x v ≠ z v ∧ y v ≠ z v)
def activeColor {N q : ℕ} (x a b : Fin N → Fin q) (v : Fin N) : Fin q :=
  if a v ≠ x v then a v else b v
noncomputable def bicliqueWitnessList {N q : ℕ}
    (R : Fin N → Fin N → Fin q → Fin q → Prop) (C₁ rStar : ℕ)
    (a b : Fin N → Fin q) : Finset (Fin N → Fin q) := by
  classical
  exact
    let W := fun x => disagreeSet x a ∪ disagreeSet x b
    let I := fun x => disagreeSet x a ∩ disagreeSet x b
    (satisfyingSet R).filter (fun x =>
      x ≠ a ∧ x ≠ b ∧
      hammingDist x a ≤ C₁ * rStar ∧
      hammingDist x b ≤ C₁ * rStar ∧
      ∃ k : ℕ, k ≤ 8 * C₁ ∧
        ∃ (A B_fut B_out : Fin k → Finset (Fin N)) (I_k : Finset (Fin N)),
          Pairwise (fun i j => Disjoint (A i) (A j)) ∧
          (∀ r : Fin k, Disjoint (A r) I_k) ∧
          Finset.univ.biUnion A ∪ I_k = I x ∧
          (I_k.card : ℝ) ≤ (rStar : ℝ) / 2 ∧
          ∀ r : Fin k,
            let I_rem := (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ I_k
            B_fut r ⊆ I_rem ∧
            B_out r ⊆ W x \ (A r ∪ I_rem) ∧
            (∀ u ∈ A r, ∀ v ∈ B_fut r ∪ B_out r, R u v (x u) (activeColor x a b v)) ∧
            (((I_rem \ B_fut r).card : ℝ) ≤ (rStar : ℝ) / 80 ∧
             ((A r).card : ℝ) - (11 : ℝ) / 40 * (rStar : ℝ) ≤ ((B_out r).card : ℝ)))
end HighDimSteinerSpanners


