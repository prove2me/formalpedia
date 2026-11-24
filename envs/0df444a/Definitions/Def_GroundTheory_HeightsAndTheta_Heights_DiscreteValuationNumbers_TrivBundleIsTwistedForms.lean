-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:02.687359+00:00
-- url     : https://prove2.me/theorems/7fc5de91-747c-469a-8ec4-231e5468143a
-- title:
--   Triv Bundle Is Twisted Forms
-- statement:
--   Definitions and structural lemmas for Triv Bundle Is Twisted Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/TrivBundleIsTwistedForms.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
universe u v w u₁ u₂
section Coordinates
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
def segreVec (pt : MRingOver o ι →ₐ[o] Ω) : ((k : K) → ι k) → Ω :=
  fun i => ∏ k, pt (X ⟨k, i k⟩)
def chartMono (pt : MRingOver o ι →ₐ[o] Ω) (i : (k : K) → ι k) (c : K → ℤ) : Ω :=
  ∏ k, pt (X ⟨k, i k⟩) ^ c k
def degLine (pt : MRingOver o ι →ₐ[o] Ω) (c : K → ℤ) (ω : Ω) (i : (k : K) → ι k) : Set Ω :=
  {a | ∃ r ∈ chartRing o (segreVec pt) i, a = r * chartMono pt i c * ω}
end Coordinates
section Flags
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
def gradedLat {x : ((k : K) → ι k) → Ω} (B : ChartBundle o x N E) (u : Basis (Fin N) Ω E)
    (l : Fin N) (i : (k : K) → ι k) : Set Ω :=
  {a | ∃ e ∈ B.lat i, (∀ j, l < j → u.repr e j = 0) ∧ u.repr e l = a}
def IsFlagGrading (pt : MRingOver o ι →ₐ[o] Ω) (B : ChartBundle o (segreVec pt) N E)
    (u : Basis (Fin N) Ω E) (m : Fin N → K → ℤ) (ω : Fin N → Ω) : Prop :=
  (∀ l, ω l ≠ 0) ∧ ∀ i, segreVec pt i ≠ 0 → ∀ l, gradedLat B u l i = degLine pt (m l) (ω l) i
def IsTwistedForms {τ : Type*} [Fintype τ] (pt : MRingOver o ι →ₐ[o] Ω)
    (B : ChartBundle o (segreVec pt) N E) (φ : τ → E →ₗ[Ω] Ω) (c : K → ℤ) : Prop :=
  ∀ i, segreVec pt i ≠ 0 →
    (∀ t, ∀ e ∈ B.lat i, φ t e ∈ degLine pt c 1 i) ∧
    ∀ ψ : E →ₗ[Ω] Ω, (∀ e ∈ B.lat i, ψ e ∈ chartRing o (segreVec pt) i) →
      ∃ a : τ → Ω, (∀ t, a t ∈ chartRing o (segreVec pt) i) ∧
        ψ = ∑ t, (a t * (chartMono pt i c)⁻¹) • φ t
def SameGenericFibre {x : ((k : K) → ι k) → Ω} (ϖ : o) (B B' : ChartBundle o x N E) : Prop :=
  ∀ i, x i ≠ 0 → ∀ e : E,
    (∃ n : ℕ, algebraMap o Ω ϖ ^ n • e ∈ B.lat i) ↔ (∃ n : ℕ, algebraMap o Ω ϖ ^ n • e ∈ B'.lat i)
end Flags
section ProjBundle
variable {K : Type*} [Fintype K]
def extIdx (ι : K → Type w) (τ : Type w) : Option K → Type w
  | none => τ
  | some k => ι k
instance extIdx.fintype {ι : K → Type w} [∀ k, Fintype (ι k)] {τ : Type w} [Fintype τ] :
    (k : Option K) → Fintype (extIdx ι τ k)
  | none => inferInstanceAs (Fintype τ)
  | some k => inferInstanceAs (Fintype (ι k))
def extDeg (Y : K → ℤ) : Option K → ℤ := fun k => k.elim 0 Y
def zetaDeg (c : K → ℤ) : Option K → ℤ := fun k => k.elim 1 fun k => -c k
variable {ι : K → Type w} [∀ k, Fintype (ι k)] {τ : Type w} [Fintype τ]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
def projBundleMap (pt : MRingOver F ι →ₐ[F] Ω) (u : Basis (Fin N) Ω E) (φ : τ → E →ₗ[Ω] Ω) :
    MRingOver F (extIdx ι τ) →ₐ[F] MvPolynomial (K ⊕ Fin N) Ω :=
  aeval fun p => match p with
    | ⟨none, t⟩ => ∑ l, C (φ t (u l)) * X (Sum.inr l)
    | ⟨some k, i⟩ => C (pt (X ⟨k, i⟩)) * X (Sum.inl k)
def projBundleIdeal (pt : MRingOver F ι →ₐ[F] Ω) (u : Basis (Fin N) Ω E) (φ : τ → E →ₗ[Ω] Ω) :
    Ideal (MRingOver F (extIdx ι τ)) :=
  RingHom.ker (projBundleMap pt u φ)
end ProjBundle
section PolyNum
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def monoList {N : ℕ} (mono : Fin N →₀ ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun l => List.replicate (mono l) l
def tupleOfList {α : Type*} [Zero α] {n : ℕ} (L : List α) : Fin n → α := fun j => L.getD j 0
variable {F : Type*} [Field F]
def polyNum (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (n : ℕ) {N : ℕ} (cls : Fin N → K → ℤ)
    (Q : MvPolynomial (Fin N) ℤ) (Y : List (K → ℤ)) : ℤ :=
  ∑ mono ∈ Q.support, Q.coeff mono * I V n (tupleOfList ((monoList mono).map cls ++ Y))
end PolyNum
section Pairs
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
structure VPair (K : Type*) [Fintype K] (O : Type*) [CommRing O] (ι : K → Type*) [∀ k, Fintype (ι k)] where

  y : K → ℤ

  b : K → ℤ

  f : MRingOver O ι

  g : MRingOver O ι
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def vNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    (p : VPair K O ι) (L : List (K → ℤ)) : ℤ :=
  redEval (fun W => Iκ W n (tupleOfList L)) (divO P p.f p.g)
def monoPairNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    {r : ℕ} (pr : Fin r → VPair K O ι) (ls : List (Fin r)) : ℤ :=
  ∑ k : Fin ls.length, vNum P Iκ n (pr (ls.get k))
    ((ls.take k).map (fun l => (pr l).y - (pr l).b) ++ (ls.drop (k + 1)).map fun l => (pr l).y)
def pairNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    {r : ℕ} (pr : Fin r → VPair K O ι) (Q : MvPolynomial (Fin r) ℤ) : ℤ :=
  ∑ mono ∈ Q.support, Q.coeff mono * monoPairNum P Iκ n pr (monoList mono)
def flagPairs {N : ℕ} (m m' : Fin N → K → ℤ) (f g : Fin N → MRingOver O ι) : Fin N → VPair K O ι :=
  fun l => ⟨m l, m l - m' l, f l, g l⟩
variable {Ω : Type*} [Field Ω] [Algebra O Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
def IsFlagPair (pt : MRingOver O ι →ₐ[O] Ω) (P : Ideal (MRingOver O ι))
    (B B' : ChartBundle O (segreVec pt) N E) (u : Basis (Fin N) Ω E) (m m' : Fin N → K → ℤ)
    (ω ω' : Fin N → Ω) (f g : Fin N → MRingOver O ι) : Prop :=
  IsFlagGrading pt B u m ω ∧ IsFlagGrading pt B' u m' ω' ∧
    ∀ l, (∃ α β : K → ℕ, IsMultiHomog (f l) α ∧ IsMultiHomog (g l) β ∧
        ∀ k, (α k : ℤ) - β k = m l k - m' l k) ∧
      g l ∉ P ∧ pt (f l) * ω l = pt (g l) * ω' l
end Pairs
def ProjectiveBundleNumbers.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
    (τ : Type w) [Fintype τ] (V : Ideal (MRingOver F ι)) (e N : ℕ) (Ω : Type u₁) [Field Ω]
    [Algebra F Ω] (pt : MRingOver F ι →ₐ[F] Ω) (E : Type u₂) [AddCommGroup E] [Module Ω E]
    (B : ChartBundle F (segreVec pt) N E) (u : Basis (Fin N) Ω E) (m : Fin N → K → ℤ)
    (ω : Fin N → Ω) (φ : τ → E →ₗ[Ω] Ω) (c : K → ℤ) (I : IFamily F ι)
    (I' : IFamily F (extIdx ι τ)) (j : ℕ) (Y : Fin j → K → ℤ),
    IsProjVarF V e → RingHom.ker pt = V → 1 ≤ N → IsFlagGrading pt B u m ω →
    IsTwistedForms pt B φ c → IsFieldIntersection I → IsFieldIntersection I' → j ≤ N - 1 + e →
    I' (projBundleIdeal pt u φ) (N - 1 + e)
        (tupleOfList (List.replicate (N - 1 + e - j) (zetaDeg c) ++ (List.ofFn Y).map extDeg)) =
      if j ≤ e then polyNum I V e (fun l => -m l) (hsymm (Fin N) ℤ (e - j)) (List.ofFn Y) else 0
def TwoExpansionsAgree.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (d N : ℕ) (Ω : Type u₁) [Field Ω] [Algebra O Ω]
      (pt : MRingOver O ι →ₐ[O] Ω) (E : Type u₂) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec pt) N E) (u₁ u₂ : Basis (Fin N) Ω E)
      (m₁ m₁' m₂ m₂' : Fin N → K → ℤ) (ω₁ ω₁' ω₂ ω₂' : Fin N → Ω)
      (f₁ g₁ f₂ g₂ : Fin N → MRingOver O ι) (G : MvPolynomial (Fin N) ℤ)
      (Iκ : IFamily (IsLocalRing.ResidueField O) ι),
      IsModelOver P d → RingHom.ker pt = P → SameGenericFibre ϖ B B' →
      IsFlagPair pt P B B' u₁ m₁ m₁' ω₁ ω₁' f₁ g₁ → IsFlagPair pt P B B' u₂ m₂ m₂' ω₂ ω₂' f₂ g₂ →
      G.IsSymmetric → G.IsHomogeneous (d + 1) → IsFieldIntersection Iκ →
      pairNum P Iκ d (flagPairs m₁ m₁' f₁ g₁) G = pairNum P Iκ d (flagPairs m₂ m₂' f₂ g₂) G
def TwoExpansionsAgree.WithPairsStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (d N : ℕ) (Ω : Type u₁) [Field Ω] [Algebra O Ω]
      (pt : MRingOver O ι →ₐ[O] Ω) (E : Type u₂) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec pt) N E) (u₁ u₂ : Basis (Fin N) Ω E)
      (m₁ m₁' m₂ m₂' : Fin N → K → ℤ) (ω₁ ω₁' ω₂ ω₂' : Fin N → Ω)
      (f₁ g₁ f₂ g₂ : Fin N → MRingOver O ι) (r : ℕ) (R : Fin r → VPair K O ι)
      (G : MvPolynomial (Fin N) ℤ) (Iκ : IFamily (IsLocalRing.ResidueField O) ι),
      IsModelOver P d → RingHom.ker pt = P → SameGenericFibre ϖ B B' →
      IsFlagPair pt P B B' u₁ m₁ m₁' ω₁ ω₁' f₁ g₁ → IsFlagPair pt P B B' u₂ m₂ m₂' ω₂ ω₂' f₂ g₂ →
      (∀ j, IsVerticalDiv ϖ P (R j).b (R j).f (R j).g) → r ≤ d + 1 →
      G.IsSymmetric → G.IsHomogeneous (d + 1 - r) → IsFieldIntersection Iκ →
      pairNum P Iκ d (Fin.append (flagPairs m₁ m₁' f₁ g₁) R)
          (rename (Fin.castAdd r) G * ∏ j : Fin r, X (Fin.natAdd N j)) =
        pairNum P Iκ d (Fin.append (flagPairs m₂ m₂' f₂ g₂) R)
          (rename (Fin.castAdd r) G * ∏ j : Fin r, X (Fin.natAdd N j))
section Inhabitants
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
def trivLat {ι' : Type*} (x : ι' → Ω) (N : ℕ) (i : ι') : AddSubgroup (Fin N → Ω) where
  carrier := {e | ∀ q, e q ∈ chartRing o x i}
  add_mem' ha hb q := add_mem (ha q) (hb q)
  zero_mem' _ := zero_mem _
  neg_mem' ha q := neg_mem (ha q)
def trivBundle {ι' : Type*} (x : ι' → Ω) (N : ℕ) : ChartBundle o x N (Fin N → Ω) where
  lat := trivLat o x N
  stable i a ha e he q := by
    show a * e q ∈ chartRing o x i
    exact mul_mem ha (he q)
  frame i _ := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    refine ⟨Pi.basisFun Ω (Fin N), (Pi.basisFun Ω (Fin N)).linearIndependent,
      (Pi.basisFun Ω (Fin N)).span_eq, fun e => ?_⟩
    simp only [one_pow, one_smul, one_mul, exists_const]
    constructor
    · intro he
      exact ⟨e, he, by simpa using ((Pi.basisFun Ω (Fin N)).sum_repr e).symm⟩
    · rintro ⟨a, ha, rfl⟩ q
      have : (∑ q', a q' • (Pi.basisFun Ω (Fin N)) q') q = a q := by
        simp [Finset.sum_apply, Pi.single_apply]
      show (∑ q', a q' • (Pi.basisFun Ω (Fin N)) q') q ∈ chartRing o x i
      rw [this]
      exact ha q
  overlap i j hi _ e he := by
    choose m hm using fun q => exists_pow_mul_mem_chartRing x i j hi (he q)
    refine ⟨∑ q, m q, fun q => ?_⟩
    have hle : m q ≤ ∑ q, m q := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have : ((x i / x j) ^ (∑ q, m q) • e) q =
        (x i / x j) ^ (∑ q, m q - m q) * ((x i / x j) ^ m q * e q) := by
      rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [this]
    exact mul_mem (pow_mem (div_mem_chartRing x j i) _) (hm q)
variable {o}
variable (o) in

def genPt (R : Type*) [CommRing R] [IsDomain R] (ι : K → Type*) [∀ k, Fintype (ι k)] :
    MRingOver R ι →ₐ[R] FractionRing (MRingOver R ι) :=
  IsScalarTower.toAlgHom R _ _
section DVR
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def unifPair (ϖ : O) : VPair K O ι := ⟨0, 0, C ϖ, 1⟩
end DVR
end Inhabitants
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR


