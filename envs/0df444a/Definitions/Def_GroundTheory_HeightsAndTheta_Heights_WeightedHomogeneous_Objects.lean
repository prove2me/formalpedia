-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:32.115599+00:00
-- url     : https://prove2.me/theorems/22d1f1a8-d557-4ebb-b48d-37d424f61bb4
-- title:
--   Objects
-- statement:
--   Definitions and structural lemmas for Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Objects.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
def conePoints (I : Ideal (MvPolynomial (Coord n) ℤ)) (F : Type*) [CommRing F] : Set (Cone n F) :=
  {z | BlockNonzero z ∧ ∀ f ∈ I, evalCone z f = 0}
namespace ArithVariety
variable (P : ArithVariety n)
def IsLive (c : (k : ι) → Fin (n k + 1)) : Prop :=
  ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal
def chartRing (c : (k : ι) → Fin (n k + 1)) : Subring P.FunField :=
  Subring.closure (Set.range (P.chartCoord c))
def chartPow (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) : P.FunField :=
  ∏ k, P.mkF (X ⟨k, c k⟩) ^ a k
def IsOfDegree (a : ι → ℤ) (x : P.FunField) : Prop :=
  ∃ (f g : MvPolynomial (Coord n) ℤ) (δf δg : ι → ℕ), IsWeightedHomogeneous (coordDeg n) f δf ∧
    IsWeightedHomogeneous (coordDeg n) g δg ∧ (∀ k, (δf k : ℤ) - δg k = a k) ∧ g ∉ P.ideal ∧
    x = P.mkF f / P.mkF g
structure IsHomogGenerators {r : ℕ} (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ) :
    Prop where
  homog : ∀ i, IsWeightedHomogeneous (coordDeg n) (G i) (δ i)
  span_eq : Ideal.span (Set.range G) = P.ideal
end ArithVariety
structure AddBlockData (P : ArithVariety n) where

  deg : ι → ℤ

  size : ℕ

  elt : Fin (size + 1) → P.FunField
  elt_deg : ∀ j, P.IsOfDegree deg (elt j)
  chart_mem : ∀ c, P.IsLive c → ∀ j, elt j / P.chartPow c deg ∈ P.chartRing c
  generating : ∀ c, P.IsLive c → ∃ u : Fin (size + 1) → P.FunField,
    (∀ j, u j ∈ P.chartRing c) ∧ ∑ j, u j * (elt j / P.chartPow c deg) = 1
namespace AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)
def xi (c : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)) : P.FunField :=
  D.elt j / P.chartPow c D.deg
def extSizes : Option ι → ℕ := fun o ↦ o.elim D.size n
def newDeg : Option ι → ℤ := fun o ↦ o.elim 1 fun _ ↦ 0
def oldCoord (v : Coord n) : Coord D.extSizes := ⟨some v.1, v.2⟩
def newCoord (j : Fin (D.size + 1)) : Coord D.extSizes := ⟨none, j⟩
def liftOld : MvPolynomial (Coord n) ℤ →ₐ[ℤ] MvPolynomial (Coord D.extSizes) ℤ :=
  rename D.oldCoord
def extVal : Coord D.extSizes → P.FunField
  | ⟨none, j⟩ => D.elt j
  | ⟨some k, i⟩ => P.mkF (X ⟨k, i⟩)
def extMap : MvPolynomial (Coord D.extSizes) ℤ →+* MvPolynomial (Option ι) P.FunField :=
  eval₂Hom (Int.castRingHom _) fun v ↦ C (D.extVal v) * X v.1
def extIdeal : Ideal (MvPolynomial (Coord D.extSizes) ℤ) := RingHom.ker D.extMap
def extPoints : Set (Cone D.extSizes ℂ) := conePoints D.extIdeal ℂ
def basePart₂ {F : Type*} (w : Cone D.extSizes F) : Cone n F := fun k ↦ w (some k)
def newPart {F : Type*} (w : Cone D.extSizes F) : Fin (D.size + 1) → F := w none
def joinPt {F : Type*} (z : Cone n F) (z' : Fin (D.size + 1) → F) : Cone D.extSizes F :=
  fun o ↦ match o with
    | none => z'
    | some k => z k
def extChartRing (c : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)) : Subring P.FunField :=
  Subring.closure (Set.range (P.chartCoord c) ∪ Set.range fun i ↦ D.elt i / D.elt j)
structure IsFormSystem (d : ι → ℕ)
    (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ) : Prop where
  pos : ∀ k, 1 ≤ d k
  nonneg : ∀ k, 0 ≤ (d k : ℤ) + D.deg k
  homog : ∀ c j, ∃ δ : ι → ℕ,
    IsWeightedHomogeneous (coordDeg n) (g c j) δ ∧ ∀ k, (δ k : ℤ) = d k + D.deg k
  value : ∀ c, P.IsLive c → ∀ j, P.mkF (g c j) = P.mkF (chartMonomial c d) * D.elt j
  dead : ∀ c, ¬ P.IsLive c → ∀ j, g c j = 0
def den (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ)
    {r : ℕ} (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ) (z : Cone n ℂ) : ℝ :=
  (∑ c, ∑ j, ‖evalCone z (g c j)‖ ^ 2) +
    ∑ i, ‖evalCone z (G i)‖ ^ 2 * ∏ k, l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k))
def plusMetric (N : HermLine n) (d : ι → ℕ)
    (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ)
    {r : ℕ} (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ) (w : Cone D.extSizes ℂ) : ℝ :=
  N.metric (D.basePart₂ w) * l2Norm (D.newPart w) *
    Real.sqrt ((∑ c, ‖evalCone (D.basePart₂ w) (chartMonomial c d)‖ ^ 2) / D.den d g G δ (D.basePart₂ w))
end AddBlockData
namespace HermLine
def pow (A : HermLine n) (m : ℕ) : HermLine n where
  deg := m • A.deg
  metric z := A.metric z ^ m
  metric_pos z hz := pow_pos (A.metric_pos z hz) m
  metric_smul c z hc hz := by
    rw [A.metric_smul c z hc hz, mul_pow, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Pi.smul_apply, nsmul_eq_mul, mul_comm, zpow_mul, zpow_natCast]
  metric_smooth := A.metric_smooth.pow m
def mul (A B : HermLine n) : HermLine n where
  deg := A.deg + B.deg
  metric z := A.metric z * B.metric z
  metric_pos z hz := mul_pos (A.metric_pos z hz) (B.metric_pos z hz)
  metric_smul c z hc hz := by
    rw [A.metric_smul c z hc hz, B.metric_smul c z hc hz]
    have h : ∏ k, ‖c k‖ ^ (A.deg + B.deg) k = (∏ k, ‖c k‖ ^ A.deg k) * ∏ k, ‖c k‖ ^ B.deg k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [Pi.add_apply, zpow_add₀ (norm_ne_zero_iff.mpr (hc k))]
    rw [h]
    ring
  metric_smooth := A.metric_smooth.mul B.metric_smooth
def inv (A : HermLine n) : HermLine n where
  deg := -A.deg
  metric z := (A.metric z)⁻¹
  metric_pos z hz := inv_pos.mpr (A.metric_pos z hz)
  metric_smul c z hc hz := by
    rw [A.metric_smul c z hc hz, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Pi.neg_apply, zpow_neg]
  metric_smooth := A.metric_smooth.inv fun z hz ↦ (A.metric_pos z hz).ne'
end HermLine
omit [DecidableEq ι] in
theorem chartMonomial_add (c : (k : ι) → Fin (n k + 1)) (d d' : ι → ℕ) :
    chartMonomial c (d + d') = chartMonomial c d * chartMonomial c d' := by
  simp only [chartMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
omit [DecidableEq ι] in
theorem chartMonomial_nsmul (c : (k : ι) → Fin (n k + 1)) (m : ℕ) (d : ι → ℕ) :
    chartMonomial c (m • d) = chartMonomial c d ^ m := by
  simp only [chartMonomial, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm]
omit [DecidableEq ι] in
theorem chartMonomial_zero (c : (k : ι) → Fin (n k + 1)) : chartMonomial c 0 = 1 := by
  simp [chartMonomial]
namespace IntegralSection
variable {P : ArithVariety n} {a b : ι → ℤ}
def toFun (s : IntegralSection P a) : P.FunField := P.mkF s.num / P.mkF s.den
def cast (h : a = b) (s : IntegralSection P a) : IntegralSection P b where
  num := s.num
  den := s.den
  numDeg := s.numDeg
  denDeg := s.denDeg
  num_isHomogeneous := s.num_isHomogeneous
  den_isHomogeneous := s.den_isHomogeneous
  deg_eq k := by subst h; exact s.deg_eq k
  den_not_mem := s.den_not_mem
  regular c hc := by subst h; exact s.regular c hc
def mul (s : IntegralSection P a) (t : IntegralSection P b) : IntegralSection P (a + b) where
  num := s.num * t.num
  den := s.den * t.den
  numDeg := s.numDeg + t.numDeg
  denDeg := s.denDeg + t.denDeg
  num_isHomogeneous := s.num_isHomogeneous.mul t.num_isHomogeneous
  den_isHomogeneous := s.den_isHomogeneous.mul t.den_isHomogeneous
  deg_eq k := by
    simp only [Pi.add_apply, Nat.cast_add]
    rw [← s.deg_eq k, ← t.deg_eq k]
    ring
  den_not_mem h := (P.isPrime.mem_or_mem h).elim s.den_not_mem t.den_not_mem
  regular c hc := by
    obtain ⟨d, e, ⟨δ, he, hδ⟩, hmem⟩ := s.regular c hc
    obtain ⟨d', e', ⟨δ', he', hδ'⟩, hmem'⟩ := t.regular c hc
    refine ⟨d + d', e * e', ⟨δ + δ', he.mul he', fun k ↦ ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Nat.cast_add, hδ k, hδ' k]
      ring
    · rw [chartMonomial_add]
      have h : s.den * t.den * (e * e') - s.num * t.num * (chartMonomial c d * chartMonomial c d') =
          (s.den * e - s.num * chartMonomial c d) * (t.den * e') +
            (s.num * chartMonomial c d) * (t.den * e' - t.num * chartMonomial c d') := by ring
      rw [h]
      exact P.ideal.add_mem (P.ideal.mul_mem_right _ hmem) (P.ideal.mul_mem_left _ hmem')
def pow (s : IntegralSection P a) (m : ℕ) : IntegralSection P (m • a) where
  num := s.num ^ m
  den := s.den ^ m
  numDeg := m • s.numDeg
  denDeg := m • s.denDeg
  num_isHomogeneous := s.num_isHomogeneous.pow m
  den_isHomogeneous := s.den_isHomogeneous.pow m
  deg_eq k := by
    simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
    rw [← s.deg_eq k]
    ring
  den_not_mem h := s.den_not_mem (P.isPrime.mem_of_pow_mem m h)
  regular c hc := by
    obtain ⟨d, e, ⟨δ, he, hδ⟩, hmem⟩ := s.regular c hc
    refine ⟨m • d, e ^ m, ⟨m • δ, he.pow m, fun k ↦ ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, hδ k]
      ring
    · rw [chartMonomial_nsmul, ← Ideal.Quotient.eq_zero_iff_mem]
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at hmem
      rw [map_sub, sub_eq_zero, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, ← mul_pow,
        ← mul_pow, ← map_mul, ← map_mul, hmem]
def one (P : ArithVariety n) : IntegralSection P 0 where
  num := 1
  den := 1
  numDeg := 0
  denDeg := 0
  num_isHomogeneous := isWeightedHomogeneous_one ℤ (coordDeg n)
  den_isHomogeneous := isWeightedHomogeneous_one ℤ (coordDeg n)
  deg_eq k := by simp
  den_not_mem := (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top
  regular _ _ := ⟨0, 1, ⟨0, isWeightedHomogeneous_one ℤ (coordDeg n), fun k ↦ by simp⟩, by
    rw [chartMonomial_zero, mul_one, sub_self]; exact P.ideal.zero_mem⟩
end IntegralSection
def blockIncl (k₀ : ι) : Coord (fun _ : Unit ↦ n k₀) → Coord n := fun v ↦ ⟨k₀, v.2⟩
def projBlock {F : Type*} (k₀ : ι) (z : Cone n F) : Cone (fun _ : Unit ↦ n k₀) F := fun _ ↦ z k₀
def ArithVariety.projIdeal (P : ArithVariety n) (k₀ : ι) :
    Ideal (MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ) :=
  P.ideal.comap (rename (blockIncl k₀))
def oneBlockSize (e r : ℕ) : ℕ := e * (r + 1) + r
abbrev oneBlockSizes (e r : ℕ) : Unit → ℕ := fun _ ↦ oneBlockSize e r
def oneBlockIndex (e r : ℕ) : Fin (oneBlockSize e r + 1) ≃ Fin (e + 1) × Fin (r + 1) :=
  (finCongr (by simp only [oneBlockSize]; ring)).trans finProdFinEquiv.symm
variable {K : Type*} [Field K] [NumberField K] {e r : ℕ}
def oneBlockMap (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    MvPolynomial (Coord (oneBlockSizes e r)) ℤ →+* MvPolynomial (Fin (r + 1)) K :=
  eval₂Hom (Int.castRingHom _) fun v ↦
    C ((om (oneBlockIndex e r v.2).1 : 𝓞 K) : K) * X (oneBlockIndex e r v.2).2
def oneBlockIdeal (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    Ideal (MvPolynomial (Coord (oneBlockSizes e r)) ℤ) :=
  RingHom.ker (oneBlockMap om)
def oneBlockPoint {F : Type*} [CommRing F] (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (σ : K →+* F)
    (w : Fin (r + 1) → F) : Cone (oneBlockSizes e r) F :=
  fun _ p ↦ σ ((om (oneBlockIndex e r p).1 : 𝓞 K) : K) * w (oneBlockIndex e r p).2
open Matrix in

def OneBlockMetricAgrees (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (F : HermLattice K (r + 1))
    (A : HermLine (oneBlockSizes e r)) : Prop :=
  ∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 →
    A.metric (oneBlockPoint om σ w) = Real.sqrt (star w ⬝ᵥ (F.metric σ *ᵥ w)).re
end
end GroundTheory.Heights₂.Heights


