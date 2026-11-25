-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:24:50.161944+00:00
-- url     : https://prove2.me/theorems/2e17854e-1f86-4a81-9bb4-dd3249f3f21b
-- title:
--   Algebra Map Mem Chart Ring Line
-- statement:
--   Definitions and structural lemmas for Algebra Map Mem Chart Ring Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_twistBundle_one_62fb03cd3d01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_primeOf_genericPt_22a3f75bc1e3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u v w
section Ideals
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
def idealMod (J : Ideal (Poly S N)) (I : Chart x) : Submodule (chartRing S x I) Ω :=
  Submodule.span _ {a | ∃ (f s : Poly S N) (e : ℕ), f ∈ J ∧ s ∈ monos I.1 ∧ f.IsHomogeneous e ∧
    s.IsHomogeneous e ∧ a = aeval x f / aeval x s}
variable (x) in

def idealSys (J : Ideal (Poly S N)) : SubSystem S x Ω where
  sub I := idealMod J I
  mono I₁ I₂ h z hz := by
    refine Submodule.span_induction (p := fun z _ => z ∈ idealMod (x := x) J I₂) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
      exact Submodule.subset_span ⟨f, s, e, hf, monos_mono h hs, hfe, hse, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz
      exact Submodule.smul_mem _ (chartIncl h a) hz
def SubSystem.extend (F : Type*) [Field F] [Algebra F Ω] (Q : SubSystem S x Ω) : SubSystem F x Ω where
  sub I := Submodule.span (chartRing F x I) (Q.sub I : Set Ω)
  mono I₁ I₂ h z hz := by
    refine Submodule.span_induction
      (p := fun z _ => z ∈ Submodule.span (chartRing F x I₂) (Q.sub I₂ : Set Ω)) ?_ ?_ ?_ ?_ hz
    · intro z hz; exact Submodule.subset_span (Q.mono I₁ I₂ h z hz)
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact Submodule.smul_mem _ (chartIncl h a) hz
variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
def FinGradedSub.tildeSys (M : FinGradedSub (S := S) (x := x) E) (c : ℤ) : SubSystem S x E where
  sub I := M.tilde c I
  mono I₁ I₂ h z hz := by
    refine Submodule.span_induction (p := fun z _ => z ∈ M.tilde c I₂) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
      exact Submodule.subset_span ⟨m, s, a, e, monos_mono h hs, hse, hm, hae, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz
      exact Submodule.smul_mem _ (chartIncl h a) hz
namespace SubSystem
def quotSub (F₁ F₂ : SubSystem S x E) (I : Chart x) : Submodule S (F₁.sub I) where
  carrier := {y | (y : E) ∈ F₂.sub I}
  add_mem' ha hb := (F₂.sub I).add_mem ha hb
  zero_mem' := (F₂.sub I).zero_mem
  smul_mem' c _y hy := (F₂.sub I).smul_of_tower_mem c hy
def quotRes (F₁ F₂ : SubSystem S x E) (I₁ I₂ : Chart x) (h : I₁.1 ⊆ I₂.1) :
    (F₁.sub I₁ ⧸ quotSub F₁ F₂ I₁) →ₗ[S] (F₁.sub I₂ ⧸ quotSub F₁ F₂ I₂) :=
  (quotSub F₁ F₂ I₁).mapQ (quotSub F₁ F₂ I₂) (F₁.res I₁ I₂ h) (fun _y hy => F₂.mono I₁ I₂ h _ hy)
def quotH (F₁ F₂ : SubSystem S x E) (i : ℕ) : Type v :=
  Cech.H (fun I => F₁.sub I ⧸ quotSub F₁ F₂ I) (quotRes F₁ F₂) i
end SubSystem
end Ideals
section Numbers
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
def restrLen (pp : Ideal (Poly S N)) (F : SubSystem S x Ω) : ℤ :=
  ((Module.length S (F.secs ⧸ ((F.twist (idealSys x pp)).secs).comap F.secs.subtype)).toNat : ℤ)
def tensorSub {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) : SubSystem S x Ω :=
  ((List.finRange n).filter (· ∈ T)).foldl (fun F i => F.twist (L i)) (twistSys S x 0)
def interSum (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω) (c : ℕ) : ℤ :=
  ∑ T : Finset (Fin n), (-1) ^ (n - T.card) *
    restrLen pp ((tensorSub L T).twist (twistSys S x (c : ℤ)))
def interNum (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω) : ℤ :=
  limUnder atTop (interSum pp L)
variable (x) in

structure IsSubvar (pp : Ideal (Poly S N)) (e : ℕ) : Prop where
  isPrime : pp.IsPrime
  homog : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp
  le : primeOf (S := S) x ≤ pp
  relevant : ∃ i, (X i : Poly S N) ∉ pp
  dim : ringKrullDim (Poly S N ⧸ pp) = ((e + 1 : ℕ) : WithBot ℕ∞)
def NefAbove (M : SubSystem S x Ω) (J : Ideal (Poly S N)) : Prop :=
  ∀ pp : Ideal (Poly S N), J ≤ pp → IsSubvar x pp 1 → 0 ≤ interNum pp ![M]
def Nef (M : SubSystem S x Ω) : Prop := NefAbove M ⊥
def twistMul (M : SubSystem S x Ω) (p : ℕ) (m : ℤ) : SubSystem S x Ω :=
  (M.pow p).twist (twistSys S x m)
structure IsVeryAmpleBy (H : SubSystem S x Ω) {r : ℕ} (h : Fin (r + 1) → Ω) : Prop where
  mem_secs : ∀ j, h j ∈ H.secs
  generates : ∀ I, Submodule.span (chartRing S x I) (Set.range h) = H.sub I
  closed : ∀ j, h j ≠ 0 → ampleRing H 1 (h j) ⊆ ampleBase (S := S) h j
  affine : ∀ j, h j ≠ 0 → ∃ (n : ℕ) (a b : Fin n → Ω) (J : Fin n → Chart x),
    (∀ k, a k ∈ ampleRing H 1 (h j)) ∧ (∀ k, b k ∈ ampleRing H 1 (h j)) ∧
    ∑ k, a k * b k = 1 ∧ ∀ (k : Fin n) (I : Chart x), ∃ e : ℕ,
      b k ^ e * (xProd I ^ (J k).1.card / xProd (J k) ^ I.1.card) ∈ ampleChart H 1 (h j) I
def IsVeryAmple (H : SubSystem S x Ω) : Prop :=
  ∃ (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy H h
def zeroIdeal (D : SubSystem S x Ω) (s : Ω) : Ideal (Poly S N) :=
  Ideal.span {f | ∃ c : ℕ, f.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ D.sub I,
    ∃ o ∈ twistMod S x (c : ℤ) I, aeval x f * δ = s * o}
def cutMult (J qq : Ideal (Poly S N)) [qq.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime qq) (LocalizedModule qq.primeCompl (Poly S N ⧸ J))
end Numbers
section Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
def pullSys (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω) : SubSystem S x' Ω where
  sub I := Submodule.span (chartRing S x' I) (Set.range x)
  mono I₁ I₂ h z hz := by
    refine Submodule.span_induction
      (p := fun z _ => z ∈ Submodule.span (chartRing S x' I₂) (Set.range x)) ?_ ?_ ?_ ?_ hz
    · intro z hz; exact Submodule.subset_span hz
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact Submodule.smul_mem _ (chartIncl h a) hz
variable (S) in

structure IsDomination (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω) : Prop where
  invertible : ∀ I : Chart x', ∃ Q' : Submodule (chartRing S x' I) Ω,
    (pullSys (S := S) x x').sub I * Q' = 1
variable (S) in

def domRing (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω) (i : Fin (N + 1)) : Set Ω :=
  ampleRing (pullSys (S := S) x x') 1 (x i)
def pullSecs {x : Fin (N + 1) → Ω} (x' : Fin (N' + 1) → Ω) (L : SubSystem S x Ω) : Submodule S Ω :=
  ⨅ (i : Fin (N + 1)) (hi : x i ≠ 0), Submodule.span S
    {z | ∃ b ∈ domRing S x x' i, ∃ l ∈ L.sub (singleChart hi), z = b * l}
variable (S) in

def IsBirationalPt (x : Fin (N + 1) → Ω) : Prop :=
  ∀ s : Ω, ∃ (I : Chart x) (a b : Ω), a ∈ chartRing S x I ∧ b ∈ chartRing S x I ∧ b ≠ 0 ∧ s * b = a
variable (S) in

def IsNormalPt (x : Fin (N + 1) → Ω) : Prop :=
  ∀ (i : Fin (N + 1)) (hi : x i ≠ 0) (b : Ω), IsIntegral (chartRing S x (singleChart hi)) b →
    b ∈ chartRing S x (singleChart hi)
end Domination
section Restrict
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
structure RestrictData {K' : Type w} [Field K'] [Algebra S K'] (Q : SubSystem S x Ω)
    {y : Fin (N + 1) → K'} (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (Q' : SubSystem S y K') (r : Ω → K') :
    Prop where
  mem : ∀ (I : Chart y), ∀ q ∈ Q.sub (liftChart hxy I), r q ∈ Q'.sub I
  add : ∀ (I : Chart y), ∀ q ∈ Q.sub (liftChart hxy I), ∀ q' ∈ Q.sub (liftChart hxy I),
    r (q + q') = r q + r q'
  smul : ∀ (I : Chart y), ∀ q ∈ Q.sub (liftChart hxy I), ∀ (f s : Poly S N) (e : ℕ), s ∈ monos I.1 →
    f.IsHomogeneous e → s.IsHomogeneous e →
    r (aeval x f / aeval x s * q) = aeval y f / aeval y s * r q
  span : ∀ I : Chart y, Submodule.span (chartRing S y I) (r '' Q.sub (liftChart hxy I)) = Q'.sub I
end Restrict
section Steps
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
structure StepData (x : Fin (N + 1) → Ω) where

  d : ℕ
  dim : IsSubvar x (primeOf (S := k) x) (d + 1)

  M : LineBundle k x
  nef : Nef M.toSubSystem
  t : ℚ
  s' : ℚ
  s'_pos : 0 < s'
  s'_lt : s' < t / (d + 1)

  p : ℕ
  p_pos : 1 ≤ p

  m : ℤ
  m_eq : (m : ℚ) = p * (t - s')
  c₁ : ℤ
  c₁_pos : 1 ≤ c₁

  si : Ω
  si_mem : si ∈ (twistMul M.toSubSystem p (m - c₁)).secs
  si_ne : si ≠ 0
variable {k}
def StepData.L {x : Fin (N + 1) → Ω} (T : StepData k x) : SubSystem k x Ω :=
  twistMul T.M.toSubSystem T.p T.m
def StepData.D {x : Fin (N + 1) → Ω} (T : StepData k x) : SubSystem k x Ω :=
  twistMul T.M.toSubSystem T.p (T.m - T.c₁)
def StepData.J {x : Fin (N + 1) → Ω} (T : StepData k x) : Ideal (Poly k N) :=
  zeroIdeal T.D T.si
end Steps
section Lemmas
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem SubSystem.ext_sub {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] {F G : SubSystem S x E} (h : ∀ I, F.sub I = G.sub I) : F = G := by
  obtain ⟨s₁, m₁⟩ := F
  obtain ⟨s₂, m₂⟩ := G
  have : s₁ = s₂ := funext h
  subst this
  rfl
theorem SubSystem.twist_twistSys_zero {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (F : SubSystem S x E) : F.twist (twistSys S x 0) = F := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x 0 I at hq
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.mem_span_singleton] at hq
    obtain ⟨a, rfl⟩ := hq
    have : (a • (1 : Ω)) • y = a • y := by
      rw [chartRing_smul_def, mul_one]; rfl
    rw [SetLike.mem_coe, this]
    exact (F.sub I).smul_mem a hy
  · intro y hy
    exact Submodule.subset_span ⟨1, one_mem_twistMod_zero I, y, hy, (one_smul Ω y).symm⟩
theorem twistSys_zero_twist (Q : SubSystem S x Ω) : (twistSys S x 0).twist Q = Q := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change y ∈ twistMod S x 0 I at hy
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    have : q • (a • (1 : Ω)) = a • q := by
      rw [chartRing_smul_def, chartRing_smul_def, mul_one, smul_eq_mul, mul_comm]
    rw [SetLike.mem_coe, this]
    exact (Q.sub I).smul_mem a hq
  · intro q hq
    exact Submodule.subset_span ⟨q, hq, 1, one_mem_twistMod_zero I, by rw [smul_eq_mul, mul_one]⟩
theorem pow_twistSys_zero (n : ℕ) : (twistSys S x 0).pow n = twistSys S x 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((twistSys S x 0).pow n).twist (twistSys S x 0) = _
    rw [ih, SubSystem.twist_twistSys_zero]
theorem foldl_twist_zero {n : ℕ} (L : Fin n → SubSystem S x Ω) (hL : ∀ i, L i = twistSys S x 0)
    (l : List (Fin n)) :
    l.foldl (fun F i => F.twist (L i)) (twistSys S x 0) = twistSys S x 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, hL a, SubSystem.twist_twistSys_zero]
    exact ih
theorem tensorSub_of_forall_eq {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (hL : ∀ i, L i = twistSys S x 0) (T : Finset (Fin n)) : tensorSub L T = twistSys S x 0 :=
  foldl_twist_zero L hL _
theorem interNum_twistSys_zero (pp : Ideal (Poly S N)) : interNum pp ![twistSys S x 0] = 0 := by
  have h0 : interSum pp ![twistSys S x 0] = fun _ => 0 := by
    funext c
    have hT : ∀ T : Finset (Fin 1), tensorSub ![twistSys S x 0] T = twistSys S x 0 :=
      tensorSub_of_forall_eq _ (fun i => by fin_cases i; rfl)
    simp only [interSum, hT]
    rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card
      (f := fun j => (-1 : ℤ) ^ (1 - j) * restrLen pp ((twistSys S x 0).twist (twistSys S x (c : ℤ))))]
    simp [Finset.sum_range_succ]
  rw [interNum, h0]
  exact tendsto_const_nhds.limUnder_eq
theorem nef_twistSys_zero : Nef (twistSys S x 0) := fun pp _ _ => by
  rw [interNum_twistSys_zero]
end Lemmas
section Inhabitants2
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem isSubvar_genericPt (k : Type u) [Field k] (N : ℕ) :
    IsSubvar (genericPt k N) (primeOf (S := k) (genericPt k N)) N where
  isPrime := inferInstance
  homog p hp d := homogeneousComponent_mem_primeOf _ hp d
  le := le_rfl
  relevant := ⟨0, by rw [primeOf_genericPt, Submodule.mem_bot]; exact X_ne_zero 0⟩
  dim := by
    rw [primeOf_genericPt, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (Poly k N)),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
end Inhabitants2
section LineData
variable (k : Type u) [Field k]
def lineStepData : StepData k (genericPt k 1) where
  d := 0
  dim := isSubvar_genericPt k 1
  M := twistBundle k (genericPt k 1) 0
  nef := nef_twistSys_zero
  t := 2
  s' := 1
  s'_pos := one_pos
  s'_lt := by norm_num
  p := 2
  p_pos := by norm_num
  m := 2
  m_eq := by norm_num
  c₁ := 1
  c₁_pos := le_rfl
  si := genericPt k 1 0
  si_mem := by
    have h0 : (twistBundle k (genericPt k 1) 0).toSubSystem = twistSys k (genericPt k 1) 0 := rfl
    rw [h0, twistMul, pow_twistSys_zero, twistSys_zero_twist, show (2 : ℤ) - 1 = 1 by norm_num]
    exact mem_secs_twistBundle_one 0
  si_ne := (map_ne_zero_iff _ (IsFractionRing.injective (Poly k 1) (FractionRing (Poly k 1)))).mpr
    (X_ne_zero 0)
def ptX : Fin (0 + 1) → k := fun _ => 1
end LineData
end
end GroundTheory.Heights₂.Heights.Kleiman


