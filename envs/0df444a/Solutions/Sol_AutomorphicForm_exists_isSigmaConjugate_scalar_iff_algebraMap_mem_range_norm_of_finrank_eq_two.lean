-- Prove2me | solution 1 for AutomorphicForm.exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8fb553eb-aed0-54e2-a724-307da35f4e2f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "sigmaTensor sigmaGL IsSigmaConjugate"
namespace KindNorm
p2m_open "AutomorphicForm"

section Galois

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem galois_facts (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    σ * σ = 1 ∧ σ ≠ 1 ∧ ∀ c : L, σ c = c → c ∈ Set.range (algebraMap K L) := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : IsGalois K L := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hσσ : σ * σ = 1 := by
    have := pow_card_eq_one' (G := L ≃ₐ[K] L) (x := σ)
    rw [hcard, pow_two] at this
    exact this
  have hpow : ∀ τ : L ≃ₐ[K] L, τ = 1 ∨ τ = σ := by
    intro τ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
    have hσ2 : σ ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hσσ]
    have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm.trans (by ring)
    have hnn : 0 ≤ k % 2 := Int.emod_nonneg k (by norm_num)
    have hlt : k % 2 < 2 := Int.emod_lt_of_pos k (by norm_num)
    have : σ ^ k = σ ^ (k % 2) := by
      conv_lhs => rw [hk, zpow_add, zpow_mul, hσ2, one_zpow, one_mul]
    rw [this]
    interval_cases (k % 2)
    · left; simp
    · right; simp
  refine ⟨hσσ, ?_, fun c hc => ?_⟩
  · intro hσ1
    have hsub : Subsingleton (L ≃ₐ[K] L) := ⟨fun τ τ' => by
      rcases hpow τ with h | h <;> rcases hpow τ' with h' | h' <;> simp [h, h', hσ1]⟩
    have := Nat.card_of_subsingleton (1 : L ≃ₐ[K] L)
    rw [hcard] at this
    exact absurd this (by norm_num)
  · rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro τ
    rcases hpow τ with rfl | rfl
    · rfl
    · exact hc

end Galois

section Algebra

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (F : Type) [Field F] [Algebra K F]

abbrev E : Type := L ⊗[K] F

abbrev σE : E K L F →+* E K L F := sigmaTensor K L F σ

theorem σE_tmul (l : L) (f : F) : σE K L σ F (l ⊗ₜ f) = σ l ⊗ₜ f := by
  simp [σE, sigmaTensor]

theorem σE_algebraMap (f : F) : σE K L σ F (algebraMap F (E K L F) f) = algebraMap F (E K L F) f := by
  rw [TensorProduct.RightActions.algebraMap_eval, σE_tmul, map_one]

theorem σE_smul (f : F) (x : E K L F) : σE K L σ F (f • x) = f • σE K L σ F x := by
  rw [Algebra.smul_def, map_mul, σE_algebraMap, ← Algebra.smul_def]

theorem σE_includeLeft (l : L) :
    σE K L σ F (Algebra.TensorProduct.includeLeftRingHom l) = Algebra.TensorProduct.includeLeftRingHom (σ l) := by
  show σE K L σ F (l ⊗ₜ 1) = σ l ⊗ₜ 1
  exact σE_tmul K L σ F l 1

variable {K L σ}

theorem σE_σE (hσσ : σ * σ = 1) (x : E K L F) : σE K L σ F (σE K L σ F x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l f =>
      rw [σE_tmul, σE_tmul, ← AlgEquiv.mul_apply, hσσ, AlgEquiv.one_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem exists_eq_algebraMap_of_fixed (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
    (x : E K L F) (hx : σE K L σ F x = x) : ∃ f : F, x = algebraMap F (E K L F) f := by
  have hex : Function.Exact (Algebra.linearMap K L) (σ.toLinearMap - LinearMap.id : L →ₗ[K] L) := by
    intro l
    constructor
    · intro hl
      have : σ l - l = 0 := hl
      exact hfix l (sub_eq_zero.1 this)
    · rintro ⟨k, rfl⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, Algebra.linearMap_apply,
        AlgEquiv.toLinearMap_apply, AlgEquiv.commutes, sub_self]
  have hexA := Module.Flat.rTensor_exact F hex
  have hrT : ∀ w : E K L F, ((σ.toLinearMap - LinearMap.id).rTensor F) w = σE K L σ F w - w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
        rw [LinearMap.rTensor_tmul, LinearMap.sub_apply, LinearMap.id_apply, TensorProduct.sub_tmul, σE_tmul]
        rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add]; abel
  have hu0 : ((σ.toLinearMap - LinearMap.id).rTensor F) x = 0 := by rw [hrT, hx, sub_self]
  obtain ⟨w, hw⟩ := (hexA x).1 hu0
  rw [← hw]
  clear hw hu0 hx
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul k a =>
      refine ⟨k • a, ?_⟩
      rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        TensorProduct.RightActions.algebraMap_eval]
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩

end Algebra

section Norm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (F : Type) [Field F] [Algebra K F]

structure MovedGen where
  β : L
  hβ : σ β ≠ β
  t₀ : K
  n₀ : K
  ht₀ : algebraMap K L t₀ = β + σ β
  hn₀ : algebraMap K L n₀ = β * σ β

variable {K L σ}

theorem exists_movedGen (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hfix : ∀ c : L, σ c = c → c ∈ Set.range (algebraMap K L)) : Nonempty (MovedGen K L σ) := by
  obtain ⟨β, hβ⟩ : ∃ β : L, σ β ≠ β := by
    by_contra h
    exact hσ1 (AlgEquiv.ext fun β => by_contra fun hβ => h ⟨β, hβ⟩)
  have hσσ' : ∀ l : L, σ (σ l) = l := fun l => by rw [← AlgEquiv.mul_apply, hσσ, AlgEquiv.one_apply]
  obtain ⟨t₀, ht₀⟩ := hfix (β + σ β) (by rw [map_add, hσσ', add_comm])
  obtain ⟨n₀, hn₀⟩ := hfix (β * σ β) (by rw [map_mul, hσσ', mul_comm])
  exact ⟨⟨β, hβ, t₀, n₀, ht₀, hn₀⟩⟩

variable (g : MovedGen K L σ)

theorem linearIndependent_one_β : LinearIndependent K ![(1 : L), g.β] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
    exact ⟨hst, rfl⟩
  · exfalso
    have hβ : g.β = algebraMap K L (-s / t) := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      rw [map_div₀, map_neg, eq_div_iff ((map_ne_zero (algebraMap K L)).mpr ht)]
      linear_combination hst
    exact g.hβ (by rw [hβ, AlgEquiv.commutes])

def bL (h2 : Module.finrank K L = 2) : Module.Basis (Fin 2) K L :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_β g) (by rw [Fintype.card_fin, h2])

theorem bL_zero (h2 : Module.finrank K L = 2) : bL g h2 0 = 1 := by
  simp [bL]

theorem bL_one (h2 : Module.finrank K L = 2) : bL g h2 1 = g.β := by
  simp [bL]

def u : E K L F := Algebra.TensorProduct.includeLeftRingHom g.β

def t : F := algebraMap K F g.t₀
def n : F := algebraMap K F g.n₀

theorem includeLeft_algebraMap (k : K) :
    (Algebra.TensorProduct.includeLeftRingHom (algebraMap K L k) : E K L F) = algebraMap F (E K L F) (algebraMap K F k) := by
  show (Algebra.TensorProduct.includeLeft : L →ₐ[K] E K L F) (algebraMap K L k) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K F (E K L F)]

theorem u_mul_u : u F g * u F g = algebraMap F (E K L F) (t F g) * u F g - algebraMap F (E K L F) (n F g) := by
  have hL : g.β * g.β = algebraMap K L g.t₀ * g.β - algebraMap K L g.n₀ := by
    rw [g.ht₀, g.hn₀]; ring
  have := congrArg (Algebra.TensorProduct.includeLeftRingHom : L →+* E K L F) hL
  rw [map_mul, map_sub, map_mul, includeLeft_algebraMap, includeLeft_algebraMap] at this
  exact this

theorem σE_u : σE K L σ F (u F g) = algebraMap F (E K L F) (t F g) - u F g := by
  have hL : σ g.β = algebraMap K L g.t₀ - g.β := by rw [g.ht₀]; ring
  show σE K L σ F (Algebra.TensorProduct.includeLeftRingHom g.β) = _
  rw [σE_includeLeft, hL, map_sub, includeLeft_algebraMap]
  rfl

def bE (h2 : Module.finrank K L = 2) : Module.Basis (Fin 2) F (E K L F) :=
  TensorProduct.RightActions.Algebra.TensorProduct.basis F (bL g h2)

theorem bE_apply (h2 : Module.finrank K L = 2) (i : Fin 2) : bE F g h2 i = bL g h2 i ⊗ₜ (1 : F) := by
  simp [bE, TensorProduct.RightActions.Algebra.TensorProduct.basis, Algebra.TensorProduct.basis_apply]

theorem bE_zero (h2 : Module.finrank K L = 2) : bE F g h2 0 = 1 := by
  rw [bE_apply, bL_zero]; rfl

theorem bE_one (h2 : Module.finrank K L = 2) : bE F g h2 1 = u F g := by
  rw [bE_apply, bL_one]; rfl

theorem eq_coord (h2 : Module.finrank K L = 2) (z : E K L F) :
    z = algebraMap F (E K L F) ((bE F g h2).repr z 0) + algebraMap F (E K L F) ((bE F g h2).repr z 1) * u F g := by
  conv_lhs => rw [← (bE F g h2).sum_repr z]
  rw [Fin.sum_univ_two, bE_zero, bE_one, Algebra.smul_def, mul_one, Algebra.smul_def]

theorem algebraMap_norm_eq (g : MovedGen K L σ) (h2 : Module.finrank K L = 2) (z : E K L F) :
    algebraMap F (E K L F) (Algebra.norm F z) = z * σE K L σ F z := by
  classical
  set b := bE F g h2 with hb
  set p : F := b.repr z 0 with hp
  set q : F := b.repr z 1 with hq
  have hz : z = algebraMap F (E K L F) p + algebraMap F (E K L F) q * u F g := eq_coord F g h2 z
  have hσz : σE K L σ F z = algebraMap F (E K L F) p +
      algebraMap F (E K L F) q * (algebraMap F (E K L F) (t F g) - u F g) := by
    conv_lhs => rw [hz]
    rw [map_add, map_mul, σE_algebraMap, σE_algebraMap, σE_u]
  have hu := u_mul_u F g

  have hzu : z * u F g = (-(q * n F g)) • b 0 + (p + q * t F g) • b 1 := by
    rw [bE_zero, bE_one, Algebra.smul_def, Algebra.smul_def, mul_one, map_neg, map_mul, map_add, map_mul]
    rw [hz]
    linear_combination (algebraMap F (E K L F) q) * hu
  have hcol0 : ∀ i, Algebra.leftMulMatrix b z i 0 = ![p, q] i := by
    intro i
    rw [Algebra.leftMulMatrix_eq_repr_mul, bE_zero, mul_one]
    fin_cases i <;> rfl
  have hcol1 : ∀ i, Algebra.leftMulMatrix b z i 1 = ![-(q * n F g), p + q * t F g] i := by
    intro i
    rw [Algebra.leftMulMatrix_eq_repr_mul, bE_one, hzu]
    have := b.repr_sum_self ![-(q * n F g), p + q * t F g]
    rw [Fin.sum_univ_two] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [this]
  have hnorm : Algebra.norm F z = p * (p + q * t F g) - (-(q * n F g)) * q := by
    rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two, hcol0, hcol0, hcol1, hcol1]
    rfl
  rw [hnorm, hσz, hz]
  simp only [map_sub, map_mul, map_add, map_neg]
  linear_combination ((algebraMap F (E K L F) q) ^ 2) * hu

end Norm

section Matrices

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (F : Type) [Field F] [Algebra K F]

abbrev sc {R : Type*} [CommRing R] (c : Rˣ) : GL (Fin 2) R := Matrix.GeneralLinearGroup.scalar (Fin 2) c

theorem scalar_mul_comm {R : Type*} [CommRing R] (c : Rˣ) (x : GL (Fin 2) R) : sc c * x = x * sc c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (x : Matrix (Fin 2) (Fin 2) R) =
    (x : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

theorem sc_apply_zero_zero {R : Type*} [CommRing R] (c : Rˣ) :
    ((sc c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 = c := by
  simp [Matrix.diagonal]

theorem sc_injective {R : Type*} [CommRing R] {c d : Rˣ} (h : (sc c : GL (Fin 2) R) = sc d) : c = d := by
  have := congrArg (fun x : GL (Fin 2) R => (x : Matrix (Fin 2) (Fin 2) R) 0 0) h
  simp only [sc_apply_zero_zero] at this
  exact Units.ext this

theorem map_sc {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : Rˣ) :
    Matrix.GeneralLinearGroup.map f (sc c) = sc (Units.map (f : R →* S) c) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show f ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : Matrix (Fin 2) (Fin 2) R) i j) = _
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem map_map_gl {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map g (Matrix.GeneralLinearGroup.map f x) = Matrix.GeneralLinearGroup.map (g.comp f) x :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem map_congr_gl {R S : Type*} [CommRing R] [CommRing S] {f g : R →+* S} (h : ∀ r, f r = g r) (x : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map f x = Matrix.GeneralLinearGroup.map g x :=
  Matrix.GeneralLinearGroup.ext fun _ _ => h _

abbrev σGL : GL (Fin 2) (E K L F) →* GL (Fin 2) (E K L F) := sigmaGL K L F σ

abbrev incl : GL (Fin 2) L →* GL (Fin 2) (E K L F) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* E K L F)

theorem σGL_incl (δ₀ : GL (Fin 2) L) :
    σGL K L σ F (incl K L F δ₀) = incl K L F (Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀) := by
  show Matrix.GeneralLinearGroup.map (σE K L σ F) (incl K L F δ₀) = _
  rw [map_map_gl, map_map_gl]
  exact map_congr_gl (fun l => σE_includeLeft K L σ F l) δ₀

theorem σGL_sc (z : (E K L F)ˣ) : σGL K L σ F (sc z) = sc (Units.map (σE K L σ F : E K L F →* E K L F) z) :=
  map_sc _ z

variable {K L σ}

theorem σGL_σGL (hσσ : σ * σ = 1) (x : GL (Fin 2) (E K L F)) : σGL K L σ F (σGL K L σ F x) = x :=
  Matrix.GeneralLinearGroup.ext fun _ _ => σE_σE F hσσ _

theorem incl_sc_algebraMap (a : Kˣ) :
    incl K L F (sc (Units.map (algebraMap K L : K →* L) a)) =
      sc (Units.map (algebraMap F (E K L F) : F →* E K L F) (Units.map (algebraMap K F : K →* F) a)) := by
  rw [map_sc]
  congr 1
  refine Units.ext ?_
  exact includeLeft_algebraMap F (a : K)

theorem norm_eq_of_isSigmaConjugate (hσσ : σ * σ = 1) (g : MovedGen K L σ) (h2 : Module.finrank K L = 2)
    (δ₀ : GL (Fin 2) L) (a : Kˣ)
    (ha : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) a))
    (z : (E K L F)ˣ) (hz : IsSigmaConjugate K L F σ (incl K L F δ₀) (sc z)) :
    Algebra.norm F (z : E K L F) = algebraMap K F a := by
  obtain ⟨x, hx⟩ := hz

  have hN : sc z * σGL K L σ F (sc z) =
      x⁻¹ * (incl K L F δ₀ * σGL K L σ F (incl K L F δ₀)) * x := by
    conv_lhs => rw [hx]
    rw [map_mul, map_mul, map_inv, σGL_σGL F hσσ]
    group
  rw [σGL_incl, ← map_mul, ha, incl_sc_algebraMap, ← scalar_mul_comm, mul_assoc, inv_mul_cancel, mul_one,
    σGL_sc, ← map_mul] at hN
  have hzz := sc_injective hN
  have hval : (z : E K L F) * σE K L σ F z = algebraMap F (E K L F) (algebraMap K F a) :=
    congrArg (fun w : (E K L F)ˣ => (w : E K L F)) hzz
  rw [← algebraMap_norm_eq F g h2] at hval
  exact (Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective) hval

end Matrices

section H90

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (F : Type) [Field F] [Algebra K F]

def σV (v : Fin 2 → E K L F) : Fin 2 → E K L F := fun i => σE K L σ F (v i)

theorem σV_add (v w : Fin 2 → E K L F) : σV σ F (v + w) = σV σ F v + σV σ F w := by
  funext i; simp [σV]

theorem σV_smul (e : E K L F) (v : Fin 2 → E K L F) : σV σ F (e • v) = σE K L σ F e • σV σ F v := by
  funext i; simp [σV]

theorem σV_smulF (f : F) (v : Fin 2 → E K L F) : σV σ F (f • v) = f • σV σ F v := by
  funext i; simp only [σV, Pi.smul_apply, σE_smul]

theorem σV_σV (hσσ : σ * σ = 1) (v : Fin 2 → E K L F) : σV σ F (σV σ F v) = v := by
  funext i; exact σE_σE F hσσ _

theorem σV_mulVec (M : Matrix (Fin 2) (Fin 2) (E K L F)) (v : Fin 2 → E K L F) :
    σV σ F (M.mulVec v) = (M.map (σE K L σ F)).mulVec (σV σ F v) := by
  funext i
  exact RingHom.map_mulVec (σE K L σ F) M v i

variable (c : GL (Fin 2) (E K L F))

def θ (v : Fin 2 → E K L F) : Fin 2 → E K L F := (c : Matrix (Fin 2) (Fin 2) (E K L F)).mulVec (σV σ F v)

theorem θ_add (v w : Fin 2 → E K L F) : θ σ F c (v + w) = θ σ F c v + θ σ F c w := by
  simp only [θ, σV_add, Matrix.mulVec_add]

theorem θ_smul (e : E K L F) (v : Fin 2 → E K L F) : θ σ F c (e • v) = σE K L σ F e • θ σ F c v := by
  simp only [θ, σV_smul, Matrix.mulVec_smul]

theorem θ_smulF (f : F) (v : Fin 2 → E K L F) : θ σ F c (f • v) = f • θ σ F c v := by
  simp only [θ]
  rw [σV_smulF, Matrix.mulVec_smul]

theorem θ_θ (hσσ : σ * σ = 1) (hc : c * σGL K L σ F c = 1) (v : Fin 2 → E K L F) : θ σ F c (θ σ F c v) = v := by
  simp only [θ]
  rw [σV_mulVec, σV_σV σ F hσσ, Matrix.mulVec_mulVec]
  have : (c : Matrix (Fin 2) (Fin 2) (E K L F)) * (c : Matrix (Fin 2) (Fin 2) (E K L F)).map (σE K L σ F) = 1 := by
    have := congrArg (fun x : GL (Fin 2) (E K L F) => (x : Matrix (Fin 2) (Fin 2) (E K L F))) hc
    exact this
  rw [this, Matrix.one_mulVec]

def W : Submodule F (Fin 2 → E K L F) where
  carrier := {v | θ σ F c v = v}
  add_mem' {v w} hv hw := by
    show θ σ F c (v + w) = v + w
    rw [θ_add, hv, hw]
  zero_mem' := by
    show θ σ F c 0 = 0
    simp [θ, σV]
  smul_mem' f {v} hv := by
    show θ σ F c (f • v) = f • v
    rw [θ_smulF, hv]

theorem mem_W {v : Fin 2 → E K L F} : v ∈ W σ F c ↔ θ σ F c v = v := Iff.rfl

theorem average_mem (hσσ : σ * σ = 1) (hc : c * σGL K L σ F c = 1) (v : Fin 2 → E K L F) :
    v + θ σ F c v ∈ W σ F c := by
  rw [mem_W, θ_add, θ_θ σ F c hσσ hc, add_comm]

variable (g : MovedGen K L σ)

theorem isUnit_σu_sub_u : IsUnit (σE K L σ F (u F g) - u F g) := by
  have h : σE K L σ F (u F g) - u F g = Algebra.TensorProduct.includeLeftRingHom (σ g.β - g.β) := by
    show σE K L σ F (Algebra.TensorProduct.includeLeftRingHom g.β) - Algebra.TensorProduct.includeLeftRingHom g.β = _
    rw [σE_includeLeft, map_sub]
  rw [h]
  exact (IsUnit.mk0 _ (sub_ne_zero.mpr g.hβ)).map _

theorem exists_eq_add_u_smul (hσσ : σ * σ = 1) (hc : c * σGL K L σ F c = 1) (h2 : Module.finrank K L = 2)
    (v : Fin 2 → E K L F) :
    ∃ w₀ ∈ W σ F c, ∃ w₁ ∈ W σ F c, v = w₀ + u F g • w₁ := by
  obtain ⟨dinv, hdinv⟩ := (isUnit_σu_sub_u σ F g).exists_left_inv
  set A₁ := v + θ σ F c v with hA₁
  set A₂ := u F g • v + θ σ F c (u F g • v) with hA₂
  have hA₁m : A₁ ∈ W σ F c := average_mem σ F c hσσ hc v
  have hA₂m : A₂ ∈ W σ F c := average_mem σ F c hσσ hc _

  have hkey : (σE K L σ F (u F g) - u F g) • v = σE K L σ F (u F g) • A₁ - A₂ := by
    rw [hA₁, hA₂, θ_smul, smul_add, sub_smul]
    abel
  have hv : v = (dinv * σE K L σ F (u F g)) • A₁ - dinv • A₂ := by
    rw [mul_smul, ← smul_sub, ← hkey, smul_smul, hdinv, one_smul]

  set e₁ := dinv * σE K L σ F (u F g) with he₁
  obtain ⟨p₁, q₁, he₁'⟩ : ∃ p q : F, e₁ = algebraMap F (E K L F) p + algebraMap F (E K L F) q * u F g :=
    ⟨_, _, eq_coord F g h2 e₁⟩
  obtain ⟨p₂, q₂, he₂'⟩ : ∃ p q : F, dinv = algebraMap F (E K L F) p + algebraMap F (E K L F) q * u F g :=
    ⟨_, _, eq_coord F g h2 dinv⟩
  refine ⟨p₁ • A₁ - p₂ • A₂, ?_, q₁ • A₁ - q₂ • A₂, ?_, ?_⟩
  · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hA₁m) (Submodule.smul_mem _ _ hA₂m)
  · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hA₁m) (Submodule.smul_mem _ _ hA₂m)
  · rw [hv, he₁', he₂', add_smul, add_smul, mul_smul, mul_smul, algebraMap_smul, algebraMap_smul, algebraMap_smul,
      algebraMap_smul, smul_sub, smul_comm (u F g) q₁ A₁, smul_comm (u F g) q₂ A₂]
    abel

theorem eq_zero_of_add_u_smul_eq_zero {w₀ w₁ : Fin 2 → E K L F} (hw₀ : w₀ ∈ W σ F c)
    (hw₁ : w₁ ∈ W σ F c) (h : w₀ + u F g • w₁ = 0) : w₀ = 0 ∧ w₁ = 0 := by
  have h' : w₀ + σE K L σ F (u F g) • w₁ = 0 := by
    have := congrArg (θ σ F c) h
    rw [θ_add, θ_smul, (mem_W σ F c).1 hw₀, (mem_W σ F c).1 hw₁] at this
    rw [this]
    simp [θ, σV]
  have hdiff : (σE K L σ F (u F g) - u F g) • w₁ = 0 :=
    calc (σE K L σ F (u F g) - u F g) • w₁ = (w₀ + σE K L σ F (u F g) • w₁) - (w₀ + u F g • w₁) := by
          rw [sub_smul]; abel
      _ = 0 := by rw [h, h', sub_zero]
  obtain ⟨dinv, hdinv⟩ := (isUnit_σu_sub_u σ F g).exists_left_inv
  have hw₁0 : w₁ = 0 := by
    have := congrArg (fun x => dinv • x) hdiff
    simp only [smul_smul, hdinv, one_smul, smul_zero] at this
    exact this
  refine ⟨?_, hw₁0⟩
  rw [hw₁0, smul_zero, add_zero] at h
  exact h

def Φ : (W σ F c × W σ F c) →ₗ[F] (Fin 2 → E K L F) where
  toFun w := (w.1 : Fin 2 → E K L F) + u F g • (w.2 : Fin 2 → E K L F)
  map_add' w w' := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
    abel
  map_smul' f w := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
    rw [smul_comm]

theorem Φ_bijective (hσσ : σ * σ = 1) (hc : c * σGL K L σ F c = 1) (h2 : Module.finrank K L = 2) :
    Function.Bijective (Φ σ F c g) := by
  constructor
  · rw [← LinearMap.ker_eq_bot (f := Φ σ F c g), Submodule.eq_bot_iff]
    rintro ⟨w₀, w₁⟩ hw
    rw [LinearMap.mem_ker] at hw
    obtain ⟨h₀, h₁⟩ := eq_zero_of_add_u_smul_eq_zero σ F c g w₀.2 w₁.2 hw
    ext i <;> simp [h₀, h₁]
  · intro v
    obtain ⟨w₀, hw₀, w₁, hw₁, hv⟩ := exists_eq_add_u_smul σ F c g hσσ hc h2 v
    exact ⟨(⟨w₀, hw₀⟩, ⟨w₁, hw₁⟩), hv.symm⟩

set_option maxHeartbeats 4000000 in
theorem finrank_W (g : MovedGen K L σ) (hσσ : σ * σ = 1) (hc : c * σGL K L σ F c = 1) (h2 : Module.finrank K L = 2) :
    Module.finrank F (W σ F c) = 2 := by
  have e : (W σ F c × W σ F c) ≃ₗ[F] (Fin 2 → E K L F) :=
    LinearEquiv.ofBijective (Φ σ F c g) (Φ_bijective σ F c g hσσ hc h2)
  have h : Module.finrank F (W σ F c × W σ F c) = Module.finrank F (Fin 2 → E K L F) := e.finrank_eq
  have hE : Module.finrank F (E K L F) = 2 := by
    rw [Module.finrank_eq_card_basis (bE F g h2), Fintype.card_fin]
  have hV : Module.finrank F (Fin 2 → E K L F) = 4 := by
    rw [Module.finrank_pi_fintype F (M := fun _ : Fin 2 => E K L F), Fin.sum_univ_two, hE]
  have hP : Module.finrank F (W σ F c × W σ F c) = Module.finrank F (W σ F c) + Module.finrank F (W σ F c) :=
    Module.finrank_prod
  omega

theorem exists_mul_σGL_eq (g : MovedGen K L σ) (hσσ : σ * σ = 1) (hc : c * σGL K L σ F c = 1) (h2 : Module.finrank K L = 2) :
    ∃ y : GL (Fin 2) (E K L F), c * σGL K L σ F y = y := by
  classical
  have hW := finrank_W σ F c g hσσ hc h2
  let bW : Module.Basis (Fin 2) F (W σ F c) := (Module.finBasis F (W σ F c)).reindex (finCongr hW)
  let w : Fin 2 → (Fin 2 → E K L F) := fun j => (bW j : Fin 2 → E K L F)
  have hwm : ∀ j, w j ∈ W σ F c := fun j => (bW j).2
  let y : Matrix (Fin 2) (Fin 2) (E K L F) := Matrix.of fun i j => w j i

  have hyv : ∀ e : Fin 2 → E K L F, y.mulVec e = ∑ j, e j • w j := by
    intro e
    funext i
    simp only [y, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

  have hWspan : ∀ x : W σ F c, ∃ e : Fin 2 → E K L F, y.mulVec e = (x : Fin 2 → E K L F) := by
    intro x
    refine ⟨fun j => algebraMap F (E K L F) (bW.repr x j), ?_⟩
    rw [hyv]
    conv_rhs => rw [← bW.sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    rfl

  have hsurj : Function.Surjective y.mulVec := by
    intro v
    obtain ⟨w₀, hw₀, w₁, hw₁, hv⟩ := exists_eq_add_u_smul σ F c g hσσ hc h2 v
    obtain ⟨e₀, he₀⟩ := hWspan ⟨w₀, hw₀⟩
    obtain ⟨e₁, he₁⟩ := hWspan ⟨w₁, hw₁⟩
    refine ⟨e₀ + u F g • e₁, ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, he₀, he₁, hv]
  have hunit : IsUnit y := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  refine ⟨hunit.unit, ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show ((c : Matrix (Fin 2) (Fin 2) (E K L F)) * y.map (σE K L σ F)) i j = y i j
  have hθ : θ σ F c (w j) = w j := (mem_W σ F c).1 (hwm j)
  have := congrFun hθ i
  simp only [θ, σV, Matrix.mulVec, dotProduct] at this
  rw [Matrix.mul_apply]
  simpa [y, Matrix.map_apply] using this

theorem isSigmaConjugate_of_norm_eq (g : MovedGen K L σ) (hσσ : σ * σ = 1) (h2 : Module.finrank K L = 2)
    (δ₀ : GL (Fin 2) L) (a : Kˣ)
    (ha : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) a))
    (z : (E K L F)ˣ) (hz : Algebra.norm F (z : E K L F) = algebraMap K F a) :
    IsSigmaConjugate K L F σ (incl K L F δ₀) (sc z) := by

  have hzz : z * Units.map (σE K L σ F : E K L F →* E K L F) z =
      Units.map (algebraMap F (E K L F) : F →* E K L F) (Units.map (algebraMap K F : K →* F) a) := by
    refine Units.ext ?_
    show (z : E K L F) * σE K L σ F z = algebraMap F (E K L F) (algebraMap K F a)
    rw [← algebraMap_norm_eq F g h2, hz]

  set c : GL (Fin 2) (E K L F) := (sc z)⁻¹ * incl K L F δ₀ with hcdef
  have hδ : incl K L F δ₀ * σGL K L σ F (incl K L F δ₀) = sc (z * Units.map (σE K L σ F : E K L F →* E K L F) z) := by
    rw [σGL_incl, ← map_mul, ha, incl_sc_algebraMap, hzz]
  have hc : c * σGL K L σ F c = 1 := by
    set w := Units.map (σE K L σ F : E K L F →* E K L F) z with hw
    have hcomm : incl K L F δ₀ * (sc w)⁻¹ = (sc w)⁻¹ * incl K L F δ₀ := by
      rw [← map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)) w]
      exact (scalar_mul_comm w⁻¹ (incl K L F δ₀)).symm
    rw [hcdef, map_mul, map_inv, σGL_sc, ← hw]
    calc (sc z)⁻¹ * incl K L F δ₀ * ((sc w)⁻¹ * σGL K L σ F (incl K L F δ₀))
        = (sc z)⁻¹ * (incl K L F δ₀ * (sc w)⁻¹) * σGL K L σ F (incl K L F δ₀) := by simp only [mul_assoc]
      _ = (sc z)⁻¹ * ((sc w)⁻¹ * incl K L F δ₀) * σGL K L σ F (incl K L F δ₀) := by rw [hcomm]
      _ = (sc z)⁻¹ * (sc w)⁻¹ * (incl K L F δ₀ * σGL K L σ F (incl K L F δ₀)) := by simp only [mul_assoc]
      _ = (sc z)⁻¹ * (sc w)⁻¹ * (sc z * sc w) := by
          rw [hδ]
          exact congrArg _ (map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)) z w)
      _ = sc (z⁻¹ * w⁻¹ * (z * w)) := by
          have hsc : ∀ p q : (E K L F)ˣ, (sc p : GL (Fin 2) (E K L F)) * sc q = sc (p * q) := fun p q =>
            (map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)) p q).symm
          have hsci : ∀ p : (E K L F)ˣ, (sc p : GL (Fin 2) (E K L F))⁻¹ = sc p⁻¹ := fun p =>
            (map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)) p).symm
          rw [hsci, hsci, hsc, hsc, hsc]
      _ = 1 := by
          rw [show z⁻¹ * w⁻¹ * (z * w) = 1 by
            rw [mul_comm z w, ← mul_assoc, mul_assoc z⁻¹, inv_mul_cancel, mul_one, inv_mul_cancel]]
          exact map_one (Matrix.GeneralLinearGroup.scalar (Fin 2))
  obtain ⟨y, hy⟩ := exists_mul_σGL_eq σ F c g hσσ hc h2
  refine ⟨y, ?_⟩

  rw [hcdef, mul_assoc] at hy
  have hkey : incl K L F δ₀ * σGL K L σ F y = sc z * y :=
    calc incl K L F δ₀ * σGL K L σ F y = sc z * ((sc z)⁻¹ * (incl K L F δ₀ * σGL K L σ F y)) := by group
      _ = sc z * y := by rw [hy]
  symm
  rw [mul_assoc, hkey, scalar_mul_comm z y, ← mul_assoc, inv_mul_cancel, one_mul]

end H90

theorem main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (F : Type) [Field F] [Algebra K F]
    (δ₀ : GL (Fin 2) L) (a : Kˣ)
    (ha : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) a)) :
    (∃ z : (L ⊗[K] F)ˣ, IsSigmaConjugate K L F σ (incl K L F δ₀) (sc z)) ↔
      algebraMap K F (a : K) ∈ Set.range (fun x : (L ⊗[K] F)ˣ => Algebra.norm F (x : L ⊗[K] F)) := by
  obtain ⟨hσσ, hσ1, hfix⟩ := galois_facts h2 σ hgen
  obtain ⟨g⟩ := exists_movedGen hσσ hσ1 hfix
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, norm_eq_of_isSigmaConjugate F hσσ g h2 δ₀ a ha z hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, isSigmaConjugate_of_norm_eq σ F g hσσ h2 δ₀ a ha z hz⟩

end AutomorphicForm.KindNorm

end

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (F : Type) [Field F] [Algebra K F]
    (δ₀ : GL (Fin 2) L) (a : Kˣ)
    (ha : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) a)) :
    (∃ z : (L ⊗[K] F)ˣ, AutomorphicForm.IsSigmaConjugate K L F σ
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] F) δ₀)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
      algebraMap K F (a : K) ∈
        Set.range (fun x : (L ⊗[K] F)ˣ => Algebra.norm F (x : L ⊗[K] F)) :=
  AutomorphicForm.KindNorm.main K L h2 σ hgen F δ₀ a ha

end S_AutomorphicForm_exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two (solution)
