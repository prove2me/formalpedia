-- Prove2me | Definitions.Def_HodgeComputerSSR_K5Field
-- name    : HodgeComputerSSR_K5Field
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T03:38:02.495894+00:00
-- url     : https://prove2.me/theorems/f99b4162-0e54-4fe5-bd98-dae6566a56e6
-- title:
--   Reduced 5-variable hypersurface field $K_5$ and weighted residue divergence
-- statement:
--   Constructs the $S_3 \times S_3$-invariant reduced hypersurface polynomial
--
--   $$F_5(S, Q, T, x, y) = 3 S x^2 + 3 T y^2 + H_0(S, Q, T)$$
--
--   over $\mathbb{C}[S, Q, T, x, y]$, proves its irreducibility over $K_4 = \mathbb{C}(S, Q, T, y)$, and defines the reduced function field $K_5 = \operatorname{AdjoinRoot}(F_5)$ with tangential derivations $\delta_0, \delta_1, \delta_2, \delta_3$ corresponding to $(S, Q, T, y)$.
--
--   Defines the weighted divergence operator `resDivW`, the reduced source `srcX`, and proves the radial normal-chart identity `radial_normal_chart_identity` reducing the 5-variable residue PDE to finding $w : \operatorname{Fin} 4 \to K_5$ with $\operatorname{resDivW}(w) = \mathrm{NA}_{Q5} / (2 W_2 H_0)$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/K5Field.lean

import Definitions.Def_HodgeComputerFormal_Algebra
import Definitions.Def_HodgeComputerFormal_FiniteDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false

/-! Reduced 5-variable hypersurface field `K5 = Frac(ℂ[S,Q,T,y])[x] / (F5)`
with tangent derivations `δ_S, δ_Q, δ_T, δ_y`, weighted residue divergence
`resDivW`, and the exact radial normal-chart identity. -/

noncomputable section
namespace SymmetricSexticResidual.K5Field
open MvPolynomial HoldoutConstruction
open scoped BigOperators Polynomial

abbrev Poly3 := MvPolynomial (Fin 3) ℂ
abbrev Poly4 := MvPolynomial (Fin 4) ℂ
abbrev Poly5 := MvPolynomial (Fin 5) ℂ

abbrev K0 := FractionRing Poly3
abbrev K4 := FractionRing Poly4

/-- Tangent indices in `Poly5` (`0=S, 1=Q, 2=T, 3=x, 4=y`). -/
def tanIdx : Fin 4 → Fin 5 := ![0, 1, 2, 4]

def poly3ToPoly4 : Poly3 →+* Poly4 :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![X 0, X 1, X 2]

def poly4ToPoly5 : Poly4 →+* Poly5 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => X (tanIdx i))

def poly3ToPoly5 : Poly3 →+* Poly5 := poly4ToPoly5.comp poly3ToPoly4

lemma poly3ToPoly4_injective : Function.Injective poly3ToPoly4 := by
  let proj : Poly4 →+* Poly3 := MvPolynomial.eval₂Hom MvPolynomial.C ![X 0, X 1, X 2, 0]
  have hcomp : proj.comp poly3ToPoly4 = RingHom.id Poly3 := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [proj, poly3ToPoly4]
    · intro i; fin_cases i <;> simp [proj, poly3ToPoly4]
  exact Function.LeftInverse.injective (g := proj)
    (fun p => congrArg (fun f : Poly3 →+* Poly3 => f p) hcomp)

lemma poly4ToPoly5_injective : Function.Injective poly4ToPoly5 := by
  let proj : Poly5 →+* Poly4 := MvPolynomial.eval₂Hom MvPolynomial.C ![X 0, X 1, X 2, 0, X 3]
  have hcomp : proj.comp poly4ToPoly5 = RingHom.id Poly4 := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [proj, poly4ToPoly5, tanIdx]
    · intro i; fin_cases i <;> simp [proj, poly4ToPoly5, tanIdx]
  exact Function.LeftInverse.injective (g := proj)
    (fun p => congrArg (fun f : Poly4 →+* Poly4 => f p) hcomp)

def k0ToK4 : K0 →+* K4 :=
  IsFractionRing.lift (g := (algebraMap Poly4 K4).comp poly3ToPoly4)
    ((IsFractionRing.injective Poly4 K4).comp poly3ToPoly4_injective)

-- Polynomials in Poly3, Poly4, Poly5
def H0_3 : Poly3 :=
  -2 * X 0 ^ 3 + 6 * X 0 ^ 2 * X 1 - 3 * X 0 * X 1 ^ 2 - 2 * X 1 ^ 3 -
  2 * X 2 ^ 3 + 6 * X 2 ^ 2 - 3 * X 2 - 2 +
  C (5 / 7 : ℂ) * X 1 ^ 2 + C (10 / 7 : ℂ) * X 1

def H0_4 : Poly4 := poly3ToPoly4 H0_3
def H0_5 : Poly5 := poly4ToPoly5 H0_4

def u3_5 : Poly5 := X 3 - X 0 + 2 * X 1
def v3_5 : Poly5 := X 4 - X 2 + 2

def F5 : Poly5 := 3 * X 0 * X 3 ^ 2 + 3 * X 2 * X 4 ^ 2 + H0_5

def DX2_5 : Poly5 :=
  X 0 * X 1 ^ 2 - 4 * X 1 ^ 3 - 4 * X 0 ^ 2 * u3_5 -
  27 * X 0 * u3_5 ^ 2 + 18 * X 0 * X 1 * u3_5

def DY2_4 : Poly4 :=
  let v3 := X 3 - X 2 + 2
  X 2 - 4 - 4 * X 2 ^ 2 * v3 - 27 * X 2 * v3 ^ 2 + 18 * X 2 * v3

def DY2_5 : Poly5 :=
  X 2 - 4 - 4 * X 2 ^ 2 * v3_5 - 27 * X 2 * v3_5 ^ 2 + 18 * X 2 * v3_5

lemma poly4ToPoly5_DY2 : poly4ToPoly5 DY2_4 = DY2_5 := by
  simp [poly4ToPoly5, DY2_4, DY2_5, v3_5, tanIdx, map_ofNat]

def W2_5 : Poly5 := X 0 * X 2 * DX2_5 * DY2_5
def MA_5 : Poly5 := X 0 * u3_5 * X 2 * v3_5

def E_rad (p : Poly5) : Poly5 := X 3 * pderiv 3 p + X 4 * pderiv 4 p
def NA_Q5 : Poly5 := 2 * W2_5 * E_rad MA_5 - MA_5 * E_rad W2_5

lemma F5_eq_u3_v3 :
    F5 = X 0 ^ 3 - 6 * X 0 ^ 2 * X 1 + 9 * X 0 * X 1 ^ 2 - 2 * X 1 ^ 3 +
         6 * X 0 ^ 2 * u3_5 - 12 * X 0 * X 1 * u3_5 + 3 * X 0 * u3_5 ^ 2 +
         X 2 ^ 3 - 6 * X 2 ^ 2 + 9 * X 2 - 2 +
         6 * X 2 ^ 2 * v3_5 - 12 * X 2 * v3_5 + 3 * X 2 * v3_5 ^ 2 +
         C (5 / 7 : ℂ) * X 1 ^ 2 + C (10 / 7 : ℂ) * X 1 := by
  simp only [F5, H0_5, H0_4, H0_3, poly4ToPoly5, poly3ToPoly4, u3_5, v3_5, tanIdx,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, eval₂Hom_X', eval₂Hom_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

-- Quadratic irreducible polynomial for x over K4
def radPoly4 : Poly4 := 3 * X 2 * X 3 ^ 2 + H0_4

private lemma X0_prime_poly4 : Prime (X 0 : Poly4) := by
  have heq : MvPolynomial.finSuccEquiv ℂ 3 (X 0 : Poly4) = Polynomial.X := by
    simp [MvPolynomial.finSuccEquiv_apply]
  have hirr : Irreducible (X 0 : Poly4) :=
    (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 3)).mp (heq ▸ Polynomial.irreducible_X)
  exact hirr.prime

private lemma X0_not_dvd_radPoly4 : ¬ (X 0 : Poly4) ∣ radPoly4 := by
  rintro ⟨q, hq⟩
  have hev := congrArg (MvPolynomial.eval ![0, 0, 0, 0]) hq
  have hlhs : MvPolynomial.eval ![0, 0, 0, 0] radPoly4 = (-2 : ℂ) := by
    simp [radPoly4, H0_4, H0_3, poly3ToPoly4, map_ofNat]
  have hrhs : MvPolynomial.eval ![0, 0, 0, 0] ((X 0 : Poly4) * q) = 0 := by simp
  rw [hlhs, hrhs] at hev
  norm_num at hev

private lemma not_sq_quad : ∀ (a b : Poly4), b ≠ 0 →
    3 * X 0 * a ^ 2 ≠ -radPoly4 * b ^ 2 := by
  intro a b
  induction hn : b.totalDegree using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    intro hb heq
    have hX0_div_rhs : (X 0 : Poly4) ∣ -radPoly4 * b ^ 2 := ⟨3 * a ^ 2, by linear_combination -heq⟩
    have hX0_div_b2 : (X 0 : Poly4) ∣ b ^ 2 := by
      rcases X0_prime_poly4.dvd_or_dvd hX0_div_rhs with h | h
      · exact (X0_not_dvd_radPoly4 (dvd_neg.mp h)).elim
      · exact h
    obtain ⟨b', rfl⟩ := X0_prime_poly4.dvd_of_dvd_pow hX0_div_b2
    have hb' : b' ≠ 0 := fun h => hb (by simp [h])
    have hX0_ne : (X 0 : Poly4) ≠ 0 := X0_prime_poly4.ne_zero
    have h1 : 3 * a ^ 2 = -radPoly4 * (X 0 * b' ^ 2) := by
      apply mul_left_cancel₀ hX0_ne
      linear_combination heq
    have hX0_div_3a2 : (X 0 : Poly4) ∣ 3 * a ^ 2 := ⟨-radPoly4 * b' ^ 2, by linear_combination h1⟩
    have hX0_not_3 : ¬ (X 0 : Poly4) ∣ (3 : Poly4) := by
      rintro ⟨q, hq⟩
      have h := congrArg (MvPolynomial.eval ![0, 0, 0, 0]) hq
      simp at h
    have hX0_div_a2 : (X 0 : Poly4) ∣ a ^ 2 := (X0_prime_poly4.dvd_or_dvd hX0_div_3a2).resolve_left hX0_not_3
    obtain ⟨a', rfl⟩ := X0_prime_poly4.dvd_of_dvd_pow hX0_div_a2
    have h2 : 3 * X 0 * a' ^ 2 = -radPoly4 * b' ^ 2 := by
      apply mul_left_cancel₀ hX0_ne
      linear_combination h1
    have hlt : b'.totalDegree < (X 0 * b').totalDegree := by
      have hsup : ∃ m ∈ b'.support, m.sum (fun _ e => e) = b'.totalDegree := by
        have hne : b'.support.Nonempty := MvPolynomial.support_nonempty.mpr hb'
        obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image b'.support (fun m => m.sum fun _ e => e) hne
        refine ⟨m, hm, le_antisymm (MvPolynomial.le_totalDegree hm) ?_⟩
        rw [MvPolynomial.totalDegree]
        exact Finset.sup_le fun m' hm' => hmax m' hm'
      obtain ⟨m, hm, hmd⟩ := hsup
      have hm' : m + Finsupp.single 0 1 ∈ (X 0 * b').support := by
        rw [MvPolynomial.mem_support_iff, mul_comm, MvPolynomial.coeff_mul_X']
        simp [MvPolynomial.mem_support_iff.mp hm]
      have hle := MvPolynomial.le_totalDegree hm'
      have hsum : (m + Finsupp.single (0 : Fin 4) 1).sum (fun _ e => e) =
          m.sum (fun _ e => e) + 1 := by
        rw [Finsupp.sum_add_index (by intros; rfl) (by intros; rfl)]
        simp
      omega
    exact ih b'.totalDegree (hn ▸ hlt) a' b' rfl hb' h2

def S_4 : K4 := algebraMap Poly4 K4 (X 0)
def Q_4 : K4 := algebraMap Poly4 K4 (X 1)
def T_4 : K4 := algebraMap Poly4 K4 (X 2)
def y_4 : K4 := algebraMap Poly4 K4 (X 3)
def H0_K4 : K4 := algebraMap Poly4 K4 H0_4

lemma S_4_ne_zero : S_4 ≠ 0 := by
  intro h
  exact X0_prime_poly4.ne_zero ((IsFractionRing.injective Poly4 K4) (by simp [S_4] at h))

def minPolyX : K4[X] :=
  Polynomial.X ^ 2 + Polynomial.C (algebraMap Poly4 K4 radPoly4 / (3 * S_4))

lemma minPolyX_monic : minPolyX.Monic := by
  apply Polynomial.monic_X_pow_add
  exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

lemma minPolyX_natDegree : minPolyX.natDegree = 2 := by
  have h1 : (Polynomial.C (algebraMap Poly4 K4 radPoly4 / (3 * S_4)) : K4[X]).degree <
      (Polynomial.X ^ 2 : K4[X]).degree :=
    lt_of_le_of_lt Polynomial.degree_C_le (by simp)
  rw [minPolyX, Polynomial.natDegree_add_eq_left_of_degree_lt h1, Polynomial.natDegree_X_pow]

private lemma minPolyX_no_root (r : K4) : minPolyX.eval r ≠ 0 := by
  intro hroot
  simp only [minPolyX, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at hroot
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective Poly4 r
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbK : algebraMap Poly4 K4 b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hclear : algebraMap Poly4 K4 (3 * X 0 * a ^ 2) = algebraMap Poly4 K4 (-radPoly4 * b ^ 2) := by
    simp only [map_mul, map_pow, map_neg, map_ofNat]
    change 3 * S_4 * algebraMap Poly4 K4 a ^ 2 = -(algebraMap Poly4 K4 radPoly4) * algebraMap Poly4 K4 b ^ 2
    have hmul := congrArg (· * (3 * S_4 * algebraMap Poly4 K4 b ^ 2)) hroot
    have hS4 := S_4_ne_zero
    field_simp [hbK, hS4] at hmul
    linear_combination hmul
  exact not_sq_quad a b hb0 (IsFractionRing.injective Poly4 K4 hclear)

lemma minPolyX_irreducible : Irreducible minPolyX := by
  refine ⟨?_, ?_⟩
  · intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [minPolyX_natDegree] at h0; omega
  · intro P Q hPQ
    have hP0 : P ≠ 0 := fun h => minPolyX_monic.ne_zero (by simp [hPQ, h])
    have hQ0 : Q ≠ 0 := fun h => minPolyX_monic.ne_zero (by simp [hPQ, h])
    have hd : P.natDegree + Q.natDegree = 2 := by
      rw [← Polynomial.natDegree_mul hP0 hQ0, ← hPQ, minPolyX_natDegree]
    by_cases hPd : P.natDegree = 0
    · left
      rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hP0, hPd]; rfl
    · by_cases hQd : Q.natDegree = 0
      · right
        rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hQ0, hQd]; rfl
      · exfalso
        have hP1 : P.natDegree = 1 := by omega
        have hPeq : P = Polynomial.C (P.coeff 1) * Polynomial.X + Polynomial.C (P.coeff 0) := by
          ext k
          rcases k with _ | _ | k
          · simp
          · simp
          · rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
            simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]
            have hge : P.natDegree < k + 2 := by omega
            exact Polynomial.coeff_eq_zero_of_natDegree_lt hge
        have hlc : P.coeff 1 ≠ 0 := by
          rw [← hP1]; exact Polynomial.leadingCoeff_ne_zero.mpr hP0
        let r : K4 := -P.coeff 0 / P.coeff 1
        have hPr : P.eval r = 0 := by
          conv_lhs => rw [hPeq]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, r]
          field_simp [hlc]; ring
        have hmr : minPolyX.eval r = 0 := by rw [hPQ, Polynomial.eval_mul, hPr, zero_mul]
        exact minPolyX_no_root r hmr

lemma minPolyX_eq : minPolyX = Polynomial.X ^ 2 + Polynomial.C (algebraMap Poly4 K4 radPoly4 / (3 * S_4)) := rfl

instance : Fact (Irreducible minPolyX) := ⟨minPolyX_irreducible⟩

attribute [irreducible] minPolyX

abbrev K5 := AdjoinRoot minPolyX

instance : Field K5 := AdjoinRoot.instField
instance : NoZeroDivisors K5 := inferInstance
instance : IsReduced K5 := inferInstance

instance : FiniteDimensional K4 K5 :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis' minPolyX_monic).basis

instance : CharZero K5 :=
  charZero_of_injective_ringHom (algebraMap K4 K5).injective

def k4ToK5 : K4 →+* K5 := algebraMap K4 K5
def S_K : K5 := k4ToK5 S_4
def Q_K : K5 := k4ToK5 Q_4
def T_K : K5 := k4ToK5 T_4
def x_K : K5 := AdjoinRoot.root minPolyX
def y_K : K5 := k4ToK5 y_4

def poly4ToK5 : Poly4 →+* K5 := k4ToK5.comp (algebraMap Poly4 K4)
def toK5 : Poly5 →+* K5 :=
  MvPolynomial.eval₂Hom (poly4ToK5.comp MvPolynomial.C) ![S_K, Q_K, T_K, x_K, y_K]

lemma toK5_poly4 (p : Poly4) : toK5 (poly4ToPoly5 p) = poly4ToK5 p := by
  change (toK5.comp poly4ToPoly5) p = poly4ToK5 p
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c; simp [toK5, poly4ToPoly5, poly4ToK5]
  · intro i
    fin_cases i <;>
      simp [toK5, poly4ToPoly5, poly4ToK5, tanIdx, S_K, Q_K, T_K, y_K, S_4, Q_4, T_4, y_4]

lemma x_K_sq_relation : 3 * S_K * x_K ^ 2 + 3 * T_K * y_K ^ 2 + poly4ToK5 H0_4 = 0 := by
  have hr := AdjoinRoot.eval₂_root minPolyX
  change minPolyX.eval₂ k4ToK5 x_K = 0 at hr
  rw [minPolyX_eq] at hr
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, map_div₀, map_mul, map_ofNat] at hr
  have hS : S_K ≠ 0 := by
    simpa [S_K, k4ToK5] using (algebraMap K4 K5).injective.ne S_4_ne_zero
  have h3S : (3 * S_K : K5) ≠ 0 := mul_ne_zero (by norm_num) hS
  have hrad : k4ToK5 (algebraMap Poly4 K4 radPoly4) = 3 * T_K * y_K ^ 2 + poly4ToK5 H0_4 := by
    simp only [radPoly4, map_add, map_mul, map_pow, map_ofNat]
    rfl
  rw [hrad] at hr
  change x_K ^ 2 + (3 * T_K * y_K ^ 2 + poly4ToK5 H0_4) / (3 * S_K) = 0 at hr
  field_simp [h3S] at hr
  linear_combination hr

lemma toK5_F5 : toK5 F5 = 0 := by
  have h5 : toK5 F5 = 3 * S_K * x_K ^ 2 + 3 * T_K * y_K ^ 2 + poly4ToK5 H0_4 := by
    simp only [F5, H0_5, map_add, map_mul, map_pow, map_ofNat, toK5_poly4]
    simp [toK5]
  rw [h5]
  exact x_K_sq_relation

-- PowerBasis decomposition: every element of K5 is a + b * x_K with a, b ∈ K4
lemma k5_linear_indep (a b : K4) (h : k4ToK5 a + k4ToK5 b * x_K = 0) : a = 0 ∧ b = 0 := by
  let P : K4[X] := Polynomial.C a + Polynomial.C b * Polynomial.X
  have hmk : AdjoinRoot.mk minPolyX P = 0 := by
    simpa [P, k4ToK5, x_K, AdjoinRoot.mk_C, AdjoinRoot.mk_X] using h
  have hdvd : minPolyX ∣ P := (AdjoinRoot.mk_eq_zero).mp hmk
  have hP0 : P = 0 := by
    by_contra hne
    have hle : minPolyX.natDegree ≤ P.natDegree := Polynomial.natDegree_le_of_dvd hdvd hne
    have hPdeg : P.natDegree ≤ 1 := by
      dsimp only [P]
      exact le_trans (Polynomial.natDegree_add_le _ _)
        (max_le (by simp) (le_trans (Polynomial.natDegree_mul_le) (by simp)))
    rw [minPolyX_natDegree] at hle; omega
  exact ⟨by simpa [P] using congrArg (fun q : K4[X] => q.coeff 0) hP0,
         by simpa [P] using congrArg (fun q : K4[X] => q.coeff 1) hP0⟩

lemma exists_k4_coeffs (z : K5) : ∃ a b : K4, z = k4ToK5 a + k4ToK5 b * x_K := by
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective z
  let R := P %ₘ minPolyX
  have hP : AdjoinRoot.mk minPolyX P = AdjoinRoot.mk minPolyX R := by
    rw [← Polynomial.modByMonic_add_div P minPolyX]
    simp [R, map_add, map_mul, AdjoinRoot.mk_self]
  rw [hP]
  have hdeg : R.degree < (2 : WithBot ℕ) := by
    have := Polynomial.degree_modByMonic_lt P minPolyX_monic
    rwa [Polynomial.degree_eq_natDegree minPolyX_monic.ne_zero, minPolyX_natDegree] at this
  have hR : R = Polynomial.C (R.coeff 0) + Polynomial.C (R.coeff 1) * Polynomial.X := by
    ext k
    rcases k with _ | _ | k
    · simp
    · simp
    · rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, zero_add]
      have hlt : R.degree < ((k + 2 : ℕ) : WithBot ℕ) :=
        lt_of_lt_of_le hdeg (by exact_mod_cast (by omega : 2 ≤ k + 2))
      exact Polynomial.coeff_eq_zero_of_degree_lt hlt
  refine ⟨R.coeff 0, R.coeff 1, ?_⟩
  conv_lhs => rw [hR]
  simp [map_add, map_mul, k4ToK5, x_K, AdjoinRoot.mk_C, AdjoinRoot.mk_X]

lemma exists_poly4_denom {ι : Type*} [Fintype ι] (w : ι → K5) :
    ∃ d : Poly4, d ≠ 0 ∧ ∃ n : ι → Poly5,
      ∀ i, toK5 (n i) = poly4ToK5 d * w i := by
  choose a b hab using fun i => exists_k4_coeffs (w i)
  let fam : ι ⊕ ι → K4 := Sum.elim a b
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors Poly4) fam
  choose c hc using hd
  have hd0 : (d : Poly4) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  refine ⟨(d : Poly4), hd0,
    fun i => poly4ToPoly5 (c (Sum.inl i)) + poly4ToPoly5 (c (Sum.inr i)) * X 3, ?_⟩
  intro i
  have h1 := congrArg k4ToK5 (hc (Sum.inl i))
  have h2 := congrArg k4ToK5 (hc (Sum.inr i))
  simp only [fam, Sum.elim_inl, Sum.elim_inr, Algebra.smul_def, map_mul] at h1 h2
  rw [map_add, map_mul, toK5_poly4, toK5_poly4]
  have hx : toK5 (X 3) = x_K := by simp [toK5]
  rw [hx, hab i, mul_add]
  change poly4ToK5 (c (Sum.inl i)) + poly4ToK5 (c (Sum.inr i)) * x_K =
    poly4ToK5 d * k4ToK5 (a i) + poly4ToK5 d * (k4ToK5 (b i) * x_K)
  change poly4ToK5 (c (Sum.inl i)) = poly4ToK5 d * k4ToK5 (a i) at h1
  change poly4ToK5 (c (Sum.inr i)) = poly4ToK5 d * k4ToK5 (b i) at h2
  rw [h1, h2]
  ring

-- Nonzero lemmas in K5
lemma poly4ToK5_ne_zero {p : Poly4} (hp : p ≠ 0) : poly4ToK5 p ≠ 0 := by
  intro h
  have h1 : algebraMap Poly4 K4 p = 0 :=
    (algebraMap K4 K5).injective (by simpa [poly4ToK5, k4ToK5] using h)
  exact hp ((IsFractionRing.injective Poly4 K4) (by simpa using h1))

lemma S_K_ne_zero : S_K ≠ 0 := poly4ToK5_ne_zero X0_prime_poly4.ne_zero

lemma T_K_ne_zero : T_K ≠ 0 := poly4ToK5_ne_zero (by
  intro h; have := congrArg (MvPolynomial.eval ![0, 0, 1, 0]) h; simp at this)

lemma x_K_ne_zero : x_K ≠ 0 := by
  intro hx
  have h := (k5_linear_indep 0 1 (by simp [hx])).2
  exact one_ne_zero h

def Fx_K : K5 := toK5 (pderiv 3 F5)
def H0_K : K5 := poly4ToK5 H0_4
def DX2_K : K5 := toK5 DX2_5
def DY2_K : K5 := toK5 DY2_5
def W2_K : K5 := toK5 W2_5
def MA_K : K5 := toK5 MA_5

lemma pderiv_ofNat {σ : Type*} (i : σ) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (no_index (OfNat.ofNat n) : MvPolynomial σ ℂ) = 0 := by
  change pderiv i (n : MvPolynomial σ ℂ) = 0
  rw [← map_natCast MvPolynomial.C]; exact MvPolynomial.pderiv_C

lemma pderiv_3_poly4ToPoly5 (p : Poly4) : pderiv (3 : Fin 5) (poly4ToPoly5 p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [poly4ToPoly5]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p j hp =>
    have hj : tanIdx j ≠ 3 := by fin_cases j <;> decide
    have hX : poly4ToPoly5 (X j) = X (tanIdx j) := by simp [poly4ToPoly5]
    simp [map_mul, Derivation.leibniz, hp, hX, pderiv_X, hj]

lemma Fx_K_eq : Fx_K = 6 * S_K * x_K := by
  have hp : pderiv (3 : Fin 5) F5 = 6 * X 0 * X 3 := by
    have hH : pderiv (3 : Fin 5) H0_5 = 0 := pderiv_3_poly4ToPoly5 H0_4
    simp only [F5, map_add, hH, add_zero, Derivation.leibniz, Derivation.leibniz_pow,
      pderiv_ofNat, pderiv_X, smul_eq_mul, nsmul_eq_mul]
    simp; ring
  rw [Fx_K, hp]; simp [toK5]

lemma Fx_K_ne_zero : Fx_K ≠ 0 := by
  rw [Fx_K_eq]; exact mul_ne_zero (mul_ne_zero (by norm_num) S_K_ne_zero) x_K_ne_zero

lemma H0_K_ne_zero : H0_K ≠ 0 := poly4ToK5_ne_zero (by
  intro h; have := congrArg (MvPolynomial.eval ![0, 0, 0, 0]) h
  simp [H0_4, H0_3, poly3ToPoly4, map_ofNat] at this)

lemma DY2_K_ne_zero : DY2_K ≠ 0 := by
  rw [DY2_K, ← poly4ToPoly5_DY2, toK5_poly4]
  exact poly4ToK5_ne_zero (by
    intro h; have := congrArg (MvPolynomial.eval ![0, 0, 0, 0]) h
    simp [DY2_4] at this)

lemma DX2_K_ne_zero : DX2_K ≠ 0 := by
  have hdx : DX2_K = k4ToK5 (algebraMap Poly4 K4
      (X 0 * X 1 ^ 2 - 4 * X 1 ^ 3 + 4 * X 0 ^ 3 - 26 * X 0 ^ 2 * X 1 -
        27 * X 0 * (-X 0 + 2 * X 1) ^ 2 + 36 * X 0 * X 1 ^ 2) +
      9 * algebraMap Poly4 K4 radPoly4) +
      k4ToK5 (algebraMap Poly4 K4 (50 * X 0 ^ 2 - 90 * X 0 * X 1)) * x_K := by
    have hsq : -27 * S_K * x_K ^ 2 = 9 * poly4ToK5 radPoly4 := by
      have hr := x_K_sq_relation
      have hrad : poly4ToK5 radPoly4 = 3 * T_K * y_K ^ 2 + poly4ToK5 H0_4 := by
        simp only [radPoly4, map_add, map_mul, map_pow, map_ofNat]; rfl
      rw [hrad]; linear_combination -9 * hr
    have h1 : DX2_K = S_K * Q_K ^ 2 - 4 * Q_K ^ 3 - 4 * S_K ^ 2 * (x_K - S_K + 2 * Q_K) -
        27 * S_K * (x_K - S_K + 2 * Q_K) ^ 2 + 18 * S_K * Q_K * (x_K - S_K + 2 * Q_K) := by
      simp [DX2_K, DX2_5, u3_5, toK5]
    rw [h1]
    have h2 : k4ToK5 (algebraMap Poly4 K4
        (X 0 * X 1 ^ 2 - 4 * X 1 ^ 3 + 4 * X 0 ^ 3 - 26 * X 0 ^ 2 * X 1 -
          27 * X 0 * (-X 0 + 2 * X 1) ^ 2 + 36 * X 0 * X 1 ^ 2) +
        9 * algebraMap Poly4 K4 radPoly4) +
        k4ToK5 (algebraMap Poly4 K4 (50 * X 0 ^ 2 - 90 * X 0 * X 1)) * x_K =
        (S_K * Q_K ^ 2 - 4 * Q_K ^ 3 + 4 * S_K ^ 3 - 26 * S_K ^ 2 * Q_K -
          27 * S_K * (-S_K + 2 * Q_K) ^ 2 + 36 * S_K * Q_K ^ 2 + 9 * poly4ToK5 radPoly4) +
        (50 * S_K ^ 2 - 90 * S_K * Q_K) * x_K := by
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
      rfl
    rw [h2, ← hsq]
    ring
  intro h0
  rw [hdx] at h0
  have hb := (k5_linear_indep _ _ h0).2
  have hpoly : (50 * X 0 ^ 2 - 90 * X 0 * X 1 : Poly4) = 0 :=
    (IsFractionRing.injective Poly4 K4) (by simpa using hb)
  have hev := congrArg (MvPolynomial.eval ![1, 0, 0, 0]) hpoly
  simp at hev

lemma W2_K_ne_zero : W2_K ≠ 0 := by
  have hw : W2_K = S_K * T_K * DX2_K * DY2_K := by
    simp [W2_K, W2_5, DX2_K, DY2_K, toK5]
  rw [hw]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero S_K_ne_zero T_K_ne_zero) DX2_K_ne_zero) DY2_K_ne_zero

-- Derivations on K4 and K5
section Derivations
local instance : Algebra ℤ K4 := Ring.toIntAlgebra K4
local instance : Algebra ℤ K5 := Ring.toIntAlgebra K5

def pderiv4_K4 (i : Fin 4) : Derivation ℤ K4 K4 :=
  HoldoutConstruction.extendRingDerivation (P := Poly4) (L := K4)
    ((MvPolynomial.pderiv i : Derivation ℂ Poly4 Poly4).restrictScalars ℤ)

lemma pderiv4_K4_map (i : Fin 4) (p : Poly4) :
    pderiv4_K4 i (algebraMap Poly4 K4 p) = algebraMap Poly4 K4 (pderiv i p) :=
  HoldoutConstruction.extendRingDerivation_apply _ p

def δ (i : Fin 4) : Derivation ℤ K5 K5 :=
  HoldoutConstruction.extendFiniteDerivation (K := K4) (L := K5) (pderiv4_K4 i)

lemma δ_k4 (i : Fin 4) (z : K4) : δ i (k4ToK5 z) = k4ToK5 (pderiv4_K4 i z) :=
  HoldoutConstruction.extendFiniteDerivation_apply (pderiv4_K4 i) z

lemma δ_poly4 (i : Fin 4) (p : Poly4) :
    δ i (poly4ToK5 p) = poly4ToK5 (pderiv i p) := by
  change δ i (k4ToK5 (algebraMap Poly4 K4 p)) = _
  rw [δ_k4, pderiv4_K4_map]; rfl

lemma δ_S (i : Fin 4) : δ i S_K = if i = 0 then 1 else 0 := by
  change δ i (poly4ToK5 (X 0)) = _
  rw [δ_poly4, pderiv_X]
  fin_cases i <;> simp

lemma δ_Q (i : Fin 4) : δ i Q_K = if i = 1 then 1 else 0 := by
  change δ i (poly4ToK5 (X 1)) = _
  rw [δ_poly4, pderiv_X]
  fin_cases i <;> simp

lemma δ_T (i : Fin 4) : δ i T_K = if i = 2 then 1 else 0 := by
  change δ i (poly4ToK5 (X 2)) = _
  rw [δ_poly4, pderiv_X]
  fin_cases i <;> simp

lemma δ_y (i : Fin 4) : δ i y_K = if i = 3 then 1 else 0 := by
  change δ i (poly4ToK5 (X 3)) = _
  rw [δ_poly4, pderiv_X]
  fin_cases i <;> simp

lemma δ_C (i : Fin 4) (c : ℂ) : δ i (poly4ToK5 (C c)) = 0 := by
  rw [δ_poly4, pderiv_C, map_zero]

lemma δ_ofNat (i : Fin 4) (n : ℕ) [n.AtLeastTwo] :
    δ i (no_index (OfNat.ofNat n)) = 0 := by
  change δ i (n : K5) = 0; exact (δ i).map_natCast n

lemma pderiv_poly4ToPoly5 (i : Fin 4) (p : Poly4) :
    pderiv (tanIdx i) (poly4ToPoly5 p) = poly4ToPoly5 (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [poly4ToPoly5]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p j hp =>
    have hX : poly4ToPoly5 (X j) = X (tanIdx j) := by simp [poly4ToPoly5]
    have hs : (Pi.single (tanIdx i) (1 : Poly5) : Fin 5 → Poly5) (tanIdx j) =
        poly4ToPoly5 ((Pi.single i (1 : Poly4) : Fin 4 → Poly4) j) := by
      fin_cases i <;> fin_cases j <;> simp [tanIdx]
    simp only [map_mul, Derivation.leibniz, map_add, smul_eq_mul, hp, hX, pderiv_X, hs]

lemma δ_x (i : Fin 4) : δ i x_K = -(toK5 (pderiv (tanIdx i) F5)) / Fx_K := by
  have h := congrArg (δ i) x_K_sq_relation
  simp only [map_zero, map_add, Derivation.leibniz, Derivation.leibniz_pow, δ_ofNat, δ_poly4,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, mul_zero, add_zero] at h
  norm_num at h
  have hF : toK5 (pderiv (tanIdx i) F5) =
      3 * δ i S_K * x_K ^ 2 + 3 * δ i T_K * y_K ^ 2 + 6 * T_K * y_K * δ i y_K +
        poly4ToK5 (pderiv i H0_4) := by
    have hp : pderiv (tanIdx i) F5 =
        3 * pderiv (tanIdx i) (X 0) * X 3 ^ 2 +
        3 * pderiv (tanIdx i) (X 2) * X 4 ^ 2 +
        6 * X 2 * X 4 * pderiv (tanIdx i) (X 4) +
        poly4ToPoly5 (pderiv i H0_4) := by
      simp only [F5, H0_5, map_add, Derivation.leibniz, Derivation.leibniz_pow,
        pderiv_ofNat, pderiv_poly4ToPoly5,
        pderiv_X, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
      fin_cases i <;> simp [tanIdx] <;> ring
    rw [hp, map_add, map_add, map_add, toK5_poly4]
    simp only [map_mul, map_pow, map_ofNat, toK5, eval₂Hom_X', pderiv_X, δ_S, δ_T, δ_y]
    fin_cases i <;> simp [tanIdx]
  rw [hF, Fx_K_eq]
  apply (eq_div_iff (by rw [← Fx_K_eq]; exact Fx_K_ne_zero)).mpr
  linear_combination h

lemma δ_toK5 (i : Fin 4) (p : Poly5) :
    δ i (toK5 p) =
      toK5 (pderiv (tanIdx i) p) - (toK5 (pderiv (tanIdx i) F5) / Fx_K) * toK5 (pderiv 3 p) := by
  have hchain := HoldoutConstruction.derivation_eval₂_chain (δ i)
    (poly4ToK5.comp MvPolynomial.C) ![S_K, Q_K, T_K, x_K, y_K]
    (fun c => δ_C i c) p
  change δ i (toK5 p) = ∑ j : Fin 5, toK5 (pderiv j p) * δ i (![S_K, Q_K, T_K, x_K, y_K] j) at hchain
  rw [hchain, Fin.sum_univ_five]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    δ_S, δ_Q, δ_T, δ_x, δ_y]
  fin_cases i <;> simp [tanIdx] <;> ring

-- Weighted residue divergence and radial normal-chart identity in K5
def resDivW (w : Fin 4 → K5) : K5 :=
  ∑ i : Fin 4, (δ i (w i) - w i * δ i Fx_K / Fx_K - w i * δ i W2_K / (2 * W2_K))

lemma resDivW_add (u v : Fin 4 → K5) :
    resDivW (fun i => u i + v i) = resDivW u + resDivW v := by
  simp only [resDivW, map_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

lemma resDivW_sub (u v : Fin 4 → K5) :
    resDivW (fun i => u i - v i) = resDivW u - resDivW v := by
  simp only [resDivW, map_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

lemma resDivW_const_smul (c : ℂ) (w : Fin 4 → K5) :
    resDivW (fun i => poly4ToK5 (C c) * w i) = poly4ToK5 (C c) * resDivW w := by
  simp only [resDivW, Derivation.leibniz, δ_C, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

def srcX : K5 :=
  ((toK5 (pderiv 3 MA_5) - MA_K * toK5 (pderiv 3 W2_5) / (2 * W2_K)) * Fx_K -
    MA_K * toK5 (pderiv 3 (pderiv 3 F5))) / Fx_K ^ 2

lemma pderiv_3_3_F5 : toK5 (pderiv 3 (pderiv 3 F5)) = 6 * S_K := by
  have hp : pderiv (3 : Fin 5) F5 = 6 * X 0 * X 3 := by
    have hH : pderiv (3 : Fin 5) H0_5 = 0 := pderiv_3_poly4ToPoly5 H0_4
    simp only [F5, map_add, hH, add_zero, Derivation.leibniz, Derivation.leibniz_pow,
      pderiv_ofNat, pderiv_X, smul_eq_mul, nsmul_eq_mul]
    simp; ring
  rw [hp]
  have hp2 : pderiv (3 : Fin 5) (6 * X 0 * X 3 : Poly5) = 6 * X 0 := by
    simp [pderiv_ofNat, pderiv_X]
  rw [hp2]; simp [toK5]

lemma pderiv_4_F5 : toK5 (pderiv 4 F5) = 6 * T_K * y_K := by
  have hH : pderiv (4 : Fin 5) H0_5 = 0 := by
    change pderiv (tanIdx 3) (poly4ToPoly5 H0_4) = 0
    rw [pderiv_poly4ToPoly5]
    have : pderiv (3 : Fin 4) H0_4 = 0 := by
      simp [H0_4, H0_3, poly3ToPoly4, map_ofNat, pderiv_ofNat, pderiv_X]
    rw [this, map_zero]
  have hp : pderiv (4 : Fin 5) F5 = 6 * X 2 * X 4 := by
    simp only [F5, map_add, hH, add_zero, Derivation.leibniz, Derivation.leibniz_pow,
      pderiv_ofNat, pderiv_X, smul_eq_mul, nsmul_eq_mul]
    simp; ring
  rw [hp]; simp [toK5]

theorem radial_normal_chart_identity :
    2 * srcX - resDivW ![0, 0, 0, y_K * MA_K / H0_K] +
      toK5 NA_Q5 / (2 * W2_K * H0_K) = 0 := by
  have hδH0 : δ 3 H0_K = 0 := by
    change δ 3 (poly4ToK5 H0_4) = 0
    rw [δ_poly4]
    have : pderiv (3 : Fin 4) H0_4 = 0 := by
      simp [H0_4, H0_3, poly3ToPoly4, map_ofNat, pderiv_ofNat, pderiv_X]
    rw [this, map_zero]
  have hδFx : δ 3 Fx_K = -(6 * T_K * y_K / x_K) := by
    rw [Fx_K_eq, Derivation.leibniz, Derivation.leibniz, δ_ofNat, δ_S, δ_x]
    simp only [smul_eq_mul, show (3 : Fin 4) ≠ 0 by decide, ↓reduceIte, tanIdx,
      Matrix.cons_val, pderiv_4_F5, Fx_K_eq]
    have hS := S_K_ne_zero; have hx := x_K_ne_zero
    field_simp [hS, hx]; ring
  have hδy : δ 3 y_K = 1 := by simp [δ_y]
  have hδMA : δ 3 MA_K = toK5 (pderiv 4 MA_5) - (T_K * y_K / (S_K * x_K)) * toK5 (pderiv 3 MA_5) := by
    rw [MA_K, δ_toK5]
    simp only [tanIdx, Matrix.cons_val, pderiv_4_F5, Fx_K_eq]
    have hS := S_K_ne_zero; have hx := x_K_ne_zero
    field_simp [hS, hx]
  have hδW2 : δ 3 W2_K = toK5 (pderiv 4 W2_5) - (T_K * y_K / (S_K * x_K)) * toK5 (pderiv 3 W2_5) := by
    rw [W2_K, δ_toK5]
    simp only [tanIdx, Matrix.cons_val, pderiv_4_F5, Fx_K_eq]
    have hS := S_K_ne_zero; have hx := x_K_ne_zero
    field_simp [hS, hx]
  have hNA : toK5 NA_Q5 =
      2 * W2_K * (x_K * toK5 (pderiv 3 MA_5) + y_K * toK5 (pderiv 4 MA_5)) -
        MA_K * (x_K * toK5 (pderiv 3 W2_5) + y_K * toK5 (pderiv 4 W2_5)) := by
    simp [NA_Q5, E_rad, W2_K, MA_K, toK5]
  have hrdiv : resDivW ![0, 0, 0, y_K * MA_K / H0_K] =
      δ 3 (y_K * MA_K / H0_K) - (y_K * MA_K / H0_K) * δ 3 Fx_K / Fx_K -
        (y_K * MA_K / H0_K) * δ 3 W2_K / (2 * W2_K) := by
    simp [resDivW, Fin.sum_univ_four]
  rw [hrdiv, Derivation.leibniz_div, Derivation.leibniz, hδH0, hδy, hδFx, hδMA, hδW2,
    srcX, pderiv_3_3_F5, hNA, Fx_K_eq]
  have hS := S_K_ne_zero; have hx := x_K_ne_zero
  have hH0 := H0_K_ne_zero; have hW2 := W2_K_ne_zero
  have hrel : H0_K = -(3 * S_K * x_K ^ 2 + 3 * T_K * y_K ^ 2) := by
    change poly4ToK5 H0_4 = _; linear_combination x_K_sq_relation
  have hS2 : S_K ^ 2 ≠ 0 := pow_ne_zero 2 hS
  have hx2 : x_K ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hH02 : H0_K ^ 2 ≠ 0 := pow_ne_zero 2 hH0
  have hden : (36 * S_K ^ 2 * x_K ^ 2 * W2_K * H0_K ^ 2 : K5) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hS2) hx2) hW2) hH02
  apply mul_left_cancel₀ hden
  rw [mul_zero]
  simp only [smul_eq_mul, mul_zero, sub_zero, mul_one]
  calc
    _ = (H0_K + 3 * S_K * x_K ^ 2 + 3 * T_K * y_K ^ 2) *
          (12 * S_K * x_K * W2_K * H0_K * toK5 (pderiv 3 MA_5) -
            6 * S_K * x_K * MA_K * H0_K * toK5 (pderiv 3 W2_5) -
            12 * S_K * W2_K * H0_K * MA_K) := by
        field_simp [hS, hx, hH0, hW2]
        ring
    _ = 0 := by rw [hrel]; ring

end Derivations

end SymmetricSexticResidual.K5Field


