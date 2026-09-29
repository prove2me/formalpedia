-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_SphericalValues
-- name    : LanglandsTunnell_CubicInduction_SphericalValues
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/a9de7c02-2be0-536b-92e1-0ae9998e1c6d
-- title:
--   Spherical values of a cubic Hecke datum on GL(3)
-- statement:
--   Fix complex numbers $e_1,e_2,e_3$, thought of as the elementary symmetric data attached to a cubic induction. The module first packages the recursion already defined by `sphericalTorusValue`: `completeHom e₁ e₂ e₃ n` is by definition that value, so $h_0=1$, $h_1=e_1$, $h_2=e_1^2-e_2$ and $h_{n+3}=e_1h_{n+2}-e_2h_{n+1}+e_3h_n$, restated as `completeHom_add_two` in the shifted form $h_{n+2}=e_1h_{n+1}-e_2h_n+e_3\,h'_n$, where `completeHomPred` is the shift $h'_0=0$, $h'_{n+1}=h_n$. The two-row value `schurTwoRow e₁ e₂ e₃ m₁ m₂` is the $2\times 2$ Jacobi–Trudi expression: it is $h_{m_1}$ when $m_2=0$ and $h_{m_1}h_{m_2}-h_{m_1+1}h_{m_2-1}$ for $m_2\ge 1$, uniformly $h_{m_1}h_{m_2}-h_{m_1+1}h'_{m_2}$ by `schurTwoRow_eq`. The abbreviation `IsDominant a b c` on an integer triple is the conjunction $b\le a$ and $c\le b$. For a further complex parameter $q$, `sphericalValue e₁ e₂ e₃ q a b c` is defined by cases: it equals $e_3^{\,c}\,(q^{-1})^{(a-c)_{\ge 0}}\cdot$ `schurTwoRow` $((a-c)_{\ge 0},(b-c)_{\ge 0})$ on dominant triples, where $(\cdot)_{\ge 0}$ denotes `Int.toNat`, and $0$ otherwise; the power of $e_3$ is an integer power, and $q^{-1}$, $e_3^{\,c}$ obey the field conventions at $0$. Two supporting lemmas record the two branches.
--
--   Under the hypotheses $q\ne 0$ and $e_3\ne 0$, the two Pieri identities are proved at every triple with $b\le a$ and $c\le b$: $q^2V(a+1,b,c)+qV(a,b+1,c)+V(a,b,c+1)=q\,e_1V(a,b,c)$ and $q^2V(a+1,b+1,c)+qV(a+1,b,c+1)+V(a,b+1,c+1)=q\,e_2V(a,b,c)$, where shifted triples outside the dominant cone contribute $0$. Finally, two lemmas evaluate $V$ at the torus points, giving $q^{-n}\,$`sphericalTorusValue`$\,n$ at $(n,0,0)$ and $q^{-k_1}(h_{k_1}h_{k_2+1}-h_{k_1+1}h_{k_2})$ at $(k_1,k_2+1,0)$ for $k_2+1\le k_1$, matching the two clauses of `HasSphericalTorusValuesAt`; numerical instances at $q=2$ and $e_1=e_2=7/2$, $e_3=1$ are also recorded.
--
--   **Relation to Mathlib.** These are the project's own constructions: the complete homogeneous and two-row Schur values are defined directly by the cubic recursion and the Jacobi–Trudi formula as complex-valued functions of $e_1,e_2,e_3$, independently of Mathlib's symmetric-function library.
--
--   **Where it is used.** These spherical values model the Satake-type values of the local Whittaker or spherical function of the automorphic representation of $\mathrm{GL}_3$ obtained by cubic induction, the Pieri identities expressing the two Hecke eigenvalue relations at a finite place encoded by `IsInducedSphericalAt`. They feed the Langlands–Tunnell input to the modularity of the mod $3$ representation in the Frey-curve route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_SphericalValues.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.CubicInduction.SphericalValues

variable (e₁ e₂ e₃ : ℂ)

def completeHom (n : ℕ) : ℂ := sphericalTorusValue e₁ e₂ e₃ n

theorem completeHom_eq (n : ℕ) : completeHom e₁ e₂ e₃ n = sphericalTorusValue e₁ e₂ e₃ n := rfl

theorem completeHom_zero : completeHom e₁ e₂ e₃ 0 = 1 := rfl

theorem completeHom_one : completeHom e₁ e₂ e₃ 1 = e₁ := rfl

theorem completeHom_two : completeHom e₁ e₂ e₃ 2 = e₁ ^ 2 - e₂ := rfl

def completeHomPred : ℕ → ℂ
  | 0 => 0
  | n + 1 => completeHom e₁ e₂ e₃ n

theorem completeHomPred_zero : completeHomPred e₁ e₂ e₃ 0 = 0 := rfl

theorem completeHomPred_one : completeHomPred e₁ e₂ e₃ 1 = 1 := rfl

theorem completeHomPred_succ (n : ℕ) :
    completeHomPred e₁ e₂ e₃ (n + 1) = completeHom e₁ e₂ e₃ n := rfl

theorem completeHom_add_two (n : ℕ) :
    completeHom e₁ e₂ e₃ (n + 2) =
      e₁ * completeHom e₁ e₂ e₃ (n + 1) - e₂ * completeHom e₁ e₂ e₃ n +
        e₃ * completeHomPred e₁ e₂ e₃ n := by
  cases n with
  | zero =>
    show sphericalTorusValue e₁ e₂ e₃ 2 =
      e₁ * sphericalTorusValue e₁ e₂ e₃ 1 - e₂ * sphericalTorusValue e₁ e₂ e₃ 0 + e₃ * 0
    simp only [sphericalTorusValue]
    ring
  | succ k =>
    show sphericalTorusValue e₁ e₂ e₃ (k + 3) =
      e₁ * sphericalTorusValue e₁ e₂ e₃ (k + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (k + 1) +
        e₃ * sphericalTorusValue e₁ e₂ e₃ k
    simp only [sphericalTorusValue]

def schurTwoRow (m₁ : ℕ) : ℕ → ℂ
  | 0 => completeHom e₁ e₂ e₃ m₁
  | k + 1 =>
    completeHom e₁ e₂ e₃ m₁ * completeHom e₁ e₂ e₃ (k + 1) -
      completeHom e₁ e₂ e₃ (m₁ + 1) * completeHom e₁ e₂ e₃ k

theorem schurTwoRow_eq (m₁ m₂ : ℕ) :
    schurTwoRow e₁ e₂ e₃ m₁ m₂ =
      completeHom e₁ e₂ e₃ m₁ * completeHom e₁ e₂ e₃ m₂ -
        completeHom e₁ e₂ e₃ (m₁ + 1) * completeHomPred e₁ e₂ e₃ m₂ := by
  cases m₂ with
  | zero => simp [schurTwoRow, completeHomPred_zero, completeHom_zero]
  | succ k => rfl

abbrev IsDominant (a b c : ℤ) : Prop := b ≤ a ∧ c ≤ b

def sphericalValue (q : ℂ) (a b c : ℤ) : ℂ :=
  if IsDominant a b c then
    e₃ ^ c * q⁻¹ ^ (a - c).toNat * schurTwoRow e₁ e₂ e₃ (a - c).toNat (b - c).toNat
  else 0

theorem sphericalValue_of_isDominant (q : ℂ) (a b c : ℤ) (hd : IsDominant a b c) :
    sphericalValue e₁ e₂ e₃ q a b c =
      e₃ ^ c * q⁻¹ ^ (a - c).toNat * schurTwoRow e₁ e₂ e₃ (a - c).toNat (b - c).toNat := by
  rw [sphericalValue, if_pos hd]

theorem sphericalValue_of_not_isDominant (q : ℂ) (a b c : ℤ) (hd : ¬ IsDominant a b c) :
    sphericalValue e₁ e₂ e₃ q a b c = 0 := by
  rw [sphericalValue, if_neg hd]

section Identities

variable {q : ℂ} (hq : q ≠ 0) (he₃ : e₃ ≠ 0)
include hq he₃

theorem pieri_first {a b c : ℤ} (hba : b ≤ a) (hcb : c ≤ b) :
    q ^ 2 * sphericalValue e₁ e₂ e₃ q (a + 1) b c + q * sphericalValue e₁ e₂ e₃ q a (b + 1) c +
        sphericalValue e₁ e₂ e₃ q a b (c + 1) =
      q * e₁ * sphericalValue e₁ e₂ e₃ q a b c := by
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hcb)
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hba)
  have hz : e₃ ^ (c + 1) = e₃ ^ c * e₃ := zpow_add_one₀ he₃ c
  have hqp : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a + 1) (b) (c) ⟨by omega, by omega⟩]
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b) (c) ⟨by omega, by omega⟩]
  cases m with
  | zero =>
    have hn3 : ¬ IsDominant (a) (b) (c + 1) := fun hd => by
      have h1 := hd.1
      have h2 := hd.2
      omega
    rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a) (b) (c + 1) hn3]
    cases j with
    | zero =>
      have hn2 : ¬ IsDominant (a) (b + 1) (c) := fun hd => by
        have h1 := hd.1
        have h2 := hd.2
        omega
      rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a) (b + 1) (c) hn2]
      have t1 : (a + 1 - c).toNat = 1 := by omega
      have t2 : (b - c).toNat = 0 := by omega
      have t3 : (a - c).toNat = 0 := by omega
      rw [t1, t2, t3]
      simp only [schurTwoRow_eq, completeHomPred_zero, completeHom_zero, completeHom_one]
      field_simp
      ring
    | succ i =>
      rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b + 1) (c) ⟨by omega, by omega⟩]
      have t1 : (a + 1 - c).toNat = i + 1 + 1 := by omega
      have t2 : (b - c).toNat = 0 := by omega
      have t3 : (a - c).toNat = i + 1 := by omega
      have t4 : (b + 1 - c).toNat = 1 := by omega
      rw [t1, t2, t3, t4]
      simp only [schurTwoRow_eq, completeHomPred_zero, completeHomPred_one, completeHom_zero,
        completeHom_one]
      linear_combination
        (e₃ ^ c * q⁻¹ ^ i * completeHom e₁ e₂ e₃ (i + 1 + 1) * q⁻¹ * q) * hqp
  | succ k =>
    rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b) (c + 1) ⟨by omega, by omega⟩]
    cases j with
    | zero =>
      have hn2 : ¬ IsDominant (a) (b + 1) (c) := fun hd => by
        have h1 := hd.1
        have h2 := hd.2
        omega
      rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a) (b + 1) (c) hn2]
      have t1 : (a + 1 - c).toNat = k + 1 + 1 := by omega
      have t2 : (b - c).toNat = k + 1 := by omega
      have t3 : (a - c).toNat = k + 1 := by omega
      have t4 : (a - (c + 1)).toNat = k := by omega
      have t5 : (b - (c + 1)).toNat = k := by omega
      rw [t1, t2, t3, t4, t5, hz]
      simp only [schurTwoRow_eq, completeHomPred_succ]
      have r1 : completeHom e₁ e₂ e₃ (k + 1 + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1 + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k + 1) +
              e₃ * completeHomPred e₁ e₂ e₃ (k + 1) :=
        completeHom_add_two e₁ e₂ e₃ (k + 1)
      have r2 : completeHom e₁ e₂ e₃ (k + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k) +
              e₃ * completeHomPred e₁ e₂ e₃ (k) :=
        completeHom_add_two e₁ e₂ e₃ (k)
      rw [completeHomPred_succ] at r1
      rw [r1, r2]
      linear_combination
        (-(e₃ ^ c * q⁻¹ ^ k *
            (e₁ ^ 2 * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + 1) * q⁻¹ * q
              - e₁ * e₂ * completeHom e₁ e₂ e₃ k ^ 2 * q⁻¹ * q
              + e₁ * e₃ * completeHom e₁ e₂ e₃ k * completeHomPred e₁ e₂ e₃ k * q⁻¹ * q
              - e₁ * completeHom e₁ e₂ e₃ (k + 1) ^ 2 * q⁻¹ * q
              + e₃ * completeHom e₁ e₂ e₃ k ^ 2 * q⁻¹ * q + e₃ * completeHom e₁ e₂ e₃ k ^ 2
              - e₃ * completeHom e₁ e₂ e₃ (k + 1) * completeHomPred e₁ e₂ e₃ k * q⁻¹ * q
              - e₃ * completeHom e₁ e₂ e₃ (k + 1) * completeHomPred e₁ e₂ e₃ k))) * hqp
    | succ i =>
      rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b + 1) (c) ⟨by omega, by omega⟩]
      have t1 : (a + 1 - c).toNat = k + i + 1 + 1 + 1 := by omega
      have t2 : (b - c).toNat = k + 1 := by omega
      have t3 : (a - c).toNat = k + i + 1 + 1 := by omega
      have t4 : (b + 1 - c).toNat = k + 1 + 1 := by omega
      have t5 : (a - (c + 1)).toNat = k + i + 1 := by omega
      have t6 : (b - (c + 1)).toNat = k := by omega
      rw [t1, t2, t3, t4, t5, t6, hz]
      simp only [schurTwoRow_eq, completeHomPred_succ]
      have r1 : completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k + i + 1 + 1) +
              e₃ * completeHomPred e₁ e₂ e₃ (k + i + 1 + 1) :=
        completeHom_add_two e₁ e₂ e₃ (k + i + 1 + 1)
      have r2 : completeHom e₁ e₂ e₃ (k + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k) +
              e₃ * completeHomPred e₁ e₂ e₃ (k) :=
        completeHom_add_two e₁ e₂ e₃ (k)
      rw [completeHomPred_succ] at r1
      rw [r1, r2]
      linear_combination
        (-(e₃ ^ c * q⁻¹ ^ (k + i) * q⁻¹ *
            (e₁ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) * q⁻¹ * q
              - e₂ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1 + 1) * q⁻¹ * q
              + e₃ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1) * q⁻¹ * q
              + e₃ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1)
              - e₃ * completeHom e₁ e₂ e₃ (k + i + 1 + 1) * completeHomPred e₁ e₂ e₃ k
              - completeHom e₁ e₂ e₃ (k + 1) * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) * q⁻¹ * q))) * hqp

theorem pieri_second {a b c : ℤ} (hba : b ≤ a) (hcb : c ≤ b) :
    q ^ 2 * sphericalValue e₁ e₂ e₃ q (a + 1) (b + 1) c + q * sphericalValue e₁ e₂ e₃ q (a + 1) b (c + 1) +
        sphericalValue e₁ e₂ e₃ q a (b + 1) (c + 1) =
      q * e₂ * sphericalValue e₁ e₂ e₃ q a b c := by
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hcb)
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hba)
  have hz : e₃ ^ (c + 1) = e₃ ^ c * e₃ := zpow_add_one₀ he₃ c
  have hqp : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a + 1) (b + 1) (c) ⟨by omega, by omega⟩]
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b) (c) ⟨by omega, by omega⟩]
  cases m with
  | zero =>
    have hn2 : ¬ IsDominant (a + 1) (b) (c + 1) := fun hd => by
      have h1 := hd.1
      have h2 := hd.2
      omega
    rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a + 1) (b) (c + 1) hn2]
    cases j with
    | zero =>
      have hn3 : ¬ IsDominant (a) (b + 1) (c + 1) := fun hd => by
        have h1 := hd.1
        have h2 := hd.2
        omega
      rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a) (b + 1) (c + 1) hn3]
      have t1 : (a + 1 - c).toNat = 1 := by omega
      have t2 : (b + 1 - c).toNat = 1 := by omega
      have t3 : (a - c).toNat = 0 := by omega
      have t4 : (b - c).toNat = 0 := by omega
      have h11 : completeHom e₁ e₂ e₃ (1 + 1) = e₁ ^ 2 - e₂ := completeHom_two e₁ e₂ e₃
      rw [t1, t2, t3, t4]
      simp only [schurTwoRow_eq, completeHomPred_zero, completeHomPred_one, completeHom_zero,
        completeHom_one, h11]
      field_simp
      ring
    | succ i =>
      rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b + 1) (c + 1) ⟨by omega, by omega⟩]
      have t1 : (a + 1 - c).toNat = i + 1 + 1 := by omega
      have t2 : (b + 1 - c).toNat = 1 := by omega
      have t3 : (a - c).toNat = i + 1 := by omega
      have t4 : (b - c).toNat = 0 := by omega
      have t5 : (a - (c + 1)).toNat = i := by omega
      have t6 : (b + 1 - (c + 1)).toNat = 0 := by omega
      rw [t1, t2, t3, t4, t5, t6, hz]
      simp only [schurTwoRow_eq, completeHomPred_zero, completeHomPred_one, completeHom_zero,
        completeHom_one]
      have r1 : completeHom e₁ e₂ e₃ (i + 1 + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (i + 1 + 1) -
            e₂ * completeHom e₁ e₂ e₃ (i + 1) +
              e₃ * completeHomPred e₁ e₂ e₃ (i + 1) :=
        completeHom_add_two e₁ e₂ e₃ (i + 1)
      rw [completeHomPred_succ] at r1
      rw [r1]
      linear_combination
        (e₃ ^ c * q⁻¹ ^ i *
            (e₂ * completeHom e₁ e₂ e₃ (i + 1) * q⁻¹ * q - e₃ * completeHom e₁ e₂ e₃ i * q⁻¹ * q
              - e₃ * completeHom e₁ e₂ e₃ i)) * hqp
  | succ k =>
    rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a + 1) (b) (c + 1) ⟨by omega, by omega⟩]
    cases j with
    | zero =>
      have hn3 : ¬ IsDominant (a) (b + 1) (c + 1) := fun hd => by
        have h1 := hd.1
        have h2 := hd.2
        omega
      rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a) (b + 1) (c + 1) hn3]
      have t1 : (a + 1 - c).toNat = k + 1 + 1 := by omega
      have t2 : (b + 1 - c).toNat = k + 1 + 1 := by omega
      have t3 : (a + 1 - (c + 1)).toNat = k + 1 := by omega
      have t4 : (b - (c + 1)).toNat = k := by omega
      have t5 : (a - c).toNat = k + 1 := by omega
      have t6 : (b - c).toNat = k + 1 := by omega
      rw [t1, t2, t3, t4, t5, t6, hz]
      simp only [schurTwoRow_eq, completeHomPred_succ]
      have r1 : completeHom e₁ e₂ e₃ (k + 1 + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1 + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k + 1) +
              e₃ * completeHomPred e₁ e₂ e₃ (k + 1) :=
        completeHom_add_two e₁ e₂ e₃ (k + 1)
      have r2 : completeHom e₁ e₂ e₃ (k + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k) +
              e₃ * completeHomPred e₁ e₂ e₃ (k) :=
        completeHom_add_two e₁ e₂ e₃ (k)
      rw [completeHomPred_succ] at r1
      rw [r1, r2]
      linear_combination
        (-(e₃ ^ c * q⁻¹ ^ k * q⁻¹ * q *
            (e₁ * e₂ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + 1)
              - e₁ * e₃ * completeHom e₁ e₂ e₃ (k + 1) * completeHomPred e₁ e₂ e₃ k
              - e₂ ^ 2 * completeHom e₁ e₂ e₃ k ^ 2 + 2 * e₂ * e₃ * completeHom e₁ e₂ e₃ k * completeHomPred e₁ e₂ e₃ k
              - e₂ * completeHom e₁ e₂ e₃ (k + 1) ^ 2 - e₃ ^ 2 * completeHomPred e₁ e₂ e₃ k ^ 2
              + e₃ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + 1)))) * hqp
    | succ i =>
      rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b + 1) (c + 1) ⟨by omega, by omega⟩]
      have t1 : (a + 1 - c).toNat = k + i + 1 + 1 + 1 := by omega
      have t2 : (b + 1 - c).toNat = k + 1 + 1 := by omega
      have t3 : (a + 1 - (c + 1)).toNat = k + i + 1 + 1 := by omega
      have t4 : (b - (c + 1)).toNat = k := by omega
      have t5 : (a - (c + 1)).toNat = k + i + 1 := by omega
      have t6 : (b + 1 - (c + 1)).toNat = k + 1 := by omega
      have t7 : (a - c).toNat = k + i + 1 + 1 := by omega
      have t8 : (b - c).toNat = k + 1 := by omega
      rw [t1, t2, t3, t4, t5, t6, t7, t8, hz]
      simp only [schurTwoRow_eq, completeHomPred_succ]
      have r1 : completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k + i + 1 + 1) +
              e₃ * completeHomPred e₁ e₂ e₃ (k + i + 1 + 1) :=
        completeHom_add_two e₁ e₂ e₃ (k + i + 1 + 1)
      have r2 : completeHom e₁ e₂ e₃ (k + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k) +
              e₃ * completeHomPred e₁ e₂ e₃ (k) :=
        completeHom_add_two e₁ e₂ e₃ (k)
      rw [completeHomPred_succ] at r1
      rw [r1, r2]
      linear_combination
        (-(e₃ ^ c * q⁻¹ ^ (k + i) * q⁻¹ *
            (e₂ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) * q⁻¹ * q
              - e₂ * completeHom e₁ e₂ e₃ (k + 1) * completeHom e₁ e₂ e₃ (k + i + 1 + 1) * q⁻¹ * q
              - e₃ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1 + 1)
              + e₃ * completeHom e₁ e₂ e₃ (k + 1) * completeHom e₁ e₂ e₃ (k + i + 1) * q⁻¹ * q
              + e₃ * completeHom e₁ e₂ e₃ (k + 1) * completeHom e₁ e₂ e₃ (k + i + 1)
              - e₃ * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) * completeHomPred e₁ e₂ e₃ k * q⁻¹ * q))) * hqp

end Identities

example {q : ℂ} (hq : q ≠ 0) (he₃ : e₃ ≠ 0) :
    q ^ 2 * sphericalValue e₁ e₂ e₃ q 1 1 0 + q * sphericalValue e₁ e₂ e₃ q 1 0 1 + sphericalValue e₁ e₂ e₃ q 0 1 1 =
      q * e₂ * sphericalValue e₁ e₂ e₃ q 0 0 0 := by
  simpa using pieri_second e₁ e₂ e₃ hq he₃ (le_refl (0 : ℤ)) (le_refl (0 : ℤ))

example {q : ℂ} (hq : q ≠ 0) (he₃ : e₃ ≠ 0) :
    q ^ 2 * sphericalValue e₁ e₂ e₃ q 2 0 0 + q * sphericalValue e₁ e₂ e₃ q 1 1 0 + sphericalValue e₁ e₂ e₃ q 1 0 1 =
      q * e₁ * sphericalValue e₁ e₂ e₃ q 1 0 0 := by
  simpa using pieri_first e₁ e₂ e₃ hq he₃ (zero_le_one' ℤ) (le_refl (0 : ℤ))

section TorusPoints

variable (q : ℂ)

theorem sphericalValue_natCast_zero_zero (n : ℕ) :
    sphericalValue e₁ e₂ e₃ q n 0 0 = q⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n := by
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q n 0 0 ⟨by exact_mod_cast Nat.zero_le n, le_refl 0⟩]
  have h1 : ((n : ℤ) - 0).toNat = n := by omega
  have h2 : ((0 : ℤ) - 0).toNat = 0 := by omega
  rw [h1, h2, zpow_zero, one_mul]
  simp [schurTwoRow, completeHom]

theorem sphericalValue_natCast_succ_zero (k₁ k₂ : ℕ) (h : k₂ + 1 ≤ k₁) :
    sphericalValue e₁ e₂ e₃ q k₁ (k₂ + 1) 0 =
      q⁻¹ ^ k₁ * (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
        sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂) := by
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q k₁ (k₂ + 1) 0 ⟨by exact_mod_cast h, by positivity⟩]
  have h1 : ((k₁ : ℤ) - 0).toNat = k₁ := by omega
  have h2 : ((k₂ : ℤ) + 1 - 0).toNat = k₂ + 1 := by omega
  rw [h1, h2, zpow_zero, one_mul]
  simp [schurTwoRow, completeHom]

end TorusPoints

section Controls

example :
    (2 : ℂ) ^ 2 * sphericalValue (7 / 2) (7 / 2) 1 2 2 0 0 + 2 * sphericalValue (7 / 2) (7 / 2) 1 2 1 1 0 +
        sphericalValue (7 / 2) (7 / 2) 1 2 1 0 1 =
      2 * (7 / 2) * sphericalValue (7 / 2) (7 / 2) 1 2 1 0 0 := by
  rw [sphericalValue_of_isDominant _ _ _ _ 2 0 0 ⟨by norm_num, le_refl 0⟩,
    sphericalValue_of_isDominant _ _ _ _ 1 1 0 ⟨le_refl 1, by norm_num⟩,
    sphericalValue_of_not_isDominant _ _ _ _ 1 0 1 (by rintro ⟨-, h⟩; norm_num at h),
    sphericalValue_of_isDominant _ _ _ _ 1 0 0 ⟨by norm_num, le_refl 0⟩]
  simp only [show ((2 : ℤ) - 0).toNat = 2 by decide, show ((1 : ℤ) - 0).toNat = 1 by decide,
    show ((0 : ℤ) - 0).toNat = 0 by decide]
  norm_num [schurTwoRow, completeHom, completeHomPred, sphericalTorusValue]

example :
    (2 : ℂ) * sphericalValue (7 / 2) (7 / 2) 1 2 2 0 0 + 2 ^ 2 * sphericalValue (7 / 2) (7 / 2) 1 2 1 1 0 +
        sphericalValue (7 / 2) (7 / 2) 1 2 1 0 1 ≠
      2 * (7 / 2) * sphericalValue (7 / 2) (7 / 2) 1 2 1 0 0 := by
  rw [sphericalValue_of_isDominant _ _ _ _ 2 0 0 ⟨by norm_num, le_refl 0⟩,
    sphericalValue_of_isDominant _ _ _ _ 1 1 0 ⟨le_refl 1, by norm_num⟩,
    sphericalValue_of_not_isDominant _ _ _ _ 1 0 1 (by rintro ⟨-, h⟩; norm_num at h),
    sphericalValue_of_isDominant _ _ _ _ 1 0 0 ⟨by norm_num, le_refl 0⟩]
  simp only [show ((2 : ℤ) - 0).toNat = 2 by decide, show ((1 : ℤ) - 0).toNat = 1 by decide,
    show ((0 : ℤ) - 0).toNat = 0 by decide]
  norm_num [schurTwoRow, completeHom, completeHomPred, sphericalTorusValue]

example {q : ℂ} (hq : q ≠ 0) (he₃ : e₃ ≠ 0) :
    q ^ 2 * sphericalValue e₁ e₂ e₃ q 3 1 0 + q * sphericalValue e₁ e₂ e₃ q 3 0 1 +
        sphericalValue e₁ e₂ e₃ q 2 1 1 =
      q * e₂ * sphericalValue e₁ e₂ e₃ q 2 0 0 := by
  simpa using pieri_second e₁ e₂ e₃ hq he₃ (show (0 : ℤ) ≤ 2 by norm_num) (le_refl (0 : ℤ))

end Controls

end LanglandsTunnell.CubicInduction.SphericalValues

end

#print axioms LanglandsTunnell.CubicInduction.SphericalValues.pieri_first
#print axioms LanglandsTunnell.CubicInduction.SphericalValues.pieri_second
#print axioms LanglandsTunnell.CubicInduction.SphericalValues.sphericalValue_natCast_zero_zero
#print axioms LanglandsTunnell.CubicInduction.SphericalValues.sphericalValue_natCast_succ_zero
#check @LanglandsTunnell.CubicInduction.SphericalValues.sphericalValue
#check @LanglandsTunnell.CubicInduction.SphericalValues.schurTwoRow
#check @LanglandsTunnell.CubicInduction.SphericalValues.pieri_first
#check @LanglandsTunnell.CubicInduction.SphericalValues.pieri_second


