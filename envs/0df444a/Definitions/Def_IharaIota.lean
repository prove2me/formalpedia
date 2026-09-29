-- Prove2me | Definitions.Def_IharaIota
-- name    : IharaIota
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/eac11004-4823-59ec-a854-9220cceb41e9
-- title:
--   The two degeneracy homomorphisms Γ0​(Nq)→Γ0​(N)
-- statement:
--   For natural numbers $N,q$ the module constructs two monoid homomorphisms $\Gamma_0(Nq)\to\Gamma_0(N)$, where $\Gamma_0(M)\le \mathrm{SL}_2(\mathbb{Z})$ is Mathlib's congruence subgroup of matrices with lower-left entry $\equiv 0 \bmod M$. The first, [`Ihara.ι₀ N q`](../def/IharaIota.html#L17), is the inclusion: [`Ihara.Gamma0_mul_le`](../def/IharaIota.html#L11) states $\Gamma_0(Nq)\le\Gamma_0(N)$ (from $N\mid Nq$), and [`Ihara.ι₀`](../def/IharaIota.html#L17) is the induced subgroup inclusion, injective by [`Ihara.iota0_injective`](../def/IharaIota.html#L25) and compatible with the coercion to $\mathrm{SL}_2(\mathbb{Z})$ by [`Ihara.coe_iota0`](../def/IharaIota.html#L21).
--
--   The second is conjugation by $w=\mathrm{diag}(1,q)$. At the level of integer matrices, [`Ihara.iota1Mat q`](../def/IharaIota.html#L41) sends $g=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ to $\begin{pmatrix}a& bq\\ c/q& d\end{pmatrix}$, the entry $c/q$ being Lean's integer (Euclidean) division; the four `iota1Mat_apply_…` lemmas record the entries. For $\gamma\in\Gamma_0(Nq)$ one has $Nq\mid c$ ([`Ihara.dvd_entry`](../def/IharaIota.html#L32)) and hence $q\mid c$ ([`Ihara.q_dvd_entry`](../def/IharaIota.html#L38)), so the division is exact; under the hypothesis $q\mid g_{10}$ the assignment preserves determinants ([`Ihara.det_iota1Mat`](../def/IharaIota.html#L66)), is multiplicative ([`Ihara.iota1Mat_mul`](../def/IharaIota.html#L71)), fixes the identity ([`Ihara.iota1Mat_one`](../def/IharaIota.html#L62)), and satisfies the denominator-free identity $w\cdot \iota_1 g = g\cdot w$ ([`Ihara.w_mul_iota1Mat`](../def/IharaIota.html#L56), restated for $\Gamma_0$-elements as [`Ihara.w_mul_iota1`](../def/IharaIota.html#L127)). These give [`Ihara.iota1SL`](../def/IharaIota.html#L91), the resulting element of $\mathrm{SL}_2(\mathbb{Z})$, its membership in $\Gamma_0(N)$ ([`Ihara.iota1SL_mem`](../def/IharaIota.html#L101), from $Nq\mid c$), and the homomorphism [`Ihara.ι₁ N q : Gamma0 (N*q) →* Gamma0 N`](../def/IharaIota.html#L111), with coercion lemmas [`Ihara.coe_iota1SL`](../def/IharaIota.html#L97), [`Ihara.coe_iota1`](../def/IharaIota.html#L119), [`Ihara.coe_coe_iota1`](../def/IharaIota.html#L123).
--
--   Both maps are defined for all $N,q\in\mathbb{N}$, with no primality or nonvanishing hypothesis. Injectivity of $\iota_1$ is proved under $q\neq 0$ ([`Ihara.iota1_injective`](../def/IharaIota.html#L132)), and for $q\neq 0$ the image is described exactly: $\delta\in\Gamma_0(N)$ lies in the range of $\iota_1$ iff $q$ divides its upper-right entry ([`Ihara.mem_range_iota1_iff`](../def/IharaIota.html#L150)), i.e. the range is $\Gamma_0(N)\cap\Gamma^0(q)$.
--
--   **Relation to Mathlib.** The group $\Gamma_0(M)$ is Mathlib's `Gamma0` from the congruence-subgroup file; the monotonicity $\Gamma_0(Nq)\le\Gamma_0(N)$ and the two homomorphisms $\iota_0,\iota_1$ are the project's own.
--
--   **Where it is used.** These are the two degeneracy maps along which the pair of copies of $\Gamma_0(N)$ is compared over $\Gamma_0(Nq)$ in the formulation of Ihara's lemma, the congruence-subgroup input to level raising in the Frey–Serre–Ribet–Wiles–Taylor–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_IharaIota.lean

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace Ihara

open Matrix CongruenceSubgroup

open scoped MatrixGroups

section Inclusion

theorem Gamma0_mul_le (N q : ℕ) : Gamma0 (N * q) ≤ Gamma0 N := by
  intro γ hγ
  rw [Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod (N * q)) (N * q)] at hγ
  rw [Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod N) N]
  exact dvd_trans (Int.natCast_dvd_natCast.mpr (dvd_mul_right N q)) hγ

def ι₀ (N q : ℕ) : Gamma0 (N * q) →* Gamma0 N :=
  Subgroup.inclusion (Gamma0_mul_le N q)

@[simp]
theorem coe_iota0 (N q : ℕ) (γ : Gamma0 (N * q)) :
    ((ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) = (γ : SL(2, ℤ)) :=
  rfl

theorem iota0_injective (N q : ℕ) : Function.Injective (ι₀ N q) :=
  Subgroup.inclusion_injective _

end Inclusion

section Conjugation

theorem dvd_entry (N q : ℕ) (γ : Gamma0 (N * q)) :
    ((N * q : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
  have h := γ.2
  rw [Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod (N * q)) (N * q)] at h
  exact h

theorem q_dvd_entry (N q : ℕ) (γ : Gamma0 (N * q)) : (q : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
  dvd_trans (Int.natCast_dvd_natCast.mpr (dvd_mul_left q N)) (dvd_entry N q γ)

def iota1Mat (q : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![g 0 0, g 0 1 * (q : ℤ); g 1 0 / (q : ℤ), g 1 1]

@[simp] theorem iota1Mat_apply_zero_zero (q : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    iota1Mat q g 0 0 = g 0 0 := rfl

@[simp] theorem iota1Mat_apply_zero_one (q : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    iota1Mat q g 0 1 = g 0 1 * (q : ℤ) := rfl

@[simp] theorem iota1Mat_apply_one_zero (q : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    iota1Mat q g 1 0 = g 1 0 / (q : ℤ) := rfl

@[simp] theorem iota1Mat_apply_one_one (q : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    iota1Mat q g 1 1 = g 1 1 := rfl

theorem w_mul_iota1Mat {q : ℕ} {g : Matrix (Fin 2) (Fin 2) ℤ} (hg : (q : ℤ) ∣ g 1 0) :
    !![(1 : ℤ), 0; 0, (q : ℤ)] * iota1Mat q g = g * !![(1 : ℤ), 0; 0, (q : ℤ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iota1Mat, Matrix.mul_apply, Fin.sum_univ_two, Int.mul_ediv_cancel' hg, mul_comm]

theorem iota1Mat_one (q : ℕ) : iota1Mat q (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [iota1Mat]

theorem det_iota1Mat {q : ℕ} {g : Matrix (Fin 2) (Fin 2) ℤ} (hg : (q : ℤ) ∣ g 1 0) :
    (iota1Mat q g).det = g.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, iota1Mat_apply_zero_zero, iota1Mat_apply_zero_one,
    iota1Mat_apply_one_zero, iota1Mat_apply_one_one, mul_assoc, Int.mul_ediv_cancel' hg]

theorem iota1Mat_mul {q : ℕ} {g h : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (q : ℤ) ∣ g 1 0) (hh : (q : ℤ) ∣ h 1 0) :
    iota1Mat q (g * h) = iota1Mat q g * iota1Mat q h := by
  obtain ⟨k, hk⟩ := hg
  obtain ⟨k', hk'⟩ := hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [iota1Mat, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, hk, hk'] <;>
    by_cases hq : (q : ℤ) = 0
  · simp [hq]
  · rw [Int.mul_ediv_cancel_left _ hq]; ring
  · simp [hq]
  · ring
  · simp [hq]
  · rw [show (q : ℤ) * k * h 0 0 + g 1 1 * ((q : ℤ) * k') = (q : ℤ) * (k * h 0 0 + g 1 1 * k') by ring,
      Int.mul_ediv_cancel_left _ hq, Int.mul_ediv_cancel_left _ hq, Int.mul_ediv_cancel_left _ hq]
  · simp [hq]
  · rw [Int.mul_ediv_cancel_left _ hq]; ring

def iota1SL (N q : ℕ) (γ : Gamma0 (N * q)) : SL(2, ℤ) :=
  ⟨iota1Mat q (γ : SL(2, ℤ)), by
    rw [det_iota1Mat (q_dvd_entry N q γ)]
    exact (γ : SL(2, ℤ)).det_coe⟩

@[simp]
theorem coe_iota1SL (N q : ℕ) (γ : Gamma0 (N * q)) :
    (iota1SL N q γ : Matrix (Fin 2) (Fin 2) ℤ) = iota1Mat q (γ : SL(2, ℤ)) :=
  rfl

theorem iota1SL_mem (N q : ℕ) (γ : Gamma0 (N * q)) : iota1SL N q γ ∈ Gamma0 N := by
  rw [Gamma0_mem, coe_iota1SL, iota1Mat_apply_one_zero, CharP.intCast_eq_zero_iff (ZMod N) N]
  obtain ⟨k, hk⟩ := dvd_entry N q γ
  rw [hk]
  by_cases hq : (q : ℤ) = 0
  · simp [hq]
  · rw [show ((N * q : ℕ) : ℤ) * k = (q : ℤ) * ((N : ℤ) * k) by push_cast; ring,
      Int.mul_ediv_cancel_left _ hq]
    exact dvd_mul_right (N : ℤ) k

def ι₁ (N q : ℕ) : Gamma0 (N * q) →* Gamma0 N where
  toFun γ := ⟨iota1SL N q γ, iota1SL_mem N q γ⟩
  map_one' := Subtype.ext <| Subtype.ext <| by
    simpa using iota1Mat_one q
  map_mul' γ δ := Subtype.ext <| Subtype.ext <| by
    simpa using iota1Mat_mul (q_dvd_entry N q γ) (q_dvd_entry N q δ)

@[simp]
theorem coe_iota1 (N q : ℕ) (γ : Gamma0 (N * q)) :
    ((ι₁ N q γ : Gamma0 N) : SL(2, ℤ)) = iota1SL N q γ :=
  rfl

theorem coe_coe_iota1 (N q : ℕ) (γ : Gamma0 (N * q)) :
    (((ι₁ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = iota1Mat q (γ : SL(2, ℤ)) :=
  rfl

theorem w_mul_iota1 (N q : ℕ) (γ : Gamma0 (N * q)) :
    !![(1 : ℤ), 0; 0, (q : ℤ)] * (((ι₁ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * !![(1 : ℤ), 0; 0, (q : ℤ)] :=
  w_mul_iota1Mat (q_dvd_entry N q γ)

theorem iota1_injective (N : ℕ) {q : ℕ} (hq : q ≠ 0) : Function.Injective (ι₁ N q) := by
  intro γ δ h
  have hq' : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq
  have hmat : iota1Mat q (γ : SL(2, ℤ)) = iota1Mat q (δ : SL(2, ℤ)) :=
    congrArg (fun x : Gamma0 N => ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) h
  refine Subtype.ext (Subtype.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using congrFun (congrFun hmat 0) 0
  · simpa [hq] using congrFun (congrFun hmat 0) 1
  · have h10 := congrFun (congrFun hmat 1) 0
    simp only [iota1Mat_apply_one_zero, Fin.isValue] at h10
    have := congrArg (fun x : ℤ => (q : ℤ) * x) h10
    simp only [Int.mul_ediv_cancel' (q_dvd_entry N q γ), Int.mul_ediv_cancel' (q_dvd_entry N q δ)]
      at this
    exact this
  · simpa using congrFun (congrFun hmat 1) 1

theorem mem_range_iota1_iff (N : ℕ) {q : ℕ} (hq : q ≠ 0) (δ : Gamma0 N) :
    δ ∈ (ι₁ N q).range ↔ (q : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 := by
  have hq' : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨(γ : SL(2, ℤ)) 0 1, by simp [mul_comm]⟩
  · rintro ⟨b, hb⟩

    have hN : ((N : ℕ) : ℤ) ∣ (δ : SL(2, ℤ)) 1 0 := by
      have h := δ.2
      rw [Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod N) N] at h
      exact h
    let M : Matrix (Fin 2) (Fin 2) ℤ :=
      !![(δ : SL(2, ℤ)) 0 0, b; (δ : SL(2, ℤ)) 1 0 * (q : ℤ), (δ : SL(2, ℤ)) 1 1]
    have hdet : M.det = 1 := by
      have h1 := (δ : SL(2, ℤ)).det_coe
      rw [Matrix.det_fin_two] at h1 ⊢
      simp only [M, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
        Fin.isValue]
      rw [hb] at h1
      linear_combination h1
    have hmem : (⟨M, hdet⟩ : SL(2, ℤ)) ∈ Gamma0 (N * q) := by
      show (((⟨M, hdet⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod (N * q)) = 0
      rw [CharP.intCast_eq_zero_iff (ZMod (N * q)) (N * q)]
      show ((N * q : ℕ) : ℤ) ∣ (δ : SL(2, ℤ)) 1 0 * (q : ℤ)
      push_cast
      exact mul_dvd_mul hN dvd_rfl
    refine ⟨⟨⟨M, hdet⟩, hmem⟩, Subtype.ext (Subtype.ext ?_)⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [iota1Mat, M]
    · simp [iota1Mat, M, hb, mul_comm]
    · show (δ : SL(2, ℤ)) 1 0 * (q : ℤ) / (q : ℤ) = (δ : SL(2, ℤ)) 1 0
      exact Int.mul_ediv_cancel _ hq'
    · simp [iota1Mat, M]

end Conjugation

end Ihara


