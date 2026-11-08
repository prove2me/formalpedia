-- Prove2me | Definitions.Def_FRouting_localTensor
-- name    : FRouting_localTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:00.58743+00:00
-- url     : https://prove2.me/theorems/59aae3ce-7229-4309-9c07-0bcfb8905dbc
-- title:
--   Local channels on two parts of a system, and channel operations in Kraus form
-- statement:
--   For channels $\mathcal N$, $\mathcal M$ with Kraus operators $K_i$, $M_j$ and an operator $X$ on $R\otimes(A\otimes C)$,
--   $$(\mathrm{id}_R\otimes\mathcal N\otimes\mathcal M)(X)=\sum_{i,j} (I\otimes K_i\otimes M_j)\,X\,(I\otimes K_i\otimes M_j)^\dagger ,$$
--   the two local channels of Alice and Bob applied with the reference untouched. The module also gives the channel operations in Kraus form that the circuit model and the proof system need: composition, tensoring with an identity, relabelling, attaching a fresh register in a basis state, and discarding a register. Each is proved to be a channel.
--
--   **Formalization Note** Channels are the published `WildeQIT.QChannel`, a Kraus family with $\sum_i K_i^\dagger K_i=I$. A single channel on the second factor, $(\mathrm{id}_R\otimes\mathcal N)(X)$, is the published `WildeQIT.QMemory.idTensorChannel`.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), §3.4, p.16

import Definitions.Def_WildeQIT_QChannel
import Mathlib

set_option autoImplicit false

open Matrix
open scoped Kronecker

namespace FRouting

open WildeQIT

variable {a b c e r : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype e] [Fintype r]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq e] [DecidableEq r]

/-- **`id_R ⊗ 𝒩 ⊗ ℳ`**: two channels applied to the two parts of the second factor. Renard,
arXiv:2609.40278 (held copy, sha256 4a327f29…), §3.4, p.16, steps 3 and 4 of the protocol. -/
noncomputable def localTensor (N : QChannel a b) (M : QChannel c e)
    (X : Matrix (r × (a × c)) (r × (a × c)) ℂ) : Matrix (r × (b × e)) (r × (b × e)) ℂ :=
  ∑ i, ∑ j, ((1 : Matrix r r ℂ) ⊗ₖ (N.K i ⊗ₖ M.K j)) * X *
    ((1 : Matrix r r ℂ) ⊗ₖ (N.K i ⊗ₖ M.K j))ᴴ

/-- The composition `ℳ ∘ 𝒩` of channels, in Kraus form. -/
noncomputable def chanComp (M : QChannel b c) (N : QChannel a b) : QChannel a c where
  ι := M.ι × N.ι
  K p := M.K p.1 * N.K p.2
  complete := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have h : ∀ j, ∑ i, (M.K i * N.K j)ᴴ * (M.K i * N.K j) = (N.K j)ᴴ * N.K j := by
      intro j
      calc ∑ i, (M.K i * N.K j)ᴴ * (M.K i * N.K j)
          = ∑ i, (N.K j)ᴴ * (((M.K i)ᴴ * M.K i) * N.K j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = (N.K j)ᴴ * ((∑ i, (M.K i)ᴴ * M.K i) * N.K j) := by
            rw [Matrix.sum_mul, Matrix.mul_sum]
        _ = (N.K j)ᴴ * N.K j := by rw [M.complete, Matrix.one_mul]
    simp only [h]
    exact N.complete

private theorem sum_kron_right {ι : Type} [Fintype ι] (A : ι → Matrix a a ℂ) (B : Matrix c c ℂ) :
    ∑ i, (A i ⊗ₖ B) = (∑ i, A i) ⊗ₖ B := by
  ext p q
  simp [Matrix.sum_apply, Finset.sum_mul]

private theorem sum_kron_left {ι : Type} [Fintype ι] (A : ι → Matrix a a ℂ) (B : Matrix c c ℂ) :
    ∑ i, (B ⊗ₖ A i) = B ⊗ₖ (∑ i, A i) := by
  ext p q
  simp [Matrix.sum_apply, Finset.mul_sum]

/-- `𝒩 ⊗ id_c`, in Kraus form. -/
noncomputable def chanTensorRight (N : QChannel a b) (c : Type) [Fintype c] [DecidableEq c] :
    QChannel (a × c) (b × c) where
  ι := N.ι
  K i := N.K i ⊗ₖ (1 : Matrix c c ℂ)
  complete := by
    have h : ∀ i, (N.K i ⊗ₖ (1 : Matrix c c ℂ))ᴴ * (N.K i ⊗ₖ (1 : Matrix c c ℂ))
        = ((N.K i)ᴴ * N.K i) ⊗ₖ (1 : Matrix c c ℂ) := by
      intro i
      rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    simp only [h]
    rw [sum_kron_right, N.complete, one_kronecker_one]

/-- `id_c ⊗ 𝒩`, in Kraus form. -/
noncomputable def chanTensorLeft (c : Type) [Fintype c] [DecidableEq c] (N : QChannel a b) :
    QChannel (c × a) (c × b) where
  ι := N.ι
  K i := (1 : Matrix c c ℂ) ⊗ₖ N.K i
  complete := by
    have h : ∀ i, ((1 : Matrix c c ℂ) ⊗ₖ N.K i)ᴴ * ((1 : Matrix c c ℂ) ⊗ₖ N.K i)
        = (1 : Matrix c c ℂ) ⊗ₖ ((N.K i)ᴴ * N.K i) := by
      intro i
      rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    simp only [h]
    rw [sum_kron_left, N.complete, one_kronecker_one]

/-- A channel read through relabellings `a ≃ c` of its input and `b ≃ e` of its output. -/
noncomputable def chanReindex (f : a ≃ c) (g : b ≃ e) (N : QChannel a b) : QChannel c e where
  ι := N.ι
  K i := (N.K i).submatrix g.symm f.symm
  complete := by
    have h : ∀ i, ((N.K i).submatrix g.symm f.symm)ᴴ * (N.K i).submatrix g.symm f.symm
        = ((N.K i)ᴴ * N.K i).submatrix f.symm f.symm := by
      intro i
      rw [conjTranspose_submatrix, submatrix_mul_equiv]
    simp only [h]
    ext p q
    simp only [Matrix.sum_apply, submatrix_apply]
    have := congrFun (congrFun N.complete (f.symm p)) (f.symm q)
    simp only [Matrix.sum_apply] at this
    rw [this]
    simp [Matrix.one_apply]

/-- `|a⟩ ↦ |a⟩|m₀⟩`: attaching a fresh register in the basis state `m₀`. -/
noncomputable def chanAttach (m : Type) [Fintype m] [DecidableEq m] (m₀ : m) :
    QChannel a (a × m) where
  ι := Unit
  K _ := Matrix.of fun p q => if p.1 = q ∧ p.2 = m₀ then 1 else 0
  complete := by
    ext p q
    simp only [Fintype.univ_unit, Finset.sum_singleton, mul_apply, conjTranspose_apply, of_apply,
      Fintype.sum_prod_type, one_apply]
    by_cases h : p = q
    · subst h
      rw [Finset.sum_eq_single p, Finset.sum_eq_single m₀] <;> simp +contextual
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
      by_cases hx : x = p
      · subst hx
        have : ¬ x = q := h
        simp [this]
      · simp [hx]

/-- The partial trace `tr_m`, in Kraus form. -/
noncomputable def chanDiscard (m : Type) [Fintype m] [DecidableEq m] : QChannel (a × m) a where
  ι := m
  K l := Matrix.of fun p q => if p = q.1 ∧ l = q.2 then 1 else 0
  complete := by
    ext ⟨p, s⟩ ⟨q, t⟩
    simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, of_apply, one_apply, Prod.mk.injEq]
    by_cases h : p = q ∧ s = t
    · obtain ⟨rfl, rfl⟩ := h
      rw [Finset.sum_eq_single s, Finset.sum_eq_single p] <;> simp +contextual
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun x _ => ?_
      by_cases h1 : x = p ∧ l = s
      · by_cases h2 : x = q ∧ l = t
        · exact absurd ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩ h
        · rw [if_neg h2, mul_zero]
      · simp [h1]

end FRouting


