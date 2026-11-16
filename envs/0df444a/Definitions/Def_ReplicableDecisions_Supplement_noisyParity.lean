-- Prove2me | Definitions.Def_ReplicableDecisions_Supplement_noisyParity
-- name    : ReplicableDecisions_Supplement_noisyParity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:02:20.162214+00:00
-- url     : https://prove2.me/theorems/e31105c3-cab8-4107-93cf-ac2b731d47f6
-- title:
--   Noisy-parity experiment on $\mathbb F_2^b$: $P_*$ uniform and $P_u=2^{-b}(1+2\varepsilon\chi_u)$
-- statement:
--   For $u,x\in\mathbb F_2^b$ write $\chi_u(x)=(-1)^{u\cdot x}$. For $0<\varepsilon\le1/2$, the **noisy-parity experiment** on $\mathbb F_2^b$ has $M=2^b$ models: the uniform law $P_*$, forced to answer $0$, and the $2^b-1$ laws
--   $$P_u(x)=2^{-b}\big(1+2\varepsilon\chi_u(x)\big),\qquad u\ne0,$$
--   forced to answer $1$. These are distinct probability vectors.
--
--   It is the experiment of Theorems 6.2 and 6.3, where the logarithmic factor of Theorem 3.1 is necessary at every scale.
--
--   **Formalization Note** $\mathbb F_2^b$ is `Fin b → ZMod 2`; models are indexed by $u$, and the index $u=0$ is $P_*$ (not the displayed formula). Nonnegativity and distinctness are proved from $0<\varepsilon\le1/2$.
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 6.2, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_ReplicableDecisions_Experiment

namespace ReplicableDecisions.Supplement

/-- **The inner product** `u · x = ∑ᵢ uᵢ xᵢ` on `F₂^b`. Chen, *Replicable Decisions in Finite
Experiments*, STOC 2027 submission (sha256 52d181db…), §6, p.27 (PDF p.29).

**Formalization Note.** `F₂^b` is `Fin b → ZMod 2`. -/
def dotF2 {b : ℕ} (u x : Fin b → ZMod 2) : ZMod 2 := ∑ i, u i * x i

/-- **The character** `χ_u(x) = (−1)^{u·x}`. Chen, STOC 2027 submission (sha256 52d181db…), p.27
(PDF p.29): "For u ∈ F₂^b write χ_u(x) = (−1)^{u·x}." -/
noncomputable def chi {b : ℕ} (u x : Fin b → ZMod 2) : ℝ := if dotF2 u x = 0 then 1 else -1

theorem chi_sq {b : ℕ} (u x : Fin b → ZMod 2) : chi u x = 1 ∨ chi u x = -1 := by
  unfold chi; split_ifs <;> simp

theorem zmod2_eq_one_of_ne {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a h; decide

theorem chi_add_single {b : ℕ} (u x : Fin b → ZMod 2) (i : Fin b) (hu : u i = 1) :
    chi u (x + Pi.single i 1) = -chi u x := by
  have hd : dotF2 u (x + Pi.single i 1) = dotF2 u x + 1 := by
    simp only [dotF2, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp [hu]
    · intro j _ hj; simp [hj]
    · simp
  unfold chi
  rw [hd]
  generalize dotF2 u x = a
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases (show a = 0 ∨ a = 1 by revert a; decide) with rfl | rfl
  · simp
  · simp [h11]

theorem sum_chi_eq_zero {b : ℕ} {u : Fin b → ZMod 2} (hu : u ≠ 0) : ∑ x, chi u x = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  have hi1 : u i = 1 := zmod2_eq_one_of_ne hi
  have h := Equiv.sum_comp (Equiv.addRight (Pi.single i (1 : ZMod 2) : Fin b → ZMod 2))
    (fun x => chi u x)
  simp only [Equiv.coe_addRight] at h
  rw [Finset.sum_congr rfl (fun x _ => chi_add_single u x i hi1), Finset.sum_neg_distrib] at h
  linarith

theorem dotF2_single {b : ℕ} (u : Fin b → ZMod 2) (i : Fin b) :
    dotF2 u (Pi.single i 1) = u i := by
  unfold dotF2
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- **The noisy-parity laws.** Chen, STOC 2027 submission (sha256 52d181db…), Theorem 6.2, p.27
(PDF p.29): "the uniform distribution P∗ … and the 2^b − 1 distributions
P_u(x) = 2^{−b}(1 + 2εχ_u(x)), u ≠ 0".

**Formalization Note.** Models are indexed by `u ∈ F₂^b`; the index `u = 0` is `P∗`, the uniform
law, and is not given by the displayed formula. -/
noncomputable def parityLaw (b : ℕ) (ε : ℝ) (u x : Fin b → ZMod 2) : ℝ :=
  if u = 0 then 1 / 2 ^ b else 1 / 2 ^ b * (1 + 2 * ε * chi u x)

theorem card_F2 (b : ℕ) : (Fintype.card (Fin b → ZMod 2) : ℝ) = 2 ^ b := by
  simp [ZMod.card]

theorem parityLaw_mem_simplex {b : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2)
    (u : Fin b → ZMod 2) : parityLaw b ε u ∈ stdSimplex ℝ (Fin b → ZMod 2) := by
  have h2 : (0 : ℝ) < 2 ^ b := by positivity
  refine ⟨fun x => ?_, ?_⟩
  · unfold parityLaw
    split_ifs
    · positivity
    · rcases chi_sq u x with h | h <;> rw [h] <;>
        apply mul_nonneg (by positivity) <;> linarith
  · unfold parityLaw
    split_ifs with hu
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_F2]; field_simp
    · rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, sum_chi_eq_zero hu]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_F2]
      field_simp; ring

theorem parityLaw_injective {b : ℕ} {ε : ℝ} (hε₀ : 0 < ε) :
    Function.Injective (parityLaw b ε) := by
  have h2 : (0 : ℝ) < 2 ^ b := by positivity
  have hchi0 : ∀ v : Fin b → ZMod 2, chi v 0 = 1 := by
    intro v; simp [chi, dotF2]
  intro u v h
  by_contra huv
  have h0 := congrFun h 0
  by_cases hu : u = 0
  · have hv : v ≠ 0 := fun hv => huv (hu.trans hv.symm)
    simp only [parityLaw, hu, hv, if_true, if_false, hchi0] at h0
    field_simp at h0
    linarith
  · by_cases hv : v = 0
    · simp only [parityLaw, hu, hv, if_true, if_false, hchi0] at h0
      field_simp at h0
      linarith
    · have hc : ∀ x, chi u x = chi v x := by
        intro x
        have hx := congrFun h x
        simp only [parityLaw, hu, hv, if_false] at hx
        field_simp at hx
        have : 2 * ε * chi u x = 2 * ε * chi v x := by linarith
        exact mul_left_cancel₀ (by positivity) this
      apply huv
      funext i
      have hi := hc (Pi.single i 1)
      simp only [chi, dotF2_single] at hi
      have key : ∀ a c : ZMod 2,
          ((if a = 0 then (1 : ℝ) else -1) = if c = 0 then 1 else -1) → a = c := by
        intro a c hac
        by_cases ha : a = 0 <;> by_cases hc' : c = 0
        · rw [ha, hc']
        · simp [ha, hc'] at hac; norm_num at hac
        · simp [ha, hc'] at hac; norm_num at hac
        · rw [zmod2_eq_one_of_ne ha, zmod2_eq_one_of_ne hc']
      exact key _ _ hi

/-- **The noisy-parity experiment** on `F₂^b` of Theorems 6.2 and 6.3. Chen, STOC 2027 submission
(sha256 52d181db…), Theorem 6.2, p.27 (PDF p.29). `M = 2^b` models.

**Formalization Note.** The hypotheses `0 < ε ≤ 1/2` are those of Theorem 6.2 and make the laws
nonnegative and distinct (both are proved here). -/
noncomputable def noisyParity (b : ℕ) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2) :
    Experiment (Fin b → ZMod 2) (Fin b → ZMod 2) where
  P := parityLaw b ε
  mem_simplex := parityLaw_mem_simplex hε₀ hε
  distinct := parityLaw_injective hε₀

/-- **The acceptable sets of the noisy-parity experiment:** `P∗` (index `0`) is forced to answer
`0`, every `P_u` with `u ≠ 0` is forced to answer `1`. Chen, STOC 2027 submission
(sha256 52d181db…), Theorem 6.2, p.27 (PDF p.29). `0 = false`, `1 = true`. -/
def parityΓ {b : ℕ} (u : Fin b → ZMod 2) : Set Bool := if u = 0 then {false} else {true}

end ReplicableDecisions.Supplement


