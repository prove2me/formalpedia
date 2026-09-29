-- Prove2me | Definitions.Def_NumberTheory_DivisorConvolution
-- name    : NumberTheory_DivisorConvolution
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/b9902e9e-9866-5198-b2dd-263df4bd6ef1
-- title:
--   Divisor power sums, their convolutions, and two classical identities
-- statement:
--   For natural numbers $k$ and $n$, `sigma k n` is $\sum_{d \mid n} d^k$, the sum taken over `Nat.divisors n`, so that it vanishes at $n = 0$ and equals $1$ at $n = 1$. For $k, l, N$, `sigmaConv k l N` is the additive convolution $\sum_{i=1}^{N-1} \sigma_k(i)\,\sigma_l(N-i)$, the index $i$ running over `Finset.Ico 1 N`; it vanishes for $N = 0$ and $N = 1$. Two propositions on a natural number $N$ are then named: `BesgeIdentity N` asserts the equality of naturals $12\,\sigma_1{*}\sigma_1(N) + 6N\sigma_1(N) = 5\sigma_3(N) + \sigma_1(N)$, and `Weight6Identity N` asserts $240\,\sigma_1{*}\sigma_3(N) + 30N\sigma_3(N) + \sigma_1(N) = 21\sigma_5(N) + 10\sigma_3(N)$. Each is shown equivalent to its rearrangement over $\mathbb{Z}$ ($12\,\sigma_1{*}\sigma_1(N) = 5\sigma_3(N) + (1-6N)\sigma_1(N)$, respectively $240\,\sigma_1{*}\sigma_3(N) = 21\sigma_5(N) + (10-30N)\sigma_3(N) - \sigma_1(N)$), verified by decision for $N \le 6$, and finally proved for every $N$ in the namespaces `BesgeCertificate` and `Weight6Certificate`.
--
--   The elementary apparatus for those proofs is also set up here. `Sols N` is the finite set of quadruples $(a,b,c,d)$ of positive naturals with $ab + cd = N$, cut out of a product of intervals by a filter, with `mem_Sols` giving exactly that description of membership. `euclidStep` sends $(a,b,c,d)$ to $(a-c,\,b,\,c,\,b+d)$ and `euclidStepInv` sends $(a,b,c,d)$ to $(a+c,\,b,\,c,\,d-b)$; these are mutually inverse bijections between the part of `Sols N` where $c < a$ and the part where $b < d$, whence a reindexing principle `sum_euclidStep` for sums of an arbitrary function into an additive commutative monoid. Two involutions of `Sols N`, `swap₁` $(a,b,c,d) \mapsto (c,d,a,b)$ and `swap₂` $(a,b,c,d) \mapsto (b,a,d,c)$, supply further reindexings; `sum_split` splits a sum over `Sols N` along the trichotomy $g < h$, $h = g$, $h < g$ for two natural-valued functions. The remaining lemmas evaluate the diagonal slices $a = c$ in terms of $\sigma_1, \dots, \sigma_5$ using the divisor antidiagonal and closed forms for $\sum_{b<M} b$, $b^2$, $b^3$, $b^4$, $b(M-b)$, $b(M-b)^3$, $b^2(M-b)^2$, identify $\sum_{\mathrm{Sols}(N)} a c$ with $\sigma_1{*}\sigma_1(N)$ and $\sum_{\mathrm{Sols}(N)} a c^3$ with $\sigma_1{*}\sigma_3(N)$, and combine these linearly.
--
--   **Relation to Mathlib.** Mathlib's divisor-sum function is `Nat.sigma`/`ArithmeticFunction.sigma`; [`FLT.DivisorConvolution.sigma`](../def/NumberTheory_DivisorConvolution.html#L10) is this module's own plain definition $\sum_{d \mid n} d^k$ as a natural number, and the convolution `sigmaConv` and the identities have no Mathlib counterparts.
--
--   **Where it is used.** The two convolution identities are the arithmetic input to the Weierstrass-coefficient computation for the Tate curve, feeding the comparison of defect coefficients with sums over lines in the modules that import this one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberTheory_DivisorConvolution.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Finset

namespace FLT
namespace DivisorConvolution

def sigma (k n : ℕ) : ℕ := ∑ d ∈ n.divisors, d ^ k

@[simp] theorem sigma_zero_right (k : ℕ) : sigma k 0 = 0 := by simp [sigma]

@[simp] theorem sigma_one_right (k : ℕ) : sigma k 1 = 1 := by simp [sigma]

def sigmaConv (k l N : ℕ) : ℕ := ∑ i ∈ Finset.Ico 1 N, sigma k i * sigma l (N - i)

@[simp] theorem sigmaConv_zero (k l : ℕ) : sigmaConv k l 0 = 0 := by simp [sigmaConv]

@[simp] theorem sigmaConv_one (k l : ℕ) : sigmaConv k l 1 = 0 := by simp [sigmaConv]

def BesgeIdentity (N : ℕ) : Prop :=
  12 * sigmaConv 1 1 N + 6 * N * sigma 1 N = 5 * sigma 3 N + sigma 1 N

def Weight6Identity (N : ℕ) : Prop :=
  240 * sigmaConv 1 3 N + 30 * N * sigma 3 N + sigma 1 N = 21 * sigma 5 N + 10 * sigma 3 N

theorem besgeIdentity_iff_int (N : ℕ) :
    BesgeIdentity N ↔
      (12 * sigmaConv 1 1 N : ℤ) = 5 * sigma 3 N + (1 - 6 * N) * sigma 1 N := by
  unfold BesgeIdentity
  constructor
  · intro h
    have h' : ((12 * sigmaConv 1 1 N + 6 * N * sigma 1 N : ℕ) : ℤ) =
        ((5 * sigma 3 N + sigma 1 N : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    linear_combination h'
  · intro h
    have h' : ((12 * sigmaConv 1 1 N + 6 * N * sigma 1 N : ℕ) : ℤ) =
        ((5 * sigma 3 N + sigma 1 N : ℕ) : ℤ) := by
      push_cast
      linear_combination h
    exact_mod_cast h'

theorem weight6Identity_iff_int (N : ℕ) :
    Weight6Identity N ↔
      (240 * sigmaConv 1 3 N : ℤ) =
        21 * sigma 5 N + (10 - 30 * N) * sigma 3 N - sigma 1 N := by
  unfold Weight6Identity
  constructor
  · intro h
    have h' : ((240 * sigmaConv 1 3 N + 30 * N * sigma 3 N + sigma 1 N : ℕ) : ℤ) =
        ((21 * sigma 5 N + 10 * sigma 3 N : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    linear_combination h'
  · intro h
    have h' : ((240 * sigmaConv 1 3 N + 30 * N * sigma 3 N + sigma 1 N : ℕ) : ℤ) =
        ((21 * sigma 5 N + 10 * sigma 3 N : ℕ) : ℤ) := by
      push_cast
      linear_combination h
    exact_mod_cast h'

theorem besgeIdentity_of_le_six {N : ℕ} (hN : N ≤ 6) : BesgeIdentity N := by
  unfold BesgeIdentity
  interval_cases N <;> decide

theorem weight6Identity_of_le_six {N : ℕ} (hN : N ≤ 6) : Weight6Identity N := by
  unfold Weight6Identity
  interval_cases N <;> decide

def Sols (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    (fun x => x.1 * x.2.1 + x.2.2.1 * x.2.2.2 = N)

theorem mem_Sols {N : ℕ} {x : ℕ × ℕ × ℕ × ℕ} :
    x ∈ Sols N ↔
      0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2 ∧
        x.1 * x.2.1 + x.2.2.1 * x.2.2.2 = N := by
  constructor
  · intro h
    have heq := (Finset.mem_filter.1 h).2
    have hmem := (Finset.mem_filter.1 h).1
    have h1 := Finset.mem_product.1 hmem
    have h2 := Finset.mem_product.1 h1.2
    have h3 := Finset.mem_product.1 h2.2
    exact ⟨(Finset.mem_Icc.1 h1.1).1, (Finset.mem_Icc.1 h2.1).1,
      (Finset.mem_Icc.1 h3.1).1, (Finset.mem_Icc.1 h3.2).1, heq⟩
  · rintro ⟨ha, hb, hc, hd, heq⟩
    have hab_pos : 0 < x.1 * x.2.1 := Nat.mul_pos ha hb
    have hcd_pos : 0 < x.2.2.1 * x.2.2.2 := Nat.mul_pos hc hd
    have hab_le : x.1 * x.2.1 ≤ N := by omega
    have hcd_le : x.2.2.1 * x.2.2.2 ≤ N := by omega
    have haN : x.1 ≤ N := le_trans (le_mul_of_one_le_right (Nat.zero_le _) hb) hab_le
    have hbN : x.2.1 ≤ N := le_trans (le_mul_of_one_le_left (Nat.zero_le _) ha) hab_le
    have hcN : x.2.2.1 ≤ N := le_trans (le_mul_of_one_le_right (Nat.zero_le _) hd) hcd_le
    have hdN : x.2.2.2 ≤ N := le_trans (le_mul_of_one_le_left (Nat.zero_le _) hc) hcd_le
    refine Finset.mem_filter.2 ⟨?_, heq⟩
    refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨ha, haN⟩, ?_⟩
    refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hb, hbN⟩, ?_⟩
    exact Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hc, hcN⟩, Finset.mem_Icc.2 ⟨hd, hdN⟩⟩

def euclidStep (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (x.1 - x.2.2.1, x.2.1, x.2.2.1, x.2.1 + x.2.2.2)

def euclidStepInv (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (x.1 + x.2.2.1, x.2.1, x.2.2.1, x.2.2.2 - x.2.1)

theorem euclidStep_mem {N : ℕ} {x : ℕ × ℕ × ℕ × ℕ}
    (hx : x ∈ (Sols N).filter fun x => x.2.2.1 < x.1) :
    euclidStep x ∈ (Sols N).filter fun x => x.2.1 < x.2.2.2 := by
  obtain ⟨hxS, hlt⟩ := Finset.mem_filter.1 hx
  obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hxS
  replace hlt : x.2.2.1 < x.1 := hlt
  have hsub : (x.1 - x.2.2.1) * x.2.1 = x.1 * x.2.1 - x.2.2.1 * x.2.1 :=
    Nat.sub_mul x.1 x.2.2.1 x.2.1
  have hcb_le : x.2.2.1 * x.2.1 ≤ x.1 * x.2.1 := mul_le_mul_left (le_of_lt hlt) _
  have hadd : x.2.2.1 * (x.2.1 + x.2.2.2) = x.2.2.1 * x.2.1 + x.2.2.1 * x.2.2.2 :=
    Nat.mul_add _ _ _
  refine Finset.mem_filter.2 ⟨mem_Sols.2 ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show 0 < x.1 - x.2.2.1
    omega
  · show 0 < x.2.1
    exact hb
  · show 0 < x.2.2.1
    exact hc
  · show 0 < x.2.1 + x.2.2.2
    omega
  · show (x.1 - x.2.2.1) * x.2.1 + x.2.2.1 * (x.2.1 + x.2.2.2) = N
    omega
  · show x.2.1 < x.2.1 + x.2.2.2
    omega

theorem euclidStepInv_mem {N : ℕ} {y : ℕ × ℕ × ℕ × ℕ}
    (hy : y ∈ (Sols N).filter fun x => x.2.1 < x.2.2.2) :
    euclidStepInv y ∈ ((Sols N).filter fun x => x.2.2.1 < x.1) ∧
      euclidStep (euclidStepInv y) = y := by
  obtain ⟨hyS, hlt⟩ := Finset.mem_filter.1 hy
  obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hyS
  replace hlt : y.2.1 < y.2.2.2 := hlt
  have hadd : (y.1 + y.2.2.1) * y.2.1 = y.1 * y.2.1 + y.2.2.1 * y.2.1 := Nat.add_mul _ _ _
  have hsub : y.2.2.1 * (y.2.2.2 - y.2.1) + y.2.2.1 * y.2.1 = y.2.2.1 * y.2.2.2 := by
    rw [← Nat.mul_add]
    congr 1
    omega
  constructor
  · refine Finset.mem_filter.2 ⟨mem_Sols.2 ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0 < y.1 + y.2.2.1
      omega
    · show 0 < y.2.1
      exact hb
    · show 0 < y.2.2.1
      exact hc
    · show 0 < y.2.2.2 - y.2.1
      omega
    · show (y.1 + y.2.2.1) * y.2.1 + y.2.2.1 * (y.2.2.2 - y.2.1) = N
      omega
    · show y.2.2.1 < y.1 + y.2.2.1
      omega
  · show (y.1 + y.2.2.1 - y.2.2.1, y.2.1, y.2.2.1, y.2.1 + (y.2.2.2 - y.2.1)) = y
    have h5 : y.1 + y.2.2.1 - y.2.2.1 = y.1 := by omega
    have h6 : y.2.1 + (y.2.2.2 - y.2.1) = y.2.2.2 := by omega
    rw [h5, h6]

theorem image_euclidStep (N : ℕ) :
    ((Sols N).filter fun x => x.2.2.1 < x.1).image euclidStep
      = (Sols N).filter fun x => x.2.1 < x.2.2.2 := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 hy
    exact hxy ▸ euclidStep_mem hx
  · intro hy
    exact Finset.mem_image.2 ⟨euclidStepInv y, (euclidStepInv_mem hy).1, (euclidStepInv_mem hy).2⟩

theorem euclidStep_injOn (N : ℕ) :
    ∀ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
      ∀ y ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), euclidStep x = euclidStep y → x = y := by
  intro x hx y hy h
  have hltx : x.2.2.1 < x.1 := (Finset.mem_filter.1 hx).2
  have hlty : y.2.2.1 < y.1 := (Finset.mem_filter.1 hy).2
  obtain ⟨h1, h2, h3, h4⟩ :
      x.1 - x.2.2.1 = y.1 - y.2.2.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧
        x.2.1 + x.2.2.2 = y.2.1 + y.2.2.2 := by
    simpa [euclidStep, Prod.ext_iff] using h
  have hx1 : x.1 = y.1 := by omega
  have hx2 : x.2.2.2 = y.2.2.2 := by omega
  have e2 : x.2.2 = y.2.2 := Prod.ext h3 hx2
  have e1 : x.2 = y.2 := Prod.ext h2 e2
  exact Prod.ext hx1 e1

theorem sum_euclidStep {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → M) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), F (euclidStep x)
      = ∑ y ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), F y := by
  rw [← image_euclidStep N, Finset.sum_image (euclidStep_injOn N)]

theorem sum_ac_filter_lt (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), x.1 * x.2.2.1
      = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), x.1 * x.2.2.1)
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), x.2.2.1 * x.2.2.1 := by
  have step : ∀ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
      x.1 * x.2.2.1 = (euclidStep x).1 * (euclidStep x).2.2.1 + x.2.2.1 * x.2.2.1 := by
    intro x hx
    have hlt : x.2.2.1 < x.1 := (Finset.mem_filter.1 hx).2
    show x.1 * x.2.2.1 = (x.1 - x.2.2.1) * x.2.2.1 + x.2.2.1 * x.2.2.1
    have h1 : (x.1 - x.2.2.1) * x.2.2.1 = x.1 * x.2.2.1 - x.2.2.1 * x.2.2.1 :=
      Nat.sub_mul _ _ _
    have h2 : x.2.2.1 * x.2.2.1 ≤ x.1 * x.2.2.1 := mul_le_mul_left (le_of_lt hlt) _
    omega
  calc
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), x.1 * x.2.2.1
        = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
            ((euclidStep x).1 * (euclidStep x).2.2.1 + x.2.2.1 * x.2.2.1) :=
      Finset.sum_congr rfl step
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
            (euclidStep x).1 * (euclidStep x).2.2.1)
          + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), x.2.2.1 * x.2.2.1 :=
      Finset.sum_add_distrib
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), x.1 * x.2.2.1)
          + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), x.2.2.1 * x.2.2.1 := by
      rw [sum_euclidStep N (fun y => y.1 * y.2.2.1)]

end DivisorConvolution
end FLT

open Finset

namespace FLT
namespace DivisorConvolution
namespace BesgeCertificate

def swap₁ (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ := (x.2.2.1, x.2.2.2, x.1, x.2.1)

def swap₂ (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ := (x.2.1, x.1, x.2.2.2, x.2.2.1)

theorem swap₁_swap₁ (x : ℕ × ℕ × ℕ × ℕ) : swap₁ (swap₁ x) = x := rfl

theorem swap₂_swap₂ (x : ℕ × ℕ × ℕ × ℕ) : swap₂ (swap₂ x) = x := rfl

theorem swap₁_mem_Sols {N : ℕ} {x : ℕ × ℕ × ℕ × ℕ} (hx : x ∈ Sols N) : swap₁ x ∈ Sols N := by
  obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hx
  refine mem_Sols.2 ⟨hc, hd, ha, hb, ?_⟩
  show x.2.2.1 * x.2.2.2 + x.1 * x.2.1 = N
  omega

theorem swap₂_mem_Sols {N : ℕ} {x : ℕ × ℕ × ℕ × ℕ} (hx : x ∈ Sols N) : swap₂ x ∈ Sols N := by
  obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hx
  refine mem_Sols.2 ⟨hb, ha, hd, hc, ?_⟩
  show x.2.1 * x.1 + x.2.2.2 * x.2.2.1 = N
  calc x.2.1 * x.1 + x.2.2.2 * x.2.2.1
      = x.1 * x.2.1 + x.2.2.1 * x.2.2.2 := by ring
    _ = N := heq

theorem sum_swap₁ {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → M)
    (p : ℕ × ℕ × ℕ × ℕ → Prop) [DecidablePred p] :
    ∑ x ∈ (Sols N).filter p, F x
      = ∑ x ∈ (Sols N).filter (fun x => p (swap₁ x)), F (swap₁ x) := by
  refine Finset.sum_nbij' swap₁ swap₁ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxS, hxp⟩ := Finset.mem_filter.1 hx
    refine Finset.mem_filter.2 ⟨swap₁_mem_Sols hxS, ?_⟩
    simpa [swap₁_swap₁] using hxp
  · intro x hx
    obtain ⟨hxS, hxp⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨swap₁_mem_Sols hxS, hxp⟩
  · intro x _; exact swap₁_swap₁ x
  · intro x _; exact swap₁_swap₁ x
  · intro x _; rfl

theorem sum_swap₂ {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → M)
    (p : ℕ × ℕ × ℕ × ℕ → Prop) [DecidablePred p] :
    ∑ x ∈ (Sols N).filter p, F x
      = ∑ x ∈ (Sols N).filter (fun x => p (swap₂ x)), F (swap₂ x) := by
  refine Finset.sum_nbij' swap₂ swap₂ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxS, hxp⟩ := Finset.mem_filter.1 hx
    refine Finset.mem_filter.2 ⟨swap₂_mem_Sols hxS, ?_⟩
    simpa [swap₂_swap₂] using hxp
  · intro x hx
    obtain ⟨hxS, hxp⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨swap₂_mem_Sols hxS, hxp⟩
  · intro x _; exact swap₂_swap₂ x
  · intro x _; exact swap₂_swap₂ x
  · intro x _; rfl

theorem sum_split {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → M)
    (g h : ℕ × ℕ × ℕ × ℕ → ℕ) :
    ∑ x ∈ Sols N, F x
      = ∑ x ∈ (Sols N).filter (fun x => g x < h x), F x
        + ∑ x ∈ (Sols N).filter (fun x => h x = g x), F x
        + ∑ x ∈ (Sols N).filter (fun x => h x < g x), F x := by
  classical
  have h1 := Finset.sum_filter_add_sum_filter_not (Sols N) (fun x => g x < h x) F
  have h2 := Finset.sum_filter_add_sum_filter_not
    ((Sols N).filter (fun x => ¬ g x < h x)) (fun x => h x = g x) F
  have e1 : ((Sols N).filter (fun x => ¬ g x < h x)).filter (fun x => h x = g x)
      = (Sols N).filter (fun x => h x = g x) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by constructor <;> intro hx <;> omega)
  have e2 : ((Sols N).filter (fun x => ¬ g x < h x)).filter (fun x => ¬ h x = g x)
      = (Sols N).filter (fun x => h x < g x) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => by constructor <;> intro hx <;> omega)
  rw [e1, e2] at h2
  rw [← h1, ← h2]
  exact (add_assoc _ _ _).symm

theorem engine_ac (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.1 * x.2.2.1 : ℤ)
      = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), (x.1 * x.2.2.1 : ℤ))
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.2.2.1 * x.2.2.1 : ℤ) := by
  have h := sum_ac_filter_lt N
  have h' : ((∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), x.1 * x.2.2.1 : ℕ) : ℤ)
      = (((∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), x.1 * x.2.2.1)
          + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), x.2.2.1 * x.2.2.1 : ℕ) : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at h'
  exact h'

theorem engine_c2 (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.2.2.1 * x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), (x.2.2.1 * x.2.2.1 : ℤ) := by
  have h := sum_euclidStep (M := ℤ) N (fun y => (y.2.2.1 * y.2.2.1 : ℤ))
  simpa [euclidStep] using h

theorem engine_a2 (N : ℕ) :
    (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.1 * x.1 : ℤ))
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.2.2.1 * x.2.2.1 : ℤ)
      = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), (x.1 * x.1 : ℤ))
        + 2 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.1 * x.2.2.1 : ℤ) := by
  have hstep : ∀ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
      (x.1 * x.1 : ℤ) + (x.2.2.1 * x.2.2.1 : ℤ)
        = ((euclidStep x).1 * (euclidStep x).1 : ℤ) + 2 * (x.1 * x.2.2.1 : ℤ) := by
    intro x hx
    have hlt : x.2.2.1 < x.1 := (Finset.mem_filter.1 hx).2
    have hsub : (((x.1 - x.2.2.1) * (x.1 - x.2.2.1) : ℕ) : ℤ)
        = ((x.1 : ℤ) - x.2.2.1) * ((x.1 : ℤ) - x.2.2.1) := by
      rw [Nat.cast_mul, Nat.cast_sub hlt.le]
    show (x.1 * x.1 : ℤ) + (x.2.2.1 * x.2.2.1 : ℤ)
        = (((x.1 - x.2.2.1) * (x.1 - x.2.2.1) : ℕ) : ℤ) + 2 * (x.1 * x.2.2.1 : ℤ)
    rw [hsub]
    ring
  have hengine := sum_euclidStep (M := ℤ) N (fun y => (y.1 * y.1 : ℤ))
  calc
    (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.1 * x.1 : ℤ))
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.2.2.1 * x.2.2.1 : ℤ)
        = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
            ((x.1 * x.1 : ℤ) + (x.2.2.1 * x.2.2.1 : ℤ)) := Finset.sum_add_distrib.symm
    _ = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
            (((euclidStep x).1 * (euclidStep x).1 : ℤ) + 2 * (x.1 * x.2.2.1 : ℤ)) :=
        Finset.sum_congr rfl hstep
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
              ((euclidStep x).1 * (euclidStep x).1 : ℤ))
          + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), 2 * (x.1 * x.2.2.1 : ℤ) :=
        Finset.sum_add_distrib
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), (x.1 * x.1 : ℤ))
          + 2 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.1 * x.2.2.1 : ℤ) := by
        rw [hengine, ← Finset.mul_sum]

theorem two_mul_sum_Ico_id (M : ℕ) :
    2 * ∑ b ∈ Finset.Ico 1 M, (b : ℤ) = M * M - M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; simp
    · rw [Finset.sum_Ico_succ_top hM]
      push_cast
      push_cast at ih
      linear_combination ih

theorem six_mul_sum_Ico_sq (M : ℕ) :
    6 * ∑ b ∈ Finset.Ico 1 M, ((b : ℤ) * b) = 2 * M * M * M - 3 * M * M + M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; simp
    · rw [Finset.sum_Ico_succ_top hM]
      push_cast
      push_cast at ih
      linear_combination ih

theorem six_mul_sum_Ico_mul_rev (M : ℕ) :
    6 * ∑ b ∈ Finset.Ico 1 M, ((b : ℤ) * (M - b)) = M * M * M - M := by
  have h1 := two_mul_sum_Ico_id M
  have h2 := six_mul_sum_Ico_sq M
  have hsplit : ∑ b ∈ Finset.Ico 1 M, ((b : ℤ) * (M - b))
      = (M : ℤ) * (∑ b ∈ Finset.Ico 1 M, (b : ℤ)) - ∑ b ∈ Finset.Ico 1 M, ((b : ℤ) * b) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [hsplit]
  linear_combination 3 * (M : ℤ) * h1 - h2

theorem sum_slice_diag {β : Type*} [AddCommMonoid β] (N : ℕ) (F : ℕ × ℕ × ℕ × ℕ → β) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), F x
      = ∑ p ∈ N.divisorsAntidiagonal, ∑ b ∈ Finset.Ico 1 p.2, F (p.1, b, p.1, p.2 - b) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨(x.1, x.2.1 + x.2.2.2), x.2.1⟩)
    (fun y => (y.1.1, y.2, y.1.1, y.1.2 - y.2)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxS, hx13⟩ := Finset.mem_filter.1 hx
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hxS
    have heq2 : x.1 * (x.2.1 + x.2.2.2) = N := by
      rw [Nat.mul_add]
      calc x.1 * x.2.1 + x.1 * x.2.2.2 = x.1 * x.2.1 + x.2.2.1 * x.2.2.2 := by rw [hx13]
        _ = N := heq
    have hN : N ≠ 0 := by
      have : 0 < x.1 * (x.2.1 + x.2.2.2) := Nat.mul_pos ha (by omega)
      omega
    refine Finset.mem_sigma.2 ⟨Nat.mem_divisorsAntidiagonal.2 ⟨heq2, hN⟩, ?_⟩
    refine Finset.mem_Ico.2 ⟨hb, ?_⟩
    show x.2.1 < x.2.1 + x.2.2.2
    omega
  · intro y hy
    obtain ⟨hp, hb⟩ := Finset.mem_sigma.1 hy
    obtain ⟨heq, hN⟩ := Nat.mem_divisorsAntidiagonal.1 hp
    obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.1 hb
    have hy11 : 0 < y.1.1 := by
      rcases Nat.eq_zero_or_pos y.1.1 with h | h
      · exfalso; apply hN; rw [← heq, h, Nat.zero_mul]
      · exact h
    refine Finset.mem_filter.2 ⟨mem_Sols.2 ⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · show 0 < y.1.1
      exact hy11
    · show 0 < y.2
      exact hb1
    · show 0 < y.1.1
      exact hy11
    · show 0 < y.1.2 - y.2
      omega
    · show y.1.1 * y.2 + y.1.1 * (y.1.2 - y.2) = N
      rw [← Nat.mul_add, Nat.add_sub_cancel' hb2.le]
      exact heq
  · intro x hx
    obtain ⟨hxS, hx13⟩ := Finset.mem_filter.1 hx
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext hx13 (by show x.2.1 + x.2.2.2 - x.2.1 = x.2.2.2; omega)))
  · intro y hy
    obtain ⟨hp, hb⟩ := Finset.mem_sigma.1 hy
    obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.1 hb
    have h2 : y.2 + (y.1.2 - y.2) = y.1.2 := by omega
    show (⟨((y.1.1, y.2, y.1.1, y.1.2 - y.2).1, (y.1.1, y.2, y.1.1, y.1.2 - y.2).2.1
        + (y.1.1, y.2, y.1.1, y.1.2 - y.2).2.2.2), (y.1.1, y.2, y.1.1, y.1.2 - y.2).2.1⟩ :
        (_ : ℕ × ℕ) × ℕ) = y
    show (⟨(y.1.1, y.2 + (y.1.2 - y.2)), y.2⟩ : (_ : ℕ × ℕ) × ℕ) = y
    rw [h2]
  · intro x hx
    obtain ⟨hxS, hx13⟩ := Finset.mem_filter.1 hx
    have htup : (x.1, x.2.1, x.1, x.2.1 + x.2.2.2 - x.2.1) = x :=
      Prod.ext rfl (Prod.ext rfl (Prod.ext hx13
        (by show x.2.1 + x.2.2.2 - x.2.1 = x.2.2.2; omega)))
    exact (congrArg F htup).symm

theorem slice_a2_eq_slice_ac (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.1 * x.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.1 * x.2.2.1 : ℤ) := by
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hx13 : x.1 = x.2.2.1 := (Finset.mem_filter.1 hx).2
  rw [← hx13]

theorem filter_diag_comm (N : ℕ) :
    (Sols N).filter (fun x => x.2.2.1 = x.1) = (Sols N).filter (fun x => x.1 = x.2.2.1) :=
  Finset.filter_congr (fun x _ => by omega)

theorem cast_sigma_one (N : ℕ) :
    ((sigma 1 N : ℕ) : ℤ) = ∑ d ∈ N.divisors, (d : ℤ) := by
  simp only [sigma, pow_one]
  push_cast
  rfl

theorem cast_sigma_two (N : ℕ) :
    ((sigma 2 N : ℕ) : ℤ) = ∑ d ∈ N.divisors, (d : ℤ) ^ 2 := by
  simp only [sigma]
  push_cast
  rfl

theorem cast_sigma_three (N : ℕ) :
    ((sigma 3 N : ℕ) : ℤ) = ∑ d ∈ N.divisors, (d : ℤ) ^ 3 := by
  simp only [sigma]
  push_cast
  rfl

theorem slice_ac (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.1 * x.2.2.1 : ℤ)
      = N * sigma 1 N - sigma 2 N := by
  rw [sum_slice_diag N (fun x => (x.1 * x.2.2.1 : ℤ))]
  have hpoint : ∀ p ∈ N.divisorsAntidiagonal,
      ∑ b ∈ Finset.Ico 1 p.2, ((p.1, b, p.1, p.2 - b).1 * (p.1, b, p.1, p.2 - b).2.2.1 : ℤ)
        = (p.1 : ℤ) * N - (p.1 : ℤ) ^ 2 := by
    intro p hp
    obtain ⟨heq, hN⟩ := Nat.mem_divisorsAntidiagonal.1 hp
    have hp2 : 0 < p.2 := by
      rcases Nat.eq_zero_or_pos p.2 with h | h
      · exfalso; apply hN; rw [← heq, h, Nat.mul_zero]
      · exact h
    have hpN : (p.1 : ℤ) * p.2 = N := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) heq
    calc ∑ b ∈ Finset.Ico 1 p.2, ((p.1, b, p.1, p.2 - b).1 * (p.1, b, p.1, p.2 - b).2.2.1 : ℤ)
        = ∑ _b ∈ Finset.Ico 1 p.2, ((p.1 : ℤ) * p.1) :=
          Finset.sum_congr rfl (fun b _ => rfl)
      _ = (Finset.Ico 1 p.2).card • ((p.1 : ℤ) * p.1) := Finset.sum_const _
      _ = ((p.2 - 1 : ℕ) : ℤ) * ((p.1 : ℤ) * p.1) := by rw [Nat.card_Ico, nsmul_eq_mul]
      _ = ((p.2 : ℤ) - 1) * ((p.1 : ℤ) * p.1) := by rw [Nat.cast_sub hp2]; norm_num
      _ = (p.1 : ℤ) * N - (p.1 : ℤ) ^ 2 := by linear_combination (p.1 : ℤ) * hpN
  rw [Finset.sum_congr rfl hpoint]
  have h1 := Nat.sum_divisorsAntidiagonal (f := fun a (_ : ℕ) => ((a : ℤ) * N - (a : ℤ) ^ 2)) (n := N)
  rw [h1, cast_sigma_one, cast_sigma_two, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun d _ => by ring)

theorem slice_b2 (N : ℕ) :
    6 * ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.2.1 * x.2.1 : ℤ)
      = 2 * sigma 3 N - 3 * sigma 2 N + sigma 1 N := by
  rw [sum_slice_diag N (fun x => (x.2.1 * x.2.1 : ℤ)), Finset.mul_sum]
  have hpoint : ∀ p ∈ N.divisorsAntidiagonal,
      6 * ∑ b ∈ Finset.Ico 1 p.2,
          ((p.1, b, p.1, p.2 - b).2.1 * (p.1, b, p.1, p.2 - b).2.1 : ℤ)
        = 2 * (p.2 : ℤ) ^ 3 - 3 * (p.2 : ℤ) ^ 2 + (p.2 : ℤ) := by
    intro p _
    have hinner : ∑ b ∈ Finset.Ico 1 p.2,
        ((p.1, b, p.1, p.2 - b).2.1 * (p.1, b, p.1, p.2 - b).2.1 : ℤ)
          = ∑ b ∈ Finset.Ico 1 p.2, ((b : ℤ) * b) :=
      Finset.sum_congr rfl (fun b _ => rfl)
    rw [hinner]
    linear_combination six_mul_sum_Ico_sq p.2
  rw [Finset.sum_congr rfl hpoint]
  rw [Nat.sum_divisorsAntidiagonal' (f := fun (_ : ℕ) b => (2 * (b : ℤ) ^ 3 - 3 * (b : ℤ) ^ 2 + b)) (n := N)]
  rw [cast_sigma_one, cast_sigma_two, cast_sigma_three]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

theorem slice_bd (N : ℕ) :
    6 * ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.2.1 * x.2.2.2 : ℤ)
      = sigma 3 N - sigma 1 N := by
  rw [sum_slice_diag N (fun x => (x.2.1 * x.2.2.2 : ℤ)), Finset.mul_sum]
  have hpoint : ∀ p ∈ N.divisorsAntidiagonal,
      6 * ∑ b ∈ Finset.Ico 1 p.2,
          ((p.1, b, p.1, p.2 - b).2.1 * (p.1, b, p.1, p.2 - b).2.2.2 : ℤ)
        = (p.2 : ℤ) ^ 3 - (p.2 : ℤ) := by
    intro p _
    have hterm : ∀ b ∈ Finset.Ico 1 p.2,
        ((p.1, b, p.1, p.2 - b).2.1 * (p.1, b, p.1, p.2 - b).2.2.2 : ℤ)
          = (b : ℤ) * ((p.2 : ℤ) - b) := by
      intro b hb
      have hb2 : b < p.2 := (Finset.mem_Ico.1 hb).2
      show ((b : ℤ) * ((p.2 - b : ℕ) : ℤ)) = (b : ℤ) * ((p.2 : ℤ) - b)
      rw [Nat.cast_sub hb2.le]
    rw [Finset.sum_congr rfl hterm]
    linear_combination six_mul_sum_Ico_mul_rev p.2
  rw [Finset.sum_congr rfl hpoint]
  rw [Nat.sum_divisorsAntidiagonal' (f := fun (_ : ℕ) b => ((b : ℤ) ^ 3 - b)) (n := N)]
  rw [cast_sigma_one, cast_sigma_three, Finset.sum_sub_distrib]

theorem cast_sigma_one_antidiagonal (n : ℕ) :
    ∑ p ∈ n.divisorsAntidiagonal, (p.1 : ℤ) = (sigma 1 n : ℤ) := by
  rw [Nat.sum_divisorsAntidiagonal (f := fun a (_ : ℕ) => (a : ℤ)) (n := n), cast_sigma_one]

theorem sum_ac_eq_sigmaConv (N : ℕ) :
    ∑ x ∈ Sols N, (x.1 * x.2.2.1 : ℤ) = (sigmaConv 1 1 N : ℤ) := by
  have hmaps : ∀ x ∈ Sols N, x.1 * x.2.1 ∈ Finset.Ico 1 N := by
    intro x hx
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hx
    have h1 : 0 < x.1 * x.2.1 := Nat.mul_pos ha hb
    have h2 : 0 < x.2.2.1 * x.2.2.2 := Nat.mul_pos hc hd
    exact Finset.mem_Ico.2 ⟨h1, by omega⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun x => (x.1 * x.2.2.1 : ℤ))
  rw [← hfib]
  have hconv : ((sigmaConv 1 1 N : ℕ) : ℤ)
      = ∑ i ∈ Finset.Ico 1 N, ((sigma 1 i : ℤ) * (sigma 1 (N - i) : ℤ)) := by
    simp only [sigmaConv]
    push_cast
    rfl
  rw [hconv]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
  have hbij : ∑ x ∈ (Sols N).filter (fun x => x.1 * x.2.1 = i), (x.1 * x.2.2.1 : ℤ)
      = ∑ q ∈ i.divisorsAntidiagonal ×ˢ (N - i).divisorsAntidiagonal, ((q.1.1 : ℤ) * q.2.1) := by
    refine Finset.sum_nbij' (fun x => ((x.1, x.2.1), (x.2.2.1, x.2.2.2)))
      (fun q => (q.1.1, q.1.2, q.2.1, q.2.2)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxS, hxi⟩ := Finset.mem_filter.1 hx
      obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hxS
      have h1 : 0 < x.1 * x.2.1 := Nat.mul_pos ha hb
      have h2 : 0 < x.2.2.1 * x.2.2.2 := Nat.mul_pos hc hd
      refine Finset.mem_product.2 ⟨Nat.mem_divisorsAntidiagonal.2 ⟨hxi, by omega⟩,
        Nat.mem_divisorsAntidiagonal.2 ⟨?_, ?_⟩⟩
      · show x.2.2.1 * x.2.2.2 = N - i
        omega
      · omega
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
      obtain ⟨he1, hn1⟩ := Nat.mem_divisorsAntidiagonal.1 hq1
      obtain ⟨he2, hn2⟩ := Nat.mem_divisorsAntidiagonal.1 hq2
      have ha : 0 < q.1.1 := Nat.pos_of_ne_zero (fun h => hn1 (by rw [← he1, h, Nat.zero_mul]))
      have hb : 0 < q.1.2 := Nat.pos_of_ne_zero (fun h => hn1 (by rw [← he1, h, Nat.mul_zero]))
      have hc : 0 < q.2.1 := Nat.pos_of_ne_zero (fun h => hn2 (by rw [← he2, h, Nat.zero_mul]))
      have hd : 0 < q.2.2 := Nat.pos_of_ne_zero (fun h => hn2 (by rw [← he2, h, Nat.mul_zero]))
      refine Finset.mem_filter.2 ⟨mem_Sols.2 ⟨ha, hb, hc, hd, ?_⟩, ?_⟩
      · show q.1.1 * q.1.2 + q.2.1 * q.2.2 = N
        omega
      · show q.1.1 * q.1.2 = i
        exact he1
    · intro x _; rfl
    · intro q _; rfl
    · intro x _; rfl
  rw [hbij,
    Finset.sum_product' i.divisorsAntidiagonal ((N - i).divisorsAntidiagonal)
      (fun p q => ((p.1 : ℤ) * q.1))]
  rw [← cast_sigma_one_antidiagonal i, ← cast_sigma_one_antidiagonal (N - i), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]

theorem swap1_ac_a (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.1 * x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), (x.1 * x.2.2.1 : ℤ) := by
  rw [sum_swap₁ N (fun x => (x.1 * x.2.2.1 : ℤ)) (fun x => x.2.2.1 < x.1)]
  exact Finset.sum_congr rfl (fun x _ => by
    show ((x.2.2.1 : ℤ) * x.1) = ((x.1 : ℤ) * x.2.2.1)
    ring)

theorem swap1_ac_d (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), (x.1 * x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), (x.1 * x.2.2.1 : ℤ) := by
  rw [sum_swap₁ N (fun x => (x.1 * x.2.2.1 : ℤ)) (fun x => x.2.1 < x.2.2.2)]
  exact Finset.sum_congr rfl (fun x _ => by
    show ((x.2.2.1 : ℤ) * x.1) = ((x.1 : ℤ) * x.2.2.1)
    ring)

theorem swap1_c2_a (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.2.2.1 * x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), (x.1 * x.1 : ℤ) := by
  rw [sum_swap₁ N (fun x => (x.2.2.1 * x.2.2.1 : ℤ)) (fun x => x.2.2.1 < x.1)]
  exact Finset.sum_congr rfl (fun x _ => rfl)

theorem swap1_c2_d (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), (x.2.2.1 * x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), (x.1 * x.1 : ℤ) := by
  rw [sum_swap₁ N (fun x => (x.2.2.1 * x.2.2.1 : ℤ)) (fun x => x.2.1 < x.2.2.2)]
  exact Finset.sum_congr rfl (fun x _ => rfl)

theorem swap2_a2_diag (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 = x.2.1), (x.1 * x.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.2.1 * x.2.1 : ℤ) := by
  rw [sum_swap₂ N (fun x => (x.1 * x.1 : ℤ)) (fun x => x.2.2.2 = x.2.1), ← filter_diag_comm N]
  exact Finset.sum_congr rfl (fun x _ => rfl)

theorem swap2_ac_diag (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 = x.2.1), (x.1 * x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.2.1 * x.2.2.2 : ℤ) := by
  rw [sum_swap₂ N (fun x => (x.1 * x.2.2.1 : ℤ)) (fun x => x.2.2.2 = x.2.1), ← filter_diag_comm N]
  exact Finset.sum_congr rfl (fun x _ => rfl)

theorem besgeIdentity_int (N : ℕ) :
    (12 * sigmaConv 1 1 N : ℤ) = 5 * sigma 3 N + (1 - 6 * N) * sigma 1 N := by

  have e1 : ∑ x ∈ Sols N, (x.1 * x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.1 * x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.1 * x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), (x.1 * x.2.2.1 : ℤ) :=
    sum_split N (fun x => (x.1 * x.2.2.1 : ℤ)) (fun x => x.2.2.1) (fun x => x.1)
  have e2 : ∑ x ∈ Sols N, (x.1 * x.2.2.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), (x.1 * x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 = x.2.1), (x.1 * x.2.2.1 : ℤ)
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), (x.1 * x.2.2.1 : ℤ) :=
    sum_split N (fun x => (x.1 * x.2.2.1 : ℤ)) (fun x => x.2.1) (fun x => x.2.2.2)
  have e12 : ∑ x ∈ Sols N, (x.1 * x.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (x.1 * x.1 : ℤ)
        + ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.1 * x.1 : ℤ)
        + ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), (x.1 * x.1 : ℤ) :=
    sum_split N (fun x => (x.1 * x.1 : ℤ)) (fun x => x.2.2.1) (fun x => x.1)
  have e13 : ∑ x ∈ Sols N, (x.1 * x.1 : ℤ)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), (x.1 * x.1 : ℤ)
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 = x.2.1), (x.1 * x.1 : ℤ)
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), (x.1 * x.1 : ℤ) :=
    sum_split N (fun x => (x.1 * x.1 : ℤ)) (fun x => x.2.1) (fun x => x.2.2.2)

  have e3 := swap1_ac_a N
  have e4 := swap1_ac_d N
  have e5 := swap1_c2_a N
  have e6 := swap1_c2_d N
  have e7 := swap2_a2_diag N
  have e8 := swap2_ac_diag N

  have e9 := engine_ac N
  have e10 := engine_c2 N
  have e11 := engine_a2 N

  have e14 := slice_ac N
  have e15 := slice_a2_eq_slice_ac N
  have e16 := slice_b2 N
  have e17 := slice_bd N
  have e18 := sum_ac_eq_sigmaConv N

  have h2T : 2 * ∑ x ∈ Sols N, (x.1 * x.2.2.1 : ℤ)
      = 2 * ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.2.1 * x.2.1 : ℤ)
        + ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.2.1 * x.2.2.2 : ℤ)
        - ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), (x.1 * x.2.2.1 : ℤ) := by
    linarith [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e15]
  linear_combination 6 * h2T - 12 * e18 + 2 * e16 + e17 - 6 * e14

theorem besgeIdentity (N : ℕ) : BesgeIdentity N :=
  (besgeIdentity_iff_int N).mpr (besgeIdentity_int N)

end BesgeCertificate
end DivisorConvolution
end FLT

open Finset

namespace FLT
namespace DivisorConvolution
namespace Weight6Certificate

open BesgeCertificate

theorem four_mul_sum_Ico_cube (M : ℕ) :
    4 * ∑ b ∈ Finset.Ico 1 M, (b : ℤ) ^ 3 = M ^ 4 - 2 * M ^ 3 + M ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; simp
    · rw [Finset.sum_Ico_succ_top hM]
      push_cast
      push_cast at ih
      linear_combination ih

theorem thirty_mul_sum_Ico_pow_four (M : ℕ) :
    30 * ∑ b ∈ Finset.Ico 1 M, (b : ℤ) ^ 4
      = 6 * M ^ 5 - 15 * M ^ 4 + 10 * M ^ 3 - M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; simp
    · rw [Finset.sum_Ico_succ_top hM]
      push_cast
      push_cast at ih
      linear_combination ih

theorem sixty_mul_sum_Ico_mul_cube_rev (M : ℕ) :
    60 * ∑ b ∈ Finset.Ico 1 M, ((b : ℤ) * ((M : ℤ) - b) ^ 3)
      = 3 * M ^ 5 - 5 * M ^ 3 + 2 * M := by
  have h1 := two_mul_sum_Ico_id M
  have h2 := six_mul_sum_Ico_sq M
  have h3 := four_mul_sum_Ico_cube M
  have h4 := thirty_mul_sum_Ico_pow_four M
  have hsplit : ∑ b ∈ Finset.Ico 1 M, ((b : ℤ) * ((M : ℤ) - b) ^ 3)
      = (M : ℤ) ^ 3 * (∑ b ∈ Finset.Ico 1 M, (b : ℤ))
          - 3 * (M : ℤ) ^ 2 * (∑ b ∈ Finset.Ico 1 M, ((b : ℤ) * b))
          + 3 * (M : ℤ) * (∑ b ∈ Finset.Ico 1 M, (b : ℤ) ^ 3)
          - ∑ b ∈ Finset.Ico 1 M, (b : ℤ) ^ 4 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [hsplit]
  linear_combination 30 * (M : ℤ) ^ 3 * h1 - 30 * (M : ℤ) ^ 2 * h2 + 45 * (M : ℤ) * h3 - 2 * h4

theorem thirty_mul_sum_Ico_sq_mul_sq_rev (M : ℕ) :
    30 * ∑ b ∈ Finset.Ico 1 M, ((b : ℤ) ^ 2 * ((M : ℤ) - b) ^ 2)
      = M ^ 5 - M := by
  have h2 := six_mul_sum_Ico_sq M
  have h3 := four_mul_sum_Ico_cube M
  have h4 := thirty_mul_sum_Ico_pow_four M
  have hsplit : ∑ b ∈ Finset.Ico 1 M, ((b : ℤ) ^ 2 * ((M : ℤ) - b) ^ 2)
      = (M : ℤ) ^ 2 * (∑ b ∈ Finset.Ico 1 M, ((b : ℤ) * b))
          - 2 * (M : ℤ) * (∑ b ∈ Finset.Ico 1 M, (b : ℤ) ^ 3)
          + ∑ b ∈ Finset.Ico 1 M, (b : ℤ) ^ 4 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [hsplit]
  linear_combination 5 * (M : ℤ) ^ 2 * h2 - 15 * (M : ℤ) * h3 + h4

theorem cast_sigma_four (N : ℕ) :
    ((sigma 4 N : ℕ) : ℤ) = ∑ d ∈ N.divisors, (d : ℤ) ^ 4 := by
  simp only [sigma]
  push_cast
  rfl

theorem cast_sigma_five (N : ℕ) :
    ((sigma 5 N : ℕ) : ℤ) = ∑ d ∈ N.divisors, (d : ℤ) ^ 5 := by
  simp only [sigma]
  push_cast
  rfl

theorem cast_sigma_three_antidiagonal (n : ℕ) :
    ∑ p ∈ n.divisorsAntidiagonal, (p.1 : ℤ) ^ 3 = (sigma 3 n : ℤ) := by
  rw [Nat.sum_divisorsAntidiagonal (f := fun a (_ : ℕ) => (a : ℤ) ^ 3) (n := n), cast_sigma_three]

theorem slice_a4 (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.1 : ℤ) ^ 4)
      = N * sigma 3 N - sigma 4 N := by
  rw [sum_slice_diag N (fun x => ((x.1 : ℤ) ^ 4))]
  have hpoint : ∀ p ∈ N.divisorsAntidiagonal,
      ∑ b ∈ Finset.Ico 1 p.2, (((p.1, b, p.1, p.2 - b).1 : ℤ) ^ 4)
        = (p.1 : ℤ) ^ 3 * N - (p.1 : ℤ) ^ 4 := by
    intro p hp
    obtain ⟨heq, hN⟩ := Nat.mem_divisorsAntidiagonal.1 hp
    have hp2 : 0 < p.2 := by
      rcases Nat.eq_zero_or_pos p.2 with h | h
      · exfalso; apply hN; rw [← heq, h, Nat.mul_zero]
      · exact h
    have hpN : (p.1 : ℤ) * p.2 = N := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) heq
    calc ∑ b ∈ Finset.Ico 1 p.2, (((p.1, b, p.1, p.2 - b).1 : ℤ) ^ 4)
        = ∑ _b ∈ Finset.Ico 1 p.2, ((p.1 : ℤ) ^ 4) :=
          Finset.sum_congr rfl (fun b _ => rfl)
      _ = (Finset.Ico 1 p.2).card • ((p.1 : ℤ) ^ 4) := Finset.sum_const _
      _ = ((p.2 - 1 : ℕ) : ℤ) * ((p.1 : ℤ) ^ 4) := by rw [Nat.card_Ico, nsmul_eq_mul]
      _ = ((p.2 : ℤ) - 1) * ((p.1 : ℤ) ^ 4) := by rw [Nat.cast_sub hp2]; norm_num
      _ = (p.1 : ℤ) ^ 3 * N - (p.1 : ℤ) ^ 4 := by linear_combination (p.1 : ℤ) ^ 3 * hpN
  rw [Finset.sum_congr rfl hpoint]
  have h1 := Nat.sum_divisorsAntidiagonal
    (f := fun a (_ : ℕ) => ((a : ℤ) ^ 3 * N - (a : ℤ) ^ 4)) (n := N)
  rw [h1, cast_sigma_three, cast_sigma_four, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun d _ => by ring)

theorem slice_b4 (N : ℕ) :
    30 * ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.2.1 : ℤ) ^ 4)
      = 6 * sigma 5 N - 15 * sigma 4 N + 10 * sigma 3 N - sigma 1 N := by
  rw [sum_slice_diag N (fun x => ((x.2.1 : ℤ) ^ 4)), Finset.mul_sum]
  have hpoint : ∀ p ∈ N.divisorsAntidiagonal,
      30 * ∑ b ∈ Finset.Ico 1 p.2, (((p.1, b, p.1, p.2 - b).2.1 : ℤ) ^ 4)
        = 6 * (p.2 : ℤ) ^ 5 - 15 * (p.2 : ℤ) ^ 4 + 10 * (p.2 : ℤ) ^ 3 - (p.2 : ℤ) := by
    intro p _
    have hinner : ∑ b ∈ Finset.Ico 1 p.2, (((p.1, b, p.1, p.2 - b).2.1 : ℤ) ^ 4)
        = ∑ b ∈ Finset.Ico 1 p.2, (b : ℤ) ^ 4 :=
      Finset.sum_congr rfl (fun b _ => rfl)
    rw [hinner]
    linear_combination thirty_mul_sum_Ico_pow_four p.2
  rw [Finset.sum_congr rfl hpoint]
  rw [Nat.sum_divisorsAntidiagonal'
    (f := fun (_ : ℕ) b => (6 * (b : ℤ) ^ 5 - 15 * (b : ℤ) ^ 4 + 10 * (b : ℤ) ^ 3 - (b : ℤ)))
    (n := N)]
  rw [cast_sigma_one, cast_sigma_three, cast_sigma_four, cast_sigma_five]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

theorem slice_bd3 (N : ℕ) :
    60 * ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.2.1 : ℤ) * (x.2.2.2 : ℤ) ^ 3)
      = 3 * sigma 5 N - 5 * sigma 3 N + 2 * sigma 1 N := by
  rw [sum_slice_diag N (fun x => ((x.2.1 : ℤ) * (x.2.2.2 : ℤ) ^ 3)), Finset.mul_sum]
  have hpoint : ∀ p ∈ N.divisorsAntidiagonal,
      60 * ∑ b ∈ Finset.Ico 1 p.2,
          (((p.1, b, p.1, p.2 - b).2.1 : ℤ) * ((p.1, b, p.1, p.2 - b).2.2.2 : ℤ) ^ 3)
        = 3 * (p.2 : ℤ) ^ 5 - 5 * (p.2 : ℤ) ^ 3 + 2 * (p.2 : ℤ) := by
    intro p _
    have hterm : ∀ b ∈ Finset.Ico 1 p.2,
        (((p.1, b, p.1, p.2 - b).2.1 : ℤ) * ((p.1, b, p.1, p.2 - b).2.2.2 : ℤ) ^ 3)
          = (b : ℤ) * ((p.2 : ℤ) - b) ^ 3 := by
      intro b hb
      have hb2 : b < p.2 := (Finset.mem_Ico.1 hb).2
      show ((b : ℤ) * ((p.2 - b : ℕ) : ℤ) ^ 3) = (b : ℤ) * ((p.2 : ℤ) - b) ^ 3
      rw [Nat.cast_sub hb2.le]
    rw [Finset.sum_congr rfl hterm]
    linear_combination sixty_mul_sum_Ico_mul_cube_rev p.2
  rw [Finset.sum_congr rfl hpoint]
  rw [Nat.sum_divisorsAntidiagonal'
    (f := fun (_ : ℕ) b => (3 * (b : ℤ) ^ 5 - 5 * (b : ℤ) ^ 3 + 2 * (b : ℤ))) (n := N)]
  rw [cast_sigma_one, cast_sigma_three, cast_sigma_five]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]

theorem slice_b2d2 (N : ℕ) :
    30 * ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.2.1 : ℤ) ^ 2 * (x.2.2.2 : ℤ) ^ 2)
      = sigma 5 N - sigma 1 N := by
  rw [sum_slice_diag N (fun x => ((x.2.1 : ℤ) ^ 2 * (x.2.2.2 : ℤ) ^ 2)), Finset.mul_sum]
  have hpoint : ∀ p ∈ N.divisorsAntidiagonal,
      30 * ∑ b ∈ Finset.Ico 1 p.2,
          (((p.1, b, p.1, p.2 - b).2.1 : ℤ) ^ 2 * ((p.1, b, p.1, p.2 - b).2.2.2 : ℤ) ^ 2)
        = (p.2 : ℤ) ^ 5 - (p.2 : ℤ) := by
    intro p _
    have hterm : ∀ b ∈ Finset.Ico 1 p.2,
        (((p.1, b, p.1, p.2 - b).2.1 : ℤ) ^ 2 * ((p.1, b, p.1, p.2 - b).2.2.2 : ℤ) ^ 2)
          = (b : ℤ) ^ 2 * ((p.2 : ℤ) - b) ^ 2 := by
      intro b hb
      have hb2 : b < p.2 := (Finset.mem_Ico.1 hb).2
      show ((b : ℤ) ^ 2 * ((p.2 - b : ℕ) : ℤ) ^ 2) = (b : ℤ) ^ 2 * ((p.2 : ℤ) - b) ^ 2
      rw [Nat.cast_sub hb2.le]
    rw [Finset.sum_congr rfl hterm]
    linear_combination thirty_mul_sum_Ico_sq_mul_sq_rev p.2
  rw [Finset.sum_congr rfl hpoint]
  rw [Nat.sum_divisorsAntidiagonal' (f := fun (_ : ℕ) b => ((b : ℤ) ^ 5 - (b : ℤ))) (n := N)]
  rw [cast_sigma_one, cast_sigma_five, Finset.sum_sub_distrib]

theorem sum_ac3_eq_sigmaConv (N : ℕ) :
    ∑ x ∈ Sols N, ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3) = (sigmaConv 1 3 N : ℤ) := by
  have hmaps : ∀ x ∈ Sols N, x.1 * x.2.1 ∈ Finset.Ico 1 N := by
    intro x hx
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hx
    have h1 : 0 < x.1 * x.2.1 := Nat.mul_pos ha hb
    have h2 : 0 < x.2.2.1 * x.2.2.2 := Nat.mul_pos hc hd
    exact Finset.mem_Ico.2 ⟨h1, by omega⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun x => ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3))
  rw [← hfib]
  have hconv : ((sigmaConv 1 3 N : ℕ) : ℤ)
      = ∑ i ∈ Finset.Ico 1 N, ((sigma 1 i : ℤ) * (sigma 3 (N - i) : ℤ)) := by
    simp only [sigmaConv]
    push_cast
    rfl
  rw [hconv]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
  have hbij : ∑ x ∈ (Sols N).filter (fun x => x.1 * x.2.1 = i), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = ∑ q ∈ i.divisorsAntidiagonal ×ˢ (N - i).divisorsAntidiagonal,
          ((q.1.1 : ℤ) * (q.2.1 : ℤ) ^ 3) := by
    refine Finset.sum_nbij' (fun x => ((x.1, x.2.1), (x.2.2.1, x.2.2.2)))
      (fun q => (q.1.1, q.1.2, q.2.1, q.2.2)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxS, hxi⟩ := Finset.mem_filter.1 hx
      obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hxS
      have h1 : 0 < x.1 * x.2.1 := Nat.mul_pos ha hb
      have h2 : 0 < x.2.2.1 * x.2.2.2 := Nat.mul_pos hc hd
      refine Finset.mem_product.2 ⟨Nat.mem_divisorsAntidiagonal.2 ⟨hxi, by omega⟩,
        Nat.mem_divisorsAntidiagonal.2 ⟨?_, ?_⟩⟩
      · show x.2.2.1 * x.2.2.2 = N - i
        omega
      · omega
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
      obtain ⟨he1, hn1⟩ := Nat.mem_divisorsAntidiagonal.1 hq1
      obtain ⟨he2, hn2⟩ := Nat.mem_divisorsAntidiagonal.1 hq2
      have ha : 0 < q.1.1 := Nat.pos_of_ne_zero (fun h => hn1 (by rw [← he1, h, Nat.zero_mul]))
      have hb : 0 < q.1.2 := Nat.pos_of_ne_zero (fun h => hn1 (by rw [← he1, h, Nat.mul_zero]))
      have hc : 0 < q.2.1 := Nat.pos_of_ne_zero (fun h => hn2 (by rw [← he2, h, Nat.zero_mul]))
      have hd : 0 < q.2.2 := Nat.pos_of_ne_zero (fun h => hn2 (by rw [← he2, h, Nat.mul_zero]))
      refine Finset.mem_filter.2 ⟨mem_Sols.2 ⟨ha, hb, hc, hd, ?_⟩, ?_⟩
      · show q.1.1 * q.1.2 + q.2.1 * q.2.2 = N
        omega
      · show q.1.1 * q.1.2 = i
        exact he1
    · intro x _; rfl
    · intro q _; rfl
    · intro x _; rfl
  rw [hbij,
    Finset.sum_product' i.divisorsAntidiagonal ((N - i).divisorsAntidiagonal)
      (fun p q => ((p.1 : ℤ) * (q.1 : ℤ) ^ 3))]
  rw [← cast_sigma_one_antidiagonal i, ← cast_sigma_three_antidiagonal (N - i), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]

theorem engine_ac3 (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3))
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.2.2.1 : ℤ) ^ 4) := by
  have hengine := sum_euclidStep (M := ℤ) N (fun y => ((y.1 : ℤ) * (y.2.2.1 : ℤ) ^ 3))
  have hstep : ∀ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
      ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
        = (((euclidStep x).1 : ℤ) * ((euclidStep x).2.2.1 : ℤ) ^ 3) + ((x.2.2.1 : ℤ) ^ 4) := by
    intro x hx
    have hlt : x.2.2.1 < x.1 := (Finset.mem_filter.1 hx).2
    show ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
        = (((x.1 - x.2.2.1 : ℕ) : ℤ) * (x.2.2.1 : ℤ) ^ 3) + ((x.2.2.1 : ℤ) ^ 4)
    rw [Nat.cast_sub hlt.le]
    ring
  calc ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
          ((((euclidStep x).1 : ℤ) * ((euclidStep x).2.2.1 : ℤ) ^ 3) + ((x.2.2.1 : ℤ) ^ 4)) :=
        Finset.sum_congr rfl hstep
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
            (((euclidStep x).1 : ℤ) * ((euclidStep x).2.2.1 : ℤ) ^ 3))
          + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.2.2.1 : ℤ) ^ 4) :=
        Finset.sum_add_distrib
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3))
          + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.2.2.1 : ℤ) ^ 4) := by
        rw [hengine]

theorem engine_c4 (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.2.2.1 : ℤ) ^ 4)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.2.2.1 : ℤ) ^ 4) := by
  have h := sum_euclidStep (M := ℤ) N (fun y => ((y.2.2.1 : ℤ) ^ 4))
  simpa [euclidStep] using h

theorem engine_a2c2 (N : ℕ) :
    (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2))
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.2.2.1 : ℤ) ^ 4)
      = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2))
        + 2 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
            ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3) := by
  have hengine := sum_euclidStep (M := ℤ) N (fun y => ((y.1 : ℤ) ^ 2 * (y.2.2.1 : ℤ) ^ 2))
  have hstep : ∀ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
      ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) + ((x.2.2.1 : ℤ) ^ 4)
        = (((euclidStep x).1 : ℤ) ^ 2 * ((euclidStep x).2.2.1 : ℤ) ^ 2)
          + 2 * ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3) := by
    intro x hx
    have hlt : x.2.2.1 < x.1 := (Finset.mem_filter.1 hx).2
    show ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) + ((x.2.2.1 : ℤ) ^ 4)
        = (((x.1 - x.2.2.1 : ℕ) : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
          + 2 * ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
    rw [Nat.cast_sub hlt.le]
    ring
  calc (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2))
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.2.2.1 : ℤ) ^ 4)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
          (((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) + ((x.2.2.1 : ℤ) ^ 4)) :=
        Finset.sum_add_distrib.symm
    _ = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
          ((((euclidStep x).1 : ℤ) ^ 2 * ((euclidStep x).2.2.1 : ℤ) ^ 2)
            + 2 * ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) := Finset.sum_congr rfl hstep
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
            (((euclidStep x).1 : ℤ) ^ 2 * ((euclidStep x).2.2.1 : ℤ) ^ 2))
          + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
              (2 * ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) := Finset.sum_add_distrib
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2))
          + 2 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
              ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3) := by
        rw [hengine, ← Finset.mul_sum]

theorem engine_a3c (N : ℕ) :
    (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)))
        + 3 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)))
        + (3 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
              ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
            + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.2.2.1 : ℤ) ^ 4)) := by
  have hengine := sum_euclidStep (M := ℤ) N (fun y => ((y.1 : ℤ) ^ 3 * (y.2.2.1 : ℤ)))
  have hstep : ∀ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
      ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)) + 3 * ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
        = (((euclidStep x).1 : ℤ) ^ 3 * ((euclidStep x).2.2.1 : ℤ))
          + (3 * ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) + (x.2.2.1 : ℤ) ^ 4) := by
    intro x hx
    have hlt : x.2.2.1 < x.1 := (Finset.mem_filter.1 hx).2
    show ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)) + 3 * ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
        = (((x.1 - x.2.2.1 : ℕ) : ℤ) ^ 3 * (x.2.2.1 : ℤ))
          + (3 * ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) + (x.2.2.1 : ℤ) ^ 4)
    rw [Nat.cast_sub hlt.le]
    ring
  calc (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)))
        + 3 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
          (((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)) + 3 * ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
          ((((euclidStep x).1 : ℤ) ^ 3 * ((euclidStep x).2.2.1 : ℤ))
            + (3 * ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) + (x.2.2.1 : ℤ) ^ 4)) :=
        Finset.sum_congr rfl hstep
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
            (((euclidStep x).1 : ℤ) ^ 3 * ((euclidStep x).2.2.1 : ℤ)))
          + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
              (3 * ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) + (x.2.2.1 : ℤ) ^ 4) :=
        Finset.sum_add_distrib
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)))
          + (3 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
                ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
              + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.2.2.1 : ℤ) ^ 4)) := by
        rw [hengine, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem engine_a4 (N : ℕ) :
    (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 4))
        + (6 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
              ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
            + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.2.2.1 : ℤ) ^ 4))
      = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) ^ 4))
        + (4 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ))
            + 4 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
                ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) := by
  have hengine := sum_euclidStep (M := ℤ) N (fun y => ((y.1 : ℤ) ^ 4))
  have hstep : ∀ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
      ((x.1 : ℤ) ^ 4) + (6 * ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) + (x.2.2.1 : ℤ) ^ 4)
        = (((euclidStep x).1 : ℤ) ^ 4)
          + (4 * ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)) + 4 * ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) := by
    intro x hx
    have hlt : x.2.2.1 < x.1 := (Finset.mem_filter.1 hx).2
    show ((x.1 : ℤ) ^ 4) + (6 * ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) + (x.2.2.1 : ℤ) ^ 4)
        = (((x.1 - x.2.2.1 : ℕ) : ℤ) ^ 4)
          + (4 * ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)) + 4 * ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3))
    rw [Nat.cast_sub hlt.le]
    ring
  calc (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 4))
        + (6 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
              ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
            + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.2.2.1 : ℤ) ^ 4))
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
          ((x.1 : ℤ) ^ 4 + (6 * ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) + (x.2.2.1 : ℤ) ^ 4)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
          ((((euclidStep x).1 : ℤ) ^ 4)
            + (4 * ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)) + 4 * ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3))) :=
        Finset.sum_congr rfl hstep
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), (((euclidStep x).1 : ℤ) ^ 4))
          + ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
              (4 * ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)) + 4 * ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) :=
        Finset.sum_add_distrib
    _ = (∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) ^ 4))
          + (4 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ))
              + 4 * ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1),
                  ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) := by
        rw [hengine, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem swap1_ac3_lt_a (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)) := by
  rw [sum_swap₁ N (fun x => ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) (fun x => x.1 < x.2.2.1)]
  exact Finset.sum_congr rfl (fun x _ => by
    show ((x.2.2.1 : ℤ) * (x.1 : ℤ) ^ 3) = ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ))
    ring)

theorem swap1_ac3_lt_d (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)) := by
  rw [sum_swap₁ N (fun x => ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) (fun x => x.2.2.2 < x.2.1)]
  exact Finset.sum_congr rfl (fun x _ => by
    show ((x.2.2.1 : ℤ) * (x.1 : ℤ) ^ 3) = ((x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ))
    ring)

theorem swap1_a2c2_lt_a (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) := by
  rw [sum_swap₁ N (fun x => ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)) (fun x => x.1 < x.2.2.1)]
  exact Finset.sum_congr rfl (fun x _ => by
    show ((x.2.2.1 : ℤ) ^ 2 * (x.1 : ℤ) ^ 2) = ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
    ring)

theorem swap1_a2c2_lt_d (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) := by
  rw [sum_swap₁ N (fun x => ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)) (fun x => x.2.2.2 < x.2.1)]
  exact Finset.sum_congr rfl (fun x _ => by
    show ((x.2.2.1 : ℤ) ^ 2 * (x.1 : ℤ) ^ 2) = ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
    ring)

theorem swap1_a4_lt_a (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), ((x.1 : ℤ) ^ 4)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.2.2.1 : ℤ) ^ 4) := by
  rw [sum_swap₁ N (fun x => ((x.1 : ℤ) ^ 4)) (fun x => x.1 < x.2.2.1)]
  exact Finset.sum_congr rfl (fun x _ => rfl)

theorem swap1_a4_lt_d (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), ((x.1 : ℤ) ^ 4)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.2.2.1 : ℤ) ^ 4) := by
  rw [sum_swap₁ N (fun x => ((x.1 : ℤ) ^ 4)) (fun x => x.2.2.2 < x.2.1)]
  exact Finset.sum_congr rfl (fun x _ => rfl)

theorem swap2_ac3_diag (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 = x.2.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.2.1 : ℤ) * (x.2.2.2 : ℤ) ^ 3) := by
  rw [sum_swap₂ N (fun x => ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) (fun x => x.2.2.2 = x.2.1),
    ← filter_diag_comm N]
  exact Finset.sum_congr rfl (fun x _ => rfl)

theorem swap2_a2c2_diag (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 = x.2.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
      = ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.2.1 : ℤ) ^ 2 * (x.2.2.2 : ℤ) ^ 2) := by
  rw [sum_swap₂ N (fun x => ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)) (fun x => x.2.2.2 = x.2.1),
    ← filter_diag_comm N]
  exact Finset.sum_congr rfl (fun x _ => rfl)

theorem swap2_a4_diag (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 = x.2.1), ((x.1 : ℤ) ^ 4)
      = ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.2.1 : ℤ) ^ 4) := by
  rw [sum_swap₂ N (fun x => ((x.1 : ℤ) ^ 4)) (fun x => x.2.2.2 = x.2.1), ← filter_diag_comm N]
  exact Finset.sum_congr rfl (fun x _ => rfl)

theorem slice_ac3_eq_slice_a4 (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.1 : ℤ) ^ 4) := by
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hx13 : x.1 = x.2.2.1 := (Finset.mem_filter.1 hx).2
  rw [← hx13]
  ring

theorem slice_a2c2_eq_slice_a4 (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
      = ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.1 : ℤ) ^ 4) := by
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hx13 : x.1 = x.2.2.1 := (Finset.mem_filter.1 hx).2
  rw [← hx13]
  ring

theorem weight6Identity_int (N : ℕ) :
    (240 * sigmaConv 1 3 N : ℤ)
      = 21 * sigma 5 N + (10 - 30 * N) * sigma 3 N - sigma 1 N := by

  have hs1 : ∑ x ∈ Sols N, ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
        + ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
        + ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3) :=
    sum_split N (fun x => ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) (fun x => x.2.2.1) (fun x => x.1)
  have hs2 : ∑ x ∈ Sols N, ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 = x.2.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3) :=
    sum_split N (fun x => ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)) (fun x => x.2.1) (fun x => x.2.2.2)
  have hs3 : ∑ x ∈ Sols N, ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
        + ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
        + ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) :=
    sum_split N (fun x => ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)) (fun x => x.2.2.1) (fun x => x.1)
  have hs4 : ∑ x ∈ Sols N, ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 = x.2.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2) :=
    sum_split N (fun x => ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2)) (fun x => x.2.1)
      (fun x => x.2.2.2)
  have hs5 : ∑ x ∈ Sols N, ((x.1 : ℤ) ^ 4)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 < x.1), ((x.1 : ℤ) ^ 4)
        + ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.1 : ℤ) ^ 4)
        + ∑ x ∈ (Sols N).filter (fun x => x.1 < x.2.2.1), ((x.1 : ℤ) ^ 4) :=
    sum_split N (fun x => ((x.1 : ℤ) ^ 4)) (fun x => x.2.2.1) (fun x => x.1)
  have hs6 : ∑ x ∈ Sols N, ((x.1 : ℤ) ^ 4)
      = ∑ x ∈ (Sols N).filter (fun x => x.2.1 < x.2.2.2), ((x.1 : ℤ) ^ 4)
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 = x.2.1), ((x.1 : ℤ) ^ 4)
        + ∑ x ∈ (Sols N).filter (fun x => x.2.2.2 < x.2.1), ((x.1 : ℤ) ^ 4) :=
    sum_split N (fun x => ((x.1 : ℤ) ^ 4)) (fun x => x.2.1) (fun x => x.2.2.2)

  have hw1 := swap1_ac3_lt_a N
  have hw2 := swap1_ac3_lt_d N
  have hw3 := swap1_a2c2_lt_a N
  have hw4 := swap1_a2c2_lt_d N
  have hw5 := swap1_a4_lt_a N
  have hw6 := swap1_a4_lt_d N

  have hd1 := swap2_ac3_diag N
  have hd2 := swap2_a2c2_diag N
  have hd3 := swap2_a4_diag N
  have hc1 := slice_ac3_eq_slice_a4 N
  have hc2 := slice_a2c2_eq_slice_a4 N

  have he1 := engine_ac3 N
  have he2 := engine_a2c2 N
  have he3 := engine_a3c N
  have he4 := engine_a4 N
  have he5 := engine_c4 N

  have h8T : 8 * ∑ x ∈ Sols N, ((x.1 : ℤ) * (x.2.2.1 : ℤ) ^ 3)
      = 2 * ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.2.1 : ℤ) ^ 4)
        + 4 * ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.2.1 : ℤ) * (x.2.2.2 : ℤ) ^ 3)
        + 3 * ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1),
            ((x.2.1 : ℤ) ^ 2 * (x.2.2.2 : ℤ) ^ 2)
        - ∑ x ∈ (Sols N).filter (fun x => x.1 = x.2.2.1), ((x.1 : ℤ) ^ 4) := by
    linear_combination 4 * hs1 + 4 * hs2 - 3 * hs3 + 3 * hs4 - 2 * hs5 + 2 * hs6
      + 4 * hw1 + 4 * hw2 - 3 * hw3 + 3 * hw4 - 2 * hw5 + 2 * hw6
      + 4 * hd1 + 3 * hd2 + 2 * hd3 + 4 * hc1 - 3 * hc2
      - 4 * he1 - 6 * he2 - 4 * he3 - 2 * he4 - 2 * he5

  have hbridge := sum_ac3_eq_sigmaConv N
  have ha4 := slice_a4 N
  have hb4 := slice_b4 N
  have hbd3 := slice_bd3 N
  have hb2d2 := slice_b2d2 N

  linear_combination 30 * h8T - 240 * hbridge - 30 * ha4 + 2 * hb4 + 2 * hbd3 + 3 * hb2d2

theorem weight6Identity (N : ℕ) : Weight6Identity N :=
  (weight6Identity_iff_int N).mpr (weight6Identity_int N)

end Weight6Certificate
end DivisorConvolution
end FLT


