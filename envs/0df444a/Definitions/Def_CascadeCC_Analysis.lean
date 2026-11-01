-- Prove2me | Definitions.Def_CascadeCC_Analysis
-- name    : CascadeCC_Analysis
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:34.270907+00:00
-- url     : https://prove2.me/theorems/d2a3491f-b7f8-4f4f-ba97-ca33f4369664
-- title:
--   Objects of the proof of Theorem 3: $R^D$, $Q$, $\delta^\sigma$, $\epsilon$, admissible thresholds, $\tau$, $\Phi_1$, $\Phi_2$
-- statement:
--   These are the objects of the appendix analysis.
--
--   1. **Revenue-to-go.** For $n$ periods, a product $j$, arrival rates $\sigma\in\mathbb R^n$ and inventories $z$,
--   $$
--   R^D_j(\sigma,z)=\sup\Bigl\{\sum_t\sigma_tr_j(\alpha_t)+R^D_{j+1}\bigl(\sigma\zeta_j-\zeta_j\sigma\circ\alpha,\ z-\bigl(\sum_t\sigma_t\alpha_t\bigr)e_j\bigr):\ \alpha\in[0,u]^n,\ \sum_t\sigma_t\alpha_t\le z_j\Bigr\},
--   $$
--   with $R^D_{J+1}=0$. With $z=y$ this is $W_j$.
--   2. **The constant $Q=\|-A^{-1}M^{-1}\|_\infty$**, explicitly $Q=\max_j\sum_{i<j}\prod_{i\le m<j}\zeta_m$, the same matrix norm written out from (15).
--   3. **Deviations.** At a correction $\delta$, $\delta^\sigma_j=\hat\sigma_j-\sigma_j(a)$ and $\epsilon_j=\hat\alpha_j-a_j$.
--   4. **Admissible threshold.** $\varphi$ is admissible for $a$ if $0<\varphi$ and, for all $j$, $\varphi\le v^D_j$, $Q\varphi\le\sigma^D_j$, and $(1+Q)\varphi\le\sigma^D_j(u-a_j)$.
--   5. **The stopping time.** $\tau$ is the first period $t\le N$ with $\|\delta^v_t\|_\infty\ge\hat\varphi$, and $N$ if there is none.
--   6. **Stopped quantities.** $R^{k,CC}(1,\tau-1)$ is the realized revenue before $\tau$, and
--   $$
--   \Phi_1=\mathbf E\Bigl[\sum_{t<\tau}\sum_j\sigma^D_jr_j(a_j+\epsilon_{tj})\Bigr],\qquad \Phi_2=\mathbf E\Bigl[\sum_{t<\tau}\sum_j\delta^\sigma_{tj}r_j(a_j+\epsilon_{tj})\Bigr],
--   $$
--   the expectation being under the law of the Cascade Correction policy.
--
--   The goal does not mention these objects. They are the vocabulary of the milestones.
--
--   **Formalization Note** The product index of `Rev` is a natural number and the recursion runs on $J-j$; `Rev` is a real `sSup`, nonempty and bounded above on $\sigma,z\ge0$ (proved in the verification file). `IsAdmissible` replaces (EC.32)–(EC.35), which as printed force $\varphi=0$ at $\lambda=1$ and leave $Q^{-1}$ undefined at $J=1$; (EC.32) is not needed, and the admissible set is nonempty when $\lambda>0$ and $a\in(0,u)^J$ (also proved there). `Q` is a supremum over the finite type `Fin J`, which is $0$ for $J\le1$. `tau` is 1-based; `delta … ω s` is $\delta^v_{s+1}$.
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, (EC.20), p.ec4; (EC.28), p.ec7; Q and (EC.32)–(EC.35), p.ec10; Step 2, p.ec11; Step 3, pp.ec11–12; (15), p.24

import Mathlib
import Definitions.Def_CascadeCC_CCPolicy

namespace CascadeCC

variable {J : ℕ}

/-- The deterministic revenue-to-go R^D_tj(σ_j, z) of (EC.20), from product `j` over `n` remaining periods
with arrival rates `σ` and inventories `z` (Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, §EC.4, p.ec4):
the supremum over rates α ∈ [0, u]^n with ∑_t σ_t α_t ≤ z_j of
∑_t σ_t r_j(α_t) + R^D_{t,j+1}(σ ζ_j − ζ_j σ ∘ α, z − (∑_t σ_t α_t) e_j), and 0 past the last product.

**Formalization Note** With n = T − t + 1 the period `t` disappears. The product index `j` is a natural
number, 0-based, and the recursion runs on `J - j`. W_j(σ) of (EC.28), p.ec7, is `Rev M T j σ y`. The
paper's `max` is a real `sSup` here, nonempty and bounded above on σ, z ≥ 0
(`Solutions/verification/CascadeCC_Bounds.lean`). -/
noncomputable def Rev (M : Instance J) (n j : ℕ) (σ : Fin n → ℝ) (z : Fin J → ℝ) : ℝ :=
  if h : j < J then
    sSup ((fun α : Fin n → ℝ =>
        ∑ t, σ t * M.r ⟨j, h⟩ (α t) +
          Rev M n (j + 1) (fun t => σ t * M.zeta ⟨j, h⟩ - M.zeta ⟨j, h⟩ * σ t * α t)
            (Function.update z ⟨j, h⟩ (z ⟨j, h⟩ - ∑ t, σ t * α t))) ''
      {α | (∀ t, α t ∈ Set.Icc 0 M.u) ∧ ∑ t, σ t * α t ≤ z ⟨j, h⟩})
  else 0
termination_by J - j
decreasing_by omega

/-- The row `j` of the matrix −A⁻¹M⁻¹ of (15), summed: ∑_{i<j} ∏_{i≤m<j} ζ_m. -/
noncomputable def qRow (M : Instance J) (j : Fin J) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin J => i < j),
    ∏ m ∈ Finset.univ.filter (fun m : Fin J => i ≤ m ∧ m < j), M.zeta m

/-- The constant Q = ‖−A⁻¹M⁻¹‖_∞ (SSRN abstract_id=3362921, p.ec10).

**Formalization Note** From (15), p.24, the inverse is explicit, A⁻¹_ij = ∏_{k=j+1}^i ζ_k for j ≤ i, and
−M⁻¹ = diag(ζ_j), so the row sums of the norm are `qRow`, with the indices shifted so that the row of
σ_{j} is `j`. The supremum is over the finite type `Fin J`, and is 0 when J = 0 or J = 1. -/
noncomputable def Q (M : Instance J) : ℝ := ⨆ j : Fin J, qRow M j

/-- The arrival deviation δ^σ_tj = σ̂_tj − σ^D_j (SSRN abstract_id=3362921, p.25) at correction `δ`. -/
noncomputable def arrivalDev (M : Instance J) (a δ : Fin J → ℝ) (j : Fin J) : ℝ :=
  hatArrival M (hatPurchase M a δ) j - arrival M a j

/-- The rate deviation ϵ_tj = α̂_tj − a_j (SSRN abstract_id=3362921, p.ec12) at correction `δ`. -/
noncomputable def rateDev (M : Instance J) (a δ : Fin J → ℝ) (j : Fin J) : ℝ :=
  hatRate M a δ j - a j

/-- `φ` is an admissible threshold for `a`: 0 < φ, φ ≤ v^D_j, Q φ ≤ σ^D_j, and (1 + Q) φ ≤ σ^D_j (u − a_j).

**Formalization Note** This replaces (EC.32)–(EC.35), p.ec10 (SSRN abstract_id=3362921), which cannot stand as
printed: (EC.34) forces φ = 0 when σ^D_1 = λ = 1, Q⁻¹ is undefined at J = 1, and (EC.35) proves α̂ < 1, not
α̂ ≤ u. (EC.32) is not needed, because the inventory is handled by the exact formula of `lemma_EC2`. The condition
Q φ ≤ σ^D_j is the counterpart of (EC.34); it follows from the last one when 0 ≤ a_j, and is kept as the page has it. The
multiplicative forms stay meaningful at Q = 0. -/
def IsAdmissible (M : Instance J) (a : Fin J → ℝ) (φ : ℝ) : Prop :=
  0 < φ ∧ (∀ j, φ ≤ purchase M a j) ∧ (∀ j, Q M * φ ≤ arrival M a j) ∧
    ∀ j, (1 + Q M) * φ ≤ arrival M a j * (M.u - a j)

/-- The correction δ^v_{s+1} on a path `ω`: its value at the beginning of the period with `s` earlier
periods (1-based period t = s + 1). -/
noncomputable def delta (M : Instance J) (N : ℕ) (Y : Fin J → ℕ) (a : Fin J → ℝ)
    (ω : Fin N → Option (Fin J)) (s : ℕ) : Fin J → ℝ :=
  (ccState M N Y a (pathPrefix ω s)).corr

/-- The expectation under the law of the Cascade Correction policy. -/
noncomputable def ccExpect (M : Instance J) (N : ℕ) (Y : Fin J → ℕ) (a : Fin J → ℝ)
    (f : (Fin N → Option (Fin J)) → ℝ) : ℝ :=
  pathExpect (outcomeProb M) (ccPolicy M N Y a) f

open scoped Classical in
/-- The stopping time τ^k, the 1-based first period t ≤ N with ‖δ^v_t‖_∞ ≥ φ̂, and N if there is none
(SSRN abstract_id=3362921, Step 2, p.ec11).

**Formalization Note** The witness `s` is t − 1, so `tau` is 1-based, as in the paper. -/
noncomputable def tau (M : Instance J) (N : ℕ) (Y : Fin J → ℕ) (a : Fin J → ℝ) (φ : ℝ)
    (ω : Fin N → Option (Fin J)) : ℕ :=
  if h : ∃ s, s < N ∧ φ ≤ ‖delta M N Y a ω s‖ then Nat.find h + 1 else N

open scoped Classical in
/-- The sum of `g s` over the periods before τ: ∑_{t=1}^{τ−1}, with the 1-based period t = s + 1. -/
noncomputable def sumBeforeTau (M : Instance J) (N : ℕ) (Y : Fin J → ℕ) (a : Fin J → ℝ) (φ : ℝ)
    (ω : Fin N → Option (Fin J)) (g : Fin N → ℝ) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin N => s.1 + 1 < tau M N Y a φ ω), g s

/-- The realized revenue R^{k,CC}(1, τ − 1) of the Cascade Correction policy in the periods before τ
(SSRN abstract_id=3362921, Step 3, p.ec11). -/
noncomputable def stoppedRevenue (M : Instance J) (N : ℕ) (Y : Fin J → ℕ) (a : Fin J → ℝ) (φ : ℝ)
    (ω : Fin N → Option (Fin J)) : ℝ :=
  sumBeforeTau M N Y a φ ω fun s =>
    periodRevenue M (ccPolicy M N Y a (pathPrefix ω s)) (ω s)

/-- The term Φ₁ = E[∑_{t<τ} ∑_j σ^D_j r_j(a_j + ϵ_tj)] (SSRN abstract_id=3362921, p.ec12). -/
noncomputable def Phi1 (M : Instance J) (N : ℕ) (Y : Fin J → ℕ) (a : Fin J → ℝ) (φ : ℝ) : ℝ :=
  ccExpect M N Y a fun ω => sumBeforeTau M N Y a φ ω fun s =>
    ∑ j, arrival M a j * M.r j (a j + rateDev M a (delta M N Y a ω s) j)

/-- The term Φ₂ = E[∑_{t<τ} ∑_j δ^σ_tj r_j(a_j + ϵ_tj)] (SSRN abstract_id=3362921, p.ec12). -/
noncomputable def Phi2 (M : Instance J) (N : ℕ) (Y : Fin J → ℕ) (a : Fin J → ℝ) (φ : ℝ) : ℝ :=
  ccExpect M N Y a fun ω => sumBeforeTau M N Y a φ ω fun s =>
    ∑ j, arrivalDev M a (delta M N Y a ω s) j *
      M.r j (a j + rateDev M a (delta M N Y a ω s) j)

end CascadeCC


