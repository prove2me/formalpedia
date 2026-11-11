-- Prove2me | Definitions.Def_OrderSelProphet_Kernel_Profiles
-- name    : OrderSelProphet_Kernel_Profiles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:56:28.48618+00:00
-- url     : https://prove2.me/theorems/9b508715-ee65-4aa1-bf0f-fbdb3422b960
-- title:
--   Profiles, $A_\lambda$ (38), local constructions (Def. 3.1), allocation kernels (Def. 3.3), $B_{K,\lambda}$ (16), the load $\ell_\Gamma(K,\lambda)$ (19), the kernel construction
-- statement:
--   - A **profile** is a measurable $\lambda:\mathbb R\to\mathbb R$ with values in $[0,1]$ on $[0,1]$ (the paper's $\Lambda$, up to a.e. equality).
--   - For $0\le u<1$: $h_\lambda(u)=\int_0^u\frac{\lambda(a)}{1-a}da$, $C_\lambda(u)=\int_0^u\lambda$, $x_\lambda(u)=1-(1-u)e^{h_\lambda(u)}$, $x_\lambda(1)=1$, $\mu_\lambda=\int_0^1\lambda$ (12).
--   - **Area curve of a profile** (38): $A_\lambda(x)=\int_0^1(x-x_\lambda(s))_+\frac{\lambda(s)}{1-s}e^{-h_\lambda(s)}ds$, defined for every profile.
--   - $\lambda$ is **the profile of item $i$** (10): $P(I^*=i,\,U\le u)=\int_0^u\lambda$ for $u\in[0,1]$, where $U=1-F_{\max}(\mathrm{OPT})$, $F_{\max}=\prod_jF_j$, under the product law; "$I^*=i$" is "$V_i\ge V_j$ for all $j$".
--   - $\mathcal A$ (`AreaClass`): restrictions to $[0,1]$ of the area curves $A_i$ of items of atomless inputs.
--   - **Local construction** (Def. 3.1): a functional $\mathfrak B$ on functions $[0,1]\to\mathbb R$ such that for $A\in\mathcal A$, $\mathfrak B[A]$ is nondecreasing on $[0,1]$ with values in $[0,A(1)]$, $\mathfrak B[A](0)=0$, $\mathfrak B[A](1)=A(1)$ (7), and $\sum_i\mathfrak B[A_i](t)=t$ on $[0,1]$ for every atomless input (8).
--   - **Allocation kernel** (Def. 3.3): $K(t,u)$ jointly measurable on $[0,1]^2$ with values in $[0,1]$; for a.e. $u\in[0,1]$, $K(\cdot,u)$ nondecreasing and right-continuous on $[0,1]$ with $K(0,u)=0$, $K(1,u)=1$; and $\int_0^1K(t,u)du=t$ for all $t\in[0,1]$ (15).
--   - $B_{K,\lambda}(t)=\int_0^1\lambda(u)K(t,u)du$ (16); $K$ **represents** $\mathfrak B$ if $\mathfrak B[A_\lambda](t)=B_{K,\lambda}(t)$ for every profile and $t\in[0,1]$ (17).
--   - $y_{K,\lambda}=A_\lambda^{\leftarrow}\circ B_{K,\lambda}$, $S_{K,\lambda}$ and the **single-profile load** $\ell_\Gamma(K,\lambda)=L_\Gamma(A_\lambda,B_{K,\lambda})$ (18)–(19), in $[0,\infty]$.
--   - **Kernel construction on an input**: $B_i(t)=\mathbb E[\mathbf 1\{I^*=i\}K(t,U)]$ ($=\int\lambda_iK$ by (10)), its load $L_i=L_\Gamma(A_i,B_i)$, thresholds $y_i$, arrival laws $G_i$, the accepted index, and a run of it (`IsKernelRun`).
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), §3, pp. 9–12; §4.1, pp. 12–13; eq. (38), pp. 18 and 39

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-! # Profiles, area curves, local constructions and allocation kernels

Peng and Tang (2026), arXiv:2610.34892, §3 (pp. 9–12), §4.1 (pp. 12–13) and Appendix B (p. 39). -/

/-- A **profile** (§3.1, p. 10): a measurable function with values in `[0,1]` on `[0,1]`. Profiles
are functions `ℝ → ℝ`; their values outside `[0,1]` are never used. The paper's `Λ` identifies
profiles that agree almost everywhere; every quantity below depends only on that class. -/
def Profile : Type :=
  {lam : ℝ → ℝ // Measurable lam ∧ ∀ u ∈ Icc (0 : ℝ) 1, lam u ∈ Icc (0 : ℝ) 1}

/-- `h_λ(u) = ∫_0^u λ(a)/(1-a) da` (eq. (12), p. 10), for `0 ≤ u < 1`. -/
noncomputable def hP (lam : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ a in (0 : ℝ)..u, lam a / (1 - a)

/-- `C_λ(u) = ∫_0^u λ(a) da` (eq. (12), p. 10). -/
noncomputable def CP (lam : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ a in (0 : ℝ)..u, lam a

/-- `x_λ(u) = 1 - (1-u) e^{h_λ(u)}` for `u < 1` (eq. (12), p. 10), and `x_λ(1) := 1`
(Appendix B, p. 38). -/
noncomputable def xP (lam : ℝ → ℝ) (u : ℝ) : ℝ :=
  if u < 1 then 1 - (1 - u) * Real.exp (hP lam u) else 1

/-- `μ_λ = ∫_0^1 λ(a) da` (eq. (12), p. 10). -/
noncomputable def muP (lam : ℝ → ℝ) : ℝ :=
  ∫ a in (0 : ℝ)..1, lam a

/-- The **area curve of a profile** (eq. (38), p. 18 and p. 39), defined for every profile:
`A_λ(x) = ∫_0^1 (x - x_λ(s))_+ λ(s)/(1-s) e^{-h_λ(s)} ds`. -/
noncomputable def areaP (lam : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, max (x - xP lam s) 0 * (lam s / (1 - s)) * Real.exp (-hP lam s)

/-- The restriction of a function to `[0,1]`: area curves are functions on `[0,1]`. -/
def onUnit (A : ℝ → ℝ) : Icc (0 : ℝ) 1 → ℝ :=
  fun x => A x

/-- Item `i` **is the maximum** at the value vector `v`. Ties have probability zero for atomless
inputs. -/
def IsMaxAt {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : Prop :=
  ∀ j, v j ≤ v i

/-- `F_max(x) = ∏_j F_j(x)` (§3.1, p. 9). -/
noncomputable def Fmax {n : ℕ} (F : Fin n → Measure ℝ) (x : ℝ) : ℝ :=
  ∏ j, distFn (F j) x

/-- `λ` is a **winning-probability profile** of item `i` (eq. (10), p. 9): for every `u ∈ [0,1]`,
`P(I* = i, U ≤ u) = ∫_0^u λ(a) da`, where the values are independent with laws `F j`,
`I*` is the index of the maximum and `U = 1 - F_max(OPT)` is the maximum rank (9). -/
def IsProfileOf {n : ℕ} (F : Fin n → Measure ℝ) [∀ i, SigmaFinite (F i)] (i : Fin n)
    (lam : ℝ → ℝ) : Prop :=
  ∀ u ∈ Icc (0 : ℝ) 1,
    (Measure.pi F {v | IsMaxAt v i ∧ 1 - Fmax F (v i) ≤ u}).toReal = ∫ a in (0 : ℝ)..u, lam a

/-- The class `𝒜` of **item area curves** arising from inputs (§3, p. 9): the restrictions to
`[0,1]` of the area curves `A_i` of the items of atomless inputs (`n ≥ 1` independent
nonnegative atomless values). -/
def AreaClass : Set (Icc (0 : ℝ) 1 → ℝ) :=
  {A | ∃ (n : ℕ) (F : Fin n → Measure ℝ) (_ : ∀ i, IsProbabilityMeasure (F i)),
    IsAtomlessInput F ∧ ∃ i, A = onUnit (inputArea F i)}

/-- A **local construction** (Definition 3.1, p. 9): a functional `𝔅` assigning to every area
curve `A ∈ 𝒜` an allocation `𝔅[A]` that is nondecreasing on `[0,1]` with values in `[0, A(1)]`,
`𝔅[A](0) = 0`, `𝔅[A](1) = A(1)` (7), and such that on every atomless input the
total-allocation identity `∑_i 𝔅[A_i](t) = t` holds for all `t ∈ [0,1]` (8). The functional sees
only the area curve, not the item label, `n`, or the other curves. -/
def IsLocalConstruction (𝔅 : (Icc (0 : ℝ) 1 → ℝ) → ℝ → ℝ) : Prop :=
  (∀ A ∈ AreaClass, MonotoneOn (𝔅 A) (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ 𝔅 A t ∧ 𝔅 A t ≤ A ⟨1, by norm_num⟩) ∧
      𝔅 A 0 = 0 ∧ 𝔅 A 1 = A ⟨1, by norm_num⟩) ∧
    ∀ (n : ℕ) (F : Fin n → Measure ℝ) (_ : ∀ i, IsProbabilityMeasure (F i)), IsAtomlessInput F →
      ∀ t ∈ Icc (0 : ℝ) 1, ∑ i, 𝔅 (onUnit (inputArea F i)) t = t

/-- An **allocation kernel** (Definition 3.3, pp. 10–11): `K : [0,1]² → [0,1]` (written
`K t u`), jointly measurable on `[0,1]²`, such that for almost every `u ∈ [0,1]` the function
`K(·, u)` is nondecreasing and right-continuous on `[0,1]` with `K(0,u) = 0` and `K(1,u) = 1`,
and `∫_0^1 K(t,u) du = t` for every `t ∈ [0,1]` (15). Values outside `[0,1]²` are not used. -/
def IsAllocationKernel (K : ℝ → ℝ → ℝ) : Prop :=
  Measurable (fun p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 => K p.1 p.2) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1, K t u ∈ Icc (0 : ℝ) 1) ∧
    (∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) 1)),
      MonotoneOn (fun t => K t u) (Icc 0 1) ∧
        (∀ t ∈ Ico (0 : ℝ) 1, ContinuousWithinAt (fun s => K s u) (Ici t) t) ∧
        K 0 u = 0 ∧ K 1 u = 1) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ∫ u in (0 : ℝ)..1, K t u = t

/-- The allocation induced by a kernel (eq. (16), p. 11): `B_{K,λ}(t) = ∫_0^1 λ(u) K(t,u) du`. -/
noncomputable def allocK (K : ℝ → ℝ → ℝ) (lam : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, lam u * K t u

/-- A kernel **represents** a functional (eq. (17), p. 11):
`𝔅[A_λ](t) = B_{K,λ}(t)` for every profile `λ` and every `t ∈ [0,1]`. -/
def Represents (K : ℝ → ℝ → ℝ) (𝔅 : (Icc (0 : ℝ) 1 → ℝ) → ℝ → ℝ) : Prop :=
  ∀ lam : Profile, ∀ t ∈ Icc (0 : ℝ) 1, 𝔅 (onUnit (areaP lam.1)) t = allocK K lam.1 t

/-- The threshold path of a profile (eq. (18), p. 12): `y_{K,λ} = A_λ^← ∘ B_{K,λ}`. -/
noncomputable def yK (K : ℝ → ℝ → ℝ) (lam : ℝ → ℝ) (t : ℝ) : ℝ :=
  threshold (areaP lam) (allocK K lam) t

/-- The survival factor of a profile (eq. (18), p. 12):
`S_{K,λ}(t) = exp(-Γ ∫_0^t dB_{K,λ}(s) / (1 - Γ s))`. -/
noncomputable def SK (Γ : ℝ) (K : ℝ → ℝ → ℝ) (lam : ℝ → ℝ) (t : ℝ) : ℝ :=
  itemSurvival Γ (allocK K lam) t

/-- The **single-profile load** (eq. (19), p. 12):
`ℓ_Γ(K, λ) = L_Γ(A_λ, B_{K,λ}) = Γ ∫_{(0,1]} S_{K,λ}(t)/S(t) dy_{K,λ}(t)`. -/
noncomputable def loadK (Γ : ℝ) (K : ℝ → ℝ → ℝ) (lam : ℝ → ℝ) : ℝ≥0∞ :=
  loadL Γ (areaP lam) (allocK K lam)

/-- The kernel allocation of item `i` of an input (eq. (16) applied to the item's profile `λ_i`,
Figure 2, p. 12): `B_i(t) = ∫_0^1 λ_i(u) K(t,u) du = E[1{I* = i} K(t, U)]` with
`U = 1 - F_max(OPT)`; the second form, used here, is the first rewritten by (10). -/
noncomputable def inputAlloc (K : ℝ → ℝ → ℝ) {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (F i)] (i : Fin n) (t : ℝ) : ℝ := by
  classical
  exact ∫ v, (if IsMaxAt v i then K t (1 - Fmax F (v i)) else 0) ∂(Measure.pi F)

/-- The arrival load of item `i` under the kernel construction: `L_i = L_Γ(A_i, B_i)` (6). -/
noncomputable def inputLoad (Γ : ℝ) (K : ℝ → ℝ → ℝ) {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (F i)] (i : Fin n) : ℝ≥0∞ :=
  loadL Γ (inputArea F i) (inputAlloc K F i)

/-- The thresholds `y_i = A_i^← ∘ B_i` of the kernel construction on an input. -/
noncomputable def inputThreshold (K : ℝ → ℝ → ℝ) {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (F i)] (i : Fin n) (t : ℝ) : ℝ :=
  threshold (inputArea F i) (inputAlloc K F i) t

/-- The arrival laws `G_i` (5) of the kernel construction at ratio `Γ` on an input. -/
noncomputable def inputArrivalLaw (Γ : ℝ) (K : ℝ → ℝ → ℝ) {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (F i)] (i : Fin n) : Measure (WithTop ℝ) :=
  arrivalLaw Γ (inputArea F i) (inputAlloc K F i)

/-- The accepted index of the **kernel arrival construction** (Figure 2, p. 12) at ratio `Γ` with
kernel `K` on input `F`, for realized arrival times `T` and values `V`: the first arrived item
`i` with `U_i ≤ y_i(T_i)`. -/
noncomputable def kernelIndex (K : ℝ → ℝ → ℝ) {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (F i)] (T : Fin n → WithTop ℝ) (V : Fin n → ℝ) : Option (Fin n) :=
  runIndex F (inputThreshold K F) T V

/-- A probability space carrying the **kernel arrival construction** at ratio `Γ` with kernel `K`
on input `F` (§2.1 step 1, eq. (5)): independent values with laws `F i` and independent arrival
times with the laws `G_i` of the construction. -/
def IsKernelRun {Ω : Type*} [MeasurableSpace Ω] (Γ : ℝ) (K : ℝ → ℝ → ℝ) {n : ℕ}
    (F : Fin n → Measure ℝ) [∀ i, SigmaFinite (F i)] (P : Measure Ω) (V : Fin n → Ω → ℝ)
    (T : Fin n → Ω → WithTop ℝ) : Prop :=
  IsArrivalRun P V T F (inputArrivalLaw Γ K F)

end OrderSelProphet.Kernel


