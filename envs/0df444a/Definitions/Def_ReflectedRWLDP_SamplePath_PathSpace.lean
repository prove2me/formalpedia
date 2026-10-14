-- Prove2me | Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
-- name    : ReflectedRWLDP_SamplePath_PathSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:33:52.032985+00:00
-- url     : https://prove2.me/theorems/211a4e1c-051e-45ba-913f-738c17e208f0
-- title:
--   Definitions 2.1–2.2, pp. 5–6 — the Skorokhod space $\mathbb D[0,T]$, the extended completed graph $\Gamma'(\xi)$, the $M_1'$ metric, pure jump paths and $\mathbb D^{(\lambda)}[0,T]$
-- statement:
--   This file sets up the path space of Bazhba, Blanchet, Rhee and Zwart.
--
--   **Càdlàg paths.** $\mathbb D[0,T]$ is the Skorokhod space of càdlàg paths $\xi:[0,T]\to\mathbb R$: right-continuous at every $t\in[0,T)$, with a left limit $\xi(t-)$ at every $t\in(0,T]$. At the origin the paper uses the convention $\xi(0-)=0$.
--
--   **Extended completed graph (Definition 2.1).** For $\xi\in\mathbb D[0,T]$,
--   $$\Gamma'(\xi)=\{(u,t)\in\mathbb R\times[0,T] : u\in[\xi(t-)\wedge\xi(t),\ \xi(t-)\vee\xi(t)]\},\qquad \xi(0-)=0 .$$
--   It is ordered by $(u_1,t_1)<(u_2,t_2)$ if $t_1<t_2$, or $t_1=t_2$ and $|\xi(t_1-)-u_1|<|\xi(t_2-)-u_2|$. A **parametrization** of $\xi$ is a continuous map $s\mapsto(u(s),t(s))$ from $[0,T]$ onto $\Gamma'(\xi)$ that is nondecreasing for this order; $\Pi'(\xi)$ is the set of all parametrizations.
--
--   **The $M_1'$ metric (Definition 2.2).**
--   $$d_{M_1'}(\xi,\zeta)=\inf_{(u,t)\in\Pi'(\xi),\ (v,r)\in\Pi'(\zeta)}\big\{\|u-v\|_\infty+\|t-r\|_\infty\big\}.$$
--   The topology $\mathcal T_{M_1'}$ has as open sets those that contain a $d_{M_1'}$-ball around each of their points.
--
--   **Pure jump paths (p. 5) and $\mathbb D^{(\lambda)}[0,T]$ (p. 6).** $\mathbb D^{\uparrow}_{\leqslant\infty}[0,T]$ is the set of non-decreasing pure jump paths $\zeta=\sum_i x_i\mathbb 1_{[u_i,T]}$ with $\zeta(0)\ge 0$, and
--   $$\mathbb D^{(\lambda)}[0,T]=\{\xi\in\mathbb D[0,T] : \xi(t)=\lambda t+\zeta(t)\ \forall t\in[0,T],\ \zeta\in\mathbb D^{\uparrow}_{\leqslant\infty}[0,T]\},$$
--   the increasing paths with slope $\lambda$ and countably many upward jumps. The file also defines the jump power sum $\sum_{t:\zeta(t)\neq\zeta(t-)}(\zeta(t)-\zeta(t-))^\alpha$, with $\zeta(0-)=0$ so that a jump at time $0$ counts, and the step paths $t\mapsto h(\lfloor nt\rfloor)$ in $\mathbb D[0,1]$.
--
--   These objects are the state space and the metric of the paper's sample-path large deviation principle (Theorem 2.1).
--
--   **Formalization Note** A path of $\mathbb D[0,T]$ is a function $\mathbb R\to\mathbb R$ that is càdlàg on $[0,T]$ and constant outside $[0,T]$ (equal to $\xi(0)$ on $(-\infty,0)$ and to $\xi(T)$ on $(T,\infty)$), so equality of paths is equality on $[0,T]$. $\xi(t-)$ is `Function.leftLim` for $t\neq0$ and $0$ at $t=0$. A point of $\Gamma'(\xi)$ is the pair `(u, t)`, space first. "Nondecreasing" uses the reflexive closure of the printed strict order. Parametrizations are pairs of functions on $\mathbb R$ restricted to $[0,T]$; $d_{M_1'}$ takes values in $[0,\infty]$, with $\|\cdot\|_\infty$ the supremum over $[0,T]$. A non-decreasing path is pure jump when $\zeta(t)$ equals the sum of its jumps over $[0,t]$ for every $t$; this is how $\mathbb D^{\uparrow}_{\leqslant\infty}[0,T]$ is stated. The step path $t\mapsto h(\lfloor n\,(0\vee t\wedge 1)\rfloor)$ comes with a proof that it is càdlàg.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, pp. 5–6, §2.1 Definitions 2.1 and 2.2, pure jump paths and 𝔻^{(λ)}[0,T]

import Mathlib

namespace ReflectedRWLDP.SamplePath

open Set Filter Topology
open scoped ENNReal

/-!
Bazhba, Blanchet, Rhee & Zwart, arXiv:2003.14381v3, §2.1 (p. 5) and §2.2 (p. 6): the Skorokhod
space `𝔻[0,T]`, the extended completed graph `Γ′(ξ)` with the convention `ξ(0−) = 0`
(Definition 2.1), its parametrizations `Π′(ξ)`, the `M₁′` metric (Definition 2.2), non-decreasing
pure jump paths `𝔻^↑_{⩽∞}[0,T]`, the subspace `𝔻^{(λ)}[0,T]`, and the step paths that the
processes `Ȳ_n`, `Z̄_n`, `S̄_n` of the paper are.
-/

/-- `f` represents a path of `𝔻[0,T]`: it is right-continuous at every `t ∈ [0,T)`, has a left
limit at every `t ∈ (0,T]`, and is extended constantly outside `[0,T]` (`f t = f 0` for `t < 0`,
`f t = f T` for `t > T`), so that two such functions are equal iff they agree on `[0,T]`. -/
def IsDPath (T : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ t ∈ Ico 0 T, ContinuousWithinAt f (Ici t) t) ∧
  (∀ t ∈ Ioc 0 T, ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) ∧
  (∀ t : ℝ, t < 0 → f t = f 0) ∧
  (∀ t : ℝ, T < t → f t = f T)

/-- The Skorokhod space `𝔻[0,T]` of càdlàg paths `[0,T] → ℝ` (p. 5), each path stored with its
constant extension outside `[0,T]`. -/
def DPath (T : ℝ) : Type := {f : ℝ → ℝ // IsDPath T f}

instance (T : ℝ) : CoeFun (DPath T) (fun _ => ℝ → ℝ) := ⟨Subtype.val⟩

/-- The left limit `ξ(t−)` with the paper's convention `ξ(0−) ≜ 0` (Definition 2.1). For
`t ∈ (0,T]` it is the left limit of the càdlàg path. -/
noncomputable def leftLim0 (ξ : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t = 0 then 0 else Function.leftLim ξ t

/-- The extended completed graph (Definition 2.1)
`Γ′(ξ) = {(u,t) ∈ ℝ × [0,T] : u ∈ [ξ(t−) ∧ ξ(t), ξ(t−) ∨ ξ(t)]}`, with `ξ(0−) = 0`.
A point is a pair `(u, t)`: first the space coordinate, then the time coordinate. -/
def extGraph {T : ℝ} (ξ : DPath T) : Set (ℝ × ℝ) :=
  {q | q.2 ∈ Icc 0 T ∧
    q.1 ∈ Icc (min (leftLim0 ξ q.2) (ξ q.2)) (max (leftLim0 ξ q.2) (ξ q.2))}

/-- The strict order on `Γ′(ξ)` (Definition 2.1): `(u₁,t₁) < (u₂,t₂)` if `t₁ < t₂`, or `t₁ = t₂` and
`|ξ(t₁−) − u₁| < |ξ(t₂−) − u₂|`. -/
def graphLT {T : ℝ} (ξ : DPath T) (q₁ q₂ : ℝ × ℝ) : Prop :=
  q₁.2 < q₂.2 ∨
    (q₁.2 = q₂.2 ∧ |leftLim0 ξ q₁.2 - q₁.1| < |leftLim0 ξ q₂.2 - q₂.1|)

/-- The reflexive closure of `graphLT` ("`<` or equal"), the order for which a parametrization is
nondecreasing. -/
def graphLE {T : ℝ} (ξ : DPath T) (q₁ q₂ : ℝ × ℝ) : Prop :=
  q₁ = q₂ ∨ graphLT ξ q₁ q₂

/-- `(u, t)` is a parametrization of `Γ′(ξ)` (Definition 2.1): `s ↦ (u(s), t(s))` is continuous on
`[0,T]`, maps `[0,T]` onto `Γ′(ξ)`, and is nondecreasing for the order of `Γ′(ξ)`. The set of all
such pairs is `Π′(ξ)`. -/
def IsParam {T : ℝ} (ξ : DPath T) (u t : ℝ → ℝ) : Prop :=
  ContinuousOn u (Icc 0 T) ∧ ContinuousOn t (Icc 0 T) ∧
  (fun s => (u s, t s)) '' Icc 0 T = extGraph ξ ∧
  ∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T, s₁ ≤ s₂ →
    graphLE ξ (u s₁, t s₁) (u s₂, t s₂)

/-- The uniform distance `‖f − g‖_∞` over `s ∈ [0,T]`, in `[0, ∞]`. -/
noncomputable def supDist (T : ℝ) (f g : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ s ∈ Icc (0 : ℝ) T, ENNReal.ofReal |f s - g s|

/-- The `M₁′` metric (Definition 2.2):
`d_{M₁′}(ξ, ζ) = inf_{(u,t) ∈ Π′(ξ), (v,r) ∈ Π′(ζ)} {‖u − v‖_∞ + ‖t − r‖_∞}`, with values in
`[0, ∞]` (an empty infimum is `∞`). -/
noncomputable def dM1 {T : ℝ} (ξ ζ : DPath T) : ℝ≥0∞ :=
  ⨅ (u : ℝ → ℝ) (t : ℝ → ℝ) (v : ℝ → ℝ) (r : ℝ → ℝ) (_ : IsParam ξ u t) (_ : IsParam ζ v r),
    supDist T u v + supDist T t r

/-- Pointwise sum of two càdlàg paths. -/
def DPath.add {T : ℝ} (ξ ζ : DPath T) : DPath T :=
  ⟨fun t => ξ t + ζ t, by
    obtain ⟨h1, h2, h3, h4⟩ := ξ.2
    obtain ⟨k1, k2, k3, k4⟩ := ζ.2
    refine ⟨fun t ht => (h1 t ht).add (k1 t ht), fun t ht => ?_, fun t ht => ?_,
      fun t ht => ?_⟩
    · obtain ⟨l, hl⟩ := h2 t ht
      obtain ⟨m, hm⟩ := k2 t ht
      exact ⟨l + m, hl.add hm⟩
    · show ξ.1 t + ζ.1 t = ξ.1 0 + ζ.1 0
      rw [h3 t ht, k3 t ht]
    · show ξ.1 t + ζ.1 t = ξ.1 T + ζ.1 T
      rw [h4 t ht, k4 t ht]⟩

instance {T : ℝ} : Add (DPath T) := ⟨DPath.add⟩

/-- The jump `ξ(t) − ξ(t−)` of `ξ` at `t`, with `ξ(0−) = 0`. -/
noncomputable def jump (ξ : ℝ → ℝ) (t : ℝ) : ℝ := ξ t - leftLim0 ξ t

/-- `ζ ∈ 𝔻^↑_{⩽∞}[0,T]` (p. 5): `ζ` is a non-decreasing pure jump path with `ζ(0) ≥ 0`. A
non-decreasing path is pure jump exactly when, for every `t ∈ [0,T]`, `ζ(t)` is the sum of its
jumps `ζ(s) − ζ(s−)` over `s ∈ [0,t]` (with `ζ(0−) = 0`, so the jump at `0` is `ζ(0)`). -/
def IsNondecPureJump {T : ℝ} (ζ : DPath T) : Prop :=
  MonotoneOn ζ (Icc 0 T) ∧ 0 ≤ ζ 0 ∧
  ∀ t ∈ Icc (0 : ℝ) T,
    ENNReal.ofReal (ζ t) =
      ∑' s : {s : ℝ // s ∈ Icc 0 t ∧ jump ζ s ≠ 0}, ENNReal.ofReal (jump ζ s)

/-- `𝔻^{(λ)}[0,T] = {ξ ∈ 𝔻[0,T] : ξ(t) = λt + ζ(t) ∀ t ∈ [0,T], ζ ∈ 𝔻^↑_{⩽∞}[0,T]}` (p. 6). -/
def DLambda (T lam : ℝ) : Set (DPath T) :=
  {ξ | ∃ ζ : DPath T, IsNondecPureJump ζ ∧ ∀ t ∈ Icc (0 : ℝ) T, ξ t = lam * t + ζ t}

/-- `∑_{t ∈ [0,T] : ζ(t) ≠ ζ(t−)} (ζ(t) − ζ(t−))^α` in `[0, ∞]`, with `ζ(0−) = 0`, so that a jump
at time `0` from `0` to `ζ(0)` is counted. -/
noncomputable def jumpPowSum {T : ℝ} (ζ : DPath T) (α : ℝ) : ℝ≥0∞ :=
  ∑' t : {t : ℝ // t ∈ Icc 0 T ∧ ζ t ≠ leftLim0 ζ t}, ENNReal.ofReal (jump ζ t ^ α)

/-- The clamp `t ↦ max 0 (min t 1)` of `ℝ` onto `[0,1]`. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min t 1)

/-- The step path `t ↦ h(⌊n t⌋)`, `t ∈ [0,1]` (extended constantly outside `[0,1]`), as an element
of `𝔻[0,1]`. The processes `Ȳ_n`, `Z̄_n`, `S̄_n` of the paper are of this form. -/
noncomputable def stepPath (n : ℕ) (h : ℕ → ℝ) : DPath 1 :=
  ⟨fun t => h ⌊(n : ℝ) * clamp01 t⌋₊, by
    have hcm : Monotone clamp01 := fun a b hab => max_le_max le_rfl (min_le_min hab le_rfl)
    have hcc : Continuous clamp01 := continuous_const.max (continuous_id.min continuous_const)
    have hφ : Monotone fun t => ⌊(n : ℝ) * clamp01 t⌋₊ := fun a b hab =>
      Nat.floor_le_floor (mul_le_mul_of_nonneg_left (hcm hab) (Nat.cast_nonneg n))
    have hnn : ∀ t, 0 ≤ (n : ℝ) * clamp01 t := fun t =>
      mul_nonneg (Nat.cast_nonneg n) (le_max_left _ _)
    refine ⟨fun t _ => ?_, fun t _ => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · -- right-continuity: the floor is eventually constant to the right of `t`
      have hev : ∀ᶠ s in 𝓝[Ici t] t,
          ⌊(n : ℝ) * clamp01 s⌋₊ = ⌊(n : ℝ) * clamp01 t⌋₊ := by
        have h1 : ∀ᶠ s in 𝓝 t,
            (n : ℝ) * clamp01 s < (⌊(n : ℝ) * clamp01 t⌋₊ : ℝ) + 1 :=
          ((continuous_const.mul hcc).tendsto t).eventually
            (gt_mem_nhds (Nat.lt_floor_add_one _))
        filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with s hs hst
        rw [Nat.floor_eq_iff (hnn s)]
        exact ⟨(Nat.floor_le (hnn t)).trans
          (mul_le_mul_of_nonneg_left (hcm hst) (Nat.cast_nonneg n)), hs⟩
      exact continuousWithinAt_const.congr_of_eventuallyEq
        (hev.mono fun s hs => by simp only [hs]) rfl
    · -- left limit: a bounded monotone `ℕ`-valued function is eventually constant to the left
      set S := (fun s => ⌊(n : ℝ) * clamp01 s⌋₊) '' Iio t with hS
      have hne : S.Nonempty := ⟨_, mem_image_of_mem _ (show t - 1 ∈ Iio t by simp)⟩
      have hbdd : BddAbove S := ⟨⌊(n : ℝ) * clamp01 t⌋₊, by
        rintro _ ⟨s, hs, rfl⟩
        exact hφ (le_of_lt hs)⟩
      obtain ⟨s₀, hs₀, hs₀eq⟩ := Nat.sSup_mem hne hbdd
      refine ⟨h (sSup S), tendsto_const_nhds.congr' ?_⟩
      filter_upwards [Ioo_mem_nhdsLT hs₀] with s hs
      have hle : ⌊(n : ℝ) * clamp01 s⌋₊ ≤ sSup S :=
        le_csSup hbdd (mem_image_of_mem _ hs.2)
      have hge : sSup S ≤ ⌊(n : ℝ) * clamp01 s⌋₊ := by
        rw [← hs₀eq]; exact hφ (le_of_lt hs.1)
      show h (sSup S) = h ⌊(n : ℝ) * clamp01 s⌋₊
      rw [le_antisymm hle hge]
    · have h1 : clamp01 t = clamp01 0 := by
        simp only [clamp01]
        rw [min_eq_left (by linarith), max_eq_left (le_of_lt ht)]
        norm_num
      show h ⌊(n : ℝ) * clamp01 t⌋₊ = h ⌊(n : ℝ) * clamp01 0⌋₊
      rw [h1]
    · have h1 : clamp01 t = clamp01 1 := by
        simp only [clamp01]
        rw [min_eq_right (le_of_lt ht)]
        norm_num
      show h ⌊(n : ℝ) * clamp01 t⌋₊ = h ⌊(n : ℝ) * clamp01 1⌋₊
      rw [h1]⟩

end ReflectedRWLDP.SamplePath


