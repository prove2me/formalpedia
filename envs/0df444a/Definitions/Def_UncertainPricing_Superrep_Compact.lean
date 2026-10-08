-- Prove2me | Definitions.Def_UncertainPricing_Superrep_Compact
-- name    : UncertainPricing_Superrep_Compact
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:42.167827+00:00
-- url     : https://prove2.me/theorems/8eff45a6-1b5e-4202-9cd7-3a142dd2664d
-- title:
--   §4.1–§4.2, §5.1–§5.2, pp. 12–22 — Stone–Čech Ω̃, extensions f̃, B̃, the set 𝒬, the modification B̃̃, Q*, and the class Γ
-- statement:
--   This file defines the compactification objects of §4–§5 of Denis–Martini.
--
--   **Stone–Čech compactification.** $\tilde\Omega$ is the Stone–Čech compactification of $\Omega$ (with the sup-norm topology), with embedding $\phi:\Omega\to\tilde\Omega$ and its Borel $\sigma$-field. Every bounded continuous $f$ on $\Omega$ has a unique continuous extension $\tilde f$ to $\tilde\Omega$ with $f=\tilde f\circ\phi$.
--
--   **Unbounded extensions** (§5.1). For continuous $f\ge0$, $\tilde f=\lim_n (f\wedge n)^\sim$, a function with values in $[0,\infty]$ (Lemma 5.1). For continuous $f$, $\tilde f^{+}=\lim_n(f^+\wedge n)^\sim$, $\tilde f^-=\lim_n(f^-\wedge n)^\sim$ and
--   $$\tilde f=\begin{cases}\tilde f^+-\tilde f^- & \tilde f^+<\infty,\ \tilde f^-<\infty,\\ +\infty & \tilde f^+=\infty,\\ -\infty & \tilde f^+<\infty,\ \tilde f^-=\infty.\end{cases}$$
--   In particular $\tilde B_t=(B_t)^\sim$ is defined everywhere on $\tilde\Omega$ with values in $[-\infty,\infty]$, and $\tilde{\mathcal F}_t=\sigma\{\tilde B_u:u\le t\}$.
--
--   **The set $\mathcal Q$.** $\mathcal Q$ is the set of probability measures $Q$ on $\tilde\Omega$ representing the linear forms on $C(\tilde\Omega)$ dominated by $\tilde\Lambda(\tilde f)=\Lambda(f)$, i.e. $E_Q\tilde f\le\Lambda(f)$ for every $f\in C_b(\Omega)$.
--
--   **Continuous modification and $Q^*$.** A continuous modification $\tilde{\tilde B}$ of $\tilde B$ under $Q$ is a real process on $\tilde\Omega$ with measurable coordinates and continuous paths starting at $0$ such that $\tilde{\tilde B}_t=\tilde B_t$ $Q$-a.s. for each $t$. Each path is a point of $\Omega$, and $Q^*$ is the law of $(\tilde{\tilde B}_t)_{t\in[0,T]}$ on $(\Omega,\mathcal B)$.
--
--   **The class $\Gamma$.** $\Gamma$ is the set of bounded continuous $f$ on $\Omega$ such that
--   $$E_Q\tilde f=E_{Q^*}f\qquad\text{for each }Q\in\mathcal Q.$$
--
--   These objects are used by the representation of $\Lambda$, Proposition 5.2, Lemmas 5.3–5.6 and Theorem 3.1 with the literal class $\Gamma$.
--
--   **Formalization Note.** $\tilde\Omega$ is Mathlib's `StoneCech`, and $\tilde f$ is `stoneCechExtend` of $f$ viewed as a map into $[-\|f\|,\|f\|]$. The sequence $(f^+\wedge n)^\sim$ is nondecreasing, so its limit is written as a supremum in $[0,\infty]$. The four-case table is an explicit `if`, not an `EReal` subtraction. $\mathcal Q$ consists of all Borel probability measures with $E_Q\tilde f\le\Lambda(f)$ for $f\in C_b(\Omega)$; regularity is not imposed, which changes no integral of a continuous function. A continuous modification is normalized to start at $0$ on every path ($\tilde B_0=0$ identically, so this is a choice of version). In $\Gamma$ the identity is required for every continuous modification; all of them have the same law $Q^*$.
-- source:
--   Denis & Martini, arXiv:math/0607111v1, §4.1 (p. 12), §4.2 (pp. 13, 15), §5 (p. 19), Lemma 5.1 and Definition and notation (pp. 19–20), Proposition 5.2 (p. 21), §5.2 (p. 22)

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal

noncomputable section

/-- `Ω̃`, the Stone–Čech compactification of `Ω` (§4.1), with its Borel σ-field. -/
abbrev Ωt (T : ℝ) : Type := StoneCech (Ω T)

instance (T : ℝ) : MeasurableSpace (Ωt T) := borel (Ωt T)

instance (T : ℝ) : BorelSpace (Ωt T) := ⟨rfl⟩

/-- A bounded continuous `f` viewed as a map into the compact interval `[-‖f‖, ‖f‖]`. -/
def toIcc {T : ℝ} (f : Ω T →ᵇ ℝ) : Ω T → Set.Icc (-‖f‖) ‖f‖ := fun ω =>
  ⟨f ω, abs_le.mp (by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm ω)⟩

theorem continuous_toIcc {T : ℝ} (f : Ω T →ᵇ ℝ) : Continuous (toIcc f) :=
  f.continuous.subtype_mk _

/-- `f̃`: the unique continuous extension to `Ω̃` of a bounded continuous `f`, so that
`f = f̃ ∘ φ` with `φ = stoneCechUnit` (§4.1 (iii)). -/
def ext {T : ℝ} (f : Ω T →ᵇ ℝ) : C(Ωt T, ℝ) :=
  ⟨fun x => ((stoneCechExtend (continuous_toIcc f) x : Set.Icc (-‖f‖) ‖f‖) : ℝ),
    continuous_subtype_val.comp (continuous_stoneCechExtend (continuous_toIcc f))⟩

/-- The bounded continuous function `f⁺ ∧ n`. -/
def truncPos {T : ℝ} (f : C(Ω T, ℝ)) (n : ℕ) : Ω T →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ω => min (max (f ω) 0) (n : ℝ), (f.continuous.max continuous_const).min continuous_const⟩
    n (fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_sub_le_iff]
      constructor <;>
        linarith [min_le_right (max (f x) 0) (n : ℝ), min_le_right (max (f y) 0) (n : ℝ),
          le_min (le_max_right (f x) 0) (Nat.cast_nonneg (α := ℝ) n),
          le_min (le_max_right (f y) 0) (Nat.cast_nonneg (α := ℝ) n)])

/-- Lemma 5.1 applied to `f⁺`: `f̃⁺ = lim_n (f⁺ ∧ n)~`, with values in `[0, ∞]` (the sequence is
nondecreasing, so the limit is the supremum). `f̃⁻` is `extNN (-f)`. -/
def extNN {T : ℝ} (f : C(Ω T, ℝ)) (x : Ωt T) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (ext (truncPos f n) x)

/-- The extension `f̃` of a continuous `f` to `Ω̃` with values in `[−∞, ∞]` (§5.1, p. 20):
`f̃⁺ − f̃⁻` if both are finite, `+∞` if `f̃⁺ = ∞`, `−∞` if `f̃⁺ < ∞` and `f̃⁻ = ∞`. -/
def extE {T : ℝ} (f : C(Ω T, ℝ)) (x : Ωt T) : EReal :=
  if extNN f x = ⊤ then ⊤
  else if extNN (-f) x = ⊤ then ⊥
  else (((extNN f x).toReal - (extNN (-f) x).toReal : ℝ) : EReal)

theorem measurable_extNN {T : ℝ} (f : C(Ω T, ℝ)) : Measurable (extNN f) :=
  Measurable.iSup fun n => (ext (truncPos f n)).continuous.measurable.ennreal_ofReal

theorem measurable_extE {T : ℝ} (f : C(Ω T, ℝ)) : Measurable (extE f) := by
  unfold extE
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const ?_)
  · exact measurable_extNN f (measurableSet_singleton ⊤)
  · exact measurable_extNN (-f) (measurableSet_singleton ⊤)
  · exact measurable_coe_real_ereal.comp
      ((measurable_extNN f).ennreal_toReal.sub (measurable_extNN (-f)).ennreal_toReal)

/-- `B_t` as a continuous function on `Ω`. -/
def Bc {T : ℝ} (t : Set.Icc (0 : ℝ) T) : C(Ω T, ℝ) := ⟨B t, continuous_B t⟩

/-- The process `B̃_t = (B_t)~` on `Ω̃`, with values in `[−∞, ∞]`. -/
def Btilde {T : ℝ} (t : Set.Icc (0 : ℝ) T) : Ωt T → EReal := extE (Bc t)

theorem measurable_Btilde {T : ℝ} (t : Set.Icc (0 : ℝ) T) : Measurable (Btilde t) :=
  measurable_extE _

/-- The filtration `𝓕̃_t = σ{B̃_u : u ≤ t}` on `Ω̃` (§4.2, p. 13). -/
def tildeFilt (T : ℝ) : Filtration (Set.Icc (0 : ℝ) T) (inferInstance : MeasurableSpace (Ωt T)) where
  seq t := ⨆ (u : Set.Icc (0 : ℝ) T) (_ : u ≤ t),
    MeasurableSpace.comap (Btilde u : Ωt T → EReal) inferInstance
  mono' _ _ hst := iSup₂_mono' fun u hu => ⟨u, le_trans hu hst, le_rfl⟩
  le' _ := iSup₂_le fun u _ => (measurable_Btilde u).comap_le

/-- `𝒬`: the probability measures `Q` on `Ω̃` whose integrals of continuous functions are dominated by
`Λ`, i.e. `E_Q f̃ ≤ Λ(f)` for every `f ∈ C_b(Ω)` (the linear forms on `C(Ω̃)` dominated by `Λ̃`,
represented by measures). -/
def Qset {T : ℝ} (Ps : Set (Measure (Ω T))) (μU : StieltjesFunction ℝ) : Set (Measure (Ωt T)) :=
  {Q | IsProbabilityMeasure Q ∧
    ∀ g : Ω T →ᵇ ℝ, ((∫ x, ext g x ∂Q : ℝ) : EReal) ≤ Lam Ps μU g}

/-- `X` is a continuous modification of `B̃` under `Q` (written `B̃̃`): each `X_t` is measurable, every path
is continuous with `X_0 = 0`, and `X_t = B̃_t` `Q`-a.s. for each `t`. -/
structure IsContModif {T : ℝ} (Q : Measure (Ωt T)) (X : Set.Icc (0 : ℝ) T → Ωt T → ℝ) : Prop where
  meas : ∀ t, Measurable (X t)
  cont : ∀ x, Continuous (fun t => X t x)
  zero : ∀ x, ∀ h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T, X ⟨0, h0⟩ x = 0
  ae_eq : ∀ t, ∀ᵐ x ∂Q, (X t x : EReal) = Btilde t x

/-- The path `t ↦ X_t(x)` of a continuous modification, as a point of `Ω`. -/
def pathOf {T : ℝ} {Q : Measure (Ωt T)} {X : Set.Icc (0 : ℝ) T → Ωt T → ℝ}
    (hX : IsContModif Q X) (x : Ωt T) : Ω T :=
  ⟨⟨fun t => X t x, hX.cont x⟩, fun h0 => hX.zero x h0⟩

/-- `Q*`: the law on `(Ω, 𝓑)` of the continuous modification `(B̃̃_t)_{t ∈ [0,T]}` under `Q`. -/
def lawOf {T : ℝ} (Q : Measure (Ωt T)) {X : Set.Icc (0 : ℝ) T → Ωt T → ℝ}
    (hX : IsContModif Q X) : Measure (Ω T) :=
  Q.map (pathOf hX)

/-- `Γ`: the bounded continuous `f` with `E_Q f̃ = E_{Q*} f` for every `Q ∈ 𝒬` (§4.2, p. 15; §5.2,
p. 22). -/
def InGamma {T : ℝ} (Ps : Set (Measure (Ω T))) (μU : StieltjesFunction ℝ) (f : Ω T →ᵇ ℝ) : Prop :=
  ∀ Q ∈ Qset Ps μU, ∀ (X : Set.Icc (0 : ℝ) T → Ωt T → ℝ) (hX : IsContModif Q X),
    ∫ x, ext f x ∂Q = ∫ ω, f ω ∂(lawOf Q hX)

end

end UncertainPricing.Superrep


