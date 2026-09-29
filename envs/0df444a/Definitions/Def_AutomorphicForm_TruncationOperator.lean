-- Prove2me | Definitions.Def_AutomorphicForm_TruncationOperator
-- name    : AutomorphicForm_TruncationOperator
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/37220b9b-27c7-5636-92d7-9dd73f3d89aa
-- title:
--   Growth conditions, high regions, and the one-cusp truncation operator
-- statement:
--   The module sets up, for a group $G$, a real-valued height $H : G \to \mathbb{R}$ and a cutoff $T \in \mathbb{R}$, the elementary apparatus of truncation for $\mathbb{C}$-valued functions on $G$.
--
--   Two growth predicates are defined relative to a subset $S \subseteq G$ and the height $H$. A function $\varphi : G \to \mathbb{C}$ satisfies `IsSlowlyIncreasingOn S H φ` when there exist a real constant $C$ and an exponent $N \in \mathbb{N}$ with $\lVert \varphi(g)\rVert \le C\,H(g)^N$ for every $g \in S$; it satisfies `IsRapidlyDecreasingOn S H φ` when for every $N \in \mathbb{N}$ there is a real $C$ with $\lVert \varphi(g)\rVert \le C\,(H(g)^{-1})^N$ for every $g \in S$. No positivity is imposed on $H$ or on the constants; the quantifiers are exactly as written. The accompanying elementary facts record that a function bounded on $S$ is slowly increasing there (hence so is the constant $1$), that $0$ is rapidly decreasing, and that rapid decrease implies slow increase (take $N = 0$).
--
--   The high region of the height is `highSet H T` $= \{g \in G : T < H(g)\}$. For a measurable space $Q$ with measure $\mu$ and a map $u : Q \to G$, write $\varphi_N(g) = \int_Q \varphi(u(q)\,g)\,\mathrm{d}\mu(q)$ for the constant term `constantTerm μ u φ`. Then
--   $$\Lambda^T\varphi(g) \;=\; \varphi(g) - \mathbf{1}_{\{H > T\}}(g)\,\varphi_N(g)$$
--   defines `lambdaT μ u H T φ`: the constant term is subtracted precisely on the high region. Thus $\Lambda^T\varphi(g) = \varphi(g)$ whenever $H(g) \le T$ and $\Lambda^T\varphi(g) = \varphi(g) - \varphi_N(g)$ whenever $T < H(g)$; $\Lambda^T$ annihilates $0$ and fixes every $\varphi$ with identically vanishing constant term, i.e. satisfying `IsCuspidalFn μ u φ`. Only the single subtraction attached to $u$ occurs: this is the one-cusp truncation, not a sum over a set of cosets.
--
--   **Relation to Mathlib.** Mathlib has no notion of automorphic truncation or of these height-relative growth conditions; the predicates, the high region and the operator $\Lambda^T$ are the project's own, built from Mathlib's Bochner integral and `Set.indicator`.
--
--   **Where it is used.** These are the basic growth and truncation notions used in the analytic treatment of automorphic forms on $\mathrm{GL}_2$ over a number field, where $u$ is the unipotent section $x \mapsto n(x)$ and $H$ a height on $\mathrm{GL}_2$ of the adeles; the truncation operator mediates between moderate growth of a general automorphic form and rapid decay of its cuspidal truncation, on the automorphic side of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_TruncationOperator.lean

import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

namespace AutomorphicForm

section GrowthDecay

variable {G : Type*}

def IsSlowlyIncreasingOn (S : Set G) (H : G → ℝ) (φ : G → ℂ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ g ∈ S, ‖φ g‖ ≤ C * H g ^ N

def IsRapidlyDecreasingOn (S : Set G) (H : G → ℝ) (φ : G → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ S, ‖φ g‖ ≤ C * (H g)⁻¹ ^ N

theorem isSlowlyIncreasingOn_of_bounded {S : Set G} {H : G → ℝ} {φ : G → ℂ} {C : ℝ}
    (hC : ∀ g ∈ S, ‖φ g‖ ≤ C) : IsSlowlyIncreasingOn S H φ :=
  ⟨C, 0, fun g hg => by simpa using hC g hg⟩

theorem isSlowlyIncreasingOn_const_one (S : Set G) (H : G → ℝ) :
    IsSlowlyIncreasingOn S H (fun _ => (1 : ℂ)) :=
  isSlowlyIncreasingOn_of_bounded (C := 1) (fun _ _ => by simp)

theorem isRapidlyDecreasingOn_zero (S : Set G) (H : G → ℝ) :
    IsRapidlyDecreasingOn S H (fun _ => (0 : ℂ)) :=
  fun _ => ⟨0, fun _ _ => by simp⟩

theorem IsRapidlyDecreasingOn.isSlowlyIncreasingOn {S : Set G} {H : G → ℝ} {φ : G → ℂ}
    (h : IsRapidlyDecreasingOn S H φ) : IsSlowlyIncreasingOn S H φ := by
  obtain ⟨C, hC⟩ := h 0
  exact ⟨C, 0, fun g hg => by simpa using hC g hg⟩

def highSet (H : G → ℝ) (T : ℝ) : Set G :=
  {g : G | T < H g}

theorem mem_highSet_iff {H : G → ℝ} {T : ℝ} {g : G} : g ∈ highSet H T ↔ T < H g :=
  Iff.rfl

end GrowthDecay

section LambdaT

variable {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]

noncomputable def lambdaT (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) (φ : G → ℂ) :
    G → ℂ :=
  fun g => φ g - Set.indicator (highSet H T) (constantTerm μ u φ) g

theorem lambdaT_apply (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) (φ : G → ℂ) (g : G) :
    lambdaT μ u H T φ g = φ g - Set.indicator (highSet H T) (constantTerm μ u φ) g :=
  rfl

theorem lambdaT_apply_of_le (μ : Measure Q) (u : Q → G) {H : G → ℝ} {T : ℝ} {g : G}
    (hg : H g ≤ T) (φ : G → ℂ) : lambdaT μ u H T φ g = φ g := by
  unfold lambdaT
  rw [Set.indicator_of_notMem (by simpa [mem_highSet_iff, not_lt] using hg), sub_zero]

theorem lambdaT_apply_of_lt (μ : Measure Q) (u : Q → G) {H : G → ℝ} {T : ℝ} {g : G}
    (hg : T < H g) (φ : G → ℂ) : lambdaT μ u H T φ g = φ g - constantTerm μ u φ g := by
  unfold lambdaT
  rw [Set.indicator_of_mem (mem_highSet_iff.mpr hg)]

theorem lambdaT_zero (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) :
    lambdaT μ u H T (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  funext g
  simp [lambdaT]

theorem lambdaT_of_isCuspidalFn (μ : Measure Q) (u : Q → G) {φ : G → ℂ}
    (hφ : IsCuspidalFn μ u φ) (H : G → ℝ) (T : ℝ) : lambdaT μ u H T φ = φ := by
  funext g
  unfold lambdaT
  by_cases hmem : g ∈ highSet H T
  · rw [Set.indicator_of_mem hmem, hφ g, sub_zero]
  · rw [Set.indicator_of_notMem hmem, sub_zero]

end LambdaT

end AutomorphicForm


