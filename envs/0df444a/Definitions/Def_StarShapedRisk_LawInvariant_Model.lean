-- Prove2me | Definitions.Def_StarShapedRisk_LawInvariant_Model
-- name    : StarShapedRisk_LawInvariant_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:05:10.729768+00:00
-- url     : https://prove2.me/theorems/e5fae289-5e5b-4485-a71e-b288f718c143
-- title:
--   Definition 1 and Sec. 7 — bounded measurable positions, risk measures, law invariance, acceptance sets
-- statement:
--   This file fixes the model of Section 7 of Castagnoli, Cattelan, Maccheroni, Tebaldi and Wang (2022).
--
--   Let $(\Omega,\mathcal F)$ be a measurable space. The **space of positions** $\mathcal X$ is the linear space of all bounded $\mathcal F$-measurable functions $X:\Omega\to\mathbb R$. It contains every constant $m\in\mathbb R$ (written $m$ as well) and carries the pointwise order: $X\geqq Y$ iff $X(\omega)\ge Y(\omega)$ for all $\omega$. A value $X(\omega)>0$ is a **loss**. A probability measure $P$ on $(\Omega,\mathcal F)$ is **atomless** if every $A\in\mathcal F$ with $P(A)>0$ contains some $B\in\mathcal F$ with $0<P(B)<P(A)$.
--
--   A function $\rho:\mathcal X\to\mathbb R$ is a **risk measure** (Definition 1) if it is
--
--   1. monotone: $X\geqq Y\Rightarrow \rho(X)\ge\rho(Y)$;
--   2. translation invariant: $\rho(X-m)=\rho(X)-m$ for all $X\in\mathcal X$, $m\in\mathbb R$;
--   3. normalized: $\rho(0)=0$.
--
--   It is **star-shaped** if $\rho(\lambda X)\ge\lambda\rho(X)$ for all $X\in\mathcal X$ and all $\lambda>1$, and **law-invariant** under $P$ if $X$ and $Y$ having the same law under $P$ implies $\rho(X)=\rho(Y)$.
--
--   The **acceptance set** of $\rho$ is $\mathcal A_\rho=\{X\in\mathcal X\mid\rho(X)\le 0\}$. A set $\mathcal A\subseteq\mathcal X$ is an **acceptance set** if
--   $$\sup\{m\in\mathbb R\mid m\in\mathcal A\}=0\quad\text{and}\quad X\in\mathcal A,\ Y\in\mathcal X,\ Y\leqq X\ \Rightarrow\ Y\in\mathcal A,$$
--   and it generates $\rho_{\mathcal A}(X)=\inf\{m\in\mathbb R\mid X-m\in\mathcal A\}$.
--
--   These are the objects in which Proposition 2, Eq. (7), the FSD-consistency step and Theorem 5 are stated.
--
--   **Formalization Note** Positions are the bounded measurable functions (a `Submodule` of `Ω → ℝ`) with the pointwise order, rather than equivalence classes in $L^\infty(P)$; for law-invariant $\rho$ the two readings coincide, and the bounded measurable functions are themselves an admissible space of Section 3. The supremum condition on an acceptance set is stated as a least upper bound (`IsLUB`), so it also asserts that $\mathcal A$ contains some constant. `rhoOf A` uses `sInf`, whose value is Lean's default $0$ when the set $\{m\mid X-m\in\mathcal A\}$ is empty or unbounded below; for an acceptance set and a bounded $X$ neither happens. Atomlessness is defined here because Mathlib's `NoAtoms` only says that singletons are null.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2641, Definition 1 items 1–4; p. 2642, acceptance sets and Eq. (7); p. 2646, Sec. 7 (L∞(Ω,F,P), P atomless, law invariance)

import Mathlib

namespace StarShapedRisk.LawInvariant

open MeasureTheory

/-- The space of positions of Castagnoli et al. (2022), Sec. 7: bounded measurable real
functions on the measurable space `(Ω, ℱ)`, as a linear subspace of `Ω → ℝ`. It contains all
constants and carries the pointwise order. A value `X ω > 0` is a loss. -/
def Positions (Ω : Type*) [MeasurableSpace Ω] : Submodule ℝ (Ω → ℝ) where
  carrier := {X | Measurable X ∧ ∃ C : ℝ, ∀ ω, |X ω| ≤ C}
  zero_mem' := ⟨measurable_const, 0, fun _ => by simp⟩
  add_mem' := by
    rintro X Y ⟨hX, C, hC⟩ ⟨hY, D, hD⟩
    exact ⟨hX.add hY, C + D, fun ω => (abs_add_le _ _).trans (add_le_add (hC ω) (hD ω))⟩
  smul_mem' := by
    rintro c X ⟨hX, C, hC⟩
    refine ⟨hX.const_smul c, |c| * C, fun ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg c)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The constant position `m`. -/
def const (m : ℝ) : Positions Ω :=
  ⟨fun _ => m, measurable_const, |m|, fun _ => le_rfl⟩

/-- `P` is atomless: every measurable set of positive probability contains a measurable subset
of strictly smaller, strictly positive probability. (This is the classical notion; Mathlib's
`NoAtoms` only says that singletons are null, which is weaker.) -/
def IsAtomless (P : Measure Ω) : Prop :=
  ∀ s : Set Ω, MeasurableSet s → 0 < P s →
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < P t ∧ P t < P s

/-- Definition 1.1, monotonicity: if `X ≧ Y` pointwise, then `ρ X ≥ ρ Y`. -/
def IsMonotone (ρ : Positions Ω → ℝ) : Prop :=
  ∀ X Y : Positions Ω, (∀ ω, Y.1 ω ≤ X.1 ω) → ρ Y ≤ ρ X

/-- Definition 1.2, translation invariance: `ρ (X - m) = ρ X - m` for all `X` and real `m`. -/
def IsTranslationInvariant (ρ : Positions Ω → ℝ) : Prop :=
  ∀ (X : Positions Ω) (m : ℝ), ρ (X - const m) = ρ X - m

/-- Definition 1.3, normalization: `ρ 0 = 0`. -/
def IsNormalized (ρ : Positions Ω → ℝ) : Prop :=
  ρ 0 = 0

/-- Definition 1: a risk measure is monotone, translation invariant and normalized. -/
def IsRiskMeasure (ρ : Positions Ω → ℝ) : Prop :=
  IsMonotone ρ ∧ IsTranslationInvariant ρ ∧ IsNormalized ρ

/-- Definition 1.4, star-shapedness: `ρ (t X) ≥ t ρ X` for all `X` and all `t > 1`. -/
def IsStarShaped (ρ : Positions Ω → ℝ) : Prop :=
  ∀ (X : Positions Ω) (t : ℝ), 1 < t → t * ρ X ≤ ρ (t • X)

/-- Sec. 7, law invariance under `P`: positions with the same law under `P` are equally risky. -/
def IsLawInvariant (P : Measure Ω) (ρ : Positions Ω → ℝ) : Prop :=
  ∀ X Y : Positions Ω, P.map X.1 = P.map Y.1 → ρ X = ρ Y

/-- The acceptance set `A_ρ = {X | ρ X ≤ 0}` of `ρ`. -/
def acceptanceSetOf (ρ : Positions Ω → ℝ) : Set (Positions Ω) :=
  {X | ρ X ≤ 0}

/-- An acceptance set: the supremum of the constants it contains is `0` (a least upper bound,
so the set of such constants is nonempty and bounded above by `0`), and it is closed downwards
in the pointwise order. -/
def IsAcceptanceSet (A : Set (Positions Ω)) : Prop :=
  IsLUB {m : ℝ | const m ∈ A} 0 ∧
    ∀ X ∈ A, ∀ Y : Positions Ω, (∀ ω, Y.1 ω ≤ X.1 ω) → Y ∈ A

/-- The risk measure generated by a set `A`: `ρ_A X = inf {m | X - m ∈ A}`. For an acceptance
set and a bounded `X` this set is nonempty and bounded below; otherwise `sInf` returns Lean's
junk value `0`. -/
noncomputable def rhoOf (A : Set (Positions Ω)) (X : Positions Ω) : ℝ :=
  sInf {m : ℝ | X - const m ∈ A}

end StarShapedRisk.LawInvariant


