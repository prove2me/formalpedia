-- Prove2me | Definitions.Def_RiskFunctionals_MultiPeriod_Functionals
-- name    : RiskFunctionals_MultiPeriod_Functionals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:25.897895+00:00
-- url     : https://prove2.me/theorems/5a641cf1-c442-4530-9bb1-668c27042310
-- title:
--   Multi-period acceptability functionals (MA0)–(MA3), (MA1′), (MA1″), the dual pairing and the conjugate on $\times_{t=1}^T L_p(\mathcal F_t)$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\boldsymbol{\mathcal F}=(\mathcal F_t)_{t=0}^T$ a filtration in $\mathcal F$, usually with $\mathcal F_0=\{\emptyset,\Omega\}$. Fix $p\in[1,\infty)$ and $q\in(1,\infty]$ with $1/p+1/q=1$.
--
--   1. The space of income processes is $\mathcal Y:=\times_{t=1}^T L_p(\mathcal F_t)$: a process $Y=(Y_1,\dots,Y_T)$ has $Y_t\in L_p(\Omega,\mathcal F,P)$ with an $\mathcal F_t$-measurable version. It carries the norm $\|Y\|_p=(\sum_{t=1}^T\mathbb E|Y_t|^p)^{1/p}$. The dual space is $\mathcal Z:=\times_{t=1}^T L_q(\mathcal F_t)$, and the pairing is
--   $$\langle Z,Y\rangle=\sum_{t=1}^T\mathbb E(Y_tZ_t).$$
--   2. The **conjugate** of a functional $\mathcal A:\mathcal Y\to\overline{\mathbb R}$ is
--   $$\mathcal A^+(Z):=\inf\{\langle Z,Y\rangle-\mathcal A(Y):Y\in\mathcal Y\},\qquad Z\in\mathcal Z.\tag{3.19}$$
--   3. The constraint sets of the three representations are
--      - (3.21): $Z_t\ge0$ and $\mathbb E(Z_t\mid\mathcal F_{t-1})=1$ a.s. for $t=1,\dots,T$;
--      - (3.22): $Z_t\ge0$ and $\mathbb E(Z_t)=1$ for $t=1,\dots,T$;
--      - (3.23): $\mathbb E(Z_1)=1$ and $Z_t\ge0$ for $t=1,\dots,T$.
--   4. A functional is **proper** if $\mathcal A(Y)<+\infty$ for all $Y$ and $\mathcal A(Y)>-\infty$ for some $Y$. It is a **probability functional** in the book's sense if it does not take both values $+\infty$ and $-\infty$.
--   5. The properties of a functional $\mathcal A(\cdot\,;\boldsymbol{\mathcal F})$ on $\mathcal Y$ are:
--      - (MA1) predictable translation-equivariance: $\mathcal A(Y_1,\dots,Y_t+C_t,\dots,Y_T;\boldsymbol{\mathcal F})=\mathbb E(C_t)+\mathcal A(Y_1,\dots,Y_T;\boldsymbol{\mathcal F})$ for every $\mathcal F_{t-1}$-measurable $C_t\in L_p$;
--      - (MA1′) weak translation-equivariance: the same identity for constants $c_t$, i.e. $\mathcal A(\dots,Y_t+c_t,\dots)=c_t+\mathcal A(Y)$;
--      - (MA1″) first period translation-equivariance: $\mathcal A(Y_1+c_1,Y_2,\dots,Y_T)=c_1+\mathcal A(Y)$ for constants $c_1$;
--      - (MA2) concavity: $\mathcal A(\lambda Y+(1-\lambda)\tilde Y)\ge\lambda\mathcal A(Y)+(1-\lambda)\mathcal A(\tilde Y)$ for $0\le\lambda\le1$;
--      - (MA3) monotonicity: $Y_t\le\tilde Y_t$ a.s. for all $t$ implies $\mathcal A(Y)\le\mathcal A(\tilde Y)$.
--   6. A family $\boldsymbol{\mathcal F}\mapsto\mathcal A(\cdot\,;\boldsymbol{\mathcal F})$ is **information monotone** (MA0) if $\mathcal F_t\subseteq\mathcal F'_t$ for all $t$ implies $\mathcal A(Y;\boldsymbol{\mathcal F})\le\mathcal A(Y;\boldsymbol{\mathcal F}')$ for every process $Y$ adapted to $\boldsymbol{\mathcal F}$. A **multi-period acceptability functional** is such a family that is proper for every filtration and satisfies (MA0)–(MA3).
--
--   These are the objects of §3.2 of the book. They are the axioms of a multi-period acceptability functional and the duality on the product of $L_p$ spaces through which such functionals are represented.
--
--   **Formalization Note** The filtration is a Mathlib `Filtration` indexed by `Fin (T+1)` (so `𝔽 i` is $\mathcal F_i$, $i=0,\dots,T$). A process is indexed by `t : Fin T`, and the component `t` is the book's $Y_{t+1}$, with $\mathcal F_{t+1}$ = `𝔽 t.succ` and $\mathcal F_t$ = `𝔽 t.castSucc`. $L_p(\mathcal F_t)$ is Mathlib's `lpMeas`, the subspace of $L_p(\Omega,\mathcal F,P)$ of classes with an $\mathcal F_t$-measurable version. The product carries the product topology, which is the topology of the norm $\|\cdot\|_p$. Functionals take values in `EReal`. Concavity is computed in `EReal`, where $0\cdot(\pm\infty)=0$ and $(+\infty)+(-\infty)=-\infty$; for functionals that do not take both infinite values this is the book's inequality. The infimum in (3.19) is taken in $[-\infty,+\infty]$. The trivial σ-algebra $\{\emptyset,\Omega\}$ is `⊥`. (MA0) is a property of a family indexed by all filtrations with trivial $\mathcal F_0$, quantified over all $t=0,\dots,T$. The book writes the functional's arguments as $\mathcal F_0,\dots,\mathcal F_{T-1}$, but a process adapted to $\boldsymbol{\mathcal F}$ must also be adapted to $\boldsymbol{\mathcal F}'$. In (MA1), (MA1′) and (MA1″) the shifted process is a second argument that agrees with $Y$ off period $t$ and equals $Y_t+C_t$ a.s. at period $t$.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 133, Definition 3.14 and Eq. (3.15); p. 134, Eqs. (3.16)–(3.17); p. 136, §3.2.1 and Eq. (3.19); pp. 136–139, constraint sets of (3.21)–(3.23); p. 27 (probability functionals)

import Mathlib

namespace RiskFunctionals.MultiPeriod

open MeasureTheory

/-- The space `𝒴 := ×_{t=1}^T L_p(ℱ_t)` of income processes adapted to the filtration
`𝓕 = (ℱ_t)_{t=0}^T` (Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific
2007, p. 136, §3.2.1). The filtration is indexed by `Fin (T + 1)` (`𝔽 i` is the book's `ℱ_i`,
`i = 0, …, T`); a process is indexed by `t : Fin T`, and its component `Y t` is the book's
`Y_{t+1}`, an element of `L_p(Ω, ℱ, P)` with an `ℱ_{t+1}`-measurable version (Mathlib's `lpMeas`).
The product carries the product topology, which is the topology of the book's norm
`‖Y‖_p = (Σ_t 𝔼|Y_t|^p)^{1/p}`. With `q` in place of `p` the same type is the dual space
`𝒵 := ×_{t=1}^T L_q(ℱ_t)`. -/
abbrev ProcessSpace {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) (T : ℕ) (p : ENNReal)
    (𝔽 : Filtration (Fin (T + 1)) m0) : Type _ :=
  (t : Fin T) → lpMeas ℝ ℝ (𝔽 t.succ) p P

/-- The dual pairing `⟨Z, Y⟩ = Σ_{t=1}^T 𝔼(Y_t Z_t)` between `𝒵` and `𝒴` (p. 136). -/
noncomputable def pairing {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω} {T : ℕ}
    {p q : ENNReal} {𝔽 : Filtration (Fin (T + 1)) m0}
    (Z : ProcessSpace P T q 𝔽) (Y : ProcessSpace P T p 𝔽) : ℝ :=
  ∑ t : Fin T, ∫ ω, ((Y t : Lp ℝ p P) : Ω → ℝ) ω * ((Z t : Lp ℝ q P) : Ω → ℝ) ω ∂P

/-- The conjugate `𝒜⁺(Z) := inf{⟨Z, Y⟩ − 𝒜(Y) : Y ∈ 𝒴}` of Eq. (3.19), p. 136, an infimum in
`EReal = [−∞, +∞]`. -/
noncomputable def concaveConj {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω} {T : ℕ}
    {p : ENNReal} {𝔽 : Filtration (Fin (T + 1)) m0} (q : ENNReal)
    (A : ProcessSpace P T p 𝔽 → EReal) (Z : ProcessSpace P T q 𝔽) : EReal :=
  ⨅ Y : ProcessSpace P T p 𝔽, ((pairing Z Y : ℝ) : EReal) - A Y

/-- The constraint set of (3.21), p. 136: `Z_t ≥ 0` and `𝔼(Z_t | ℱ_{t−1}) = 1` a.s. for
`t = 1, …, T` (with the index shift of `ProcessSpace`: component `t` is constrained by `𝔽 t`). -/
def predictableDensities {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) (T : ℕ)
    (q : ENNReal) (𝔽 : Filtration (Fin (T + 1)) m0) : Set (ProcessSpace P T q 𝔽) :=
  {Z | ∀ t : Fin T, (∀ᵐ ω ∂P, 0 ≤ ((Z t : Lp ℝ q P) : Ω → ℝ) ω) ∧
    condExp (𝔽 t.castSucc) P ((Z t : Lp ℝ q P) : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ)}

/-- The constraint set of (3.22), p. 138: `Z_t ≥ 0` a.s. and `𝔼(Z_t) = 1` for `t = 1, …, T`. -/
def densities {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) (T : ℕ)
    (q : ENNReal) (𝔽 : Filtration (Fin (T + 1)) m0) : Set (ProcessSpace P T q 𝔽) :=
  {Z | ∀ t : Fin T, (∀ᵐ ω ∂P, 0 ≤ ((Z t : Lp ℝ q P) : Ω → ℝ) ω) ∧
    ∫ ω, ((Z t : Lp ℝ q P) : Ω → ℝ) ω ∂P = 1}

/-- The constraint set of (3.23), p. 139: `𝔼(Z_1) = 1` and `Z_t ≥ 0` a.s. for `t = 1, …, T`
(the first component is `t = 0` in `Fin T`). -/
def firstPeriodDensities {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) (T : ℕ)
    (q : ENNReal) (𝔽 : Filtration (Fin (T + 1)) m0) : Set (ProcessSpace P T q 𝔽) :=
  {Z | (∀ t : Fin T, ∀ᵐ ω ∂P, 0 ≤ ((Z t : Lp ℝ q P) : Ω → ℝ) ω) ∧
    ∀ t : Fin T, (t : ℕ) = 0 → ∫ ω, ((Z t : Lp ℝ q P) : Ω → ℝ) ω ∂P = 1}

/-- A proper functional (p. 133, Definition 3.14): `𝒜(Y) < +∞` for all `Y` and `𝒜(Y) > −∞` for
some `Y`. The same notion is used for the functional `𝒜⁺ : 𝒵 → ℝ̄` of Theorems 3.20–3.22. -/
def IsProper {X : Type*} (A : X → EReal) : Prop :=
  (∀ Y, A Y ≠ ⊤) ∧ ∃ Y, A Y ≠ ⊥

/-- The book's convention for a probability functional (p. 27): it is extended real valued and
may take the value `+∞` or the value `−∞`, but not both. -/
def IsProbabilityFunctional {X : Type*} (A : X → EReal) : Prop :=
  (∀ Y, A Y ≠ ⊤) ∨ (∀ Y, A Y ≠ ⊥)

/-- (MA0) Information monotonicity (p. 133, Definition 3.14) of a family `𝓕 ↦ 𝒜(·; 𝓕)`
indexed by filtrations with trivial `ℱ₀`: if `ℱ_t ⊆ ℱ′_t` for all `t`, then
`𝒜(Y; 𝓕) ≤ 𝒜(Y; 𝓕′)` for every process `Y` adapted to `𝓕` (hence to `𝓕′`); `Y` and `Y'` are
the same process seen in the two spaces. -/
def IsInformationMonotone {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) (T : ℕ)
    (p : ENNReal) (A : (𝔽 : Filtration (Fin (T + 1)) m0) → ProcessSpace P T p 𝔽 → EReal) :
    Prop :=
  ∀ 𝔽 𝔽' : Filtration (Fin (T + 1)) m0, 𝔽 0 = ⊥ → 𝔽' 0 = ⊥ → (∀ i, 𝔽 i ≤ 𝔽' i) →
    ∀ (Y : ProcessSpace P T p 𝔽) (Y' : ProcessSpace P T p 𝔽'),
      (∀ t, (Y t : Lp ℝ p P) = (Y' t : Lp ℝ p P)) → A 𝔽 Y ≤ A 𝔽' Y'

/-- (MA1) Predictable translation-equivariance (p. 133, Eq. (3.15)):
`𝒜(Y₁, …, Y_t + C_t, …, Y_T; 𝓕) = 𝔼(C_t) + 𝒜(Y₁, …, Y_T; 𝓕)` for all `ℱ_{t−1}`-measurable
`C_t` (in `L_p`, so that the shifted process lies in `𝒴`). `Y'` is the shifted process. -/
def IsPredictableTranslationEquivariant {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    {T : ℕ} {p : ENNReal} (𝔽 : Filtration (Fin (T + 1)) m0)
    (A : ProcessSpace P T p 𝔽 → EReal) : Prop :=
  ∀ (Y Y' : ProcessSpace P T p 𝔽) (t : Fin T) (C : Ω → ℝ),
    Measurable[𝔽 t.castSucc] C → MemLp C p P →
    (∀ s, s ≠ t → (Y' s : Lp ℝ p P) = (Y s : Lp ℝ p P)) →
    (∀ᵐ ω ∂P, ((Y' t : Lp ℝ p P) : Ω → ℝ) ω = ((Y t : Lp ℝ p P) : Ω → ℝ) ω + C ω) →
    A Y' = ((∫ ω, C ω ∂P : ℝ) : EReal) + A Y

/-- (MA1′) Weak translation-equivariance (p. 134, Eq. (3.16)):
`𝒜(Y₁, …, Y_t + c_t, …, Y_T; 𝓕) = c_t + 𝒜(Y₁, …, Y_T; 𝓕)` for all constants `c_t`. -/
def IsWeakTranslationEquivariant {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    {T : ℕ} {p : ENNReal} (𝔽 : Filtration (Fin (T + 1)) m0)
    (A : ProcessSpace P T p 𝔽 → EReal) : Prop :=
  ∀ (Y Y' : ProcessSpace P T p 𝔽) (t : Fin T) (c : ℝ),
    (∀ s, s ≠ t → (Y' s : Lp ℝ p P) = (Y s : Lp ℝ p P)) →
    (∀ᵐ ω ∂P, ((Y' t : Lp ℝ p P) : Ω → ℝ) ω = ((Y t : Lp ℝ p P) : Ω → ℝ) ω + c) →
    A Y' = (c : EReal) + A Y

/-- (MA1″) First period translation-equivariance (p. 134, Eq. (3.17)):
`𝒜(Y₁ + c₁, Y₂, …, Y_T; 𝓕) = c₁ + 𝒜(Y₁, …, Y_T; 𝓕)` for all constants `c₁` (the first period is
`t = 0` in `Fin T`). -/
def IsFirstPeriodTranslationEquivariant {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    {T : ℕ} {p : ENNReal} (𝔽 : Filtration (Fin (T + 1)) m0)
    (A : ProcessSpace P T p 𝔽 → EReal) : Prop :=
  ∀ (Y Y' : ProcessSpace P T p 𝔽) (t : Fin T) (c : ℝ), (t : ℕ) = 0 →
    (∀ s, s ≠ t → (Y' s : Lp ℝ p P) = (Y s : Lp ℝ p P)) →
    (∀ᵐ ω ∂P, ((Y' t : Lp ℝ p P) : Ω → ℝ) ω = ((Y t : Lp ℝ p P) : Ω → ℝ) ω + c) →
    A Y' = (c : EReal) + A Y

/-- (MA2) Concavity (p. 133): `(Y₁, …, Y_T) ↦ 𝒜(Y₁, …, Y_T; 𝓕)` is concave, i.e.
`𝒜(λY + (1 − λ)Ỹ) ≥ λ𝒜(Y) + (1 − λ)𝒜(Ỹ)` for `0 ≤ λ ≤ 1`, computed in `EReal`. -/
def IsConcaveFunctional {X : Type*} [AddCommGroup X] [Module ℝ X] (A : X → EReal) : Prop :=
  ∀ (Y₁ Y₂ : X) (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
    (lam : EReal) * A Y₁ + ((1 - lam : ℝ) : EReal) * A Y₂ ≤ A (lam • Y₁ + (1 - lam) • Y₂)

/-- (MA3) Monotonicity (p. 133): `Y_t ≤ Ỹ_t` a.s. for all `t` implies
`𝒜(Y₁, …, Y_T; 𝓕) ≤ 𝒜(Ỹ₁, …, Ỹ_T; 𝓕)`. -/
def IsMonotoneFunctional {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    {T : ℕ} {p : ENNReal} (𝔽 : Filtration (Fin (T + 1)) m0)
    (A : ProcessSpace P T p 𝔽 → EReal) : Prop :=
  ∀ Y Y' : ProcessSpace P T p 𝔽,
    (∀ t, ∀ᵐ ω ∂P, ((Y t : Lp ℝ p P) : Ω → ℝ) ω ≤ ((Y' t : Lp ℝ p P) : Ω → ℝ) ω) → A Y ≤ A Y'

/-- Definition 3.14 (p. 133): a multi-period acceptability functional is a family
`𝓕 ↦ 𝒜(·; 𝓕)` (over filtrations with trivial `ℱ₀ = {∅, Ω}`, p. 133) that is proper for every
filtration and satisfies (MA0)–(MA3). -/
def IsMultiPeriodAcceptability {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) (T : ℕ)
    (p : ENNReal) (A : (𝔽 : Filtration (Fin (T + 1)) m0) → ProcessSpace P T p 𝔽 → EReal) :
    Prop :=
  (∀ 𝔽 : Filtration (Fin (T + 1)) m0, 𝔽 0 = ⊥ → IsProper (A 𝔽)) ∧
  IsInformationMonotone P T p A ∧
  (∀ 𝔽 : Filtration (Fin (T + 1)) m0, 𝔽 0 = ⊥ → IsPredictableTranslationEquivariant P 𝔽 (A 𝔽)) ∧
  (∀ 𝔽 : Filtration (Fin (T + 1)) m0, 𝔽 0 = ⊥ → IsConcaveFunctional (A 𝔽)) ∧
  (∀ 𝔽 : Filtration (Fin (T + 1)) m0, 𝔽 0 = ⊥ → IsMonotoneFunctional P 𝔽 (A 𝔽))

end RiskFunctionals.MultiPeriod


