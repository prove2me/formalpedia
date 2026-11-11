-- Prove2me | Definitions.Def_OptAbstention_TLA_CappedReweighting
-- name    : OptAbstention_TLA_CappedReweighting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:06:26.33366+00:00
-- url     : https://prove2.me/theorems/2e2c160b-cf6c-4872-819b-bb1dbfbeb3d8
-- title:
--   Capped-reweighting sets $K_R(M)$, support functions, the class $\mathcal F$ of hinge differences, VC-subgraph dimension and pointwise measurability
-- statement:
--   Let $\Omega$ be a measurable space and $\psi:\Omega\to\mathbb R^k$. For a distribution $M$ on $\Omega$ and $R\ge1$,
--   $$K_R(M)=\{\mathbb E_{x\sim M}[r(x)\psi(x)]:\ r:\Omega\to[0,R]\text{ measurable},\ \mathbb E_{x\sim M}[r(x)]=1\}\subseteq\mathbb R^k .$$
--   $U(S)$ for a list $S$ is the uniform measure $\frac1n\sum_i\delta_{S_i}$. The **support function** of $A\subseteq\mathbb R^k$ is $H_A(q)=\sup_{a\in A}q\cdot a$ (the published support functional, in the extended reals). $[-a,a]^k$ is the $\ell_\infty$ box and $\|q\|_1=\sum_i|q_i|$. For $t\in\mathbb R$, $q\in\mathbb R^k$ let $\phi_{t,q}(x)=(q\cdot\psi(x)-t)_+-(-t)_+$ and $\mathcal F=\{\phi_{t,q}:\|q\|_1\le1\}$.
--
--   The **subgraph** of $f:\Omega\to\mathbb R$ is $\{(x,t):t<f(x)\}$; the **VC-subgraph dimension** of a class $\mathcal F\subseteq\mathbb R^\Omega$ is the VC dimension of its subgraphs (the published Vapnik VC dimension, in $\mathbb N\cup\{\infty\}$). $\mathcal F$ is **pointwise measurable** if a countable $\mathcal F_0\subseteq\mathcal F$ approximates every $f\in\mathcal F$ pointwise by a sequence from $\mathcal F_0$.
--
--   **Formalization Note.** $K_R(M)$ requires $r\psi$ to be $M$-integrable, so that the expectation is a vector of $\mathbb R^k$. $H_\emptyset=-\infty$.
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 35, Definitions A.2, A.3, A.7 and footnote 12; p. 38, Lemma B.2; p. 39

import Mathlib
import Definitions.Def_VectorSpaceOpt_support_functional
import Definitions.Def_NatureSLT_GrowthFunction_vcDim

/-!
# Capped-reweighting sets `K_R(M)`, support functions, the class `F` and VC-subgraph dimension

Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, *Achieving the Optimal Abstention Rate
for Learning with Distribution Shift*, STOC 2027 submission (manuscript sha256 0fb30af1…):
Definitions A.2, A.3 and A.7 and footnote 12 (p. 35); Lemma B.2 (p. 38, the set `K_R(M)`);
p. 39 (the functions `ϕ_{t,q}` and the class `F`).

Conventions.
* `Ω` is a measurable space; `ψ : Ω → ℝ^k` with `ℝ^k = Fin k → ℝ`. `‖ψ(x)‖_∞` is the norm of
  `Fin k → ℝ` (Mathlib's sup norm).
* `U(S)` of a list `S : Fin n → Ω` is the measure `(1/n) ∑_i δ_{S i}`.
* `K_R(M)` collects `E_M[r ψ]` over measurable `r : Ω → [0, R]` with `E_M[r] = 1` for which `r ψ`
  is `M`-integrable (so that the expectation is a vector of `ℝ^k`).
* The support function `H_A(q) = sup_{a∈A} q · a` is the published
  `VectorSpaceOpt_support_functional` (valued in `EReal`, `-∞` on the empty set) applied to the
  linear functional `a ↦ q · a`.
* VC-subgraph dimension: the VC dimension (published `NatureSLT.GrowthFunction.vcDim`) of the
  subgraphs `subg(f) = {(x, t) : t < f(x)}`, `f ∈ F`.
-/

open MeasureTheory

namespace OptAbstention.TLA

/-- `U(S)`, the uniform distribution on the occurrences of `S : Fin n → Ω`. -/
noncomputable def empMeasure {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (S : Fin n → Ω) :
    Measure Ω :=
  (n : ENNReal)⁻¹ • ∑ i, Measure.dirac (S i)

/-- Lemma B.2: `K_R(M) = {E_{x∼M}[r(x) ψ(x)] : r ∈ [0, R]^Ω measurable, E_{x∼M}[r(x)] = 1}`. -/
def KR {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : Measure Ω) (ψ : Ω → Fin k → ℝ) (R : ℝ) :
    Set (Fin k → ℝ) :=
  {v | ∃ r : Ω → ℝ, Measurable r ∧ (∀ x, 0 ≤ r x ∧ r x ≤ R) ∧ ∫ x, r x ∂M = 1 ∧
    Integrable (fun x => r x • ψ x) M ∧ v = ∫ x, r x • ψ x ∂M}

/-- The linear functional `a ↦ q · a = ∑_i q_i a_i` on `ℝ^k`. -/
noncomputable def dotCLM {k : ℕ} (q : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i, q i • ContinuousLinearMap.proj i

/-- Definition A.7: the support function `H_A(q) = sup_{a∈A} q · a` (in `EReal`). -/
noncomputable def supportFn {k : ℕ} (A : Set (Fin k → ℝ)) (q : Fin k → ℝ) : EReal :=
  VectorSpaceOpt_support_functional A (dotCLM q)

/-- The box `[-a, a]^k`. -/
def boxSet (k : ℕ) (a : ℝ) : Set (Fin k → ℝ) :=
  Set.pi Set.univ fun _ => Set.Icc (-a) a

/-- `‖q‖₁ = ∑_i |q_i|`. -/
def l1norm {k : ℕ} (q : Fin k → ℝ) : ℝ := ∑ i, |q i|

/-- p. 39: `ϕ_{t,q}(x) = (q · ψ(x) − t)_+ − (−t)_+`. -/
def phiFn {Ω : Type*} {k : ℕ} (ψ : Ω → Fin k → ℝ) (t : ℝ) (q : Fin k → ℝ) : Ω → ℝ :=
  fun x => max (∑ i, q i * ψ x i - t) 0 - max (-t) 0

/-- p. 39: the class `F = {ϕ_{t,q} : t ∈ ℝ, q ∈ ℝ^k, ‖q‖₁ ≤ 1}`. -/
def phiClass {Ω : Type*} {k : ℕ} (ψ : Ω → Fin k → ℝ) : Set (Ω → ℝ) :=
  {φ | ∃ t q, l1norm q ≤ 1 ∧ φ = phiFn ψ t q}

open Classical in
/-- Definitions A.2–A.3: the VC-subgraph dimension of `F ⊆ ℝ^Ω`, the VC dimension of the
collection of subgraphs `subg(f) = {(x, t) ∈ Ω × ℝ : t < f(x)}`, `f ∈ F` (in `ℕ∞`). -/
noncomputable def vcSubgraphDim {Ω : Type*} (F : Set (Ω → ℝ)) : ℕ∞ :=
  NatureSLT.GrowthFunction.vcDim (fun (f : F) (p : Ω × ℝ) => decide (p.2 < (f : Ω → ℝ) p.1))

/-- Footnote 12: `F` is pointwise measurable: some countable subclass `F₀ ⊆ F` approximates every
`f ∈ F` pointwise by a sequence of its members. -/
def PointwiseMeasurableClass {Ω : Type*} (F : Set (Ω → ℝ)) : Prop :=
  ∃ F₀ ⊆ F, F₀.Countable ∧ ∀ f ∈ F, ∃ g : ℕ → Ω → ℝ, (∀ j, g j ∈ F₀) ∧
    ∀ x, Filter.Tendsto (fun j => g j x) Filter.atTop (nhds (f x))

end OptAbstention.TLA


