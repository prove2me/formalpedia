-- Prove2me | Definitions.Def_HiddenCorr_ERM_Complexity
-- name    : HiddenCorr_ERM_Complexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:34:29.113589+00:00
-- url     : https://prove2.me/theorems/4c8137be-07f6-477e-b097-ef10e2166b00
-- title:
--   Coefficient-normalized Rademacher complexities $\hat{\mathfrak R}_X$, $\hat{\mathfrak R}^{\mathrm{vec}}_X$, $\hat{\mathfrak R}^{\mathrm{multi}}_X$, the growth function $S_H(n)$ and label encodings
-- statement:
--   Let $\varepsilon_1,\dots,\varepsilon_n$ be independent unbiased **Rademacher signs** in $\{-1,+1\}$, independent of everything else; $\mathbb E_\varepsilon$ averages over the signs only, conditionally on a fixed sample $X=(X_1,\dots,X_n)$.
--
--   For a class $\mathcal G$ of real functions, points $u_1,\dots,u_m$ and coefficients $a_1,\dots,a_m$, the **weighted Rademacher average** is $\mathbb E_\varepsilon\sup_{g\in\mathcal G}\big|\sum_i\varepsilon_i a_i g(u_i)\big|$ (the quantity $R$ of Lemma 11).
--
--   **Definition 2** (coefficient-normalized empirical Rademacher complexity). For a class $F$ of real-valued functions on $\mathcal X$,
--   $$\hat{\mathfrak R}_X(F)=\sup_{\alpha\in\mathbb R^n,\ \|\alpha\|_2\le 1}\ \mathbb E_\varepsilon\sup_{f\in F}\Big|\sum_{i=1}^n\varepsilon_i\alpha_i f(X_i)\Big|.$$
--
--   **Definition 3** (vector version). For a class $F$ of functions $\mathcal X\to\mathbb R^k$,
--   $\hat{\mathfrak R}^{\mathrm{vec}}_X(F)=\sup_{a_1,\dots,a_n\in\mathbb R^k,\ \sum_i\|a_i\|_2^2\le1}\mathbb E_\varepsilon\sup_{f\in F}\big|\sum_i\varepsilon_i\langle a_i,f(X_i)\rangle\big|$.
--
--   **Multivariate version** (Lemma 4). With $nk$ independent signs $\varepsilon_{ir}$,
--   $\hat{\mathfrak R}^{\mathrm{multi}}_X(F)=\sup_{\|\alpha\|_2\le1}\mathbb E_\varepsilon\sup_{f\in F}\sum_{i=1}^n\sum_{r=1}^k\varepsilon_{ir}\alpha_i f_r(X_i)$ (no absolute value).
--
--   **Growth function** (Eq. (50)). For a class $H$ of hypotheses with values in $[k]$ (read as one-hot predictors $x\mapsto e_{h(x)}$), $S_H(n)=\sup_{x_1,\dots,x_n\in\mathcal X}\big|\{(h(x_1),\dots,h(x_n)):h\in H\}\big|$.
--
--   **Pointwise measurable class** (vector version of the published definition): some countable $F_0\subseteq F$ has every $f\in F$ as a pointwise limit of a sequence from $F_0$.
--
--   **Formalization Note.** A sign is a `Bool` (`sgn true = 1`, `sgn false = -1`); $\mathbb E_\varepsilon$ is the finite average over all $2^n$ (resp. $2^{nk}$) sign vectors. `radX`, `radVec` and `rademacherAvg` take values in $[0,\infty]$ (`ℝ≥0∞`), since they can be infinite for unbounded classes. `radMulti` takes values in `EReal`: its inner supremum may be negative for some sign vectors, and only the empty class gives $-\infty$. $\mathbb R^k$ is `EuclideanSpace ℝ (Fin k)`. `b2r b ∈ {0,1}` and `onehot r = e_r` encode binary and multiclass labels. `IsPointwiseMeasurableClassV` is, for real values, literally the published `IsPointwiseMeasurableClass`; it is used for vector- and pair-valued classes.
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 21, Definitions 2 and 3; p. 22, Lemma 4; p. 31, Eq. (50); p. 61, Lemma 11; p. 13, footnote 1

import Mathlib

open scoped ENNReal
open Filter Topology

namespace HiddenCorr.ERM

/-!
# Coefficient-normalized Rademacher complexities, growth function, label encodings

Chen, Gentile, Kaplan, Koren, *Supervised Learning with Hidden Correspondences*, STOC 2027
submission (manuscript sha256 d0029978…), Definitions 2 and 3 (p. 21), `R̂^multi_X` (Lemma 4,
p. 22), Lemma 11 (p. 61), Eq. (50) (p. 31), footnote 1 (p. 13).

* A Rademacher sign `εᵢ ∈ {−1, +1}` is encoded by a `Bool` (`true ↦ +1`, `false ↦ −1`); the
  expectation `E_ε` over independent unbiased signs is the uniform average over all sign vectors
  (a finite sum divided by `2^n`), conditional on the sample.
* The complexities with an absolute value (`R̂_X`, `R̂^vec_X`, the Rademacher average of
  Lemma 11) take values in `[0, ∞]` (`ℝ≥0∞`), since they may be infinite for unbounded classes.
* `R̂^multi_X` has no absolute value; its inner supremum may be negative for some sign vectors,
  so it takes values in `EReal` (`⊥` only for the empty class).
* `ℝ^k` is `EuclideanSpace ℝ (Fin k)` (Euclidean norm and inner product).
-/

/-- The value `±1` of a Rademacher sign encoded by a `Bool`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The real number `0` or `1` encoding a binary label or prediction in `{0, 1}`. -/
def b2r (b : Bool) : ℝ := if b then 1 else 0

/-- The one-hot encoding `e_r ∈ ℝ^k` of the class label `r ∈ [k]`. -/
noncomputable def onehot {k : ℕ} (r : Fin k) : EuclideanSpace ℝ (Fin k) :=
  EuclideanSpace.single r 1

/-- The weighted Rademacher average `E_ε sup_{g ∈ G} |∑ᵢ εᵢ aᵢ g(uᵢ)|` of a class `G` of
real-valued functions at the points `u₁, …, u_m` with coefficients `a₁, …, a_m` (the quantity `R` of
Lemma 11, p. 61), the expectation being over independent unbiased signs only. -/
noncomputable def rademacherAvg {𝒳 : Type*} {m : ℕ} (a : Fin m → ℝ) (u : Fin m → 𝒳)
    (G : Set (𝒳 → ℝ)) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ m)⁻¹ *
    ∑ ε : Fin m → Bool, ⨆ g ∈ G, ENNReal.ofReal |∑ i, sgn (ε i) * a i * g (u i)|

/-- Definition 2 (p. 21), the coefficient-normalized empirical Rademacher complexity
`R̂_X(F) = sup_{α ∈ ℝⁿ, ‖α‖₂ ≤ 1} E_ε sup_{f ∈ F} |∑ᵢ εᵢ αᵢ f(Xᵢ)|` of a class `F` of real-valued
functions at the sample `X = (X₁, …, Xₙ)`. -/
noncomputable def radX {𝒳 : Type*} {n : ℕ} (X : Fin n → 𝒳) (F : Set (𝒳 → ℝ)) : ℝ≥0∞ :=
  ⨆ (α : Fin n → ℝ) (_ : ∑ i, α i ^ 2 ≤ 1), rademacherAvg α X F

/-- Definition 3 (p. 21), the vector coefficient-normalized Rademacher complexity
`R̂^vec_x(F) = sup_{a₁, …, aₙ ∈ ℝ^k, ∑ᵢ ‖aᵢ‖₂² ≤ 1} E_ε sup_{f ∈ F} |∑ᵢ εᵢ ⟨aᵢ, f(xᵢ)⟩|` of a class `F`
of functions `X → ℝ^k`. -/
noncomputable def radVec {𝒳 : Type*} {n k : ℕ} (X : Fin n → 𝒳)
    (F : Set (𝒳 → EuclideanSpace ℝ (Fin k))) : ℝ≥0∞ :=
  ⨆ (a : Fin n → EuclideanSpace ℝ (Fin k)) (_ : ∑ i, ‖a i‖ ^ 2 ≤ 1),
    ((2 : ℝ≥0∞) ^ n)⁻¹ *
      ∑ ε : Fin n → Bool, ⨆ f ∈ F, ENNReal.ofReal |∑ i, sgn (ε i) * inner ℝ (a i) (f (X i))|

/-- The multivariate coefficient-normalized complexity of Lemma 4 (p. 22),
`R̂^multi_X(F) = sup_{‖α‖₂ ≤ 1} E_ε sup_{f ∈ F} ∑ᵢ ∑_{r=1}^k ε_{ir} αᵢ f_r(Xᵢ)`, with `n·k` independent
unbiased signs `ε_{ir}` and no absolute value. Valued in `EReal`. -/
noncomputable def radMulti {𝒳 : Type*} {n k : ℕ} (X : Fin n → 𝒳)
    (F : Set (𝒳 → EuclideanSpace ℝ (Fin k))) : EReal :=
  ⨆ (α : Fin n → ℝ) (_ : ∑ i, α i ^ 2 ≤ 1),
    ((((2 : ℝ) ^ (n * k))⁻¹ : ℝ) : EReal) *
      ∑ ε : Fin n → Fin k → Bool,
        ⨆ f ∈ F, ((∑ i, ∑ r, sgn (ε i r) * α i * f (X i) r : ℝ) : EReal)

/-- The growth function of Eq. (50) (p. 31) of a class `H` of `[k]`-valued hypotheses (the class
`{x ↦ e_{h(x)}}` of one-hot predictors, with `h̄ = h`):
`S_H(n) = sup_{x₁, …, xₙ ∈ X} |{(h(x₁), …, h(xₙ)) : h ∈ H}|`. -/
noncomputable def growthFn {𝒳 : Type*} {k : ℕ} (H : Set (𝒳 → Fin k)) (n : ℕ) : ℕ := by
  classical
  exact ⨆ x : Fin n → 𝒳,
    (Finset.univ.filter (fun v : Fin n → Fin k => ∃ h ∈ H, ∀ i, h (x i) = v i)).card

/-- Pointwise measurability of a class of functions with values in a topological space `V` (the
mission's reading of footnote 1, p. 13, for vector-valued classes): some countable subclass
`F₀ ⊆ F` has every `f ∈ F` as a pointwise limit of a sequence in `F₀`. For `V = ℝ` this is
literally the published `BartlettBousquetMendelson.LocalRad.IsPointwiseMeasurableClass`. -/
def IsPointwiseMeasurableClassV {𝒳 V : Type*} [TopologicalSpace V] (F : Set (𝒳 → V)) : Prop :=
  ∃ F₀ ⊆ F, F₀.Countable ∧ ∀ f ∈ F, ∃ u : ℕ → 𝒳 → V, (∀ j, u j ∈ F₀) ∧
    ∀ y, Tendsto (fun j => u j y) atTop (𝓝 (f y))

end HiddenCorr.ERM


