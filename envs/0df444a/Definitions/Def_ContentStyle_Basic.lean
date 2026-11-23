-- Prove2me | Definitions.Def_ContentStyle_Basic
-- name    : ContentStyle_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T19:11:18.556233+00:00
-- url     : https://prove2.me/theorems/bd915f8e-3388-4e7f-87c7-6901e230687c
-- title:
--   Content-style latent model, augmentation process, block-identifiability and SSL objectives
-- statement:
--   Objects of Sections 3 and 4 of von Kügelgen et al. (NeurIPS 2021).
--
--   1. **Latent space.** A latent is $z=(c,s)$ with content $c\in\mathbb{R}^{n_c}$ and style $s\in\mathbb{R}^{n_s}$. The representation space is $\mathcal Z=\mathcal C\times\mathcal S$, an open, simply connected subset of $\mathbb{R}^{n}$, $n=n_c+n_s$. Observations live in $\mathbb{R}^d$.
--   2. **Generative process (eqs. (2)–(3), Assumptions 3.1–3.2).** A model consists of a probability density $p_z$ on $\mathcal Z$, a probability distribution $p_A$ on the subsets $A\subseteq\{1,\dots,n_s\}$, and for each $A$ a conditional density $p(\tilde s_A\mid s_A)$ on $\mathbb{R}^{A}$, which is a probability density in $\tilde s_A$ for every $s_A\in\mathcal S_A$ (the image of $\mathcal S$ under $s\mapsto s_A$). The pair is drawn as $z\sim p_z$, $A\sim p_A$, $\tilde s_A\sim p(\cdot\mid s_A)$, $\tilde c=c$, $\tilde s_{A^c}=s_{A^c}$, and the augmented latent $\tilde z$ stays in $\mathcal Z$. With a mixing map $f$, the views are $x=f(z)$ and $\tilde x=f(\tilde z)$. $\mathbb P_p$ denotes the law of $(z,\tilde z)$, and $p_{x,\tilde x}$ the law of $(x,\tilde x)$.
--   3. **Conditions of Theorem 4.2.** (i) $f$ is smooth on $\mathcal Z$, injective, and its inverse is smooth on the observation space $\mathcal X=f(\mathcal Z)$. A function on a subset of $\mathbb{R}^m$ is smooth if near each point it agrees with a $C^\infty$ function on an open set. (ii) $p_z$ is smooth on $\mathcal Z$ and $p_z>0$ almost everywhere on $\mathcal Z$. (iii) Every style index $l$ lies in some $A$ with $p_A(A)>0$ for which $p(\tilde s_A\mid s_A)$ is smooth on $\mathcal S_A\times\mathcal S_A$, and for every $s_A\in\mathcal S_A$, $p(\cdot\mid s_A)>0$ on an open set containing $s_A$.
--   4. **Block-identifiability (Definition 4.1).** An inferred content map $\hat c$ on observations block-identifies the content if there is a map $h:\mathbb{R}^{n_c}\to\mathbb{R}^{n_c}$, injective on $\mathcal C$, with $\hat c(f(c,s))=h(c)$ for all $(c,s)\in\mathcal Z$.
--   5. **Objectives.** For a smooth bijection $g:\mathcal X\to\mathcal Z$, $L_{\mathrm{Align}}(g)=\mathbb E\,\|g(x)_{1:n_c}-g(\tilde x)_{1:n_c}\|_2^2$ (eq. (4)). For $g:\mathcal X\to(0,1)^{n_c}$, $L_{\mathrm{AlignMaxEnt}}(g)=\mathbb E\,\|g(x)-g(\tilde x)\|_2^2-H(g(x))$ (eq. (5)). Here $H(\mu)=-\int p\log p$ is the differential entropy of a law $\mu=p\,d\lambda$.
--
--   **Formalization Note** Latents are pairs in $\mathbb{R}^{n_c}\times\mathbb{R}^{n_s}$, and observations are points of $\mathbb{R}^d$; maps are total functions, and only their values on $\mathcal Z$ and $\mathcal X$ enter the statements. Expectations under the generative process are nonnegative extended-real integrals, so they are always defined. The differential entropy takes values in $[-\infty,\infty]$. It is $-\infty$ when the law has no density or $g\circ f$ is not measurable, which makes $L_{\mathrm{AlignMaxEnt}}=+\infty$. The inverse $f^{-1}$ is the inverse of $f$ on $\mathcal Z$ (`Function.invFunOn`). "Invertible $h$" in Definition 4.1 is formalized as injectivity on the content space $\mathcal C$, which is the invertibility the paper's proofs establish (as a map from $\mathcal C$ onto its image).
-- source:
--   von Kügelgen, Sharma, Gresele, Brendel, Schölkopf, Besserve and Locatello, Self-Supervised Learning with Data Augmentations Provably Isolates Content from Style, NeurIPS 2021, arXiv:2106.04619v4, Section 3 (eqs. (2)-(3), Assumptions 3.1-3.2, pp. 4-5) and Section 4 (Definition 4.1, p. 5; conditions (i)-(iii) of Theorem 4.2 and eq. (4), p. 6; eq. (5), p. 7)

import Mathlib

/-!
von Kügelgen, Sharma, Gresele, Brendel, Schölkopf, Besserve and Locatello,
*Self-Supervised Learning with Data Augmentations Provably Isolates Content from Style*,
NeurIPS 2021, arXiv:2106.04619v4: the latent space, the content-preserving augmentation process
(Section 3, eqs. (2)-(3), Assumptions 3.1-3.2), the regularity conditions (i)-(iii) of Theorem 4.2,
block-identifiability (Definition 4.1) and the objectives of eqs. (4)-(5) (Section 4).
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace ContentStyle

/-- Section 3: the latent space `ℝ^n = ℝ^{n_c} × ℝ^{n_s}`; a latent is `z = (c, s)` with content
`c = z_{1:n_c}` and style `s = z_{(n_c+1):n}`. -/
abbrev Latent (nc ns : ℕ) : Type := (Fin nc → ℝ) × (Fin ns → ℝ)

/-- Section 3: the ambient space `ℝ^d` of the observation space `𝒳 ⊆ ℝ^d`. -/
abbrev Obs (d : ℕ) : Type := Fin d → ℝ

/-- Section 3: `Z = C × S` is an open, simply connected subset of `ℝ^n`. -/
def IsLatentSpace {nc ns : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ)) : Prop :=
  IsOpen (C ×ˢ S) ∧ SimplyConnectedSpace (C ×ˢ S : Set (Latent nc ns))

/-- Assumption 3.2: the coordinates `s_A` of a style vector on the subset `A` of style indices. -/
def restr {ns : ℕ} (A : Finset (Fin ns)) (s : Fin ns → ℝ) : A → ℝ := fun i => s i

/-- Assumption 3.2: the subspace `S_A` of changing style variables, the image of `S` under
`s ↦ s_A`. -/
def projA {ns : ℕ} (A : Finset (Fin ns)) (S : Set (Fin ns → ℝ)) : Set (A → ℝ) := restr A '' S

/-- Assumption 3.2: the augmented style `s̃` with `s̃_{A^c} = s_{A^c}` and `s̃_A = t`. -/
def merge {ns : ℕ} (A : Finset (Fin ns)) (s : Fin ns → ℝ) (t : A → ℝ) : Fin ns → ℝ :=
  fun i => if h : i ∈ A then t ⟨i, h⟩ else s i

/-- Section 3, eqs. (2)-(3): the latent part of a generative model of pairs: the density `p_z`,
the distribution `p_A` on subsets `A ⊆ {1, …, n_s}` of changing style variables, and for each `A`
the conditional density `q A s_A s̃_A = p(s̃_A | s_A)` of Assumption 3.2. -/
structure LatentModel (nc ns : ℕ) where
  /-- The latent density `p_z`. -/
  pz : Latent nc ns → ℝ
  /-- The distribution `p_A` on subsets of style indices. -/
  pA : Finset (Fin ns) → ℝ
  /-- The conditional density `p(s̃_A | s_A)`. -/
  q : (A : Finset (Fin ns)) → (A → ℝ) → (A → ℝ) → ℝ

/-- Section 3, Assumptions 3.1 and 3.2: `p_z` is a probability density on `Z = C × S`; `p_A` is a
probability distribution on the subsets of `{1, …, n_s}`; for each `A` and `s_A ∈ S_A`,
`p(· | s_A)` is a probability density on `ℝ^A`; and the augmented latent `z̃ = (c, s̃)` stays in `Z`
(the conditional `p_{z̃|z}` lives on `Z × Z`). -/
def IsAugModel {nc ns : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (M : LatentModel nc ns) : Prop :=
  Measurable M.pz ∧ (∀ z ∈ C ×ˢ S, 0 ≤ M.pz z) ∧
    (∫⁻ z in C ×ˢ S, ENNReal.ofReal (M.pz z)) = 1 ∧
    (∀ A, 0 ≤ M.pA A) ∧ (∑ A, M.pA A) = 1 ∧
    ∀ A : Finset (Fin ns), Measurable (Function.uncurry (M.q A)) ∧
      (∀ a ∈ projA A S, ∀ t, 0 ≤ M.q A a t) ∧
      (∀ a ∈ projA A S, (∫⁻ t, ENNReal.ofReal (M.q A a t)) = 1) ∧
      (∀ s ∈ S, ∀ t, merge A s t ∉ S → M.q A (restr A s) t = 0)

/-- Eqs. (2)-(3): `E[φ(z, z̃)]` for the pair `(z, z̃)` drawn by `z ∼ p_z`, `A ∼ p_A`,
`s̃_A ∼ p(· | s_A)`, `c̃ = c`, `s̃_{A^c} = s_{A^c}` (as an extended nonnegative integral). -/
def pairLIntegral {nc ns : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (M : LatentModel nc ns) (φ : Latent nc ns × Latent nc ns → ENNReal) : ENNReal :=
  ∑ A : Finset (Fin ns), ENNReal.ofReal (M.pA A) *
    ∫⁻ z in C ×ˢ S, ENNReal.ofReal (M.pz z) *
      ∫⁻ t : A → ℝ, ENNReal.ofReal (M.q A (restr A z.2) t) * φ (z, (z.1, merge A z.2 t))

/-- Eqs. (2)-(3): the probability that the latent pair `(z, z̃)` lies in `E`. -/
def pairProb {nc ns : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (M : LatentModel nc ns) (E : Set (Latent nc ns × Latent nc ns)) : ENNReal :=
  pairLIntegral C S M (fun w => E.indicator (fun _ => 1) w)

/-- Eqs. (2)-(3): the probability that the observed pair `(x, x̃) = (f(z), f(z̃))` lies in `E`
(the law `p_{x,x̃}` of original and augmented views). -/
def obsPairProb {nc ns d : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (M : LatentModel nc ns) (f : Latent nc ns → Obs d) (E : Set (Obs d × Obs d)) : ENNReal :=
  pairLIntegral C S M (fun w => E.indicator (fun _ => 1) (f w.1, f w.2))

/-- Eq. (2): the law of the latent `z ∼ p_z` on `Z`. -/
def latentLaw {nc ns : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (M : LatentModel nc ns) : Measure (Latent nc ns) :=
  (volume.restrict (C ×ˢ S)).withDensity (fun z => ENNReal.ofReal (M.pz z))

/-- Section 3: a function on a subset `s` of a finite-dimensional space is smooth if near each
point of `s` it agrees on `s` with a `C^∞` function on an open set (for open `s` this is
`ContDiffOn ℝ ∞`; for the submanifold `𝒳 ⊆ ℝ^d` it is smoothness on `𝒳`). -/
def SmoothOnSet {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (s : Set E) (g : E → F) : Prop :=
  ∀ x ∈ s, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
    ∃ G : E → F, ContDiffOn ℝ ∞ G U ∧ Set.EqOn g G (U ∩ s)

/-- Theorem 4.2 (i): `f : Z → 𝒳 = f(Z)` is smooth and invertible with smooth inverse
(a diffeomorphism onto `𝒳`). -/
def CondI {nc ns d : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (f : Latent nc ns → Obs d) : Prop :=
  SmoothOnSet (C ×ˢ S) f ∧ Set.InjOn f (C ×ˢ S) ∧
    SmoothOnSet (f '' (C ×ˢ S)) (Function.invFunOn f (C ×ˢ S))

/-- Theorem 4.2 (ii): `p_z` is a smooth density on `Z` with `p_z(z) > 0` almost everywhere. -/
def CondII {nc ns : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (M : LatentModel nc ns) : Prop :=
  ContDiffOn ℝ ∞ M.pz (C ×ˢ S) ∧ ∀ᵐ z ∂(volume.restrict (C ×ˢ S)), 0 < M.pz z

/-- Theorem 4.2 (iii): for every style index `l` there is `A ∋ l` with `p_A(A) > 0` such that
`p(s̃_A | s_A)` is smooth in `(s_A, s̃_A)` on `S_A × S_A` and, for every `s_A ∈ S_A`,
`p(· | s_A) > 0` on some open set containing `s_A`. -/
def CondIII {nc ns : ℕ} (S : Set (Fin ns → ℝ)) (M : LatentModel nc ns) : Prop :=
  ∀ l : Fin ns, ∃ A : Finset (Fin ns), l ∈ A ∧ 0 < M.pA A ∧
    ContDiffOn ℝ ∞ (Function.uncurry (M.q A)) (projA A S ×ˢ projA A S) ∧
    ∀ a ∈ projA A S, ∃ O : Set (A → ℝ), IsOpen O ∧ a ∈ O ∧ ∀ t ∈ O, 0 < M.q A a t

/-- Definition 4.1: the true content `c = f⁻¹(x)_{1:n_c}` is block-identified by the inferred
content `ĉ(x)` if `ĉ = h(c)` for an invertible `h` (here: `h` injective on the content space
`C`), i.e. `ĉ(f(c, s)) = h(c)` for all `(c, s) ∈ Z`. -/
def BlockIdentifies {nc ns d : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (f : Latent nc ns → Obs d) (chat : Obs d → (Fin nc → ℝ)) : Prop :=
  ∃ h : (Fin nc → ℝ) → (Fin nc → ℝ), Set.InjOn h C ∧ ∀ z ∈ C ×ˢ S, chat (f z) = h z.1

/-- Squared Euclidean distance `‖a - b‖₂²`. -/
def sqDist {m : ℕ} (a b : Fin m → ℝ) : ℝ := ∑ i, (a i - b i) ^ 2

/-- Theorem 4.3: `g : 𝒳 → Z` is smooth and invertible (a smooth bijection of `𝒳 = f(Z)` onto `Z`). -/
def IsSmoothInvertible {nc ns d : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (f : Latent nc ns → Obs d) (g : Obs d → Latent nc ns) : Prop :=
  SmoothOnSet (f '' (C ×ˢ S)) g ∧ Set.BijOn g (f '' (C ×ˢ S)) (C ×ˢ S)

/-- Eq. (4): `L_Align(g) = E_{(x, x̃)} ‖g(x)_{1:n_c} - g(x̃)_{1:n_c}‖₂²`. -/
def alignLoss {nc ns d : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (M : LatentModel nc ns) (f : Latent nc ns → Obs d) (g : Obs d → Latent nc ns) : ENNReal :=
  pairLIntegral C S M (fun w => ENNReal.ofReal (sqDist (g (f w.1)).1 (g (f w.2)).1))

/-- Theorem 4.4: the open unit cube `(0,1)^{n_c}`. -/
def cube (m : ℕ) : Set (Fin m → ℝ) := Set.univ.pi (fun _ => Set.Ioo (0 : ℝ) 1)

open Classical in
/-- Theorem 4.4: differential entropy `H = -∫ p log p` of a law `μ` on `ℝ^m` with density
`p = dμ/dλ`, in `[-∞, ∞]`; it is `-∞` when `μ` has no density. -/
def diffEntropy {m : ℕ} (μ : Measure (Fin m → ℝ)) : EReal :=
  if μ ≪ volume then
    ((∫⁻ x, ENNReal.ofReal (Real.negMulLog (μ.rnDeriv volume x).toReal) : ENNReal) : EReal) -
      ((∫⁻ x, ENNReal.ofReal (-Real.negMulLog (μ.rnDeriv volume x).toReal) : ENNReal) : EReal)
  else ⊥

open Classical in
/-- Eq. (5): `L_AlignMaxEnt(g) = E_{(x, x̃)} ‖g(x) - g(x̃)‖₂² - H(g(x))` for `g : 𝒳 → (0,1)^{n_c}`,
where `g(x)` has the law of `g(f(z))`, `z ∼ p_z` (the entropy is `-∞`, so the loss `+∞`, when
`g ∘ f` is not a random variable). -/
def alignMaxEntLoss {nc ns d : ℕ} (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (M : LatentModel nc ns) (f : Latent nc ns → Obs d) (g : Obs d → (Fin nc → ℝ)) : EReal :=
  ((pairLIntegral C S M (fun w => ENNReal.ofReal (sqDist (g (f w.1)) (g (f w.2)))) : ENNReal) :
      EReal) -
    (if AEMeasurable (fun z => g (f z)) (latentLaw C S M) then
      diffEntropy ((latentLaw C S M).map (fun z => g (f z)))
    else ⊥)

end ContentStyle


