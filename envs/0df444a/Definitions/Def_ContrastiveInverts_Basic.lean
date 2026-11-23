-- Prove2me | Definitions.Def_ContrastiveInverts_Basic
-- name    : ContrastiveInverts_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T18:41:05.740677+00:00
-- url     : https://prove2.me/theorems/211f38f5-a9f5-4e16-8c62-54f8fa3713f4
-- title:
--   Latent spaces, positive-pair conditionals, cross-entropies and InfoNCE objectives of Zimmermann et al. (2021)
-- statement:
--   Objects of Section 3, Definition 1 and Appendices A.1.1 and A.2.1 of Zimmermann, Sharma, Schneider, Bethge and Brendel (2021). Observations are $x=g(z)$ for latents $z$, an encoder $f$ is trained on observations, and every objective depends on $f$ only through $h=f\circ g$, so it is written on latents.
--
--   1. **Hypersphere.** $Z=\mathbb{S}^{N-1}\subset\mathbb{R}^N$ carries its surface measure $\sigma$, of total mass $|Z|$. The marginal is uniform, $p(z)=|Z|^{-1}$.
--   2. **von Mises–Fisher conditional (eq. 2).** $p(\tilde z\mid z)=C_p^{-1}e^{\kappa z^\top\tilde z}$ with $C_p=\int_Z e^{\kappa z^\top\tilde z}\,d\sigma(\tilde z)$.
--   3. **Model conditional (eq. 4).** For $\tau>0$, $q_h(\tilde z\mid z)=C_h(z)^{-1}e^{h(\tilde z)^\top h(z)/\tau}$ with $C_h(z)=\int_Z e^{h(\tilde z)^\top h(z)/\tau}\,d\sigma(\tilde z)$.
--   4. **Cross-entropies.** $H(p(\cdot\mid z),q_h(\cdot\mid z))=\int_Z p(\tilde z\mid z)\,(-\log q_h(\tilde z\mid z))\,d\sigma(\tilde z)$ at a fixed anchor $z$, and its average $\mathbb{E}_{z\sim p(z)}H(p(\cdot\mid z),q_h(\cdot\mid z))$.
--   5. **InfoNCE (eq. 1).** With $(z,\tilde z)$ drawn as $z\sim p(z)$, $\tilde z\sim p(\tilde z\mid z)$, and negatives $z_1^-,\dots,z_M^-$ i.i.d. uniform,
--   $$\mathcal{L}_{\mathsf{contr}}(f;\tau,M)=\mathbb{E}\Big[-\log\frac{e^{h(z)^\top h(\tilde z)/\tau}}{e^{h(z)^\top h(\tilde z)/\tau}+\sum_{i=1}^M e^{h(z)^\top h(z_i^-)/\tau}}\Big].$$
--   The objective minimised "for $M\to\infty$" is $\lim_{M\to\infty}(\mathcal{L}_{\mathsf{contr}}(f;\tau,M)-\log M)$.
--   6. **Convex bodies.** $Z\subset\mathbb{R}^N$ is compact and convex with nonempty interior, carries Lebesgue measure, has volume $|Z|$ and uniform marginal $p(z)=|Z|^{-1}$.
--   7. **(Semi-)metrics induced by a norm (eq. 5, Lemma 1).** $\delta(a,b)=j(\nu(a-b))$ for a norm $\nu$ on $\mathbb{R}^N$ and a continuous bijection $j$ of $[0,\infty)$ with $j(0)=0$ ($j=\mathrm{id}$ is the metric case). The $L^\alpha$ metric is $\big(\sum_i|a_i-b_i|^\alpha\big)^{1/\alpha}$.
--   8. **Exponential conditional (eq. 5, Appendix A.2.1).** For $\lambda>0$, $p(\tilde z\mid z)=C_p(z)^{-1}e^{-\lambda\delta(\tilde z,z)}$ with $C_p(z)=\int_Z e^{-\lambda\delta(z,\tilde z)}\,d\tilde z$. Eq. (5) is the case $\lambda=1$.
--   9. **Model conditional (eq. 7).** $q_h(\tilde z\mid z)=C_h(z)^{-1}e^{-\delta(h(\tilde z),h(z))/\tau}$ with $C_h(z)=\int_Z e^{-\delta(h(\tilde z),h(z))/\tau}\,d\tilde z$. The cross-entropies are defined as in item 4, with Lebesgue measure on $Z$.
--   10. **General InfoNCE (Definition 1, eq. 6).**
--   $$\mathcal{L}_{\delta\text{-contr}}(f;\tau,M)=\mathbb{E}\Big[-\log\frac{e^{-\delta(h(z),h(\tilde z))/\tau}}{e^{-\delta(h(z),h(\tilde z))/\tau}+\sum_{i=1}^M e^{-\delta(h(z),h(z_i^-))/\tau}}\Big],$$
--   with positive pairs from $p$ and i.i.d. uniform negatives. Its alignment and uniformity parts (Proposition 3) are $\mathcal{L}_{\delta\text{-align}}=\tau^{-1}\mathbb{E}_{z,\tilde z}\,\delta(h(\tilde z),h(z))$ and $\mathcal{L}_{\delta\text{-unif}}=\mathbb{E}_{z\sim p(z)}\log\mathbb{E}_{\tilde z\sim p(\tilde z)}e^{-\delta(h(\tilde z),h(z))/\tau}$, where $p(\tilde z)$ is the uniform marginal.
--
--   **Formalization Note** The ground-truth distance $\delta_p$ (with $\lambda$) and the model distance $\delta$ (with $\tau$) are separate arguments of the convex-body objectives, so that Theorem 6 can use a model distance equal to a constant multiple of the ground-truth one. $C_p$ is defined as a function of the anchor $z$; on the sphere this is the paper's constant, by rotation invariance. The objective "for $M\to\infty$" is Lean's `limUnder`, which equals the true limit whenever the limit exists; Theorem 1 asserts that it exists for every measurable encoder with values in a sphere $\mathbb{S}^{N-1}_r$ (under the standing assumptions on $g$), and Theorem 3 for every encoder with values in the convex body $Z'$ that is a.e.-measurable.
-- source:
--   Zimmermann, Sharma, Schneider, Bethge and Brendel, Contrastive Learning Inverts the Data Generating Process, ICML 2021, arXiv:2102.08850v4, Section 3 (eqs. (1)-(7), Definition 1, pp. 2-5), Appendix A.1.1 (p. 13) and Appendix A.2.1 (p. 15)

import Mathlib

/-!
Zimmermann, Sharma, Schneider, Bethge and Brendel, *Contrastive Learning Inverts the Data
Generating Process*, ICML 2021, arXiv:2102.08850v4: the latent spaces, ground-truth and model
conditional distributions, cross-entropies and InfoNCE objectives of Section 3, Definition 1 and
Appendices A.1.1 and A.2.1 (PDF pp. 2-5, 13-18).

Hypersphere setting (Sections 3.1-3.2, Appendix A.1): latents live on the unit sphere
`S^{N-1} ⊂ ℝ^N` with its surface measure, the marginal is uniform and positive pairs follow a
von Mises-Fisher conditional. Convex-body setting (Section 3.3, Appendix A.2): latents live in a
convex body `Z ⊂ ℝ^N` with Lebesgue measure, the marginal is uniform and the conditional is
`∝ exp(-λ δ(z̃, z))` for a (semi-)metric `δ` induced by a norm. Objectives are written in terms of
`h = f ∘ g`, as in the paper, since observations are `x = g(z)`.
-/

open MeasureTheory Filter

noncomputable section

namespace ContrastiveInverts

/-- Section 3: the latent and representation space `ℝ^N`, with its Euclidean inner product. -/
abbrev Vec (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- Section 3 and Appendix A.1.1: the unit hypersphere `Z = S^{N-1} ⊂ ℝ^N`, as a type. -/
abbrev Sph (N : ℕ) := Metric.sphere (0 : Vec N) 1

/-- Section 3, eq. (2): the surface (Hausdorff) measure on `S^{N-1}`, against which `dz̃` in the
normalising constants is taken. -/
def sphereMeasure (N : ℕ) : Measure (Sph N) := (volume : Measure (Vec N)).toSphere

/-- Section 3, eq. (2) and Theorem 1: `|Z|`, the surface area of `S^{N-1}`. -/
def sphereArea (N : ℕ) : ℝ := (sphereMeasure N Set.univ).toReal

/-- Section 3, eq. (2): the uniform marginal `p(z) = |Z|^{-1}` on `S^{N-1}`. -/
def sphereUnif (N : ℕ) : Measure (Sph N) := (sphereMeasure N Set.univ)⁻¹ • sphereMeasure N

/-- Eq. (2) and Appendix A.1.1: the von Mises-Fisher normalising constant
`C_p = ∫ exp(κ zᵀ z̃) dz̃` (independent of `z` by rotation invariance). -/
def vmfConst (N : ℕ) (κ : ℝ) (z : Vec N) : ℝ :=
  ∫ w : Sph N, Real.exp (κ * inner ℝ z (w : Vec N)) ∂sphereMeasure N

/-- Eq. (2): the von Mises-Fisher conditional of positive pairs,
`p(z̃ | z) = C_p^{-1} exp(κ zᵀ z̃)`, a density with respect to the surface measure. -/
def vmfCond (N : ℕ) (κ : ℝ) (z z' : Vec N) : ℝ :=
  Real.exp (κ * inner ℝ z z') / vmfConst N κ z

/-- Theorem 1, eq. (4): the partition function `C_h(z) = ∫ exp(h(z̃)ᵀ h(z) / τ) dz̃` of the model
conditional. -/
def sphModelConst {N : ℕ} (τ : ℝ) (h : Vec N → Vec N) (z : Vec N) : ℝ :=
  ∫ w : Sph N, Real.exp (inner ℝ (h w) (h z) / τ) ∂sphereMeasure N

/-- Theorem 1, eq. (4): the model conditional `q_h(z̃ | z) = C_h(z)^{-1} exp(h(z̃)ᵀ h(z) / τ)`. -/
def sphModelCond {N : ℕ} (τ : ℝ) (h : Vec N → Vec N) (z z' : Vec N) : ℝ :=
  Real.exp (inner ℝ (h z') (h z) / τ) / sphModelConst τ h z

/-- Proposition 1: the cross-entropy `H(p(· | z), q_h(· | z)) = E_{p(z̃|z)}[-log q_h(z̃ | z)]` at a
fixed anchor `z`. -/
def sphCondCrossEntropy {N : ℕ} (κ τ : ℝ) (h : Vec N → Vec N) (z : Vec N) : ℝ :=
  ∫ w : Sph N, vmfCond N κ z w * -Real.log (sphModelCond τ h z w) ∂sphereMeasure N

/-- Theorem 1, eq. (3): the expected cross-entropy `E_{z ∼ p(z)} H(p(· | z), q_h(· | z))`. -/
def sphCrossEntropy {N : ℕ} (κ τ : ℝ) (h : Vec N → Vec N) : ℝ :=
  ∫ z : Sph N, sphCondCrossEntropy κ τ h z ∂sphereUnif N

/-- Section 3: the law of latent positive pairs `(z, z̃)`, `z ∼ p(z)` uniform and
`z̃ ∼ p(z̃ | z)` von Mises-Fisher; `p_pos` is its image under `g × g`. -/
def sphPosPairLaw (N : ℕ) (κ : ℝ) : Measure (Sph N × Sph N) :=
  ((sphereUnif N).prod (sphereMeasure N)).withDensity
    (fun q => ENNReal.ofReal (vmfCond N κ q.1 q.2))

/-- Eq. (1): the InfoNCE objective `L_contr(f; τ, M)` with `M` negatives, written on latents with
`h = f ∘ g`: `(x, x̃) = (g z, g z̃)` is a positive pair and `x_i^- = g z_i^-` with
`z_i^-` i.i.d. uniform. -/
def infoNCE {N : ℕ} (κ τ : ℝ) (h : Vec N → Vec N) (M : ℕ) : ℝ :=
  ∫ w : (Sph N × Sph N) × (Fin M → Sph N),
    -Real.log (Real.exp (inner ℝ (h w.1.1) (h w.1.2) / τ) /
      (Real.exp (inner ℝ (h w.1.1) (h w.1.2) / τ) +
        ∑ i, Real.exp (inner ℝ (h w.1.1) (h (w.2 i)) / τ)))
    ∂(sphPosPairLaw N κ).prod (Measure.pi fun _ : Fin M => sphereUnif N)

/-- Theorems 1-2: the objective minimised "for `M → ∞`",
`lim_{M → ∞} (L_contr(f; τ, M) - log M)`. -/
def infoNCELimit {N : ℕ} (κ τ : ℝ) (h : Vec N → Vec N) : ℝ :=
  limUnder atTop (fun M : ℕ => infoNCE κ τ h M - Real.log M)

/-- Section 3.3 and Appendix A.2.1: a convex body in `ℝ^N` (compact, convex, nonempty
interior). -/
def IsConvexBody {N : ℕ} (Z : Set (Vec N)) : Prop :=
  Convex ℝ Z ∧ IsCompact Z ∧ (interior Z).Nonempty

/-- Eq. (5): `|Z|`, the Lebesgue volume of the latent space. -/
def bodyVolume {N : ℕ} (Z : Set (Vec N)) : ℝ := (volume Z).toReal

/-- Eq. (5): the uniform marginal `p(z) = |Z|^{-1}` on `Z`, as a measure on `ℝ^N`. -/
def bodyUnif {N : ℕ} (Z : Set (Vec N)) : Measure (Vec N) := (volume Z)⁻¹ • volume.restrict Z

/-- Eq. (5): `ν` is a norm on `ℝ^N` (not necessarily the Euclidean one). -/
structure IsNormFn {N : ℕ} (ν : Vec N → ℝ) : Prop where
  eq_zero_iff : ∀ x, ν x = 0 ↔ x = 0
  smul : ∀ (c : ℝ) (x : Vec N), ν (c • x) = |c| * ν x
  add_le : ∀ x y, ν (x + y) ≤ ν x + ν y

/-- Appendix A.2.1 and Lemma 1: `j : ℝ≥0 → ℝ≥0` is a continuous bijection with `j(0) = 0`
(a "continuously invertible map"); values of `j` off `[0, ∞)` are irrelevant. -/
def IsReparam (j : ℝ → ℝ) : Prop :=
  Set.BijOn j (Set.Ici 0) (Set.Ici 0) ∧ ContinuousOn j (Set.Ici 0) ∧ j 0 = 0

/-- Eq. (5), Appendix A.2.1 and Lemma 1: `δ` is a metric induced by a norm, `δ(a, b) = ν(a - b)`,
or a semi-metric `δ = j ∘ δ'` of such a metric (`j = id` gives the metric case). -/
def IsNormSemimetric {N : ℕ} (δ : Vec N → Vec N → ℝ) : Prop :=
  ∃ (ν : Vec N → ℝ) (j : ℝ → ℝ), IsNormFn ν ∧ IsReparam j ∧ ∀ a b, δ a b = j (ν (a - b))

/-- Theorem 6: the `L^α` metric `δ(a, b) = (∑_i |a_i - b_i|^α)^{1/α}`. -/
def lpDist {N : ℕ} (α : ℝ) (a b : Vec N) : ℝ := (∑ i, |a i - b i| ^ α) ^ (1 / α)

/-- Appendix A.2.1: the normalising constant `C_p(z) = ∫_Z exp(-λ δ(z, z̃)) dz̃`. -/
def expConst {N : ℕ} (lam : ℝ) (δ : Vec N → Vec N → ℝ) (Z : Set (Vec N)) (z : Vec N) : ℝ :=
  ∫ w in Z, Real.exp (-lam * δ z w)

/-- Eq. (5) and Appendix A.2.1: the ground-truth conditional
`p(z̃ | z) = C_p(z)^{-1} exp(-λ δ(z̃, z))` on `Z` (eq. (5) is the case `λ = 1`). -/
def expCond {N : ℕ} (lam : ℝ) (δ : Vec N → Vec N → ℝ) (Z : Set (Vec N)) (z z' : Vec N) : ℝ :=
  Real.exp (-lam * δ z' z) / expConst lam δ Z z

/-- Eq. (7) and Theorem 3: `C_h(z) = ∫_Z exp(-δ(h(z̃), h(z)) / τ) dz̃`. -/
def bodyModelConst {N : ℕ} (τ : ℝ) (δ : Vec N → Vec N → ℝ) (Z : Set (Vec N))
    (h : Vec N → Vec N) (z : Vec N) : ℝ :=
  ∫ w in Z, Real.exp (-δ (h w) (h z) / τ)

/-- Eq. (7) and Theorem 3: the model conditional
`q_h(z̃ | z) = C_h(z)^{-1} exp(-δ(h(z̃), h(z)) / τ)`. -/
def bodyModelCond {N : ℕ} (τ : ℝ) (δ : Vec N → Vec N → ℝ) (Z : Set (Vec N))
    (h : Vec N → Vec N) (z z' : Vec N) : ℝ :=
  Real.exp (-δ (h z') (h z) / τ) / bodyModelConst τ δ Z h z

/-- Proposition 4: `H(p(· | z), q_h(· | z)) = E_{p(z̃|z)}[-log q_h(z̃ | z)]` at a fixed anchor `z`;
`p` uses `(λ, δp)` and `q_h` uses `(τ, δ)`. -/
def bodyCondCrossEntropy {N : ℕ} (lam : ℝ) (δp : Vec N → Vec N → ℝ) (τ : ℝ)
    (δ : Vec N → Vec N → ℝ) (Z : Set (Vec N)) (h : Vec N → Vec N) (z : Vec N) : ℝ :=
  ∫ w in Z, expCond lam δp Z z w * -Real.log (bodyModelCond τ δ Z h z w)

/-- Theorems 3-4: the expected cross-entropy `E_{z ∼ p(z)} H(p(· | z), q_h(· | z))`. -/
def bodyCrossEntropy {N : ℕ} (lam : ℝ) (δp : Vec N → Vec N → ℝ) (τ : ℝ)
    (δ : Vec N → Vec N → ℝ) (Z : Set (Vec N)) (h : Vec N → Vec N) : ℝ :=
  ∫ z, bodyCondCrossEntropy lam δp τ δ Z h z ∂bodyUnif Z

/-- Appendix A.2.1: the law of latent positive pairs `(z, z̃)`, `z ∼ p(z)` uniform on `Z` and
`z̃ ∼ p(z̃ | z)`. -/
def bodyPosPairLaw {N : ℕ} (lam : ℝ) (δp : Vec N → Vec N → ℝ) (Z : Set (Vec N)) :
    Measure (Vec N × Vec N) :=
  ((bodyUnif Z).prod (volume.restrict Z)).withDensity
    (fun q => ENNReal.ofReal (expCond lam δp Z q.1 q.2))

/-- Definition 1, eq. (6): the general InfoNCE objective `L_δ-contr(f; τ, M)` with similarity
measure `δ`, written on latents with `h = f ∘ g`; positive pairs come from `p` with `(λ, δp)` and
the `M` negatives are i.i.d. uniform on `Z`. -/
def deltaInfoNCE {N : ℕ} (lam : ℝ) (δp : Vec N → Vec N → ℝ) (τ : ℝ) (δ : Vec N → Vec N → ℝ)
    (Z : Set (Vec N)) (h : Vec N → Vec N) (M : ℕ) : ℝ :=
  ∫ w : (Vec N × Vec N) × (Fin M → Vec N),
    -Real.log (Real.exp (-δ (h w.1.1) (h w.1.2) / τ) /
      (Real.exp (-δ (h w.1.1) (h w.1.2) / τ) + ∑ i, Real.exp (-δ (h w.1.1) (h (w.2 i)) / τ)))
    ∂(bodyPosPairLaw lam δp Z).prod (Measure.pi fun _ : Fin M => bodyUnif Z)

/-- Theorems 5-6: the objective minimised "for `M → ∞`",
`lim_{M → ∞} (L_δ-contr(f; τ, M) - log M)`. -/
def deltaInfoNCELimit {N : ℕ} (lam : ℝ) (δp : Vec N → Vec N → ℝ) (τ : ℝ)
    (δ : Vec N → Vec N → ℝ) (Z : Set (Vec N)) (h : Vec N → Vec N) : ℝ :=
  limUnder atTop (fun M : ℕ => deltaInfoNCE lam δp τ δ Z h M - Real.log M)

/-- Proposition 3: the alignment loss `L_δ-align(f; τ) = τ^{-1} E_{z ∼ p(z), z̃ ∼ p(z̃|z)}
δ(h(z̃), h(z))`. -/
def deltaAlign {N : ℕ} (lam : ℝ) (δp : Vec N → Vec N → ℝ) (τ : ℝ) (δ : Vec N → Vec N → ℝ)
    (Z : Set (Vec N)) (h : Vec N → Vec N) : ℝ :=
  (1 / τ) * ∫ q, δ (h q.2) (h q.1) ∂bodyPosPairLaw lam δp Z

/-- Proposition 3: the uniformity loss
`L_δ-unif(f; τ) = E_{z ∼ p(z)} log E_{z̃ ∼ p(z̃)} exp(-δ(h(z̃), h(z)) / τ)`, where `p(z̃)` is the
uniform marginal. -/
def deltaUnif {N : ℕ} (τ : ℝ) (δ : Vec N → Vec N → ℝ) (Z : Set (Vec N)) (h : Vec N → Vec N) :
    ℝ :=
  ∫ z, Real.log (∫ w, Real.exp (-δ (h w) (h z) / τ) ∂bodyUnif Z) ∂bodyUnif Z

end ContrastiveInverts


