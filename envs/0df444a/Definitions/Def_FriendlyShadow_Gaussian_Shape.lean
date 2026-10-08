-- Prove2me | Definitions.Def_FriendlyShadow_Gaussian_Shape
-- name    : FriendlyShadow_Gaussian_Shape
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:53:09.019903+00:00
-- url     : https://prove2.me/theorems/7708dfa3-4733-4c05-8058-5ff1e8146a58
-- title:
--   §3.1.2, Defs 31, 33, 34 — projected shapes, kernel combinations z(S), chord combinations C_S(q) and their ℓ₁-diameter
-- statement:
--   This file fixes the objects of the conditioned-simplex analysis in §3.1.2 of Dadush and Huiberts. Let $V$ be a real inner product space (the paper's $\mathbb R^{d-1}$) and $\bar\omega\in V$ a unit vector.
--
--   1. **Projection.** $\pi_{\bar\omega^\perp}(v)=v-(\bar\omega^\mathsf{T}v)\,\bar\omega$.
--   2. **Shape** (Definition 31). For $b_1,\dots,b_d\in V$, the projected shift is $x=\pi_{\bar\omega^\perp}(b_1)$ and the shape is
--   $$S(b_1,\dots,b_d)=(0,\ \pi_{\bar\omega^\perp}(b_2)-x,\ \dots,\ \pi_{\bar\omega^\perp}(b_d)-x).$$
--   3. **Kernel combination** (Definition 33). For a shape $S=(s_1,\dots,s_d)$, a vector $z\in\mathbb R^d$ is a kernel combination if
--   $$\sum_{i=1}^d z_is_i=0,\qquad\sum_{i=1}^d z_i=0,\qquad \|z\|_1=1.$$
--   4. **Chord combinations** (Definition 34). For $q$,
--   $$C_S(q)=\Big\{(\lambda_1,\dots,\lambda_d)\ge0:\ \sum_i\lambda_i=1,\ \sum_i\lambda_is_i=q\Big\},$$
--   and $\|C(q)\|_1$ is the $\ell_1$-diameter of $C_S(q)$.
--   5. **Height-marginal density** (Lemmas 37–38). Writing the hyperplane as $\bar\omega^\perp\times\mathbb R\bar\omega$ and $\bar\mu_i(u,h)=\bar\mu_i(u+h\bar\omega)$, the unnormalised density of the projected shift $x$ is
--   $$\int_{\mathbb R^d}\Big|\sum_{i=1}^d z_ih_i\Big|\prod_{i=1}^d\bar\mu_i(x+s_i,h_i)\,dh .$$
--
--   These objects carry Lemmas 35, 36 and 39 of the mission.
--
--   **Formalization Note** Indices run over `Fin d`, and the page's index $1$ is `0`. Under the rank condition of the allowed shapes, $z(S)$ is unique up to sign; the file states "z is a kernel combination" as a predicate, so no sign is chosen. $\|C(q)\|_1$ is the supremum of $\sum_i|\lambda_i-\lambda_i'|$ over $\lambda,\lambda'\in C_S(q)$. These values are at most $2$ because $C_S(q)$ lies in the standard simplex; the supremum is $0$ when $q\notin\operatorname{conv}(S)$ (empty set), and every statement uses it only for $q\in\operatorname{conv}(S)$. The height-marginal is a lower Lebesgue integral in $[0,\infty]$.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Def 31 (p. 25), Defs 33–34 (p. 26), ‖C(q)‖₁ (p. 27), Lemmas 37–38 (pp. 28–29), proof of Lemma 39 (p. 30)

import Mathlib

open scoped RealInnerProductSpace

namespace FriendlyShadow.Gaussian

/-! ### Shapes, kernel combinations and chord combinations (§3.1.2, pp. 25–27)

Indices run over `Fin d`; the page's index `1` is `0 : Fin d`. The page's ambient space
`ℝ^{d−1}` with the unit vector `ω̄` is a general real inner product space `V`. -/

/-- The orthogonal projection `π_{ω⊥}(v) = v − ⟨ω, v⟩ ω` onto the orthogonal complement of a
unit vector `ω`. -/
noncomputable def projPerp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (ω v : V) : V :=
  v - ⟪ω, v⟫ • ω

/-- The shape `S_ω(b₁, …, b_d) = (0, π_{ω⊥}(b₂) − x, …, π_{ω⊥}(b_d) − x)` of Definition 31
(p. 25), where `x = π_{ω⊥}(b₁)` is the projected shift. -/
noncomputable def shapeOf {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {d : ℕ} [NeZero d] (ω : V) (b : Fin d → V) : Fin d → V :=
  fun i => projPerp ω (b i) - projPerp ω (b 0)

/-- Definition 33 (p. 26): `z` is a kernel combination of the shape `s = (s₁, …, s_d)`:
`Σ zᵢ sᵢ = 0`, `Σ zᵢ = 0`, `‖z‖₁ = 1`. Under the rank condition of the allowed shapes it is
unique up to sign; it is stated as a predicate, so no sign is chosen. -/
def IsKernelComb {V : Type*} [AddCommGroup V] [Module ℝ V] {d : ℕ} (s : Fin d → V)
    (z : Fin d → ℝ) : Prop :=
  ∑ i, z i • s i = 0 ∧ ∑ i, z i = 0 ∧ ∑ i, |z i| = 1

/-- Definition 34 (p. 26): the chord combinations
`C_S(q) = {(λ₁, …, λ_d) ≥ 0 : Σ λᵢ = 1, Σ λᵢ sᵢ = q}`. -/
def chordSet {V : Type*} [AddCommGroup V] [Module ℝ V] {d : ℕ} (s : Fin d → V) (q : V) :
    Set (Fin d → ℝ) :=
  {l | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1 ∧ ∑ i, l i • s i = q}

/-- `‖C(q)‖₁`, the `ℓ₁`-diameter of `C_S(q)` (p. 27): the supremum of `Σ |λᵢ − λ'ᵢ|` over
`λ, λ' ∈ C_S(q)`. The set `C_S(q)` lies in the standard simplex, so these values are bounded
by `2`; `C_S(q)` is nonempty exactly when `q ∈ conv(S)`, and the value is `0` otherwise (it is
only used for `q ∈ conv(S)`). -/
noncomputable def chordLen {V : Type*} [AddCommGroup V] [Module ℝ V] {d : ℕ} (s : Fin d → V)
    (q : V) : ℝ :=
  sSup {t | ∃ l ∈ chordSet s q, ∃ l' ∈ chordSet s q, t = ∑ i, |l i - l' i|}

/-- The unnormalised density at the projected shift `x` of the conditioned simplex of Lemmas
37–38 (pp. 28–29), integrated over the heights:
`∫ |Σ zᵢhᵢ| · Π μ̄ᵢ(x + sᵢ + hᵢ ω̄) dh`, where the hyperplane `ℝ^{d−1}` is written as
`ω̄⊥ × ℝ ω̄` and `mubar i u h = μ̄ᵢ(u + h ω̄)` for `u ∈ ω̄⊥`, `h ∈ ℝ`. For `q = p̄ − x` this is
the density of `q` (up to normalisation) used in Lemma 39. -/
noncomputable def heightMarginal {U : Type*} [AddCommGroup U] {d : ℕ}
    (mubar : Fin d → U → ℝ → ℝ) (s : Fin d → U) (z : Fin d → ℝ) (x : U) : ENNReal :=
  ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (|∑ i, z i * h i| * ∏ i, mubar i (x + s i) (h i))

end FriendlyShadow.Gaussian


