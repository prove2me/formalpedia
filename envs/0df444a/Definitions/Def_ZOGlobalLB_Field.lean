-- Prove2me | Definitions.Def_ZOGlobalLB_Field
-- name    : ZOGlobalLB_Field
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:47:36.748864+00:00
-- url     : https://prove2.me/theorems/f5bb6451-4d48-4661-a3d6-506693cfe868
-- title:
--   The one-stage Gaussian field $Q$ and the tensor features $\phi,\theta$
-- statement:
--   For $q\in\mathbb R^m$, $g\in\mathbb R$ let $S=1+\|q\|^2+A^2g^2$, $t=2Agq/S$, $c_\ell=\binom{1/2}{\ell}(-1)^\ell$ and $\omega_\ell=\ell^2|c_\ell|$. One label carries independent standard Gaussian tensors $G_\ell\in(\mathbb R^m)^{\otimes\ell}$, $\ell\ge1$, and its field is
--   $$Q(q,g)=\frac{\sigma}{\sqrt m}\sum_{\ell\ge1}\omega_\ell\sqrt S\,\langle G_\ell,t^{\otimes\ell}\rangle .$$
--   In $\mathcal H=\bigoplus_{\ell\ge1}(\mathbb R^m)^{\otimes\ell}$ the features are $\phi_\ell(q,g)=\frac{\sigma}{\sqrt m}\omega_\ell\sqrt S\,t^{\otimes\ell}$ and $\theta_\ell(v)=-\frac{4\sqrt m}{\sigma\ell^2}v^{\otimes\ell}$; the translated well is $\mu_v(q,g)=4(\sqrt{1+\|q-Agv\|^2}-1)$.
--
--   The mean and the noise are expressed through the same feature map, which is what makes reuse of a label uninformative beyond a Gaussian innovation.
--
--   **Formalization Note.** A degree-$\ell$ tensor is an array over $\{1,\dots,m\}^\ell$; degree index $\ell$ in Lean is the paper's $\ell+1$. $Q$ is the `tsum` of the series ($0$ where not summable, a null event). $\phi,\theta$ are elements of $\mathcal H$ when their coordinates are square-summable (on the query strip and the unit sphere), else $0$.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Appendix C.1, (85)–(86), pp.44–45; (28)–(29), p.15

import Mathlib
import Definitions.Def_ZOGlobalLB_Profiles

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace ZOGlobalLB

/-! # The one-stage Gaussian field and its tensor features

Xia, Yuan, arXiv:2610.19652, Appendix C.1, pp.44–45, (85)–(86); Section 3.2, (28)–(29), p.15.

For `q ∈ ℝᵐ`, `g ∈ [0,1]`: `S = 1 + ‖q‖² + A²g²`, `t = 2Agq/S`, `c_ℓ = binom(1/2, ℓ)(-1)^ℓ`,
`ω_ℓ = ℓ²|c_ℓ|` (`ℓ ≥ 1`). Each label retains independent standard Gaussian tensors `G_ℓ`, and
`Q(q, g) = (σ/√m) Σ_{ℓ≥1} ω_ℓ √S ⟨G_ℓ, t^{⊗ℓ}⟩` (85). In `H = ⊕_{ℓ≥1} (ℝᵐ)^{⊗ℓ}`,
`ϕ_ℓ(q, g) = (σ/√m) ω_ℓ √S t^{⊗ℓ}` and `θ_ℓ(v) = -(4√m/(σℓ²)) v^{⊗ℓ}` (86).

**Formalization Note.**
* Degrees are shifted: index `ℓ : ℕ` stands for the paper's degree `ℓ + 1`.
* A degree-`(ℓ+1)` tensor on `ℝᵐ` is an array indexed by `Fin (ℓ+1) → Fin m`, and
  `⟨G, e^{⊗(ℓ+1)}⟩ = Σ_I G(I) Π_a e_{I a}`. One label's tensors are one array
  `G : Idx m → ℝ` over `Idx m = Σ ℓ, (Fin (ℓ+1) → Fin m)`; the law of independent standard
  Gaussian entries is `gaussArr` (an infinite product of `N(0,1)`).
* `Q` is the `tsum` of the series. Where the series is not summable `tsum` is `0`; the paper's
  version (proof of Lemma C.2, p.47) also sets the field to `0` off a null event. The samples
  are the same on the almost-sure event of Lemma C.1.
* `H` is `lp (fun ℓ => EuclideanSpace ℝ (Fin (ℓ+1) → Fin m)) 2`. The features are elements of
  `H` when their coordinate sequences are square-summable (on the query strip and the sphere,
  Lemma C.3); elsewhere `phiFeat`, `thetaFeat` are `0` by definition. -/

/-- Index set of all tensor coordinates of one label: degree `ℓ + 1` and a multi-index. -/
abbrev Idx (m : ℕ) := Σ ℓ : ℕ, (Fin (ℓ + 1) → Fin m)

/-- The law of an array of independent standard Gaussian variables indexed by `ι`. -/
noncomputable def gaussArr (ι : Type*) : Measure (ι → ℝ) :=
  Measure.infinitePi (fun _ : ι => gaussianReal 0 1)

/-- The tensor pairing `⟨G_{ℓ+1}, e^{⊗(ℓ+1)}⟩ = Σ_I G(I) Π_a e_{I a}` of one degree. -/
noncomputable def tensorPair {m : ℕ} (G : Idx m → ℝ) (ℓ : ℕ) (e : E m) : ℝ :=
  ∑ I : Fin (ℓ + 1) → Fin m, G ⟨ℓ, I⟩ * ∏ a, e (I a)

/-- `c_ℓ = binom(1/2, ℓ)(-1)^ℓ` (p.45), with the generalized binomial coefficient. -/
noncomputable def cBin (ℓ : ℕ) : ℝ := Ring.choose (1 / 2 : ℝ) ℓ * (-1) ^ ℓ

/-- `ω_ℓ = ℓ²|c_ℓ|` (p.45). -/
noncomputable def omegaC (ℓ : ℕ) : ℝ := (ℓ : ℝ) ^ 2 * |cBin ℓ|

/-- `S = 1 + ‖q‖² + A²g²` (p.44). -/
noncomputable def Sq {m : ℕ} (q : E m) (g : ℝ) : ℝ := 1 + ‖q‖ ^ 2 + Acst ^ 2 * g ^ 2

/-- `t = 2Agq/S` (p.44). -/
noncomputable def tq {m : ℕ} (q : E m) (g : ℝ) : E m := (2 * Acst * g / Sq q g) • q

/-- The degree-`(ℓ+1)` term `(σ/√m) ω_{ℓ+1} √S ⟨G_{ℓ+1}, t^{⊗(ℓ+1)}⟩` of (85). -/
noncomputable def Qterm {m : ℕ} (σ : ℝ) (G : Idx m → ℝ) (ℓ : ℕ) (q : E m) (g : ℝ) : ℝ :=
  σ / Real.sqrt m * (omegaC (ℓ + 1) * Real.sqrt (Sq q g) * tensorPair G ℓ (tq q g))

/-- The finite tensor sums of (85): degrees `1, …, L`. -/
noncomputable def Qpartial {m : ℕ} (σ : ℝ) (G : Idx m → ℝ) (L : ℕ) (q : E m) (g : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.range L, Qterm σ G ℓ q g

/-- **The one-stage field** (85), p.45: `Q(q, g) = (σ/√m) Σ_{ℓ≥1} ω_ℓ √S ⟨G_ℓ, t^{⊗ℓ}⟩`, for the
array `G` of one label. -/
noncomputable def Qfield {m : ℕ} (σ : ℝ) (G : Idx m → ℝ) (q : E m) (g : ℝ) : ℝ :=
  ∑' ℓ, Qterm σ G ℓ q g

/-- The tensor power `e^{⊗(ℓ+1)}` as a vector of `EuclideanSpace ℝ (Fin (ℓ+1) → Fin m)`. -/
noncomputable def tensorPow {m : ℕ} (e : E m) (ℓ : ℕ) :
    EuclideanSpace ℝ (Fin (ℓ + 1) → Fin m) :=
  WithLp.toLp 2 (fun I => ∏ a, e (I a))

/-- The feature space `H = ⊕_{ℓ≥1} (ℝᵐ)^{⊗ℓ}` (p.45), a Hilbert direct sum. -/
noncomputable abbrev Hsp (m : ℕ) := lp (fun ℓ : ℕ => EuclideanSpace ℝ (Fin (ℓ + 1) → Fin m)) 2

/-- Coordinates of `ϕ(q, g)`: `ϕ_{ℓ+1} = (σ/√m) ω_{ℓ+1} √S t^{⊗(ℓ+1)}` (86). -/
noncomputable def phiSeq {m : ℕ} (σ : ℝ) (q : E m) (g : ℝ) :
    ∀ ℓ : ℕ, EuclideanSpace ℝ (Fin (ℓ + 1) → Fin m) :=
  fun ℓ => (σ / Real.sqrt m * omegaC (ℓ + 1) * Real.sqrt (Sq q g)) • tensorPow (tq q g) ℓ

/-- Coordinates of `θ(v)`: `θ_{ℓ+1} = -(4√m/(σ(ℓ+1)²)) v^{⊗(ℓ+1)}` (86). -/
noncomputable def thetaSeq {m : ℕ} (σ : ℝ) (v : E m) :
    ∀ ℓ : ℕ, EuclideanSpace ℝ (Fin (ℓ + 1) → Fin m) :=
  fun ℓ => (-(4 * Real.sqrt m / (σ * ((ℓ : ℝ) + 1) ^ 2))) • tensorPow v ℓ

open Classical in
/-- The feature `ϕ(q, g) ∈ H` (86) (when its coordinates are square-summable; else `0`). -/
noncomputable def phiFeat {m : ℕ} (σ : ℝ) (q : E m) (g : ℝ) : Hsp m :=
  if h : Memℓp (phiSeq σ q g) 2 then ⟨phiSeq σ q g, h⟩ else 0

open Classical in
/-- The parameter feature `θ(v) ∈ H` (86) (when its coordinates are square-summable; else `0`). -/
noncomputable def thetaFeat {m : ℕ} (σ : ℝ) (v : E m) : Hsp m :=
  if h : Memℓp (thetaSeq σ v) 2 then ⟨thetaSeq σ v, h⟩ else 0

/-- The translated workspace well `μ_v(q, g) = 4(√(1 + ‖q - Agv‖²) - 1)` (28), p.15 and p.44. -/
noncomputable def muV {m : ℕ} (v : E m) (q : E m) (g : ℝ) : ℝ :=
  4 * (Real.sqrt (1 + ‖q - (Acst * g) • v‖ ^ 2) - 1)

/-- The field (85) as a function of the query `(q, g)` in `WithLp 2 (E m × ℝ)` (Euclidean norm). -/
noncomputable def QfieldP {m : ℕ} (σ : ℝ) (G : Idx m → ℝ) (p : WithLp 2 (E m × ℝ)) : ℝ :=
  Qfield σ G p.ofLp.1 p.ofLp.2

/-- The finite tensor sums of (85) as functions of the query `(q, g)` in `WithLp 2 (E m × ℝ)`. -/
noncomputable def QpartialP {m : ℕ} (σ : ℝ) (G : Idx m → ℝ) (L : ℕ) (p : WithLp 2 (E m × ℝ)) :
    ℝ :=
  Qpartial σ G L p.ofLp.1 p.ofLp.2

/-- The query strip `ℝᵐ × [0, 1]` (Lemma C.1, p.45). -/
def strip (m : ℕ) : Set (WithLp 2 (E m × ℝ)) := {p | p.ofLp.2 ∈ Set.Icc (0 : ℝ) 1}

end ZOGlobalLB


