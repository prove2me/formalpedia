-- Prove2me | Definitions.Def_CondGeoVerif_hiddenErr
-- name    : CondGeoVerif_hiddenErr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:28:18.554788+00:00
-- url     : https://prove2.me/theorems/1ca2461f-9b1b-4c26-a966-51d4f802c6d4
-- title:
--   Hidden-frame alternatives: blocks $(U,Z)$, $e(U,V^\top Z)$, comparator $h_V$, gain $\Gamma$, $b_u$, correlated Gaussian pairs
-- statement:
--   Write $X=(U,Z)\in\mathbb R^{k+D}$ with $U\in\mathbb R^k$ and $Z\in\mathbb R^D$. For an allocation $e:\mathbb R^k\times\mathbb R^k\to[0,1]$ and a residual frame $V\in\mathbb R^{D\times k}$, the **hidden-frame error probability** is $X\mapsto e(U,V^\top Z)$; the alternative $P_V$ is the labeled law with base rule $h_0(U,Z)=f(U)$ and this error probability (regression $r_V=f(U)(1-2e(U,V^\top Z))$). The **improving comparator** is
--   $$h_V(U,Z)=g(A^\top U+B_AV^\top Z).$$
--   The **gain** of $e$ is (B.1)
--   $$\Gamma=\mathbb E\big[2e(U,G)D_{f,g,A}(U,G)-D_{f,g,A}(U,G)\big],\qquad U,G\sim N(0,I_k)\text{ independent}.$$
--   The **normalized allocation** is $b_u(g)=(e(u,g)-\eta)/\sqrt{\eta(1-\eta)}$ (B.3). Labels are mapped to $\pm1$ by $\mathrm{sgn}$. The law of **jointly standard Gaussian vectors** $(G,H)$ in $\mathbb R^k$ with cross-covariance $R=\mathbb E[GH^\top]$ is that of $(G,\ R^\top G+(I-R^\top R)^{1/2}G')$ with $G'$ an independent copy.
--
--   These objects build the indistinguishable alternatives of the lower bounds.
--
--   **Formalization Note** For a contraction $R$ the last law is the centered Gaussian on $\mathbb R^k\times\mathbb R^k$ with covariance $\begin{pmatrix}I&R\\R^\top&I\end{pmatrix}$, singular cases included. The gain is a Bochner integral of a bounded integrand, measurable for jointly measurable $e$ and Borel rules.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §B.1–B.3, pp.25–26 (PDF pp.28–29)

import Mathlib
import Definitions.Def_CondGeoVerif_Jprog

set_option autoImplicit false

namespace CondGeoVerif

open MeasureTheory
open scoped Matrix

/-- The anchor block `U = (X₁, …, X_k)` of `X = (U, Z) ∈ ℝ^{k+D}` (Chen, *The Conditional Geometry
of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, §B.2, p.25 = PDF p.28). -/
noncomputable def splitU {k D : ℕ} (x : Vec (k + D)) : Vec k :=
  matVec (coordFrame (k + D) k)ᵀ x

/-- The residual block `Z = (X_{k+1}, …, X_{k+D}) ∈ ℝᴰ` of `X = (U, Z)` (§B.2, p.25). -/
noncomputable def splitZ {k D : ℕ} (x : Vec (k + D)) : Vec D :=
  WithLp.toLp 2 (fun i : Fin D => x (Fin.natAdd k i))

/-- The **hidden-frame error probability** `X ↦ e(U, VᵀZ)` of the alternative `P_V` (§B.2, p.25:
`r_V(U, Z) = f(U)(1 − 2e(U, VᵀZ))`), for an allocation `e : ℝᵏ × ℝᵏ → [0, 1]` and a residual frame
`V ∈ ℝ^{D×k}`. The alternative `P_V` is the labeled law with base rule `X ↦ f(U)` and this error
probability (`IsLabelLaw`). -/
noncomputable def hiddenErr {k D : ℕ} (e : Vec k → Vec k → ℝ) (V : Matrix (Fin D) (Fin k) ℝ)
    (x : Vec (k + D)) : ℝ :=
  e (splitU x) (matVec Vᵀ (splitZ x))

/-- The **improving comparator** `h_V(U, Z) = g(AᵀU + B_A VᵀZ)` (§B.2, p.25, with the competitor
rule `g` of the family form, §A.9, p.23). Its frame is the vertical block matrix with blocks `A`
and `V B_A`. -/
noncomputable def hiddenComp {k D : ℕ} (g : Vec k → Bool) (A : Matrix (Fin k) (Fin k) ℝ)
    (V : Matrix (Fin D) (Fin k) ℝ) (x : Vec (k + D)) : Bool :=
  g (matVec Aᵀ (splitU x) + matVec (sqrtGram A) (matVec Vᵀ (splitZ x)))

/-- The **gain** (B.1) of an allocation `e` (§B.1, p.25):
`Γ = E[2e(U, G)D_{f,g,A}(U, G) − D_{f,g,A}(U, G)]`, with `U, G ∼ N(0, I_k)` independent.

**Formalization Note** The expectation is the Bochner integral against the product Gaussian; the
integrand is bounded, and measurable whenever `e` is jointly measurable and `f, g` are Borel. -/
noncomputable def gainOf {k : ℕ} (e : Vec k → Vec k → ℝ) (f g : Vec k → Bool)
    (A : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  ∫ p, (2 * e p.1 p.2 - 1) * ind (Dfga f g A p.1 p.2) ∂((gauss k).prod (gauss k))

/-- The normalized allocation `b_u(g) = (e(u, g) − η)/√(η(1 − η))` of (B.3) (§B.3, p.26). -/
noncomputable def normAlloc {k : ℕ} (η : ℝ) (e : Vec k → Vec k → ℝ) (u z : Vec k) : ℝ :=
  (e u z - η) / Real.sqrt (η * (1 - η))

/-- The `±1` value of a Boolean label (`true ↦ 1`, `false ↦ −1`), used to transcribe the paper's
regressions `r₀ = a f(U)` and `r_V = f(U)(1 − 2e)`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The law of **jointly standard Gaussian vectors** `(G, H)` in `ℝᵏ` with cross-covariance
`R = E[GHᵀ]` (Lemma B.3, p.26): `G ∼ N(0, I_k)` and `H = RᵀG + (I_k − RᵀR)^{1/2} G'` with `G'` an
independent copy.

**Formalization Note** For a contraction `R` this is the centered Gaussian law on `ℝᵏ × ℝᵏ` with
covariance `[[I, R], [Rᵀ, I]]`, the unique jointly Gaussian law with standard marginals and
cross-covariance `R`, singular cases included. -/
noncomputable def corrPair {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ) : Measure (Vec k × Vec k) :=
  ((gauss k).prod (gauss k)).map (fun p => (p.1, matVec Rᵀ p.1 + matVec (sqrtGram R) p.2))

end CondGeoVerif


