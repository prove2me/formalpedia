-- Prove2me | Definitions.Def_BootstrapRecolorVerify_MetricGap_Resampling
-- name    : BootstrapRecolorVerify_MetricGap_Resampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:23.516493+00:00
-- url     : https://prove2.me/theorems/5eace4ee-f476-43c9-9530-211dc5363c72
-- title:
--   Actual spectral acceptance and the sequential accepted graph law
-- statement:
--   For a cloud of size $s=n_{i+1}$ with $\Delta$ matchings encoded by permutations $p_\ell$, spectral acceptance means that the normalized adjacency quadratic form has absolute value at most $C/L$ on mean-zero functions:
--
--   $$\left|2\sum_{\ell=1}^{\Delta}\sum_{a=0}^{s/2-1}f(p_\ell(2a))f(p_\ell(2a+1))\right|\le\frac{C\Delta}{L}\sum_{u=0}^{s-1} f(u)^2,\quad \sum_u f(u)=0.$$
--
--   This is the source's bound $|\lambda_j-1|\le C/\sqrt\Delta$ for all nontrivial normalized Laplacian eigenvalues. An absolute spectral constant has unconditioned success probability at least $1/2$ at every stage for all sufficiently large $r$.
--
--   At each stage, condition every internal cloud array independently on this actual spectral event. Given the preceding history, condition the whole lift array on the simultaneous sampling event. The resulting history mass is the product of the previous mass and these conditional uniform masses. A history is accepted exactly when these spectral and sampling events hold at every stage; exceptional length control and all cost inequalities are absent from this predicate.
--
--   These laws distinguish a fresh unconditioned attempt from the distribution after rejection sampling. If an acceptance event is empty its conditional mass is defined as zero. Claim 6.3 explicitly asserts both total mass one and its exceptional-edge probability bound, precluding a vacuous probability statement.
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), §6.3 pp.23–24; Appendix B.1–B.3 pp.30–33, p.23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=23; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Recoloring

open scoped Classical

namespace BootstrapRecolorVerify.MetricGap

/-- Uniform probability of an event on a finite space. -/
noncomputable def finiteProbability {A : Type*} [Fintype A] (P : A → Prop) : ℝ :=
  average (fun a => if P a then 1 else 0)

/-- Uniform sampling conditioned on the actual event P, i.e. rejection sampling.
If P is empty this is the zero subprobability law; the exceptional-edge theorem
also asserts total mass one, so an impossible acceptance event cannot certify it. -/
noncomputable def conditionalUniform {A : Type*} [Fintype A]
    (P : A → Prop) (a : A) : ℝ :=
  if P a then ((Finset.univ.filter P).card : ℝ)⁻¹ else 0

abbrev CloudArray (r i : ℕ) :=
  Fin (delta r) → Equiv.Perm (Fin (cloudSize r (i + 1)))

/-- Actual spectral acceptance event, §6.3 p.23 and Appendix B.1 pp.30--31.
This quadratic-form version says that every nonconstant eigenvalue of the
normalized adjacency matrix has absolute value at most C/L = C/sqrt(Delta).
Each unordered edge contributes twice to the adjacency quadratic form. -/
def CloudSpectral (r i : ℕ) (C : ℝ) (a : CloudArray r i) : Prop :=
  ∀ f : Fin (cloudSize r (i + 1)) → ℝ, (∑ u, f u) = 0 →
    |2 * ∑ label : Fin (delta r), ∑ b : Fin (cloudSize r (i + 1) / 2),
      f (a label (evenPosition b)) * f (a label (oddPosition b))| ≤
    C / L r * delta r * ∑ u, (f u) ^ 2

/-- Meaning of the fixed absolute spectral constant supplied by Appendix B.1.
This property is not assumed to prove a gap: Claim 6.3 below asserts that such
a constant exists. Its success probability concerns an unconditioned attempt. -/
def IsSpectralConstant (C : ℝ) : Prop :=
  0 < C ∧ ∃ R : ℕ, 3 ≤ R ∧ ∀ r ≥ R, ∀ i, i + 1 ≤ r →
    1 / 2 ≤ finiteProbability (CloudSpectral r i C)

/-- The deterministic support conditions imposed by the two rejection steps.
Neither exceptional LP control nor local embeddings nor any cost lower bound
is included (§6.3 pp.23--24). -/
def Accepted {r : ℕ} (C : ℝ) : {i : ℕ} → History r i → Prop
  | 0, _ => True
  | _ + 1, H => Accepted C H.1 ∧
      (∀ u, CloudSpectral r _ C (H.2.1 u)) ∧ SamplingEvent H.1 H.2.2

/-- The complete accepted history law. Internal cloud arrays are conditioned
independently on their spectral event; the entire lift array is conditioned on
(17) given the preceding history. These two samples are independent given that
history. Fresh exceptional marks are deterministic functions of these arrays. -/
noncomputable def acceptedMass {r : ℕ} (C : ℝ) : {i : ℕ} → History r i → ℝ
  | 0, _ => 1
  | _ + 1, H => acceptedMass C H.1 *
      (∏ u, conditionalUniform (CloudSpectral r _ C) (H.2.1 u)) *
      conditionalUniform (SamplingEvent H.1) H.2.2

end BootstrapRecolorVerify.MetricGap


