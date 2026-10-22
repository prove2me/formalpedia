-- Prove2me | Definitions.Def_TraceClassRep_Characterization_Setting
-- name    : TraceClassRep_Characterization_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:59.83727+00:00
-- url     : https://prove2.me/theorems/b3516bde-f368-4763-8f06-02de5cec4c33
-- title:
--   Notation and §1 — derived action, Nelson Laplacian, resolvent, test functions and five conditions
-- statement:
--   Let $G$ be a finite-dimensional Lie group with left Haar measure $\mu$, $H$ a complex Hilbert space, and $\pi$ a unitary representation. Fix a basis $X_1,\ldots,X_n$ of the Lie algebra. This file defines the infinitesimal action on smooth orbit vectors, $\Delta=\sum_jX_j^2$, a bounded resolvent $R$ satisfying $R(w-d\pi(\Delta)w)=w$ on smooth vectors, right-invariant derivatives of test functions, their $C^m$ seminorms, and the integrated operator $\pi(f)$.
--
--   $$
--   \pi(f)v=\int_G f(g)\pi(g)v\,d\mu(g),\qquad
--   \|f\|_{C^m}=\sup_{|w|\le m,g\in G}|X_w^r f(g)|.
--   $$
--
--   It also gives the five conditions (i)–(v) of Theorem 1.3 one shared meaning. On the function side, a first-order enveloping-algebra action is minus the right-invariant derivative, so the squared Laplacian has the displayed positive second-order sign. The resolvent predicate identifies the inverse of $1-\overline{d\pi(\Delta)}$ through its action on the dense smooth-vector core; its existence and uniqueness come from the self-adjointness statement cited in the paper.
--
--   **Formalization Note** Differentiation uses the manifold derivative at the identity and is used for the derived representation only on smooth vectors. The Haar measure is regular; the function spaces are compactly supported; $m,k\ge1$ where the paper writes $m,k\in\mathbb N$. The $C^m$ seminorm is extended nonnegative. The published Schatten definitions and smooth-orbit definitions are reused.
-- source:
--   van Dijk, Neeb, Salmasian, Zellner, On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, pp. 2–5, Notation, §1, Theorem 1.3

import Mathlib
import Definitions.Def_TeschlQM_TraceClass_schattenClass
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P09

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace TraceClassRep.Characterization

variable {E G H ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [T2Space G]
  [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

/-- The infinitesimal action on a smooth orbit vector. -/
def derivedRep (π : G →* (H ≃ₗᵢ[ℂ] H)) (x : E) (v : H) : H :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) (fun g => π g v) 1 x

/-- The Nelson Laplacian on smooth orbit vectors. -/
def laplacianVec (b : Module.Basis ι ℝ E) (π : G →* (H ≃ₗᵢ[ℂ] H)) (v : H) : H :=
  ∑ i : ι, derivedRep π (b i) (derivedRep π (b i) v)

/-- A bounded realization of the inverse of one minus the closed Nelson Laplacian. -/
def IsLaplacianResolvent (b : Module.Basis ι ℝ E)
    (π : G →* (H ≃ₗᵢ[ℂ] H)) (R : H →L[ℂ] H) : Prop :=
  ∀ w : H,
    QAlgorithms.Papers.Independent.Renew46.P09.HasSmoothOrbit (E := E) (fun g => π g) w →
      R (w - laplacianVec b π w) = w

/-- The right-invariant directional derivative of a function. -/
def rightDeriv (x : E) (f : G → ℂ) (h : G) : ℂ :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f h
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun g : G => g * h) 1 x)

/-- The right-invariant Nelson Laplacian on functions. -/
def laplacianFun (b : Module.Basis ι ℝ E) (f : G → ℂ) (h : G) : ℂ :=
  ∑ i : ι, rightDeriv (b i) (rightDeriv (b i) f) h

/-- The kth iterate of one minus the function-side Laplacian. -/
def oneSubLaplacianPow (b : Module.Basis ι ℝ E) (k : ℕ) (f : G → ℂ) : G → ℂ :=
  ((fun u : G → ℂ => u - laplacianFun b u)^[k]) f

/-- Iterated right-invariant derivatives along a word in the fixed basis. -/
def wordDeriv (b : Module.Basis ι ℝ E) : List ι → (G → ℂ) → (G → ℂ)
  | [], f => f
  | i :: w, f => rightDeriv (b i) (wordDeriv b w f)

/-- A C^m seminorm formed from derivatives of order at most m. -/
def cmSeminorm (b : Module.Basis ι ℝ E) (m : ℕ) (f : G → ℂ) : ℝ≥0∞ :=
  ⨆ w : {w : List ι // w.length ≤ m}, ⨆ g : G, ‖wordDeriv b w f g‖ₑ

/-- A bounded operator represents the integrated action of the test function. -/
def IsIntegratedOp (μ : Measure G) (π : G →* (H ≃ₗᵢ[ℂ] H))
    (f : G → ℂ) (T : H →L[ℂ] H) : Prop :=
  ∀ v : H, T v = QAlgorithms.Papers.Independent.Renew46.P09.integratedVector μ (fun g => π g) f v

/-- The compactly supported C^m test functions. -/
def IsCmCompact (m : ℕ) (f : G → ℂ) : Prop :=
  ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (m : WithTop ℕ∞) f ∧ HasCompactSupport f

/-- The compactly supported smooth test functions. -/
def IsSmoothCompact (f : G → ℂ) : Prop :=
  ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f

/-- Condition (i) of Theorem 1.3. -/
def ConditionI (b : Module.Basis ι ℝ E) (μ : Measure G)
    (π : G →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧
    (∀ f : G → ℂ, IsCmCompact (E := E) m f →
      ∃ T : H →L[ℂ] H, IsIntegratedOp μ π f T ∧ TeschlQM.TraceClass.IsTraceClass T) ∧
    (∀ K : Set G, IsCompact K → ∃ C : ℝ≥0,
      ∀ (f : G → ℂ) (T : H →L[ℂ] H),
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (m : WithTop ℕ∞) f →
        tsupport f ⊆ K → IsIntegratedOp μ π f T →
        TeschlQM.TraceClass.schattenNorm 1 T ≤ (C : ℝ≥0∞) * cmSeminorm b m f)

/-- Condition (ii) of Theorem 1.3. -/
def ConditionII (b : Module.Basis ι ℝ E) (μ : Measure G)
    (π : G →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  (∀ f : G → ℂ, IsSmoothCompact (E := E) f →
    ∃ T : H →L[ℂ] H, IsIntegratedOp μ π f T ∧ TeschlQM.TraceClass.IsTraceClass T) ∧
  (∀ K : Set G, IsCompact K → ∃ (m : ℕ) (C : ℝ≥0),
    ∀ (f : G → ℂ) (T : H →L[ℂ] H),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f →
      tsupport f ⊆ K → IsIntegratedOp μ π f T →
      TeschlQM.TraceClass.schattenNorm 1 T ≤ (C : ℝ≥0∞) * cmSeminorm b m f)

/-- Condition (iii): the representation is trace class. -/
def ConditionIII (μ : Measure G) (π : G →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∀ f : G → ℂ, IsSmoothCompact (E := E) f →
    ∃ T : H →L[ℂ] H, IsIntegratedOp μ π f T ∧ TeschlQM.TraceClass.IsTraceClass T

/-- Condition (iv): integrated smooth test functions act by Hilbert-Schmidt operators. -/
def ConditionIV (μ : Measure G) (π : G →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∀ f : G → ℂ, IsSmoothCompact (E := E) f →
    ∃ T : H →L[ℂ] H, IsIntegratedOp μ π f T ∧ TeschlQM.TraceClass.IsHilbertSchmidt T

/-- Condition (v): a positive power of the resolvent is trace class. -/
def ConditionV (R : H →L[ℂ] H) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ TeschlQM.TraceClass.IsTraceClass (R ^ k)

end TraceClassRep.Characterization


