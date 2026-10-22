-- Prove2me | Definitions.Def_MultipartiteREE_Approx_Setting
-- name    : MultipartiteREE_Approx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:38.4583+00:00
-- url     : https://prove2.me/theorems/1bd99536-bd9f-45fe-bfc2-4bb9d589f381
-- title:
--   Multipartite states, separability, FA-property, E_R, universal extension and approximation classes
-- statement:
--   Let the parties be indexed by $s\in\operatorname{Fin}(n)$ and let each party have a separable Hilbert space $\mathcal H_{A_s}=\ell^2(I_s)$. The joint coefficient space uses the Cartesian product of the basis index types. A marginal traces out all other parties, and a product state is the tensor product of one state per party. The separable states form the trace-norm closed convex hull of product states. The relative entropy of entanglement is
--
--   $$E_R(\rho)=\inf_{\sigma\in\mathfrak S_s}H(\rho\|\sigma).$$
--
--   The file also defines the FA-property from a genuine orthonormal eigenbasis and the two conditions in (1), $\mathfrak S_*$ as states with at least $n-1$ FA marginals, the finite-rank approximation map $\Lambda_r$, the binary entropy, the class $L_n^m(C,D)$, the universal extension $\widehat E_R$ from finite-rank local compressions, and positive linear maps on the trace class (Lemma 1). These definitions supply the common model for the goal and all milestones.
--
--   **Formalization Note** Entropy and relative entropy are reused from the published P01 definition and take values in $[0,+\infty]$. The homogeneous extension compares a positive operator only with separable operators of the same trace; its value at zero is zero. Natural logarithms are used throughout.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, pp. 2–14, (1), (4), (14)–(15), (17), (26), (31), (34)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize traceClosure rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

attribute [local instance] Classical.propDecidable

namespace MultipartiteREE.Approx

/-- Coefficient index of H_{A_1} ⊗ … ⊗ H_{A_n}. -/
abbrev Joint {n : ℕ} (I : Fin n → Type) := (s : Fin n) → I s

/-- Marginal ρ_{A_s}: trace out every party except s. -/
def marginal {n : ℕ} {I : Fin n → Type} (X : Matrix (Joint I) (Joint I) ℂ) (s : Fin n) :
    Matrix (I s) (I s) ℂ :=
  fun a b => ∑' x : Joint I, if x s = a then X x (Function.update x s b) else 0

/-- ρ_1 ⊗ … ⊗ ρ_n. -/
def productCoeffN {n : ℕ} {I : Fin n → Type} (X : (s : Fin n) → Matrix (I s) (I s) ℂ) :
    Matrix (Joint I) (Joint I) ℂ :=
  fun x y => ∏ s, X s (x s) (y s)

def productStatesN {n : ℕ} (I : Fin n → Type) : Set (Matrix (Joint I) (Joint I) ℂ) :=
  {X | ∃ rho : (s : Fin n) → State (I s), X = productCoeffN (fun s => (rho s).coefficients)}

/-- S_s(H_{A_1…A_n}): trace-norm closed convex hull of product states (p. 10, p. 11). -/
def separableStates {n : ℕ} (I : Fin n → Type) : Set (State (Joint I)) :=
  {sigma | sigma.coefficients ∈ traceClosure (convexHull ℝ (productStatesN I))}

/-- Countably decomposable separable (Lemma 3). -/
def IsCountablyDecomposableN {n : ℕ} {I : Fin n → Type} (X : Matrix (Joint I) (Joint I) ℂ) : Prop :=
  ∃ (w : ℕ → ℝ) (rho : ℕ → (s : Fin n) → State (I s)),
    (∀ k, 0 ≤ w k) ∧ Summable w ∧ (∑' k, w k) = 1 ∧
    ∀ x y, X x y = ∑' k, (w k : ℂ) * productCoeffN (fun s => (rho k s).coefficients) x y

/-- The real trace of a trace-class coefficient operator. -/
def traceRe {J : Type} (X : Matrix J J ℂ) : ℝ := ∑' j, (X j j).re

/-- Homogeneous E_R(X) for a positive trace-class X: infimum over separable
operators of the same trace, hence c E_R(X/c) when c = Tr X > 0. -/
def relEntEntCoeff {n : ℕ} {I : Fin n → Type} (X : Matrix (Joint I) (Joint I) ℂ) : ℝ≥0∞ :=
  ⨅ sigma ∈ separableStates I,
    generalizedRelativeEntropy X ((traceRe X : ℂ) • sigma.coefficients)

/-- Direct relative entropy of entanglement (26). -/
def relEntEnt {n : ℕ} {I : Fin n → Type} (rho : State (Joint I)) : ℝ≥0∞ :=
  ⨅ sigma ∈ separableStates I, generalizedRelativeEntropy rho.coefficients sigma.coefficients

/-- H(ρ_{A_s}). -/
def marginalEntropy {n : ℕ} {I : Fin n → Type} (rho : State (Joint I)) (s : Fin n) : ℝ≥0∞ :=
  homogeneousEntropy (marginal rho.coefficients s)

/-- FA-property, (1), p. 2 and p. 4. `lam` is the spectrum of X: each `b j` is an
eigenvector of X with eigenvalue `lam j ≥ 0`, and X = Σ_j lam j |b j⟩⟨b j|. -/
def HasFAProperty {J : Type} (X : Matrix J J ℂ) : Prop :=
  ∃ (b : HilbertBasis J ℂ (Hilbert J)) (lam : J → ℝ),
    (∀ j, 0 ≤ lam j) ∧
    (∀ j i, ∑' k, X i k * b j k = (lam j : ℂ) * b j i) ∧
    (∀ i k, X i k = ∑' j, (lam j : ℂ) * b j i * star (b j k)) ∧
    ∃ g : J → ℝ, (∀ j, 0 ≤ g j) ∧
      (∑' j, ENNReal.ofReal (lam j * g j)) < ⊤ ∧
      Tendsto (fun beta : ℝ => (∑' j, ENNReal.ofReal (Real.exp (-(beta * g j)))) ^ beta)
        (𝓝[>] 0) (𝓝 1)

/-- S_*(H_{A_1…A_n}), (34). -/
def SStar {n : ℕ} (I : Fin n → Type) : Set (State (Joint I)) :=
  {rho | ∃ t : Fin n, ∀ s, s ≠ t → HasFAProperty (marginal rho.coefficients s)}

/-- Finite-rank orthogonal projector from a finite orthonormal family. -/
def projOf {J : Type} {k : ℕ} (e : Fin k → Hilbert J) : Matrix J J ℂ :=
  fun i j => ∑ m, e m i * star (e m j)

/-- Q X Q for Q = P_1 ⊗ … ⊗ P_n. -/
def compress {n : ℕ} {I : Fin n → Type} (P : (s : Fin n) → Matrix (I s) (I s) ℂ)
    (X : Matrix (Joint I) (Joint I) ℂ) : Matrix (Joint I) (Joint I) ℂ :=
  fun x y => ∑' x' : Joint I, ∑' y' : Joint I,
    productCoeffN P x x' * X x' y' * productCoeffN P y' y

/-- universal extension (31) with E = E_R and E(ϱ) = c E(ϱ/c). -/
def univExt {n : ℕ} {I : Fin n → Type} (rho : State (Joint I)) : ℝ≥0∞ :=
  ⨆ (k : Fin n → ℕ) (e : (s : Fin n) → {v : Fin (k s) → Hilbert (I s) // Orthonormal ℂ v}),
    relEntEntCoeff (compress (fun s => projOf (e s).1) rho.coefficients)

/-- applies the coefficient operator to a vector, entrywise. -/
def applyCoeff {J : Type} (X : Matrix J J ℂ) (v : J → ℂ) : J → ℂ := fun i => ∑' j, X i j * v j

def quadForm {J : Type} (X : Matrix J J ℂ) (v : J → ℂ) : ℝ := (∑' i, star (v i) * applyCoeff X v i).re

/-- e is an orthonormal family of eigenvectors of X for its r maximal eigenvalues. -/
def IsTopEigenFamily {J : Type} (X : Matrix J J ℂ) (r : ℕ) (e : Fin r → Hilbert J) : Prop :=
  Orthonormal ℂ e ∧ (∀ m, ∃ lam : ℝ, applyCoeff X (e m) = fun i => (lam : ℂ) * e m i) ∧
  ∀ v : Hilbert J, (∀ m, inner ℂ (e m) v = 0) →
    ∀ m, quadForm X v ≤ quadForm X (e m) * ‖v‖ ^ 2

/-- The rank-r top spectral projector; once a finite-dimensional spectrum is exhausted,
the projector is the identity. -/
def IsTopEigenProjector {J : Type} (X : Matrix J J ℂ) (r : ℕ)
    (P : Matrix J J ℂ) : Prop :=
  (∃ e : Fin r → Hilbert J, IsTopEigenFamily X r e ∧ P = projOf e) ∨
  (Finite J ∧ Nat.card J ≤ r ∧ P = 1)

/-- ρ_r = Λ^{L}_r(ρ), (17), with the identity projector after finite-dimensional
spectral exhaustion. -/
def IsApproxState {n : ℕ} {I : Fin n → Type} (L : Finset (Fin n)) (r : ℕ)
    (rho rhoR : State (Joint I)) : Prop :=
  ∃ P : (s : Fin n) → Matrix (I s) (I s) ℂ,
    (∀ s ∈ L, IsTopEigenProjector (marginal rho.coefficients s) r (P s)) ∧
    (∀ s ∉ L, P s = 1) ∧
    0 < traceRe (compress P rho.coefficients) ∧
    rhoR.coefficients = (traceRe (compress P rho.coefficients))⁻¹ • compress P rho.coefficients

def binEnt (p : ℝ) : ℝ := -(p * Real.log p) - (1 - p) * Real.log (1 - p)

def SM {n : ℕ} {I : Fin n → Type} (M : Finset (Fin n)) : Set (State (Joint I)) :=
  {rho | ∀ s ∈ M, marginalEntropy rho s < ⊤}

def IsMixture {J : Type} (p : ℝ) (rho sigma tau : State J) : Prop :=
  tau.coefficients = (p : ℂ) • rho.coefficients + ((1 - p : ℝ) : ℂ) • sigma.coefficients

/-- L^m_n(C,D), (14)–(15), with M the parties carrying finite entropy. -/
def InClassL {n : ℕ} {I : Fin n → Type} (M : Finset (Fin n)) (C D : ℝ)
    (f : State (Joint I) → ℝ) : Prop :=
  ∃ a b cm cp : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ cm ∧ 0 ≤ cp ∧ a + b = D ∧ cm + cp = C ∧
    (∀ rho ∈ SM M, ∀ sigma ∈ SM M, ∀ tau : State (Joint I), ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      IsMixture p rho sigma tau →
        -(a * binEnt p) ≤ f tau - p * f rho - (1 - p) * f sigma ∧
        f tau - p * f rho - (1 - p) * f sigma ≤ b * binEnt p) ∧
    (∀ rho ∈ SM M,
      -(cm * ∑ s ∈ M, (marginalEntropy rho s).toReal) ≤ f rho ∧
      f rho ≤ cp * ∑ s ∈ M, (marginalEntropy rho s).toReal)

/-- Positive linear map on T(H), Lemma 1 (values off trace class irrelevant). -/
def IsPositiveTraceMap {J : Type} (Phi : Matrix J J ℂ → Matrix J J ℂ) : Prop :=
  (∀ X, QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClass X →
      QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClass (Phi X)) ∧
  (∀ X Y, QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClass X →
      QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClass Y → Phi (X + Y) = Phi X + Phi Y) ∧
  (∀ (c : ℂ) X, QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClass X →
      Phi (c • X) = c • Phi X) ∧
  (∀ X, QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClass X →
      QAlgorithms.Papers.Independent.Frontier18.P01.IsPositive X →
      QAlgorithms.Papers.Independent.Frontier18.P01.IsPositive (Phi X))

end MultipartiteREE.Approx


