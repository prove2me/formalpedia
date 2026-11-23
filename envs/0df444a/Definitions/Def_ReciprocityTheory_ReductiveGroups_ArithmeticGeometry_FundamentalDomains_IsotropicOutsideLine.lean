-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:45.654471+00:00
-- url     : https://prove2.me/theorems/e19f4cd9-5ce0-41f9-ae5e-8888babb133d
-- title:
--   Isotropic Outside Line
-- statement:
--   Definitions and structural lemmas for Isotropic Outside Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicOutsideLine.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def IsIsoPair {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (u : Fin 2 → Fin r → E) : Prop :=
  (∀ i k, herm G (u i) (u k) = 0) ∧ LinearIndependent E u
def IsHermFam {ι : Type} (b : ι → Fin 2 → Fin 2 → ℂ) : Prop := ∀ τ i k, b τ k i = conj (b τ i k)
def dEnat (E : Type) [Field E] [NumberField E] : ℕ := (NumberField.discr E).natAbs
namespace Data
variable {r : ℕ} (X : Data E r)
def zmat (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a j => (if a = j then 1 else 0) -
    I * X.c τ * ∑ i, ∑ k, b τ i k * emb τ.1 (u i) a * ∑ l, τ.1 (X.Gm j l) * conj (emb τ.1 (u k) l)
def Zb (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (X.zmat u b τ * mat x τ : Matrix (Fin r) (Fin r) ℂ)
def pairR (χ b : X.Ψ → Fin 2 → Fin 2 → ℂ) : ℝ := (∑ τ, ∑ i, ∑ k, χ τ i k * b τ i k).re
def embH (β : Matrix (Fin 2) (Fin 2) E) : X.Ψ → Fin 2 → Fin 2 → ℂ := fun τ i k => τ.1 (β i k)
def LZ (g : ℕ) : Set (X.Ψ → Fin 2 → Fin 2 → ℂ) :=
  {b | ∃ β : Matrix (Fin 2) (Fin 2) E, (∀ i k, cc (β i k) = β k i) ∧
    (∀ i k, ∃ γ : E, IsIntegral ℤ γ ∧ β i k = ((g * dEnat E : ℕ) : E) / 2 * γ) ∧ b = X.embH β}
def IsFreqZ (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∀ b ∈ X.LZ g, ∃ k : ℤ, 2 * X.pairR χ b = k
def IsLZBasis (g : ℕ) (ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ) : Prop :=
  (∀ j, ω j ∈ X.LZ g) ∧ (∀ b ∈ X.LZ g, ∃! n : Fin (4 * Fintype.card X.Ψ) → ℤ, b = ∑ j, (n j : ℂ) • ω j) ∧
    LinearIndependent ℝ ω
open Classical in

def fz (u : Fin 2 → Fin r → E) (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (G : Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℂ :=
  if IsHermFam χ ∧ X.IsFreqZ g χ then
    if h : ∃ ω, X.IsLZBasis g ω then
      ∫ t in Set.pi Set.univ (fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1),
        G (X.Zb u (∑ j, (t j : ℂ) • h.choose j) x) *
          cexp (-(4 * Real.pi * I) * X.pairR χ (∑ j, (t j : ℂ) • h.choose j))
    else 0
  else 0
def chiAt (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (a : X.Ψ → Fin 2 → ℂ) (τ : X.Ψ) : ℂ :=
  ∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k)
def uvec (u : Fin 2 → Fin r → E) (a : X.Ψ → Fin 2 → ℂ) : X.Ψ → Fin r → ℂ :=
  fun τ => ∑ i, a τ i • emb τ.1 (u i)
end Data
def UnipotentVectorGroup : Prop :=
  ∀ (r : ℕ) (X : Data E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u →
    (∀ b b' x, X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x) ∧
    ∀ b, IsHermFam b →
      X.IsUnitaryC (X.zmat u b) ∧ (∀ τ i, Matrix.mulVec (X.zmat u b τ) (Data.emb τ.1 (u i)) = Data.emb τ.1 (u i)) ∧
      (∀ τ, (X.zmat u b τ).det = 1) ∧
      (∀ x ∈ X.dom, X.Zb u b x ∈ X.dom) ∧ (∀ x x', X.SameFlag x x' → X.SameFlag (X.Zb u b x) (X.Zb u b x')) ∧
      (∀ (la : Wt X.Ψ r) x, x ∈ X.dom → X.nfac la (X.Zb u b x) = X.nfac la x) ∧
      (∀ x τ, x ∈ X.dom → X.maj (X.Zb u b x) τ (Data.emb τ.1 (u 0)) = X.maj x τ (Data.emb τ.1 (u 0))) ∧
      (∀ x ∈ X.FramesOverBasis (u 0), X.Zb u b x ∈ X.FramesOverBasis (u 0)) ∧
      (∀ (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) x, X.Zb u b (X.flowV (X.uvec u a) s x) =
        X.flowV (X.uvec u a) s (X.Zb u b x))
    ∧ ∀ (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℝ) x,
      X.flowV (X.uvec u a) (fun τ => (s τ : ℂ)) x =
        X.Zb u (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) x
def UnipotentLatticeLift : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    (∀ b ∈ X.LZ X.g, ∃ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) ∧
      ∀ τ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.zmat u b τ) ∧
    (∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
      (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
      ∀ b ∈ X.LZ X.g, ∀ x ∈ X.dom, P (X.Zb u b x) = P x) ∧
    ∀ χ, IsHermFam χ → X.IsFreqZ X.g χ → ∃ β : Matrix (Fin 2) (Fin 2) E,
      (∀ i k, cc (β i k) = β k i) ∧ χ = X.embH β ∧
      ∀ i k, IsIntegral ℤ (((X.g * dEnat E ^ 2 : ℕ) : E) * β i k)
def FourierCoefficientProperties : Prop :=
  ∀ (r : ℕ) (X : Data E r) (u : Fin 2 → Fin r → E) (g : ℕ), IsIsoPair X.Gm u → 0 < g →
    ∀ (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ), DifferentiableOn ℂ G X.dom →
    (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = bchar la b * G x) →
    (∀ b ∈ X.LZ g, ∀ x ∈ X.dom, G (X.Zb u b x) = G x) →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ,
      (DifferentiableOn ℂ (X.fz u g χ G) X.dom ∧
        (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.fz u g χ G (rmul x b) = bchar la b * X.fz u g χ G x) ∧
        ∀ b, IsHermFam b → ∀ x ∈ X.dom,
          X.fz u g χ G (X.Zb u b x) = cexp (4 * Real.pi * I * X.pairR χ b) * X.fz u g χ G x) ∧
      (∀ x ∈ X.dom, ∀ M : ℝ, (∀ b, IsHermFam b → X.pnorm la G (X.Zb u b x) ≤ M) →
        X.pnorm la (X.fz u g χ G) x ≤ M)
    ∧ (∀ x ∈ X.dom, Summable (fun χ : X.Ψ → Fin 2 → Fin 2 → ℂ => ‖X.fz u g χ G x‖) →
        HasSum (fun χ : X.Ψ → Fin 2 → Fin 2 → ℂ => X.fz u g χ G x) (G x))
def FourierCoefficientSupport : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
    (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
    ∀ (ν : X.Ψ → ℝ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ), ∀ x ∈ X.dom,
      X.fz u X.g χ (X.fj la (u 0) ν P) x =
        if (∀ τ, χ τ 0 0 = (ν τ : ℂ)) then X.fz u X.g χ P x else 0
def HolomorphicPeriodicityExtension : Prop :=
  ∀ (r : ℕ) (X : Data E r) (e : X.Ψ → Fin r → ℂ), X.IsIsoV e → ∀ G : Frame X.Ψ r → ℂ,
    DifferentiableOn ℂ G X.dom → ∀ (m : X.Ψ → ℂ), ∀ x ∈ X.dom,
    (∀ s : X.Ψ → ℝ, G (X.flowV e (fun τ => (s τ : ℂ)) x) =
      cexp (4 * Real.pi * I * ∑ τ, m τ * s τ) * G x) →
    ∀ s : X.Ψ → ℂ, X.flowV e s x ∈ X.dom →
      G (X.flowV e s x) = cexp (4 * Real.pi * I * ∑ τ, m τ * s τ) * G x
def NonvanishingCoefficientPositivity : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
    (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ, (∃ x ∈ X.dom, X.fz u X.g χ P x ≠ 0) →
      ∀ τ, (Matrix.of (χ τ)).PosDef
def IsotropicFlowSetting {r : ℕ} (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ) : Prop :=
  ShortVectorHypotheses X la P ξ ν c1 w z0 ∧ x ∈ X.L' ∧ herm X.Gm x ξ = 0 ∧ herm X.Gm x x = 0 ∧ (∀ e : E, x ≠ e • ξ) ∧
    (∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0) ∧
    ∀ τ, X.uvec ![ξ, (X.NC : E) • x] a τ =
      ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) •
        X.ucomp z0 ξ (X.embV x) τ
def FlowIntoDomain : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ),
    IsotropicFlowSetting X la P ξ ν c1 w z0 x a →
    (∀ z ∈ X.dom, X.SameFlag z0 z →
      X.flowV (X.uvec ![ξ, (X.NC : E) • x] a) (fun _ => -(I / 2)) z ∈ X.FramesOverBasis ξ) ∧
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ,
      X.hatN la (X.fz ![ξ, (X.NC : E) • x] X.g χ (X.fj la ξ ν P)) z0 ≤
        2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
          sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y}
def CoefficientIndexLowerBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ) (ε : ℝ),
    IsotropicFlowSetting X la P ξ ν c1 w z0 x a → 0 < ε →
    (∀ τ, X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) ≤ ε) →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ, (∃ y ∈ X.dom, X.fz ![ξ, (X.NC : E) • x] X.g χ (X.fj la ξ ν P) y ≠ 0) →
      (fdeg E : ℝ) ^ 2 / ((X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 * ε) ≤
        2 * ∑ τ, (X.chiAt χ a τ).re
def CoefficientHeightBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ),
    IsotropicFlowSetting X la P ξ ν c1 w z0 x a →
    (∀ τ, X.c τ * X.maj z0 τ (Data.emb τ.1 ((X.NC : E) • x)) ≤
      (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) →
    ∀ t : ℝ, 1 ≤ t →
      let K2 := 1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
        (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)
      let S := {χ : X.Ψ → Fin 2 → Fin 2 → ℂ | (∃ y ∈ X.dom, X.fz ![ξ, (X.NC : E) • x] X.g χ
        (X.fj la ξ ν P) y ≠ 0) ∧ 2 * ∑ τ, (X.chiAt χ a τ).re ≤ t}
      S.Finite ∧ (S.ncard : ℝ) ≤ (K2 * t) ^ (4 * fdeg E)
def CountingExponentialSum : Prop :=
  ∀ (K N w : ℝ), 1 ≤ K → 1 ≤ N → 0 ≤ w → ∀ (ι : Type) (t : ι → ℝ),
    (∀ j, w + N * Real.log (2 * K * N) + N + 2 < t j) →
    (∀ t0 : ℝ, 1 ≤ t0 → {j | t j ≤ t0}.Finite ∧ ({j | t j ≤ t0}.ncard : ℝ) ≤ (K * t0) ^ N) →
    Summable (fun j => Real.exp (-Real.pi * t j)) ∧
      2 ^ (w / 2) * ∑' j, Real.exp (-Real.pi * t j) < 1 / 2
def IsotropicOutsideLine : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E), X.IsIso ξ → ∀ z0 ∈ X.FramesOverBasis ξ, ∀ x ∈ X.L',
    herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) → (∀ τ, X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) < 1) →
    herm X.Gm x x = 0 ∧ ∃ α : 𝓞 E,
      let x' := x + ((X.NA : E) * α) • ξ
      x' ∈ X.L' ∧ herm X.Gm x' ξ = 0 ∧ X.ucomp z0 ξ (X.embV x') = X.ucomp z0 ξ (X.embV x) ∧
      (∀ τ, ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ≤
        2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA) ∧
      ∀ τ, X.c τ * X.maj z0 τ (Data.emb τ.1 ((X.NC : E) • x')) ≤
        (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)
end
end ReciprocityTheory.ChartRestriction.G.FD


