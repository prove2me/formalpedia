-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:12.035137+00:00
-- url     : https://prove2.me/theorems/fe3f5f29-7981-41da-9613-2e8c4005cce2
-- title:
--   Fundamental Domain Point Bound
-- statement:
--   Definitions and structural lemmas for Fundamental Domain Point Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainPointBound.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def EFf {r : ℕ} (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) : ℚ :=
  Algebra.trace ℚ E (-ξ0 * herm G x y)
structure DataX (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) extends Data E r where
  k0 : ℝ
  minWeight_pos : 0 < k0
  k0_le : k0 ≤ 2
  ξ0_abs : ∀ τ : Ψ, ‖τ.1 ξ0‖ = k0 / 2
  EF_int : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 Gm x y = k
  EF_perf : ∀ φ : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (φ y : ℚ) = EFf ξ0 Gm x y
  L' : Submodule (𝓞 E) (Fin r → E)
  L'_fg : L'.FG
  L'_int : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (herm Gm x y)
  L'_dual : ∀ x, (∀ y ∈ L', IsIntegral ℤ (herm Gm x y)) → x ∈ L'
  NA : ℕ
  NC : ℕ
  NA_pos : 0 < NA
  NC_pos : 0 < NC
  NA_sub : ∀ x ∈ Λ, (NA : E) • x ∈ L'
  NC_sub : ∀ x ∈ L', (NC : E) • x ∈ Λ
  g : ℕ
  g_pos : 0 < g
  cong : ∀ γ : GL (Fin r) E, IsUStab Gm Λ γ →
    (∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ Γ
def fdeg (E : Type) [Field E] [NumberField E] : ℕ := Module.finrank ℚ E / 2
def dE (E : Type) [Field E] [NumberField E] : ℝ := |(NumberField.discr E : ℝ)|
def rdE (E : Type) [Field E] [NumberField E] : ℝ := dE E ^ (1 / (Module.finrank ℚ E : ℝ))
namespace Data
variable {r : ℕ} (X : Data E r)
def embV (v : Fin r → E) : X.Ψ → Fin r → ℂ := fun τ => emb τ.1 v
def lineV (ξ : Fin r → E) (s : X.Ψ → ℂ) : X.Ψ → Fin r → ℂ := fun τ => s τ • emb τ.1 ξ
def ppos (x : Frame X.Ψ r) (τ : X.Ψ) (u : Fin r → ℂ) : Fin r → ℂ :=
  ∑ a : Fin X.p0, (∑ b : Fin X.p0, hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a) • col (mat x τ) (Fin.castLE X.p0_le a)
def Jz (x : Frame X.Ψ r) (u : X.Ψ → Fin r → ℂ) : X.Ψ → Fin r → ℂ :=
  fun τ => I • ((2 : ℂ) • X.ppos x τ (u τ) - u τ)
def Hf (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) : ℂ :=
  hermC τ.1 X.Gm ((2 : ℂ) • X.ppos x τ u - u) w
def reHF (x : Frame X.Ψ r) (u w : X.Ψ → Fin r → ℂ) : ℝ :=
  ∑ τ, X.c τ * (X.Hf x τ (u τ) (w τ)).re
def Iperp (ξ : Fin r → E) : Set (X.Ψ → Fin r → ℂ) :=
  {u | ∀ τ : X.Ψ, hermC τ.1 X.Gm (u τ) (emb τ.1 ξ) = 0}
def Uz (x : Frame X.Ψ r) (ξ : Fin r → E) : Set (X.Ψ → Fin r → ℂ) :=
  {u | u ∈ X.Iperp ξ ∧ X.Jz x u ∈ X.Iperp ξ}
def aproj (x : Frame X.Ψ r) (ξ : Fin r → E) (u : X.Ψ → Fin r → ℂ) : X.Ψ → Fin r → ℂ :=
  X.lineV ξ fun τ => X.Hf x τ (u τ) (emb τ.1 ξ) / X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ)
def ucomp (x : Frame X.Ψ r) (ξ : Fin r → E) (u : X.Ψ → Fin r → ℂ) : X.Ψ → Fin r → ℂ :=
  u - X.aproj x ξ u
def hermL (ξ : Fin r → E) : (Fin r → E) →+ E where
  toFun x := herm X.Gm x ξ
  map_zero' := by simp [herm]
  map_add' x y := by simp [herm, add_mul, Finset.sum_add_distrib]
def Λp (ξ : Fin r → E) : AddSubgroup (Fin r → E) := X.Λ.toAddSubgroup ⊓ (X.hermL ξ).ker
def lmulC (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (n τ * mat x τ : Matrix (Fin r) (Fin r) ℂ)
def applyV (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (u : X.Ψ → Fin r → ℂ) : X.Ψ → Fin r → ℂ :=
  fun τ => Matrix.mulVec (n τ) (u τ)
def IsUnitaryC (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : X.Ψ, ∀ u w, hermC τ.1 X.Gm (Matrix.mulVec (n τ) u) (Matrix.mulVec (n τ) w) = hermC τ.1 X.Gm u w
def IsDominant (la : Wt X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, i ≤ j → (j : ℕ) < X.p0 → la τ j ≤ la τ i) ∧
    (∀ i j : Fin r, X.p0 ≤ (i : ℕ) → i ≤ j → la τ j ≤ la τ i) ∧
    (∀ i j : Fin r, (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → la τ i ≤ la τ j)
def SameFlag (x x' : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) =
    Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x' τ) (Fin.castLE X.p0_le a))
def hatN (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  sSup {t | ∃ x' ∈ X.dom, X.SameFlag x x' ∧ t = X.pnorm la Q x'}
def FramesOverBasis (ξ : Fin r → E) : Set (Frame X.Ψ r) :=
  {x | x ∈ X.dom ∧ ∀ τ : X.Ψ, X.c τ * X.maj x τ (emb τ.1 ξ) = 1}
end Data
def flowEpsilonBound (g d f NA NC c1 w : ℝ) : ℝ :=
  let rd := d ^ (1 / (2 * f))
  let N0 := g * d ^ 2
  let H := NC ^ 2 * (2 + 4 * f ^ 4 * rd ^ 2 * NA ^ 2)
  let K2 := 1 + N0 * H * (2 * c1 + 1)
  let N2 := 4 * f
  let R2 := w + N2 * Real.log (2 * K2 * N2) + N2 + 2
  min 1 (f ^ 2 / (N0 ^ 2 * NC ^ 2 * c1 * R2))
def OrthogonalRealDecomposition : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ → ∀ x ∈ X.dom,
    (∀ u : X.Ψ → Fin r → ℂ, ∃ s t : X.Ψ → ℂ,
      u - X.lineV ξ s - X.Jz x (X.lineV ξ t) ∈ X.Uz x ξ) ∧
    ∀ s t : X.Ψ → ℂ, ∀ w ∈ X.Uz x ξ,
      X.reHF x (X.lineV ξ s) (X.Jz x (X.lineV ξ t)) = 0 ∧ X.reHF x (X.lineV ξ s) w = 0 ∧
        X.reHF x (X.Jz x (X.lineV ξ t)) w = 0
def ProjectionAlongComplement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ → ∀ x ∈ X.dom, ∀ u ∈ X.Iperp ξ,
    X.ucomp x ξ u ∈ X.Uz x ξ
def PerfectPairingQuotient : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E), X.IsIso ξ →
    (∀ φ : X.Λp ξ →+ ℤ, (∀ μ : X.Λp ξ, (∃ e : E, (μ : Fin r → E) = e • ξ) → φ μ = 0) →
      ∃ μ : X.Λp ξ, ∀ ν : X.Λp ξ, (φ ν : ℚ) = EFf X.ξ0 X.Gm μ ν) ∧
    ∀ μ : X.Λp ξ, (∀ ν : X.Λp ξ, EFf X.ξ0 X.Gm μ ν = 0) → ∃ e : E, (μ : Fin r → E) = e • ξ
def PerpQuotientSelfDual : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E), X.IsIso ξ → ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
    (∀ y ∈ X.L', herm X.Gm y ξ = 0 → IsIntegral ℤ (herm X.Gm x y)) → ∃ e : E, x + e • ξ ∈ X.L'
def FlowFixesComplement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℂ,
    X.flow ξ s x ∈ X.dom →
    X.Uz (X.flow ξ s x) ξ = X.Uz x ξ ∧ (∀ u ∈ X.Uz x ξ, X.Jz (X.flow ξ s x) u = X.Jz x u) ∧
      ∀ u ∈ X.Iperp ξ, X.aproj (X.flow ξ s x) ξ u = X.aproj x ξ u
def UnitaryComplementMove : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ → ∀ x ∈ X.dom,
    ∀ h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ, X.IsUnitaryC h1 →
    (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz x (X.lineV ξ t)) =
      X.lineV ξ s + X.Jz x (X.lineV ξ t)) →
    (∀ u ∈ X.Uz x ξ, X.applyV h1 u ∈ X.Uz x ξ) →
    X.lmulC h1 x ∈ X.dom ∧ (∀ u ∈ X.Iperp ξ, X.aproj (X.lmulC h1 x) ξ u = X.aproj x ξ u) ∧
      (∀ τ, X.maj (X.lmulC h1 x) τ (Data.emb τ.1 ξ) = X.maj x τ (Data.emb τ.1 ξ)) ∧
      ∀ u ∈ X.Uz x ξ, X.Jz (X.lmulC h1 x) (X.applyV h1 u) = X.applyV h1 (X.Jz x u)
def ReducedFrameDomainCovering : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ → ∀ x ∈ X.dom,
    ∀ (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) (κ : ℝ), 0 ≤ κ → κ ≤ 1 →
    (∀ u ∈ X.Uz x ξ, ∀ τ, X.maj x τ (δ τ (u τ) • Data.emb τ.1 ξ) ≤ κ ^ 2 * X.maj x τ (u τ)) →
    ∃ n : X.Ψ → Matrix (Fin r) (Fin r) ℂ, X.IsUnitaryC n ∧
      (∀ τ, Matrix.mulVec (n τ) (Data.emb τ.1 ξ) = Data.emb τ.1 ξ) ∧
      (∀ u ∈ X.Uz x ξ, X.applyV n u = u + X.lineV ξ (fun τ => δ τ (u τ))) ∧
      X.lmulC n x ∈ X.dom ∧
      (∀ u ∈ X.Iperp ξ, X.aproj (X.lmulC n x) ξ u =
        X.aproj x ξ u - X.lineV ξ (fun τ => δ τ (X.ucomp x ξ u τ))) ∧
      (∀ τ, X.maj (X.lmulC n x) τ (Data.emb τ.1 ξ) = X.maj x τ (Data.emb τ.1 ξ)) ∧
      (∀ u ∈ X.Uz x ξ, X.ucomp (X.lmulC n x) ξ (X.Jz x u) =
        X.Jz (X.lmulC n x) (X.ucomp (X.lmulC n x) ξ u)) ∧
      ∀ τ (v : Fin r → ℂ), X.maj x τ (Matrix.mulVec (n τ - 1) v) ≤ (3 * κ) ^ 2 * X.maj x τ v
def ReducedFrameDomainFiniteOverlap : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E), X.IsIso ξ → ∀ x ∈ X.dom, ∀ n' : ℕ,
    (∀ μ ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧ (n' : ℂ) • X.aproj x ξ (X.embV μ) = X.embV (e • ξ)) →
    (∀ μ ∈ X.Λp ξ, ∃ μ' ∈ X.Λp ξ, (n' : ℂ) • X.ucomp x ξ (X.embV μ) = X.embV μ') ∧
    ∀ γ ∈ X.Λ, ∀ (s t : X.Ψ → ℂ) (u : X.Ψ → Fin r → ℂ), u ∈ X.Uz x ξ →
      X.embV γ = X.lineV ξ s + X.Jz x (X.lineV ξ t) + u →
      ∃ μ ∈ X.Λp ξ, (n' : ℂ) • u = X.ucomp x ξ (X.embV μ)
def IntegerApproximationCount : Prop :=
  ∀ (r : ℕ) (X : Data E r),
    (∀ w : X.Ψ → ℂ, ∃ α : 𝓞 E, ∀ τ : X.Ψ, ‖τ.1 (α : E) - w τ‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E) ∧
    ∀ R : ℝ, 0 ≤ R → {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.Finite ∧
      ({α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.ncard : ℝ) ≤ (1 + 2 * R) ^ (2 * fdeg E)
def ShortVectorHypotheses {r : ℕ} (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (c1 w : ℝ) (z0 : Frame X.Ψ r) : Prop :=
  X.IsDominant la ∧ P ∈ X.SS la ∧ X.IsIso ξ ∧ 0 < c1 ∧ ∑ τ, ν τ ≤ c1 ∧
    (∃ x ∈ X.dom, X.fj la ξ ν P x ≠ 0) ∧ 1 ≤ w ∧ (∑ τ, X.spread la τ) ≤ w ∧
    (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
      Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) ∧
    z0 ∈ X.FramesOverBasis ξ ∧
    sSup {t | ∃ x ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) x} < 2 * X.hatN la (X.fj la ξ ν P) z0
def ShortVectorBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ≤
        X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)
def d6rh (c1 w : ℝ) : ℝ := 1 / (12 * Real.pi * (c1 + w))
def d6La (r p0 : ℕ) (f : ℕ) (d ep0 rh : ℝ) : ℝ :=
  (2 * ReciprocityTheory.MultiplicativeHeights.approxR (r - 2) (d5mu f (r - 2) d (Real.sqrt ep0)) (rh / 40)) ^ (2 * p0 - 1)
def frameIndexBound (r f : ℕ) (d rd NA NC ep0 : ℝ) : ℝ :=
  (f : ℝ) * ((2 * f * (r - 2) : ℕ) : ℝ) ^ 3 * d * NA * Real.sqrt (NC ^ 2 * rd / ep0)
def FundamentalDomainPointBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 → (r : ℝ) ≤ w →
    let ep0 := flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w
    let rh := d6rh c1 w
    let La := d6La r X.p0 (fdeg E) (dE E) ep0 rh
    let ms := frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0
    ∀ n' : ℕ, 1000 * ms / rh ≤ n' →
    ∃ x ∈ X.dom, ∃ lam : Fin (r - 2) → Fin r → E,
      (∀ j, lam j ∈ X.L' ∧ herm X.Gm (lam j) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
      (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → (∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
        X.Jz x (X.ucomp x ξ (X.embV (lam j))) = I • X.ucomp x ξ (X.embV (lam j))) ∧
      (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) →
        (∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
        X.Jz x (X.ucomp x ξ (X.embV (lam j))) = -(I • X.ucomp x ξ (X.embV (lam j)))) ∧
      (∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2) ∧
      (∀ μ ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧ (n' : ℂ) • X.aproj x ξ (X.embV μ) = X.embV (e • ξ)) ∧
      X.fj la ξ ν P x ≠ 0
end
end ReciprocityTheory.ChartRestriction.G.FD


