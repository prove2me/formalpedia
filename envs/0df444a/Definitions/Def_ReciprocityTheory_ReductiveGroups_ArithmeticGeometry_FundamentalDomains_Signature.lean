-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:30:29.381607+00:00
-- url     : https://prove2.me/theorems/b04958e2-d461-4d0c-851c-15c356ba5ce5
-- title:
--   Signature
-- statement:
--   Definitions and structural lemmas for Signature, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/Signature.lean

import Mathlib
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
def cc (x : E) : E := IsCMField.complexConj E x
def herm {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) : E :=
  ∑ a, ∑ b, x a * G a b * cc (y b)
def hermC {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) : ℂ :=
  ∑ a, ∑ b, u a * τ (G a b) * conj (v b)
def col {r : ℕ} (x : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : Fin r → ℂ := fun k => x k a
def gram {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => hermC τ G (col x a) (col x b)
def lminor {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)) : ℂ :=
  (M.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det
def sgn (p0 a : ℕ) : ℝ := if a < p0 then 1 else -1
def psgn (p0 i : ℕ) : ℝ := ∏ a ∈ Finset.range i, sgn p0 a
abbrev Frame (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Type := Ψ → Fin r → Fin r → ℂ
def mat {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) (τ : Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of (x τ)
def dmin {Ψ : Finset (E →+* ℂ)} {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (τ : Ψ)
    (i : Fin (r + 1)) : ℂ :=
  lminor (gram τ.1 G (mat x τ)) i
def GG (Ψ : Finset (E →+* ℂ)) {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ) : Set (Frame Ψ r) :=
  {x | ∀ τ : Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn p0 i * (dmin G x τ i).re}
def Bor (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Set (Frame Ψ r) :=
  {b | ∀ τ : Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0}
def rmul {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x b : Frame Ψ r) : Frame Ψ r :=
  fun τ => (mat x τ * mat b τ : Matrix (Fin r) (Fin r) ℂ)
def lact {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (x : Frame Ψ r) : Frame Ψ r :=
  fun τ => ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)
def IsUStab {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (γ : GL (Fin r) E) : Prop :=
  (∀ x y, herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x) (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) y) =
    herm G x y) ∧
  ∀ x, x ∈ Λ ↔ Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x ∈ Λ
def transvMat {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) (α : E) :
    Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => (if a = b then 1 else 0) + α * ξ a * ∑ k, G b k * cc (ξ k)
abbrev Wt (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Type := Ψ → Fin r → ℤ
def bchar {Ψ : Finset (E →+* ℂ)} {r : ℕ} (la : Wt Ψ r) (b : Frame Ψ r) : ℂ :=
  ∏ τ, ∏ i, b τ i i ^ la τ i
structure Data (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) where

  Ψ : Finset (E →+* ℂ)
  cmType : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ

  Gm : Matrix (Fin r) (Fin r) E
  Gm_herm : ∀ a b, cc (Gm a b) = Gm b a
  Gm_det : Gm.det ≠ 0
  p0 : ℕ
  p0_le : p0 ≤ r

  signature : ∀ τ : Ψ, ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
    gram τ.1 Gm P = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)

  Λ : Submodule (𝓞 E) (Fin r → E)
  Λ_fg : Λ.FG
  Λ_span : Submodule.span E (Λ : Set (Fin r → E)) = ⊤
  den : 𝓞 E
  den_ne : den ≠ 0
  Λ_int : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((den : E) * herm Gm x y)

  Γ : Subgroup (GL (Fin r) E)
  Γ_stab : ∀ γ ∈ Γ, IsUStab Gm Λ γ
  Γ_index : ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab Gm Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ
  Γ_free : ∀ γ ∈ Γ, ∀ x ∈ GG Ψ Gm p0, ∀ b ∈ Bor Ψ r, lact γ x = rmul x b → γ = 1

  χ : Wt Ψ r → GL (Fin r) E → ℂ
  χ_mul : ∀ la, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, χ la (γ * γ') = χ la γ * χ la γ'
  χ_add : ∀ la la', ∀ γ ∈ Γ, χ (la + la') γ = χ la γ * χ la' γ
  χ_fin : ∀ la, ∃ n : ℕ, 0 < n ∧ ∀ γ ∈ Γ, χ la γ ^ n = 1

  ξ0 : E
  ξ0_im : cc ξ0 = -ξ0
  ξ0_ne : ξ0 ≠ 0

  κ0 : E
  κ0_xi : κ0 = 2 * ξ0 ∨ κ0 = -(2 * ξ0)
  κ0_sign : ∀ τ : Ψ, (τ.1 κ0).im < 0
  m : ℕ
  m_pos : 0 < m
  transv : ∀ ξ ∈ Λ, herm Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s →
    ∃ γ ∈ Γ, (γ : Matrix (Fin r) (Fin r) E) = transvMat Gm ξ ((m : E) * s * κ0)
namespace Data
variable {r : ℕ} (X : Data E r)
def c (τ : X.Ψ) : ℝ := 2 * ‖τ.1 X.ξ0‖
abbrev dom : Set (Frame X.Ψ r) := GG X.Ψ X.Gm X.p0
def IsSec (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ P X.dom ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, P (lact γ x) = X.χ la γ * P x
def pnorm (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  ‖P x‖ * ∏ τ, ∏ i : Fin r,
    ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)
def gramPos (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  (gram τ.1 X.Gm (mat x τ)).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le)
def posPart (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : ℝ :=
  (∑ a : Fin X.p0, ∑ b : Fin X.p0,
    hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b *
      conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)))).re
def maj (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : ℝ :=
  2 * X.posPart x τ v - (hermC τ.1 X.Gm v v).re
def emb (τ : E →+* ℂ) (v : Fin r → E) : Fin r → ℂ := fun a => τ (v a)
def firstMinimumSq (x : Frame X.Ψ r) : ℝ :=
  sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (emb τ.1 v)}
def la1 (x : Frame X.Ψ r) : ℝ := Real.sqrt (X.firstMinimumSq x)
def tt (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) : ℝ := 1 / (X.c τ * X.maj x τ (emb τ.1 ξ))
def flowMat (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) -
    I * X.c τ * s * τ.1 (ξ a) * ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))
def flow (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (X.flowMat ξ τ (s τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)
end Data
end
end ReciprocityTheory.ChartRestriction.G.FD


