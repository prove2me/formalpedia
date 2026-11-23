-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
-- name    : Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:10.844277+00:00
-- url     : https://prove2.me/theorems/9202af27-cff1-45ba-a560-a1c8f5790568
-- title:
--   Adelic Pair
-- statement:
--   Definitions and structural lemmas for Adelic Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/AdelicPair.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.ClassFin
open Matrix
variable {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def ev {R : Type} [CommRing R] [Algebra ℚ R] (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι R) : R :=
  MvPolynomial.aeval (fun ij : ι × ι => g ij.1 ij.2) f
noncomputable def evC (f : MvPolynomial (ι × ι) ℂ) (g : Matrix ι ι ℂ) : ℂ :=
  MvPolynomial.eval (fun ij : ι × ι => g ij.1 ij.2) f
def vanI (Γ : Set (Matrix ι ι ℂ)) : Set (MvPolynomial (ι × ι) ℚ) := {f | ∀ g ∈ Γ, ev f g = 0}
def pts (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] : Set (Matrix ι ι R) :=
  {g | ∀ f ∈ vanI Γ, ev f g = 0}
structure IsPre (Γ : Set (Matrix ι ι ℂ)) : Prop where
  one_mem : (1 : Matrix ι ι ℂ) ∈ Γ
  mul_mem : ∀ g ∈ Γ, ∀ h ∈ Γ, g * h ∈ Γ
  adj_mem : ∀ g ∈ Γ, g.adjugate ∈ Γ
  det_eq : ∀ g ∈ Γ, g.det = 1
  aut_mem : ∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ
structure IsQGroup (Γ : Set (Matrix ι ι ℂ)) : Prop extends IsPre Γ where
  closed : pts Γ ℂ ⊆ Γ
def SS (Γ : Set (Matrix ι ι ℂ)) : Prop :=
  ∀ W : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W, g *ᵥ v ∈ W) →
    ∃ W' : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W', g *ᵥ v ∈ W') ∧ IsCompl W W'
structure AdelicPair (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R) : Prop where
  int_of_mem : ∀ q : ℚ, algebraMap ℚ R q ∈ R₀ → ∃ z : ℤ, q = z
  approx : ∀ M : ℕ, 0 < M → ∀ r : R, ∃ q : ℚ, ∃ a ∈ R₀, r = algebraMap ℚ R q + (M : R) * a
def CF (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R) : Prop :=
  ∃ T : Finset (Matrix ι ι R), (∀ s ∈ T, s ∈ pts Γ R) ∧ ∀ x ∈ pts Γ R, ∃ γ ∈ pts Γ ℚ, ∃ s ∈ T, ∃ u ∈ pts Γ R,
    (∀ i j, u i j ∈ R₀) ∧ x = γ.map (algebraMap ℚ R) * s * u
noncomputable def blk {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ) (g : Matrix ι ι R) : Matrix ι ι R :=
  e.map (algebraMap ℚ R) * g * e.map (algebraMap ℚ R) +
    (1 - e.map (algebraMap ℚ R)) * g * (1 - e.map (algebraMap ℚ R))
noncomputable def linExt {R : Type} [CommRing R] [Algebra ℚ R] (c : ι × ι → ι × ι → ℚ) (X : Matrix ι ι R) :
    Matrix ι ι R :=
  Matrix.of fun i j => ∑ kl : ι × ι, algebraMap ℚ R (c (i, j) kl) * X kl.1 kl.2
def IsLog (H A : Matrix ι ι ℂ) : Prop :=
  ∃ (U : Matrix ι ι ℂ) (d : ι → ℝ), U * Uᴴ = 1 ∧ H = U * diagonal (fun i => (d i : ℂ)) * Uᴴ ∧
    A = U * diagonal (fun i => (Real.exp (d i) : ℂ)) * Uᴴ
def Harm {σ : Type} [Fintype σ] (g : σ → Matrix ι ι ℂ) : Prop :=
  ∃ H : σ → Matrix ι ι ℂ, (∀ s, IsLog (H s) ((g s)ᴴ * g s)) ∧ ∑ s, H s = 0
def tpow {R : Type} [CommRing R] (d : ℕ) (y : Matrix ι ι R) : Matrix (Fin d → ι) (Fin d → ι) R :=
  Matrix.of fun a b => ∏ k, y (a k) (b k)
abbrev TIdx (ι : Type) {m : ℕ} (d : Fin m → ℕ) : Type := Σ i : Fin m, (Fin (d i) → ι)
def act {R : Type} [CommRing R] {m : ℕ} (d : Fin m → ℕ) (t : TIdx ι d → R) (y : Matrix ι ι R) : TIdx ι d → R :=
  fun k => ((fun a => t ⟨k.1, a⟩) ᵥ* tpow (d k.1) y) k.2
noncomputable def nsq {κ : Type} [Fintype κ] (v : κ → ℂ) : ℝ := ∑ k, ‖v k‖ ^ 2
def orb {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ) : Set (TIdx ι d → ℂ) :=
  {w | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ w = act d v y}
def IsMinVec {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ) : Prop := ∀ w ∈ orb d v, nsq v ≤ nsq w
def IsInv (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) : Prop :=
  ∀ g ∈ Γ, ∀ y : Matrix ι ι ℂ, evC f (g * y) = evC f y
noncomputable def ltr (g : Matrix ι ι ℂ) : MvPolynomial (ι × ι) ℂ →ₐ[ℂ] MvPolynomial (ι × ι) ℂ :=
  MvPolynomial.aeval fun ij : ι × ι => ∑ k, MvPolynomial.C (g ij.1 k) * MvPolynomial.X (k, ij.2)
structure IsReynolds (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) : Prop where
  inv : ∀ f, IsInv Γ (Rey f)
  fix : ∀ f, IsInv Γ f → Rey f = f
  mul : ∀ a f, IsInv Γ a → Rey (a * f) = a * Rey f
  stable : ∀ U : Submodule ℂ (MvPolynomial (ι × ι) ℂ), (∀ g ∈ Γ, ∀ f ∈ U, ltr g f ∈ U) → ∀ f ∈ U, Rey f ∈ U
structure IsSiegel [LinearOrder ι] (C : ℝ) (k : Matrix ι ι ℝ) (a : ι → ℝ) (n : Matrix ι ι ℝ) : Prop where
  orth : kᵀ * k = 1
  det_k : k.det = 1
  pos : ∀ i, 0 < a i
  prod_eq : ∏ i, a i = 1
  le : ∀ i j, i < j → a i ≤ C * a j
  diag : ∀ i, n i i = 1
  lower : ∀ i j, j < i → n i j = 0
  bdd : ∀ i j, |n i j| ≤ C
noncomputable def res {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    (b : Module.Basis β R A) (g : Matrix κ κ A) : Matrix (κ × β) (κ × β) R :=
  Matrix.of fun p q => Algebra.leftMulMatrix b (g p.1 q.1) p.2 q.2
noncomputable def emb {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (g : GL κ A) :
    Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R :=
  Matrix.fromBlocks (res b (g : Matrix κ κ A)) 0 0
    (Matrix.of fun _ _ => (res b ((g⁻¹ : GL κ A) : Matrix κ κ A)).det)
end GlobalTheory.ClassFin


