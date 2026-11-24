-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_OddDualWeyl
-- name    : Formalism_PeriodIntegrals_OddDualWeyl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:45.113018+00:00
-- url     : https://prove2.me/theorems/e6861f73-47ae-4450-b791-04cda9b3609d
-- title:
--   Odd Dual Weyl
-- statement:
--   Definitions and structural lemmas for Odd Dual Weyl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OddDualWeyl.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl
def rowAct (R : Type*) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun v => ∑ b : Fin r, C (g v.1 b) * X (b, v.2)
def rowGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => Polynomial.C (X v) +
    (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)
def rowDiv (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  (rowGen R a b f).coeff k
def lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s =>
    (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)).det
def nuNext {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ :=
  if h : s.val + 1 < n then ν ⟨s.val + 1, h⟩ else 0
def hw (R : Type*) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    MvPolynomial (Fin r × Fin n) R :=
  ∏ s : Fin n, (lpMinor R (s.val + 1) (by omega) (by omega)) ^ (ν s - nuNext ν s)
def applyWord (R : Type*) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  w.foldr (fun x g => rowDiv R x.1 x.2.1 x.2.2 g) f
def weyl (R : Type*) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord R w (hw R hn ν))
def colSpan (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
    (g : Matrix (Fin k) (Fin k) K) : Submodule R (Fin k → K) :=
  Submodule.span R (Set.range fun c : Fin k => fun i => g i c)
def nuOf {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℕ :=
  fun t => (lam t - lam (Fin.last m)).toNat
def deltaL (R K : Type*) [CommRing R] [Field K] [Algebra R K] (k : ℕ) (ν : Fin k → ℕ)
    (g : Matrix (Fin k) (Fin k) K) : Submodule R (MvPolynomial (Fin k × Fin k) K) :=
  Submodule.comap ((rowAct K (n := k) g).toLinearMap.restrictScalars R)
    (Submodule.map (mapAlgHom (Algebra.ofId R K)).toLinearMap (weyl R k k le_rfl ν))
def deltaLTw (R K : Type*) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
  Submodule.map ((LinearMap.lsmul K (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
      (g.det ^ (-(lam (Fin.last m))))).restrictScalars R)
    (deltaL R K (m + 1) (nuOf lam) g)
def Dl0 (O : Type*) {Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (Λ : Submodule O (Fin (m + 1) → Kf)) : Submodule O (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
  if Antitone lam then
    ⨅ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (_ : IsUnit g.det ∧ Λ = colSpan O g), deltaLTw O Kf m lam g
  else ⊥
section GlobalTheory
variable {K : Type} [Field K]
def lamStar {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ := fun i => -lam i.rev
def revCol {m : ℕ} (z : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  z.submatrix id Fin.rev
def OddFact (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : Prop :=
  ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit g.det →
    (∀ F ∈ Dl0 O m lam (colSpan O g), ∃ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F') ∧
    (∀ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ), ∃ F ∈ Dl0 O m lam (colSpan O g),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F')
end GlobalTheory
end PI.OddDualWeyl


