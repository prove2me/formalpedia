-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_BlockRatReal
-- name    : Formalism_PeriodIntegrals_BlockRatReal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:27.005585+00:00
-- url     : https://prove2.me/theorems/1d834d80-eeb5-4daf-b307-bfe65e1eb054
-- title:
--   Block Rat Real
-- statement:
--   Definitions and structural lemmas for Block Rat Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/BlockRatReal.lean

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
namespace PI.BlockRatReal
def colW (r n : ℕ) : Fin r × Fin n → (Fin n → ℕ) := fun v => Pi.single v.2 1
def colAddGen (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)
def dualWeyl (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  weightedHomogeneousSubmodule R (colW r n) ν ⊓
    ⨅ (l : Fin n) (j : Fin n) (_ : l < j),
      LinearMap.ker ((colAddGen R (r := r) l j).toLinearMap -
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).toLinearMap)
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
def detShift {N : ℕ} (w : Fin N → ℤ) : ℤ := if h : 0 < N then w ⟨N - 1, by omega⟩ else 0
def natW {N : ℕ} (w : Fin N → ℤ) : Fin N → ℕ := fun i => (w i - detShift w).toNat
def delSq (R : Type) [CommRing R] (N : ℕ) (w : Fin N → ℤ) : Submodule R (MvPolynomial (Fin N × Fin N) R) :=
  weyl R N N le_rfl (natW w)
def nuOf {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℕ :=
  fun t => (lam t - lam (Fin.last m)).toNat
def lamAt {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') : Fin (m + 1) → ℤ :=
  if Even s.val then lam0 s else fun i => -lam0 s i.rev
def Frames {ι : Type} {n : ℕ} (_G : ι → Matrix (Fin n) (Fin n) ℂ) : Type :=
  {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}
section Blocks
variable {nV : ℕ} {n' : Fin nV → ℕ} {m : ℕ} {Tau : Type} [Fintype Tau] {n : ℕ}
def reM (h : m + 1 = n) (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  A.submatrix (finCongr h) (finCongr h)
def zAt (h : m + 1 = n) (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau) (M y : Tau → Matrix (Fin n) (Fin n) ℂ)
    (v : Fin nV) (s : Fin (n' v)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  if Even s.val then reM h (M (pos ⟨v, s⟩) * y (pos ⟨v, s⟩))
  else ((reM h (M (pos ⟨v, s⟩) * y (pos ⟨v, s⟩)))⁻¹)ᵀ.submatrix id Fin.rev
def eAt (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) (v : Fin nV) (s : Fin (n' v)) : ℤ :=
  lamAt (lam0 v) s (Fin.last m)
def blkMod (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) (R : Type) [Field R] (v : Fin nV) (s : Fin (n' v)) :
    Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
  if Antitone (lamAt (lam0 v) s) then dualWeyl R (m + 1) (m + 1) (nuOf (lamAt (lam0 v) s)) else ⊥
def WtTie (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) (h : m + 1 = n)
    (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau) (lam : Tau → Fin n → ℤ) : Prop :=
  ∀ v (s : Fin (n' v)) (i : Fin (m + 1)), lam0 v s i = lam (pos ⟨v, s⟩) (finCongr h i)
def BlockRational (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) {LL : Type} [Field LL] (h : m + 1 = n)
    (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau) (G M : Tau → Matrix (Fin n) (Fin n) ℂ)
    (embLL : LL →+* ℂ) (lam : Tau → Fin n → ℤ) : Prop :=
  ∀ v (s : Fin (n' v)) (f : MvPolynomial (Fin n × Fin n) ℤ), f ∈ delSq ℤ n (lam (pos ⟨v, s⟩)) →
    ∃ F ∈ blkMod lam0 LL v s, ∀ y : Frames G,
      (zAt h pos M y.1 v s).det ^ (eAt lam0 v s) *
          eval (fun x => zAt h pos M y.1 v s x.1 x.2) (MvPolynomial.map embLL F) =
        (y.1 (pos ⟨v, s⟩)).det ^ detShift (lam (pos ⟨v, s⟩)) *
          eval (fun x => y.1 (pos ⟨v, s⟩) x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) f)
end Blocks
def Stmt : Prop :=
  ∀ {nV : ℕ} {n' : Fin nV → ℕ} {m : ℕ} (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) {Tau : Type} [Fintype Tau]
    {n : ℕ} {LL : Type} [Field LL] (h : m + 1 = n) (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau)
    (G M : Tau → Matrix (Fin n) (Fin n) ℂ) (embLL : LL →+* ℂ) (lam : Tau → Fin n → ℤ), (∀ τ, Antitone (lam τ)) →
    WtTie lam0 h pos lam → (∀ τ, ∃ M0 : GL (Fin n) LL, M τ = M0.1.map embLL) →
    BlockRational lam0 h pos G M embLL lam
end PI.BlockRatReal


