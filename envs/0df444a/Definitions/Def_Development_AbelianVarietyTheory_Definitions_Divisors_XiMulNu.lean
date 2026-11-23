-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:08.891037+00:00
-- url     : https://prove2.me/theorems/8c6eed31-6804-4588-a668-d4b5e8fc4c3a
-- title:
--   Xi Mul Nu
-- statement:
--   Definitions and structural lemmas for Xi Mul Nu, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/XiMulNu.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix
namespace GlobalTheory.Sandwich
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
abbrev Ainf : Type := WittVector p (PreTilt O p)
def phiInv : Ainf p O →+* Ainf p O :=
  WittVector.map ((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p)
def ofPadic : ℤ_[p] →+* Ainf p O :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt O p))).comp (WittVector.equiv p).symm.toRingHom
def padicToO : ℤ_[p] →+* O := (fontaineTheta O p).comp (ofPadic p O)
variable {p O}
def root (ε : PreTilt O p) : PreTilt O p := (_root_.frobeniusEquiv (PreTilt O p) p).symm ε
def mu (ε : PreTilt O p) : Ainf p O := teichmuller p ε - 1
def nu (ε : PreTilt O p) : Ainf p O := teichmuller p (root ε) - 1
def xi (ε : PreTilt O p) : Ainf p O := ∑ i ∈ Finset.range p, teichmuller p (root ε) ^ i
open WittVector Ideal Matrix in
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
variable {p O} in
theorem _root_.GlobalTheory.Sandwich.xi_mul_nu (ε : PreTilt O p) :
    _root_.GlobalTheory.Sandwich.xi ε * _root_.GlobalTheory.Sandwich.nu ε = _root_.GlobalTheory.Sandwich.mu ε := by
  unfold _root_.GlobalTheory.Sandwich.xi _root_.GlobalTheory.Sandwich.nu _root_.GlobalTheory.Sandwich.mu
  rw [geom_sum_mul, ← map_pow]
  congr 2
  unfold _root_.GlobalTheory.Sandwich.root
  rw [← frobenius_def, frobenius_apply_frobeniusEquiv_symm]
open WittVector Ideal Matrix in
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
variable {p O} in
theorem _root_.GlobalTheory.Sandwich.phiInv_mu (ε : PreTilt O p) :
    _root_.GlobalTheory.Sandwich.phiInv p O (_root_.GlobalTheory.Sandwich.mu ε) = _root_.GlobalTheory.Sandwich.nu ε := by
  unfold _root_.GlobalTheory.Sandwich.phiInv _root_.GlobalTheory.Sandwich.mu _root_.GlobalTheory.Sandwich.nu
  rw [map_sub, map_one, WittVector.map_teichmuller]
  rfl
structure Datum (ε : PreTilt O p) (h : ℕ) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] where

  F : Matrix (Fin h) (Fin h) (Ainf p O)

  G : Matrix (Fin h) (Fin h) (Ainf p O)

  Ψ : Matrix (Fin h) (Fin h) (Ainf p O)

  Ψ' : Matrix (Fin h) (Fin h) (Ainf p O)

  ρT : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]

  ρM : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O)
  G_mul_F : G * F = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))
  F_eq : F = Ψ * F.map (phiInv p O)
  Ψ_mul : Ψ * Ψ' = xi ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))
  F_act : ∀ a, F * (ρT a).map (ofPadic p O) = ρM a * F
def etale (ε : PreTilt O p) (h : ℕ) : Datum ε h ℤ_[p] where
  F := 1
  G := mu ε • 1
  Ψ := 1
  Ψ' := xi ε • 1
  ρT := Algebra.ofId _ _
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (algebraMap _ _)
  G_mul_F := by simp
  F_eq := by simp
  Ψ_mul := by simp
  F_act := by intro a; simp [Algebra.ofId_apply]
def mult (ε : PreTilt O p) : Datum ε 1 ℤ_[p] where
  F := Matrix.of fun _ _ => mu ε
  G := 1
  Ψ := Matrix.of fun _ _ => xi ε
  Ψ' := 1
  ρT := Algebra.ofId _ _
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (algebraMap _ _)
  G_mul_F := by ext1 i j; simp [Subsingleton.elim i j]
  F_eq := by ext1 i j; simp [Matrix.mul_apply, phiInv_mu, xi_mul_nu]
  Ψ_mul := by ext1 i j; simp [Subsingleton.elim i j]
  F_act := by
    intro a; ext1 i j
    simp [Matrix.mul_apply, Algebra.ofId_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0]
namespace Datum
variable {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)
def al : (Fin h → O) →ₗ[O] (Fin h → O) := Matrix.toLin' (D.F.map (fontaineTheta O p))
def bb : (Fin h → O) →ₗ[O] (Fin h → O) := Matrix.toLin' (D.G.map (fontaineTheta O p))
def Fil : Submodule O (Fin h → O) := LinearMap.ker D.bb
def Lie : Submodule O (Fin h → O) := LinearMap.range D.bb
def Tsub (τ : Λ →+* O) : Submodule O (Fin h → O) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((D.ρT a).map (padicToO p O))) (τ a)
def Hsub (τ : Λ →+* O) : Submodule O (Fin h → O) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((D.ρM a).map (fontaineTheta O p))) (τ a)
def W (τ : Λ →+* O) : Submodule O (Fin h → O) := D.Tsub τ ⊓ LinearMap.ker D.al
def lieRank (τ : Λ →+* O) : ℕ := Module.finrank O ↥(D.Lie ⊓ D.Tsub τ)
def filRank (τ : Λ →+* O) : ℕ := Module.finrank O ↥(D.Fil ⊓ D.Hsub τ)
abbrev QOne (τ : Λ →+* O) : Type := D.W τ ⧸ (D.Lie ⊓ D.Tsub τ).comap (D.W τ).subtype
abbrev QTwo (τ : Λ →+* O) : Type :=
  ↥(D.Fil ⊓ D.Hsub τ) ⧸ ((D.Tsub τ).map D.al).comap (D.Fil ⊓ D.Hsub τ).subtype
abbrev QDel (τ : Λ →+* O) : Type :=
  ↥(D.Lie ⊓ D.Tsub τ) ⧸ ((D.Hsub τ).map D.bb).comap (D.Lie ⊓ D.Tsub τ).subtype
end Datum
end GlobalTheory.Sandwich


