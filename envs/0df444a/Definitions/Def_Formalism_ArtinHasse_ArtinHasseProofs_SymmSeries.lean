-- Prove2me | Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
-- name    : Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:54.566287+00:00
-- url     : https://prove2.me/theorems/9f7b8eb7-b48e-4cb1-8426-2c412ead7704
-- title:
--   Symm Series
-- statement:
--   Definitions and structural lemmas for Symm Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/ArtinHasseProofs/SymmSeries.lean

import Definitions.Def_Formalism_ArtinHasse_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.FT.SymmetricSeries
variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
end Formalism.FT.SymmetricSeries
namespace Formalism.FT.SymmetricSeries
variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
end Formalism.FT.SymmetricSeries
namespace Formalism.FT.SymmetricSeries
variable (R : Type*) [CommRing R] (n : ℕ)
def yv (m : ℕ) : MvPolynomial (Fin n) R :=
  if h : 1 ≤ m ∧ m ≤ n then MvPolynomial.X ⟨m - 1, by omega⟩ else 0
def tri : ℕ → MvPolynomial (Fin n) R
  | 0 => 1
  | k + 1 => ∑ i : Fin (k + 1), (-1) ^ (i : ℕ) * yv R n (i + 1) * tri (k - i)
decreasing_by omega
variable {R n}
variable (R n)
def Ee : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval (fun j : Fin n => MvPolynomial.esymm (Fin n) R (j + 1))
def Eh : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval (fun j : Fin n => MvPolynomial.hsymm (Fin n) R (j + 1))
def Tt : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval (fun j : Fin n => tri R n (j + 1))
variable {R n}
end Formalism.FT.SymmetricSeries
namespace Formalism.FT.SymmetricSeries
variable {R : Type*} [CommRing R] {n : ℕ}
variable (R n) in
abbrev hv : Fin n → MvPowerSeries (Fin n) R := fun j => Formalism.FT.hPS R n (j.val + 1)
def wt (α : Fin n →₀ ℕ) : ℕ := ∑ j : Fin n, ((j : ℕ) + 1) * α j
end Formalism.FT.SymmetricSeries
namespace Formalism.FT.SymmetricSeries
variable {R : Type*} [CommRing R] {n : ℕ}
def Fm (F : MvPowerSeries (Fin n) R) (m : ℕ) : MvPolynomial (Fin n) R :=
  ∑ d ∈ finsuppAntidiag (univ : Finset (Fin n)) m, MvPolynomial.monomial d (MvPowerSeries.coeff d F)
def Aw (n m : ℕ) : Finset (Fin n →₀ ℕ) :=
  ((range (m + 1)).biUnion fun k => finsuppAntidiag (univ : Finset (Fin n)) k).filter
    (fun α => wt α = m)
end Formalism.FT.SymmetricSeries


