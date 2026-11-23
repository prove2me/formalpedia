-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:20.569796+00:00
-- url     : https://prove2.me/theorems/cfc1faed-4b81-449d-910c-1b3baf575d60
-- title:
--   Crude Min
-- statement:
--   Definitions and structural lemmas for Crude Min, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
def Dom (a : T → ℕ → ℕ) : Prop := ∀ (σ : T) (i j : Fin (r σ)), i ≤ j → a σ j ≤ a σ i
def GoodL (β : (Σ σ : T, Fin (r σ)) → Fin n) : Set (Letter T r n) := {ℓ | ∃ i, β ⟨ℓ.1, i⟩ = ℓ.2.2}
def diagExp (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) : Letter T r n →₀ ℕ :=
  ∑ p : Σ σ : T, Fin (r σ), Finsupp.single ⟨p.1, p.2, β p⟩ (a p.1 p.2)
def crMinor (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (σ : T) (kk : Fin (r σ)) :
    Matrix (Fin (kk.val + 1)) (Fin (kk.val + 1)) (MvPolynomial (Letter T r n) R) :=
  fun i j => X ⟨σ, Fin.castLE kk.isLt i, β ⟨σ, Fin.castLE kk.isLt j⟩⟩
def crExp (a : T → ℕ → ℕ) (σ : T) (kk : Fin (r σ)) : ℕ :=
  a σ kk - (if kk.val + 1 < r σ then a σ (kk.val + 1) else 0)
def crP (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) :
    MvPolynomial (Letter T r n) R :=
  ∏ σ : T, ∏ kk : Fin (r σ), (crMinor r n R β σ kk).det ^ crExp r a σ kk
def Pmin (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) : MvPolynomial (Letter T r n) ℤ :=
  crP r n ℤ β a
section Part1
variable {r n}
end Part1
section Part2
variable {r n}
end Part2
section Part3
variable {r n}
def crW (σ : T) (i : ℕ) : Letter T r n → ℕ := fun ℓ => if ℓ.1 = σ ∧ (ℓ.2.1 : ℕ) = i then 1 else 0
end Part3
section Part4
variable {r n}
def crDl (β : (Σ σ : T, Fin (r σ)) → Fin n) : (Σ σ : T, Fin (r σ)) → Letter T r n :=
  fun p => ⟨p.1, p.2, β p⟩
def crRho (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) :
    MvPolynomial (Letter T r n) R →ₐ[R] MvPolynomial (Letter T r n) R :=
  aeval fun ℓ => if ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩ then X ℓ else 0
def crDiag (β : (Σ σ : T, Fin (r σ)) → Fin n) : Set (Letter T r n) := {ℓ | ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩}
def crIsMono {R : Type} [CommRing R] (p : MvPolynomial (Letter T r n) R) : Prop :=
  ∃ E, p = monomial E 1
end Part4
variable (k : Type) [Field k] [CharZero k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
end Formalism.L2.Pj.Crude


