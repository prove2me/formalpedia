-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:50.127834+00:00
-- url     : https://prove2.me/theorems/12621612-6a0b-470d-bbb6-e408b226ede1
-- title:
--   Transfer Rtt
-- statement:
--   Definitions and structural lemmas for Transfer Rtt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
def Good (P : Par) (Y : ℂ) : Prop :=
  ∀ π : Ty P, ∀ j ∈ Icc 1 (P.k - 1), ∀ n ∈ ({-2, -1, 0, 1, 2} : Finset ℤ), Y + (rho P π j : ℂ) + (n : ℂ) ≠ 0
def dA (P : Par) (Y : ℂ) : A P := qC P Y • (ggiA P * kap P fun π => (xC P π (Y + 1))⁻¹)
def mt (P : Par) (Y : ℂ) : A P := star (lA P (star Y))
end
end Formalism.FourierDecayAlt.P.Mx6
namespace Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
def rr (j : ℕ) (u : ℂ) : Ty P → ℂ := fun π => (u + (rho P π j : ℂ))⁻¹
def lam (j : ℕ) (u : ℂ) : A P := kap P (rr P j u) * SS P j
def abelian₂ (u : ℂ) : A P := ∑ j ∈ Icc 1 (P.k - 1), lam P j u
def lams (j : ℕ) (u : ℂ) : A P := star (SS P j) * kap P (rr P j u)
def Lams (u : ℂ) : A P := ∑ j ∈ Icc 1 (P.k - 1), lams P j u
end
end Formalism.FourierDecayAlt.P.Mx6
namespace Formalism.FourierDecayAlt.P.Mx6
variable {B : Type*} [Ring B] [Algebra ℂ B]
end Formalism.FourierDecayAlt.P.Mx6
namespace Formalism.FourierDecayAlt.P.Mx6.GA
section Gauss
variable {B : Type*} [Ring B] [Algebra ℂ B]
end Gauss
end Formalism.FourierDecayAlt.P.Mx6.GA
namespace Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section
def pX (I : Finset ℕ) (ρ : ℕ → ℂ) : ℂ[X] := ∏ i ∈ I, (X + C (ρ i))
theorem pX_eval (I : Finset ℕ) (ρ : ℕ → ℂ) (u : ℂ) : (pX I ρ).eval u = ∏ i ∈ I, (u + ρ i) := by
  simp [pX, eval_prod]
def W1 (I : Finset ℕ) (ρ : ℕ → ℂ) (q w : ℂ[X]) (N : ℕ → ℂ) : Prop :=
  w * pX I (fun i => ρ i + 1) = q + ∑ l ∈ I, C (N l) * (pX (I.erase l) ρ * pX (I.erase l) (fun i => ρ i + 1))
theorem W1.eval {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (h : W1 I ρ q w N) (u : ℂ) :
    w.eval u * ∏ i ∈ I, (u + (ρ i + 1)) = q.eval u +
      ∑ l ∈ I, N l * ((∏ j ∈ I.erase l, (u + ρ j)) * ∏ j ∈ I.erase l, (u + (ρ j + 1))) := by
  have := congrArg (Polynomial.eval u) h
  simpa [eval_finsetSum, pX_eval] using this
def rc (P : Par) (π : Ty P) : ℕ → ℂ := fun i => (rho P π i : ℂ)
def q1P (P : Par) : ℂ[X] :=
  ∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))
end
end Formalism.FourierDecayAlt.P.Mx6.WB
namespace Formalism.FourierDecayAlt.P.Mx6.PC
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W
noncomputable section
section Poly
variable {B : Type*} [Ring B] [Algebra ℂ B]
def ev (y : ℂ) : B[X] →+* B :=
  Polynomial.eval₂RingHom' (RingHom.id B) (algebraMap ℂ B y) fun a => (Algebra.commutes y a).symm
def IsPoly (f : ℂ → B) : Prop := ∃ p : B[X], ∀ y, f y = ev y p
def IsPolyS (a : ℂ → ℂ) : Prop := ∃ s : ℂ[X], ∀ y, a y = s.eval y
end Poly
variable (P : Par)
section Entries
variable {B : Type} [Ring B]
end Entries
end
end Formalism.FourierDecayAlt.P.Mx6.PC
namespace Formalism.FourierDecayAlt.P.Mx6.L3
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
def sh (i j : ℕ) (b : ℂ) : Ty P → ℂ := fun π => (b + (rho P π j : ℂ) - if j = i then 1 else 0)⁻¹
def ee (i j : ℕ) (u v : ℂ) : Ty P → ℂ :=
  (u - v) • (rr P i u * sh P i j v - rr P i v * sh P i j u) -
    (rr P i u * sh P i j u - rr P i u * sh P i j v - (rr P i v * sh P i j u - rr P i v * sh P i j v))
def FF (i j : ℕ) (u v : ℂ) : A P :=
  (u - v) • (lam P i u * lam P j v - lam P i v * lam P j u) -
    (lam P i u - lam P i v) * (lam P j u - lam P j v)
def cc (i j : ℕ) (u v : ℂ) : Ty P → ℂ := fun π =>
  -((u - v) ^ 2) * (rr P i u π * rr P i v π * rr P j u π * rr P j v π)
end
end Formalism.FourierDecayAlt.P.Mx6.L3
namespace Formalism.FourierDecayAlt.P.Mx6.L4
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
def rr1 (j : ℕ) (u : ℂ) : Ty P → ℂ := fun π => (u + (rho P π j : ℂ) + 1)⁻¹
end
end Formalism.FourierDecayAlt.P.Mx6.L4
namespace Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
section Abs
variable {B : Type*} [Ring B] [Algebra ℂ B]
end Abs
noncomputable section
variable (P : Par)
def cc : A P := zbA P * ggiA P
def cz : A P := zA P * ggiA P
end
end Formalism.FourierDecayAlt.P.Mx6
namespace Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
section Abs2
variable {B : Type*} [Ring B] [Algebra ℂ B]
end Abs2
noncomputable section
variable (P : Par)
def hh (u : ℂ) : Ty P → ℂ := fun π => qC P u / (xC P π u * xC P π (u + 1))
end
end Formalism.FourierDecayAlt.P.Mx6
namespace Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
section Abs3
variable {B : Type*} [Ring B] [Algebra ℂ B]
end Abs3
noncomputable section
variable (P : Par)
end
end Formalism.FourierDecayAlt.P.Mx6
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


