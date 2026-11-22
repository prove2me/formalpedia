-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_StatementW
-- name    : Formalism_SatakeDualWeyl_StatementW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:14:33.926054+00:00
-- url     : https://prove2.me/theorems/2a9039a9-0fc5-4395-84f1-05ff94d31a2e
-- title:
--   Statement W
-- statement:
--   Definitions and structural lemmas for Statement W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/StatementW.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace Formalism.UG
def dwAct (R : Type) [CommRing R] (r n : ℕ) (g : GL (Fin r) R) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  Formalism.GradedWeylDivisibility.rowAct R (n := n) ((g⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)
def oneCol (R : Type) [CommRing R] (r : ℕ) :
    MvPolynomial (Fin r × Fin 1) R →ₐ[R] MvPolynomial (Fin r) R :=
  rename (Prod.fst : Fin r × Fin 1 → Fin r)
def DwActMul : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (g h : GL (Fin r) R),
    dwAct R r n (g * h) = (dwAct R r n g).comp (dwAct R r n h) ∧ dwAct R r n 1 = AlgHom.id R _
def DwStable : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν
def WeylGLStable : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν
def WeylGLStableLocal : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν
def OneColAct : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (g : GL (Fin r) R) (f : MvPolynomial (Fin r × Fin 1) R),
    oneCol R r (dwAct R r 1 g f) = polyAct R (Fin r) g (oneCol R r f)
def DualWeylOne : Prop :=
  ∀ (R : Type) [CommRing R] (r k : ℕ),
    (Formalism.GradedWeylDivisibility.dualWeyl R r 1 (fun _ => k)).map (oneCol R r).toLinearMap = nabla R (Fin r) k
def WeylOne : Prop :=
  ∀ (R : Type) [CommRing R] (r k : ℕ) (hr : 1 ≤ r),
    (Formalism.GradedWeylDivisibility.weyl R r 1 hr (fun _ => k)).map (oneCol R r).toLinearMap = weylSub R (Fin r) k
def OneColInj : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ), Function.Injective (oneCol R r)
end Formalism.UG


