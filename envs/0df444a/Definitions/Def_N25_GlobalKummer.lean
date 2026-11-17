-- Prove2me | Definitions.Def_N25_GlobalKummer
-- name    : N25_GlobalKummer
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:23:16.075852+00:00
-- url     : https://prove2.me/theorems/a970050e-91aa-4547-81e9-5334377382e6
-- title:
--   Kummer cocycles in the selected $71$-torsion kernel
-- statement:
--   Defines the selected endomorphism on rational fixed points, the inherited Galois action on its kernel $V$, the resulting $F_{71}$-module and representation structures under the order-five relation, and the cocycle $σ↦σQ−Q$ attached to $71Q=P$. These objects form the global Kummer-theoretic carrier for the descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerPolynomial
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_N25_KummerFactorization
noncomputable section
namespace N25.GlobalKummer
/-- The selected operator restricted to rational fixed points. -/
def piM : ↥M →+ ↥M where
  toFun x := ⟨piEnd x, fun σ => by
    rw [piEnd_galois_comm, x.property σ]⟩
  map_zero' := Subtype.ext (map_zero piEnd)
  map_add' x y := Subtype.ext (map_add piEnd (x : J) (y : J))

instance : DistribMulAction Gal ↥V where
  smul := vAct
  one_smul v := Subtype.ext (one_smul _ (v : J))
  mul_smul σ τ v := Subtype.ext (mul_smul σ τ (v : J))
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ v w := Subtype.ext (smul_add σ (v : J) (w : J))

/-- The kernel has exponent 71 by the complementary polynomial identity. -/
def vModule (hPhi : PhiFiveZero) : Module (ZMod 71) ↥V :=
  AddCommGroup.zmodModule fun v => by
    apply Subtype.ext
    change 71 • (v : J) = 0
    have h := congrArg (fun f : J →+ J => f (v : J)) (rhoEnd_comp_piEnd hPhi)
    change rhoEnd (piEnd (v : J)) = 71 • (v : J) at h
    rw [show piEnd (v : J) = 0 from v.2, map_zero] at h
    exact h.symm

/-- The literal kernel with its arithmetic Galois representation. -/
def vRep (hPhi : PhiFiveZero) : Rep (ZMod 71) Gal := by
  letI := vModule hPhi
  letI : SMulCommClass Gal (ZMod 71) ↥V := ⟨fun σ a v =>
    ZMod.map_smul (DistribSMul.toAddMonoidHom ↥V σ) a v⟩
  exact Rep.of (DistribMulAction.toModuleEnd (ZMod 71) ↥V)

/-- A division point defines a cocycle in the literal selected kernel. -/
def divisionCocycle (hPhi : PhiFiveZero) (P : ↥M) (Q : J)
    (hQ : piEnd Q = (P : J)) : groupCohomology.cocycles₁ (vRep hPhi) :=
  ⟨fun σ => ⟨σ • Q - Q, by
    change piEnd (σ • Q - Q) = 0
    rw [map_sub, ← piEnd_galois_comm, hQ, P.property σ, sub_self]⟩, by
      apply (groupCohomology.mem_cocycles₁_iff _).2
      intro σ τ
      apply Subtype.ext
      change (σ * τ) • Q - Q = σ • (τ • Q - Q) + (σ • Q - Q)
      rw [mul_smul, smul_sub]
      abel⟩
end N25.GlobalKummer


