-- Prove2me | Definitions.Def_N25_GlobalKummerSequence
-- name    : N25_GlobalKummerSequence
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:28.047315+00:00
-- url     : https://prove2.me/theorems/eac3b4cd-baa0-4d76-9c26-df52f0b1689c
-- title:
--   The character–kernel–cyclotomic filtration
-- statement:
--   Defines the order-five character line $F_{71}(ψ)$, the cyclotomic line $F_{71}(1)$, and the inclusion and quotient maps in the fixed filtration $0→F_{71}(ψ)→V→F_{71}(1)→0$. It is a technical packaging of the concrete $K_2$ sequence used to pass between kernel-valued and one-dimensional Kummer classes.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerRamification
import Definitions.Def_DualSelmer_ExtConditions
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace N25.GlobalKummer
local instance instL_N25_GlobalKummerSequence_23397f : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- The order-five character line in the frozen kernel filtration. -/
abbrev psiRep : Rep (ZMod 71) Gal := groupCohomology.ofChar psi

/-- The multiplicative quotient line in the frozen kernel filtration. -/
abbrev cyclotomicRep : Rep (ZMod 71) Gal :=
  groupCohomology.ofChar (ExtCitation.cycloChar 71)

/-- The literal inclusion supplied by the frozen K2 sequence, as a representation map. -/
def kernelInclusion (hPhi : PhiFiveZero) (K2 : K2Rows) : psiRep ⟶ vRep hPhi := by
  letI := vModule hPhi
  exact Rep.ofHom
    ⟨{ toFun := K2.i
       map_add' := K2.i.map_add
       map_smul' := fun a b => ZMod.map_smul K2.i a b },
      fun σ => by
        apply LinearMap.ext
        intro a
        change K2.i ((psi σ : ZMod 71) * a) = vAct σ (K2.i a)
        exact (K2.i_galois σ a).symm⟩

/-- The literal multiplicative quotient supplied by K2, as a representation map. -/
def kernelQuotient (hPhi : PhiFiveZero) (K2 : K2Rows) : vRep hPhi ⟶ cyclotomicRep := by
  letI := vModule hPhi
  exact Rep.ofHom
    ⟨{ toFun := K2.q
       map_add' := K2.q.map_add
       map_smul' := fun a b => ZMod.map_smul K2.q a b },
      fun σ => by
        apply LinearMap.ext
        intro v
        change K2.q (vAct σ v) = (ExtCitation.cycloChar 71 σ : ZMod 71) * K2.q v
        exact K2.q_galois σ v⟩

end N25.GlobalKummer


