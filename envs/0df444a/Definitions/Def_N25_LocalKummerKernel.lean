-- Prove2me | Definitions.Def_N25_LocalKummerKernel
-- name    : N25_LocalKummerKernel
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:11:20.402077+00:00
-- url     : https://prove2.me/theorems/431c5f66-b969-4e42-a7a3-f38e7a323a90
-- title:
--   The explicit $K_2$ kernel sequence
-- statement:
--   Defines the inherited Galois action on $V$ and packages maps $i:F_{71}↪V$ and $q:V↠F_{71}$ with kernel of $q$ equal to the image of $i$, where $i$ transforms by $ψ$ and $q$ by the cyclotomic character. This is a technical certificate for the concrete short exact sequence used by the global Kummer construction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25_LocalKummerEquivariance
noncomputable section
local instance prime71_Def_N25_LocalKummerKernel : Fact (Nat.Prime 71) := ⟨by decide⟩
namespace N25
def vAct (σ : Gal) (v : ↥V) : ↥V :=
  ⟨σ • (v : J), by
    change piEnd (σ • (v : J)) = 0
    rw [← piEnd_galois_comm, show piEnd (v : J) = 0 from v.2]
    exact smul_zero (A := J) σ⟩

structure K2Rows where
  i : ZMod 71 →+ ↥V
  q : ↥V →+ ZMod 71
  i_injective : Function.Injective i
  exact_at_V : q.ker = i.range
  q_surjective : Function.Surjective q
  i_galois : ∀ (σ : Gal) (a : ZMod 71),
    vAct σ (i a) = i ((psi σ : ZMod 71) * a)
  q_galois : ∀ (σ : Gal) (v : ↥V),
    q (vAct σ v) =
      (ExtCitation.cycloChar 71 σ : ZMod 71) * q v

end N25


