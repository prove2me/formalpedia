-- Prove2me | Definitions.Def_N25_LocalKummerOperators
-- name    : N25_LocalKummerOperators
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:49.885716+00:00
-- url     : https://prove2.me/theorems/1dedd2ff-f4a8-4d1b-b05a-401a2b102ed5
-- title:
--   Selected and complementary local endomorphisms
-- statement:
--   Restricts the selected endomorphism $π$ and the explicit complementary endomorphism $ρ$ to the local fixed-point group $M_5$. These additive operators encode the local factorization underlying the $71$-torsion kernel and its divisibility argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerPolynomial
import Definitions.Def_N25_LocalFiveCondition
noncomputable section
namespace N25

/-! Galois equivariance of the complementary operator, and stability of the fixed module `M5` under both
operators; the restricted operators `pi5`, `rho5` below need these. -/

theorem rhoEnd_galois_comm (σ : Gal) (x : J) :
    σ • rhoEnd x = rhoEnd (σ • x) := by
  let a : J →+ J :=
    { toFun := fun y => σ • y
      map_zero' := smul_zero (A := J) σ
      map_add' := fun y z => smul_add σ y z }
  have hg (y : J) : a (gamma y) = gamma (a y) := gamma_galois_comm σ y
  change a (rhoEnd x) = rhoEnd (a x)
  simp only [rhoEnd, AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply,
    AddMonoidHom.id_apply, AddMonoidHom.comp_apply, map_add, map_zsmul, hg]

theorem piEnd_mem_M5 {x : J} (hx : x ∈ M5) : piEnd x ∈ M5 := by
  intro τ
  rw [piEnd_galois_comm, hx τ]

theorem rhoEnd_mem_M5 {x : J} (hx : x ∈ M5) : rhoEnd x ∈ M5 := by
  intro τ
  rw [rhoEnd_galois_comm, hx τ]

def pi5 : ↥M5 →+ ↥M5 where
  toFun x := ⟨piEnd x, piEnd_mem_M5 x.2⟩
  map_zero' := Subtype.ext (map_zero piEnd)
  map_add' x y := Subtype.ext (map_add piEnd (x : J) (y : J))

def rho5 : ↥M5 →+ ↥M5 where
  toFun x := ⟨rhoEnd x, rhoEnd_mem_M5 x.2⟩
  map_zero' := Subtype.ext (map_zero rhoEnd)
  map_add' x y := Subtype.ext (map_add rhoEnd (x : J) (y : J))
end N25


