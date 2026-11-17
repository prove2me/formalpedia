-- Prove2me | Definitions.Def_N25_KummerFactorization
-- name    : N25_KummerFactorization
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:07.810328+00:00
-- url     : https://prove2.me/theorems/b2c5d919-7623-4f20-ad73-e510c7d4ad14
-- title:
--   Complementary factors of multiplication by $71$
-- statement:
--   Records the endomorphism identities $π∘ρ=[71]$ and $ρ∘π=[71]$ on the Jacobian under the order-five relation $1+γ+γ^2+γ^3+γ^4=0$. These complementary factorizations make the selected kernel a $71$-torsion object and supply the algebraic input for the Kummer descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerOperators
/-! The two polynomial operators `piEnd` and `rhoEnd` are complementary factors of multiplication by 71
once the order-five relation `PhiFiveZero` holds. The `ZMod 71`-module structure on `V` needs this. -/
noncomputable section
namespace N25

/-- The complementary polynomial factors multiplication by 71. -/
theorem piEnd_comp_rhoEnd (hPhi : PhiFiveZero) :
    piEnd.comp rhoEnd = nsmulAddMonoidHom (α := J) 71 := by
  apply AddMonoidHom.ext
  intro x
  have h := hPhi x
  have hg := congrArg gamma h
  simp only [map_add, map_zero] at hg
  simp only [piEnd, rhoEnd, AddMonoidHom.comp_apply, AddMonoidHom.add_apply,
    AddMonoidHom.nsmul_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply,
    map_add, map_zsmul, nsmulAddMonoidHom_apply]
  have hc := congrArg (fun z : J => (-127 : ℤ) • z) h
  have hgc := congrArg (fun z : J => (-37 : ℤ) • z) hg
  linear_combination (norm := abel_nf) hc + hgc

/-- The reverse product also equals multiplication by 71. -/
theorem rhoEnd_comp_piEnd (hPhi : PhiFiveZero) :
    rhoEnd.comp piEnd = nsmulAddMonoidHom (α := J) 71 := by
  apply AddMonoidHom.ext
  intro x
  have h := DFunLike.congr_fun (piEnd_comp_rhoEnd hPhi) x
  simp only [piEnd, rhoEnd, AddMonoidHom.comp_apply, AddMonoidHom.add_apply,
    AddMonoidHom.nsmul_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply,
    map_add, map_nsmul, map_zsmul, nsmulAddMonoidHom_apply] at h ⊢
  linear_combination (norm := abel_nf) h
end N25


