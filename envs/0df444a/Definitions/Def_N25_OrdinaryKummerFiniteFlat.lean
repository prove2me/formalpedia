-- Prove2me | Definitions.Def_N25_OrdinaryKummerFiniteFlat
-- name    : N25_OrdinaryKummerFiniteFlat
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:12:19.733557+00:00
-- url     : https://prove2.me/theorems/669523ef-6f75-4b0e-952b-77c2c8eca201
-- title:
--   Finite-flatness of ordinary $71$-division cocycles
-- statement:
--   Defines the proposition that every global geometric point $Q$ with $71Q$ rational has, after restriction to the local Galois group at $71$, a division-cocycle extension admitting a finite-flat model. It states the ordinary local Kummer condition at $71$ that must be established for the descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
set_option autoImplicit false

namespace N25

local instance instL_N25_OrdinaryKummerFiniteFlat_23397f : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- The ordinary division-cocycle condition at 71: every global geometric point
whose 71-multiple is rational has a finite-flat model of its local cocycle
extension. This is a proposition to prove, not an assumed coefficient model.
The natural-number representative of the scalar acts on the 71-torsion group. -/
def OrdinaryKummerFiniteFlat : Prop :=
  ∀ (Q : J) (hQ : (71 : ℕ) • Q ∈ M),
    let T := AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) 71
    let c : Gal → T := fun σ => ⟨σ • Q - Q, by
      apply AlgebraicCurve.Pic0.mem_torsion.mpr
      have hNat : (71 : ℕ) • (σ • Q - Q) = 0 := by
        have hs : σ • ((71 : ℕ) • Q) = (71 : ℕ) • (σ • Q) :=
          (DistribSMul.toAddMonoidHom J σ).map_nsmul 71 Q
        rw [nsmul_sub, ← hs, hQ σ, sub_self]
      exact (Nat.cast_smul_eq_nsmul ℤ 71 (σ • Q - Q)).trans hNat⟩
    groupCohomology.IsFiniteFlatRepresentation 71
      (fun σ (x : T × ZMod 71) =>
        (ModularCurve.JH.torsionGaloisRep 25 H25 71 (localGaloisToGlobal 71 σ) x.1 +
          x.2.val • c (localGaloisToGlobal 71 σ), x.2))

end N25


