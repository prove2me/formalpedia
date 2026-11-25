-- Prove2me | Definitions.Def_RPLib_FX_EtP1_09
-- name    : RPLib_FX_EtP1_09
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T02:50:25.702872+00:00
-- url     : https://prove2.me/theorems/4ea7865c-ca3c-51fa-af0b-f251743d373d
-- title:
--   Étale cohomology of the projective line, library file 09 of 34
-- statement:
--   File 09 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_H1`: S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_08

/-!
# Étale cohomology of the projective line, library file 09 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_H1`: S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_H1 =====
section

/-!
# S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`

* `isRepExt_fibRep`: the generic stalk of `0 → G → P → Λ_X → 0` (`G`, `P` lisse) is an extension of
  `π₁`-representations;
* **`exists_kappa_eq`**: `κ` is surjective (write `e` as the class of a short exact sequence, its middle term is lisse
  by `isLisse_of_ext`, its generic stalk gives the cocycle);
* `kappaZ : Z¹ →+ H¹`, with kernel the coboundaries;
* **`h1Equiv A K hG : H Λ G 1 ≃+ CurveCoh.H1 (fibRep G) ⊤`**, with `h1Equiv_symm_mk`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr RamanujanPetersson.EtSheaves.TorSec

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

variable [IsNoetherianRing A]

section Z1

variable {A K} {G : EtSh Λ (Spec (CommRingCat.of A))} {hG : IsLisse Λ G}

end Z1

variable {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)

/-- The induced map `H¹_cont(π₁, G_η̄) → H¹(Spec A, G)`. -/
def h1ToH : CurveCoh.H1 (EssSurj.fibRep A K G hG) ⊤ →+ H Λ G 1 :=
  QuotientAddGroup.lift ((CurveCoh.B1 (EssSurj.fibRep A K G hG) ⊤).comap
    (CurveCoh.Z1 (EssSurj.fibRep A K G hG) ⊤).subtype).toAddSubgroup (kappaZ A K hG)
    fun z hz => AddMonoidHom.mem_ker.2 ((kappaZ_eq_zero_iff A K hG z).2 hz)

theorem h1ToH_mk (z : CurveCoh.Z1 (EssSurj.fibRep A K G hG) ⊤) :
    h1ToH A K hG (CurveCoh.H1.mk (EssSurj.fibRep A K G hG) ⊤ z) = kappaZ A K hG z := rfl

theorem h1ToH_bijective : Function.Bijective (h1ToH A K hG) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun q hq => ?_, fun e => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ q
    have hz : kappaZ A K hG z = 0 := hq
    rw [kappaZ_eq_zero_iff] at hz
    exact (Submodule.Quotient.mk_eq_zero _).2 hz
  · obtain ⟨c, hc, hcl, rfl⟩ := exists_kappa_eq A K hG e
    refine ⟨CurveCoh.H1.mk (EssSurj.fibRep A K G hG) ⊤ ⟨fun g => c g.1, (CurveCoh.mem_Z1 _ _ _).2
      ⟨hcl.comp_continuous continuous_subtype_val, fun g h => hc g.1 h.1⟩⟩, ?_⟩
    rw [h1ToH_mk, kappaZ_apply]
    exact kappa_congr A K hG _ _ _ _ (funext fun _ => rfl)

end RamanujanPetersson.EtCompact

end

end


