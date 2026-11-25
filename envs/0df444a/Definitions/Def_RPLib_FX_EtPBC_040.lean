-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_040
-- name    : RPLib_FX_EtPBC_040
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:12:13.292644+00:00
-- url     : https://prove2.me/theorems/69866842-dc55-53a9-a5c7-4cb2f2382e43
-- title:
--   Proper base change for the projective line, library file 040
-- statement:
--   File 040 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2N2`: S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)
--   * `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
--   * `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_033

/-!
# Proper base change for the projective line, library file 040

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2N2`: S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)
* `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
* `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2N2 =====
section

/-!
# S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)

* `unitCoc χ : τ ↦ χ τ • 1` (a cocycle for the trivial action on `(Λ_X)_η̄` when `χ` is additive),
  `fibRep_unitSh'`, `unitCoc_isCocycle`, `unitCoc_isLocallyConstant`;
* `kappaL A K Λ hχ hl : H¹(Spec A, Λ)`, the class of an additive locally constant `χ : π₁(A) → Λ`;
* `resLE g n : H^n(X, Λ) → H^n(U, Λ)` for an etale `g : U ⟶ X` (`resHE` and `unitResIso`);
* **`resLE_kappaL`** (NAT for constant coefficients): for `g : Spec A' ⟶ Spec A` etale with `g η' = η`,
  `resLE g 1 (κ χ) = κ χ'` whenever `χ' (σ|) = χ ((galTrX σ)|)` for all `σ ∈ Gal(η')`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec

section Unit

end Unit

section ResL

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {Λ : Type u} [CommRing Λ]

/-- **Restriction `H^n(X, Λ) → H^n(U, Λ)`** along an etale `g` (`resHE`, then `g^* Λ_X ≅ Λ_U`). -/
def resLE (n : ℕ) (e : H Λ (unitSh Λ X) n) : H Λ (unitSh Λ U) n :=
  (resHE g _ n e).comp (Ext.mk₀ (unitResIso g Λ).inv) (add_zero n)

theorem resLE_apply (n : ℕ) (e : H Λ (unitSh Λ X) n) :
    resLE g n e = (resHE g _ n e).comp (Ext.mk₀ (unitResIso g Λ).inv) (add_zero n) := rfl

end ResL

section NatL

end NatL

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2P3a =====
section

/-!
# S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps

* `ChL A K Λ`: the additive group of additive locally constant characters `π₁(A) → Λ`; `mem_ChL`, `chl_cyc`;
* `zetaE_prim`, `zetaE_fix`: a primitive root `ζ₀ ∈ K` in `maxUnram A K`;
* `kumTau hζ hζΓ hτ hΛ : Λ →+ ChL`, `c ↦ kumChi ζ τ c`;
* **`kappaLH A K Λ : ChL A K Λ →+ H¹(Spec A, Λ)`** (`kappaL`, additive by `kappa_add`), **`kappaLH_surj`**;
* `resLEHom g n : H^n(X, Λ) →+ H^n(U, Λ)` (`resLE` is additive).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer RamanujanPetersson.EtPi1
  RamanujanPetersson.EtCompact.GalTrE

section ChL

end ChL

section KappaLH

end KappaLH

section ResH

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {Λ : Type u} [CommRing Λ]

/-- `resLE` as an additive map. -/
def resLEHom (n : ℕ) : H Λ (unitSh Λ X) n →+ H Λ (unitSh Λ U) n :=
  AddMonoidHom.mk' (resLE g n) (fun a b => by
    rw [resLE_apply, resLE_apply, resLE_apply, map_add, Ext.add_comp])

end ResH

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapP =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map

For `f : X₁ ⟶ X` etale between affine schemes whose rings are finite products of Dedekind domains, and a Kummer
class `kapS p (kumD α)` on the piece `p` of `X` (`α^d = u`):
* `kerMap f p₁ : Γ(X) → Γ(X₁) ⧸ p₁`, `exists_minimalPrime_le_ker`, `kerLift`, **`piHom_comp_eq`**
  (the piece `p₁` of `X₁` maps into the piece `q` of `X` through `Spec (Γ(X₁) ⧸ p₁) ⟶ Spec (Γ(X) ⧸ q)`),
  `injective_of_etale` (an etale map of domains is injective), `resLE_congr`, `resLE_kapS_self`, `resLE_kapS_ne`;
* **`resLE_kapS_kumD_eq_zero`**: if `u` becomes a `d`-th power in the fraction field of every piece of `X₁` lying
  over `p`, then `resLE f 1 (kapS p (kumD α)) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

universe u

theorem resLE_congr {U X : Scheme.{u}} {Λ : Type u} [CommRing Λ] {g₁ g₂ : U ⟶ X} [Etale g₁] [Etale g₂]
    (e : g₁ = g₂) (n : ℕ) (c : H Λ (unitSh Λ X) n) : resLE g₁ n c = resLE g₂ n c := by
  subst e
  rfl

section Fac

end Fac

section KappaRes

end KappaRes

section Red

end Red

section KapP

end KapP

end RamanujanPetersson.EtPBC.EtKum

end

end


