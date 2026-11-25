-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_097
-- name    : RPLib_FX_EtPBC_097
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:42:31.634924+00:00
-- url     : https://prove2.me/theorems/2b9ba9ff-f85f-546b-a88d-7c8b94edcbb3
-- title:
--   Proper base change for the projective line, library file 097
-- statement:
--   File 097 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Coh`: S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces
--   * `S4.Def_RP_EtPBC_A_O2KapD`: S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_086

/-!
# Proper base change for the projective line, library file 097

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Coh`: S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces
* `S4.Def_RP_EtPBC_A_O2KapD`: S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2Coh =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces

* **`unitRes_eq_adj W`**: `Λ_W ⟶ W^* Λ_X` (`1 ↦ 1`) is the adjunction unit followed by
  `W^*(Λ[W] ⟶ Λ[X] ≅ Λ_X)`;
* **`resLE_eq_extFreeU W c`**: `resLE W.hom 1 c = extFreeU W 1 (Λ[W ⟶ X]^* c)`;
* `extFreeU_splitIn`, **`h1_eq_zero_of_pieces`** (a class vanishing on every piece of a clopen decomposition is `0`),
  `splitIn_splitPr`, `resLE_splitPr(_self/_ne)`, **`resLE_kapS_self`**, **`resLE_kapS_ne`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtCompact.GalTrE

universe u

section Coh

end Coh

section Pieces

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} {ι : Type u} (S : ι → X.Etale) [IsIso (cop S).hom]
  [Fintype ι] [DecidableEq ι]

variable (Λ) in
theorem resLE_splitPr_ne {k z : ι} (hkz : k ≠ z) (y : Ext.{u} (freeSh Λ (S z)) (unitSh Λ X) 1) :
    resLE (S k).hom 1 ((Ext.mk₀ (splitPr S Λ z)).comp y (zero_add 1)) = 0 := by
  rw [resLE_splitPr, copι_copPr_ne S hkz, Ext.mk₀_zero, Ext.zero_comp, map_zero]

end Pieces

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapD =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class

* **`resLE_kapS_sum`**: the global class `Σ_Q kapS Q (χ Q)` restricts to `κ(χ Q)` on the piece `Q`;
* **`resLE_kapS_kumD_eq`**: for etale `f : X₁ ⟶ X`, `g : X₁ ⟶ Y` of affine schemes whose rings are finite products of
  Dedekind domains, `resLE f (kapS p (kumD α)) = resLE g c_Y` when `c_Y` is the Kummer class of a unit `H` of `Γ(Y)`
  (piecewise), `α ^ d = u`, the roots of unity match, and on every piece `p₁` of `X₁`: over `p`, `u = H · v ^ d`;
  over another piece of `X`, `H` is a `d`-th power.
  Proof: `h1_eq_zero_of_pieces` on `X₁`, `piHom_comp_eq` for `f` and `g`, `resLE_kapS_self/ne`, `resLE_kumD_eq`
  (O2KapN) and `resLE_kumD_eq_zero` (O2KapF).
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

section KapSum

end KapSum

section KapB

variable {A K A' K' A'' K'' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing A'] [IsDedekindDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K']
  [CommRing A''] [IsDomain A''] [Field K''] [Algebra A'' K''] [IsFractionRing A'' K'']
  [IsIntegrallyClosed A] [IsNoetherianRing A] [IsIntegrallyClosed A''] [IsNoetherianRing A'']
  (φ : CommRingCat.of A ⟶ CommRingCat.of A') [Etale (Spec.map φ)]
  (φ'' : CommRingCat.of A'' ⟶ CommRingCat.of A') [Etale (Spec.map φ'')]
  {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ ζ = ζ) {ζ'' : maxUnram A'' K''} (hζ'' : IsPrimitiveRoot ζ'' N)
  (hζΓ'' : ∀ σ ∈ (⊤ : Subgroup (Pi1 A'' K'')), σ ζ'' = ζ'') {d : ℕ} [NeZero d] (hdN : d ∣ N)
  {α : (maxUnram A K)ˣ} (hα : α ∈ rad (⊤ : Subgroup (Pi1 A K)) d)
  {β : (maxUnram A'' K'')ˣ} (hβ : β ∈ rad (⊤ : Subgroup (Pi1 A'' K'')) d) {g : Λ} (hg : d • g = 0)

/-- **Ring form of the off-piece kill.** -/
theorem resLE_kumD_eq_zero_ring (hinj'' : Function.Injective φ''.hom) {s'' : A''}
    (hz'' : ζ'' = algebraMap K'' (maxUnram A'' K'') (algebraMap A'' K'' s'')) {H'' : A''}
    (hu'' : (β : maxUnram A'' K'') ^ d = algebraMap K'' (maxUnram A'' K'') (algebraMap A'' K'' H''))
    {v : K'} (hv : v ^ d = algebraMap A' K' (φ''.hom H'')) :
    resLE (Spec.map φ'') 1 (kappaLH A'' K'' Λ (kumD hζ'' hζΓ'' hdN hβ hg)) = 0 := by
  have hiK'' : Function.Injective ((algebraMap A' K').comp φ''.hom) := (IsFractionRing.injective A' K').comp hinj''
  have hψ'' : ∀ a : A'', IsFractionRing.lift hiK'' (algebraMap A'' K'' a) = algebraMap A' K' (φ''.hom a) :=
    fun a => IsFractionRing.lift_algebraMap hiK'' a
  exact resLE_kumD_eq_zero φ'' (map_genPt_of_injective _ hinj'') hζ'' hζΓ'' hdN hβ hg (IsFractionRing.lift hiK'')
    hψ'' hz'' hu'' (hv.trans (hψ'' H'').symm)

end KapB

section Piece

end Piece

section GenPieces

universe u'

end GenPieces

section KapD

end KapD

end RamanujanPetersson.EtPBC.EtKum

end

end


