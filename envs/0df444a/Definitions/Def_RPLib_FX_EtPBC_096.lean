-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_096
-- name    : RPLib_FX_EtPBC_096
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:42:28.129039+00:00
-- url     : https://prove2.me/theorems/5777eb8e-e9b4-5b96-aa3a-1947fe3ba2b9
-- title:
--   Proper base change for the projective line, library file 096
-- statement:
--   File 096 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Coh`: S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces
--   * `S4.Def_RP_EtPBC_A_O2KapN`: S4-EtPBC-A, O2 M6 (O2KapN): naturality of Kummer classes along etale maps of Dedekind domains
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_085
import Definitions.Def_RPLib_FX_EtPBC_086

/-!
# Proper base change for the projective line, library file 096

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Coh`: S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces
* `S4.Def_RP_EtPBC_A_O2KapN`: S4-EtPBC-A, O2 M6 (O2KapN): naturality of Kummer classes along etale maps of Dedekind domains
-/

set_option autoImplicit false

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
theorem resLE_splitPr_self (z : ι) (y : Ext.{u} (freeSh Λ (S z)) (unitSh Λ X) 1) :
    resLE (S z).hom 1 ((Ext.mk₀ (splitPr S Λ z)).comp y (zero_add 1)) = extFreeU Λ (S z) 1 y := by
  rw [resLE_splitPr, copι_copPr_self, Ext.mk₀_id_comp]

end Pieces

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapN =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapN): naturality of Kummer classes along etale maps of Dedekind domains

* **`resLE_kumD`**: along an etale `Spec.map φ` (`η' ↦ η`) with `ψ : K → K'` extending `φ`, the class `κ(kumD α)`
  (`α^d = u`) restricts to `κ(kumD γ)` for any radical `γ` with `γ^d = ψ u` (roots of unity matched by `ψ`);
* **`exists_root_of_isUnit`**: a unit of a Dedekind domain has a `d`-th root in `K_U` (`d` invertible);
* **`resLE_kumD_eq`**: two Kummer classes from `A` and `A''` agree on `A'` once their radicands differ by a `d`-th
  power there and one of them is a unit of `A'`.
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

section Root

end Root

section KapN

end KapN

section KapE

variable {A K A' K' A'' K'' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing A'] [IsDedekindDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K']
  [CommRing A''] [IsDomain A''] [Field K''] [Algebra A'' K''] [IsFractionRing A'' K'']
  [IsIntegrallyClosed A] [IsNoetherianRing A] [IsIntegrallyClosed A''] [IsNoetherianRing A'']
  (φ : CommRingCat.of A ⟶ CommRingCat.of A') [Etale (Spec.map φ)]
  (h : Spec.map φ (GenBr.genPt A') = GenBr.genPt A)
  (φ'' : CommRingCat.of A'' ⟶ CommRingCat.of A') [Etale (Spec.map φ'')]
  (h'' : Spec.map φ'' (GenBr.genPt A') = GenBr.genPt A'')
  {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ ζ = ζ) {ζ'' : maxUnram A'' K''} (hζ'' : IsPrimitiveRoot ζ'' N)
  (hζΓ'' : ∀ σ ∈ (⊤ : Subgroup (Pi1 A'' K'')), σ ζ'' = ζ'') {d : ℕ} [NeZero d] (hdN : d ∣ N)
  {α : (maxUnram A K)ˣ} (hα : α ∈ rad (⊤ : Subgroup (Pi1 A K)) d)
  {β : (maxUnram A'' K'')ˣ} (hβ : β ∈ rad (⊤ : Subgroup (Pi1 A'' K'')) d) {g : Λ} (hg : d • g = 0)

include h h'' in
/-- **Two Kummer classes agree on `A'`** when `ψ u = ψ'' u'' · v^d` and `ψ'' u''` is a unit of `A'`. -/
theorem resLE_kumD_eq (ψ : K →+* K') (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (φ.hom a))
    (ψ'' : K'' →+* K') (hψ'' : ∀ a : A'', ψ'' (algebraMap A'' K'' a) = algebraMap A' K' (φ''.hom a))
    {z₀ u : K} {z₀'' u'' : K''} (hz : ζ = algebraMap K (maxUnram A K) z₀)
    (hz'' : ζ'' = algebraMap K'' (maxUnram A'' K'') z₀'') (hzz : ψ z₀ = ψ'' z₀'')
    (hu : (α : maxUnram A K) ^ d = algebraMap K (maxUnram A K) u)
    (hu'' : (β : maxUnram A'' K'') ^ d = algebraMap K'' (maxUnram A'' K'') u'')
    (hd : IsUnit (d : A')) {w : A'} (hw : IsUnit w) (hw' : algebraMap A' K' w = ψ'' u'') {v : K'}
    (hv : ψ u = ψ'' u'' * v ^ d) :
    resLE (Spec.map φ) 1 (kappaLH A K Λ (kumD hζ hζΓ hdN hα hg)) =
      resLE (Spec.map φ'') 1 (kappaLH A'' K'' Λ (kumD hζ'' hζΓ'' hdN hβ hg)) := by
  have hz1 : IsPrimitiveRoot z₀ N := by
    have h0 := hζ
    rw [hz] at h0
    exact h0.of_map_of_injective (algebraMap K (maxUnram A K)).injective
  obtain ⟨ζ', hζ'def⟩ : ∃ ζ' : maxUnram A' K', ζ' = algebraMap K' (maxUnram A' K') (ψ z₀) := ⟨_, rfl⟩
  have hζ' : IsPrimitiveRoot ζ' N := by
    rw [hζ'def]
    exact (hz1.map_of_injective ψ.injective).map_of_injective (algebraMap K' (maxUnram A' K')).injective
  have hζΓ' : ∀ σ ∈ (⊤ : Subgroup (Pi1 A' K')), σ ζ' = ζ' := fun σ _ => by
    rw [hζ'def]
    exact AlgEquiv.commutes σ _
  obtain ⟨γ, hγd⟩ := exists_root_of_isUnit (K := K') hd hw
  have hγd' : (γ : maxUnram A' K') ^ d = algebraMap K' (maxUnram A' K') (ψ'' u'') := by rw [hγd, hw']
  have hγ : γ ∈ rad (⊤ : Subgroup (Pi1 A' K')) d := mem_rad_of_pow_eq hγd'
  have hu0 : ψ u ≠ 0 := by
    intro h0
    rw [(map_eq_zero ψ).1 h0, map_zero] at hu
    exact pow_ne_zero d α.ne_zero hu
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne d), mul_zero] at hv
    exact hu0 hv
  obtain ⟨vU, hvU⟩ : ∃ vU : (maxUnram A' K')ˣ, (vU : maxUnram A' K') = algebraMap K' (maxUnram A' K') v :=
    ⟨Units.mk0 _ ((map_ne_zero (algebraMap K' (maxUnram A' K'))).2 hv0), rfl⟩
  have hfix : vU ∈ fixUnits (⊤ : Subgroup (Pi1 A' K')) := (mem_fixUnits _ vU).2 fun σ _ => by
    rw [hvU]
    exact AlgEquiv.commutes σ v
  have hγv : γ * vU ∈ rad (⊤ : Subgroup (Pi1 A' K')) d :=
    (rad (⊤ : Subgroup (Pi1 A' K')) d).mul_mem hγ (fixUnits_le_rad _ d hfix)
  have hpow : ((γ * vU : (maxUnram A' K')ˣ) : maxUnram A' K') ^ d = algebraMap K' (maxUnram A' K') (ψ u) := by
    rw [Units.val_mul, mul_pow, hγd', hvU, ← map_pow, ← map_mul, hv]
  rw [resLE_kumD φ h hζ hζΓ hζ' hζΓ' hdN hα hg ψ hψ hz hζ'def hu hγv hpow,
    resLE_kumD φ'' h'' hζ'' hζΓ'' hζ' hζΓ' hdN hβ hg ψ'' hψ'' hz'' (by rw [hζ'def, hzz]) hu'' hγ hγd',
    kumD_mul_fix hζ' hζΓ' hdN hγ hfix hg]

end KapE

end RamanujanPetersson.EtPBC.EtKum

end

end


