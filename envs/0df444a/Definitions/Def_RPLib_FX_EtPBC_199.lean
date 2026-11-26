-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_199
-- name    : RPLib_FX_EtPBC_199
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:03:28.192644+00:00
-- url     : https://prove2.me/theorems/0808e36e-7399-5ab0-83e8-4fea37c99117
-- title:
--   Proper base change for the projective line, library file 199
-- statement:
--   File 199 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_SecNat`: S4-EtPBC-A, L1c': naturality of `secExt` in the etale object
--   * `S4.Def_RP_EtPBC_A_Inj0f`: S4-EtPBC-A, G1d part 3: **`bcInj_zero`** (base change is injective on germs in degree `0` for universally closed `g`)
--   * `S4.Def_RP_EtPBC_A_Emb`: S4-EtPBC-A, M4(B): closure properties of `BCSurj 0`
--   * `S4.Def_RP_EtPBC_A_NInd`: S4-EtPBC-A, M4(C,D,F): noetherian induction on supports
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_192
import Definitions.Def_RPLib_FX_EtPBC_193

/-!
# Proper base change for the projective line, library file 199

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_SecNat`: S4-EtPBC-A, L1c': naturality of `secExt` in the etale object
* `S4.Def_RP_EtPBC_A_Inj0f`: S4-EtPBC-A, G1d part 3: **`bcInj_zero`** (base change is injective on germs in degree `0` for universally closed `g`)
* `S4.Def_RP_EtPBC_A_Emb`: S4-EtPBC-A, M4(B): closure properties of `BCSurj 0`
* `S4.Def_RP_EtPBC_A_NInd`: S4-EtPBC-A, M4(C,D,F): noetherian induction on supports
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_SecNat =====
section

/-!
# S4-EtPBC-A, L1c': naturality of `secExt` in the etale object

`secExt_π`: `secExt` of the class of a cycle `c` is `cocExt c`. `secExt_nat`: for `w : W' ⟶ W` and a morphism of short
complexes `φ : I^•(W)_(p+1) ⟶ I^•(W')_(p+1)` that restricts along `w` in the middle,
`secExt W' (H(φ) x) = Λ[w]^* (secExt W x)`. `germExt`: the presheaf `V ↦ H^(p+1)(I^•(g⁻¹ V))` at `V` is
`Ext^(p+1)(Λ[g⁻¹ V], F)`, naturally in `V` (`germExt_map`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

section Sec

end Sec

section Germ

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) {F : EtSh Λ P} (I : InjectiveResolution F)

/-- `H^(p+1)(I^•(g⁻¹ V)) ≃+ Ext^(p+1)(Λ[g⁻¹ V], F)` on the presheaf homology. -/
def germExt (p : ℕ) (V : S.Etale) :
    ((preCx Λ g I.cocomplex).homology (p + 1)).obj (op V) ≃+
      Ext.{u} (freeSh Λ ((etPull g).obj V)) F (p + 1) :=
  (preHomologyObjIso Λ g I.cocomplex (p + 1) V).toLinearEquiv.toAddEquiv.trans
    (secExt Λ I ((etPull g).obj V) p)

theorem germExt_apply (p : ℕ) (V : S.Etale) (h : ((preCx Λ g I.cocomplex).homology (p + 1)).obj (op V)) :
    germExt Λ g I p V h = secExt Λ I ((etPull g).obj V) p ((preHomologyObjIso Λ g I.cocomplex (p + 1) V).hom h) :=
  rfl

/-- **Naturality of `germExt`** in `V`. -/
theorem germExt_map (p : ℕ) {V' V : S.Etale} (a : V' ⟶ V)
    (h : ((preCx Λ g I.cocomplex).homology (p + 1)).obj (op V)) :
    germExt Λ g I p V' (((preCx Λ g I.cocomplex).homology (p + 1)).map a.op h) =
      (Ext.mk₀ (freeMap Λ ((etPull g).map a))).comp (germExt Λ g I p V h) (zero_add _) := by
  have key : ((evaluation (S.Etale)ᵒᵖ (ModuleCat.{u} Λ)).map a.op).app (preSc Λ g I p).homology ≫
      ((preSc Λ g I p).mapHomologyIso ((evaluation (S.Etale)ᵒᵖ (ModuleCat.{u} Λ)).obj (op V'))).inv =
      ((preSc Λ g I p).mapHomologyIso ((evaluation (S.Etale)ᵒᵖ (ModuleCat.{u} Λ)).obj (op V))).inv ≫
        ShortComplex.homologyMap ((preSc Λ g I p).mapNatTrans ((evaluation (S.Etale)ᵒᵖ (ModuleCat.{u} Λ)).map a.op)) := by
    rw [NatTrans.app_homology, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hkey : (preHomologyObjIso Λ g I.cocomplex (p + 1) V').hom
      (((preCx Λ g I.cocomplex).homology (p + 1)).map a.op h) =
      ShortComplex.homologyMap ((preSc Λ g I p).mapNatTrans ((evaluation (S.Etale)ᵒᵖ (ModuleCat.{u} Λ)).map a.op))
        ((preHomologyObjIso Λ g I.cocomplex (p + 1) V).hom h) :=
    ConcreteCategory.congr_hom key h
  exact (congrArg (secExt Λ I ((etPull g).obj V') p) hkey).trans (secExt_nat Λ I ((etPull g).map a) p
    ((preSc Λ g I p).mapNatTrans ((evaluation (S.Etale)ᵒᵖ (ModuleCat.{u} Λ)).map a.op)) (fun _ => rfl) _)

end Germ

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0f =====
section

/-!
# S4-EtPBC-A, G1d part 3: **`bcInj_zero`** (base change is injective on germs in degree `0` for universally closed `g`)
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Base change is injective on germs in degree `0`** (universally closed `g`, every sheaf). -/
theorem bcInj_zero [UniversallyClosed g] (G : EtSh Λ P) : BCInj Λ g s 0 G := by
  intro j α h
  exact ⟨goodNbhd Λ g s j G α h, goodHom Λ g s j G α h,
    res0_eq_zero Λ g s (goodHom Λ g s j G α h) G α (eq_zero_of_germs G _ (good_germ_zero Λ g s j G α))⟩

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_Emb =====
section

/-!
# S4-EtPBC-A, M4(B): closure properties of `BCSurj 0`

* `bcSurj_zero_of_hom`, `hom_of_bcSurj_zero`: `BCSurj 0` as a statement about morphisms `Λ_{P_s} ⟶ ι^* H`;
* **`bcSurj_of_mono`**: `BCSurj 0` passes to subobjects (`g` universally closed: `bcInj_zero` on the cokernel);
* **`bcSurj_biprod`**: `BCSurj 0` for `H₁` and `H₂` gives it for `H₁ ⊞ H₂`;
* `EmbC F`: `F` embeds into a sheaf with `BCSurj 0`; **`bcSurj_of_embC`**, **`embC_of_mono`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **`BCSurj 0` passes to subobjects.** -/
theorem bcSurj_of_mono [UniversallyClosed g] {F H : EtSh Λ P} (m : F ⟶ H) [Mono m]
    (hH : BCSurj Λ g s 0 H) : BCSurj Λ g s 0 F :=
  Delta.surjAt_zero_of_ses (bcUnit_comp Λ g s) (Cech.cokSC_shortExact m) hH (bcInj_zero Λ g s _)

theorem bcSurj_of_embC [UniversallyClosed g] {F : EtSh Λ P} (h : EmbC g s F) : BCSurj Λ g s 0 F := by
  obtain ⟨H, m, hm, hH⟩ := h
  exact bcSurj_of_mono g s m hH

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NInd =====
section

/-!
# S4-EtPBC-A, M4(C,D,F): noetherian induction on supports

* `FGT Λ F`: `F` is a quotient of a finite sum `∐ Λ[W j]` with every `(W j).left` affine;
* `fgt_image`, `fgt_quotCut`; `mono_lift_of_stalk` (a stalkwise criterion for `biprod.lift a b` to be mono);
  `bcSurj_of_isZero`;
* `GenStep Λ g s`: the generic step: an `FGT` sheaf `F` with stalks zero off a nonempty closed `Z` maps to a sheaf
  with `BCSurj 0`, injectively on stalks over `V ∩ Z ≠ ∅` for some open `V`;
* **`embC_of_fgt`**: under `GenStep` (and `P` noetherian) every `FGT` sheaf embeds into a sheaf with `BCSurj 0`;
* **`bcSurj_zero_all`**: under `GenStep`, `BCSurj 0` holds for every sheaf (`P_s` compact, `g` universally closed).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **`BCSurj 0` for all sheaves from the generic step.** -/
theorem bcSurj_zero_all [CompactSpace (fib g s)] [UniversallyClosed g] [NoetherianSpace P] (hE : GenStep Λ g s)
    (G : EtSh Λ P) : BCSurj Λ g s 0 G :=
  bcSurj_of_fg_aff g s G fun t W hW φ => bcSurj_of_embC g s (embC_of_fgt g s hE _ (fgt_image t W hW φ))

end RamanujanPetersson.EtPBC

end

end


