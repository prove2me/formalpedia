-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_102
-- name    : RPLib_FX_EtPBC_102
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:00:34.322357+00:00
-- url     : https://prove2.me/theorems/1272afc7-fc8b-53f5-bb5f-0a55346986f4
-- title:
--   Proper base change for the projective line, library file 102
-- statement:
--   File 102 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_EmbQ`: S4-EtPBC-A, R3 (degree `q` of M4): closure properties of `BCSurj q`, noetherian induction for a predicate
--   * `S4.Def_RP_EtPBC_A_H1FG`: S4-EtPBC-A, R2(c-e): degree-1 base change reduces to finitely generated subsheaves
--   * `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_082
import Definitions.Def_RPLib_FX_EtPBC_089

/-!
# Proper base change for the projective line, library file 102

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_EmbQ`: S4-EtPBC-A, R3 (degree `q` of M4): closure properties of `BCSurj q`, noetherian induction for a predicate
* `S4.Def_RP_EtPBC_A_H1FG`: S4-EtPBC-A, R2(c-e): degree-1 base change reduces to finitely generated subsheaves
* `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_EmbQ =====
section

/-!
# S4-EtPBC-A, R3 (degree `q` of M4): closure properties of `BCSurj q`, noetherian induction for a predicate

* `Delta.surjAt_of_isZero`, **`Delta.surjAt_biprod`** (abstract): surjectivity on germs in degree `q` holds for zero
  objects and passes to binary biproducts;
* **`bcSurj_succ_of_mono`**: `BCSurj (q+1)` passes from `H` to a subobject `F ↪ H` given `BCInj (q+1)` and
  `BCSurj q` for the cokernel (the epi four-lemma `Delta.surjAt_succ_of_ses`);
* `GenStepP Λ C`, `EmbP C`: the generic step and embeddability for an arbitrary predicate `C` on sheaves;
  **`embP_of_fgt`**: if `C` holds for zero sheaves and is closed under `⊞`, the generic step for `C` embeds every
  `FGT` sheaf into a sheaf satisfying `C` (`GenStep Λ g s = GenStepP Λ (BCSurj Λ g s 0)`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}}

/-- **`BCSurj (q+1)` passes to subobjects** (given `BCInj (q+1)` and `BCSurj q` for the cokernel). -/
theorem bcSurj_succ_of_mono (g : P ⟶ S) (s : GeomPt S) {F H : EtSh Λ P} (m : F ⟶ H) [Mono m] (q : ℕ)
    (hH : BCSurj Λ g s (q + 1) H) (hI : BCInj Λ g s (q + 1) (cokernel m))
    (hS : BCSurj Λ g s q (cokernel m)) : BCSurj Λ g s (q + 1) F :=
  Delta.surjAt_succ_of_ses (bcUnit_comp Λ g s) (Cech.cokSC_shortExact m) q hH hI hS

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_H1FG =====
section

/-!
# S4-EtPBC-A, R2(c-e): degree-1 base change reduces to finitely generated subsheaves

* `ofSec_sc`: `ofSec (c(1)) = c` for `c : Λ_Y ⟶ F`;
* `presHom c`: the map of injective presentations `injPres A ⟶ injPres B` over `c : A ⟶ B`;
* **`exists_kill`**: for `X` compact with affine maps from affines, every `β ∈ Ext¹(Λ_X, ι^* G)` is killed by
  `ι^* (coker φ)` for some `φ : ∐ Λ[W x] ⟶ G` from finitely many affines (local lift of the class on one affine
  etale surjection `V ⟶ X`, its Cech coboundary on `V ×_X V`, `exists_fg_sec`, gluing in the presentation of
  `ι^* (coker φ)`);
* **`bcSurj_one_of_fgt`**: `BCSurj 1` for every sheaf on `P` from `BCSurj 1` for `FGT` sheaves.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp RamanujanPetersson.EtCompact.PtSec

universe u

section Kill

end Kill

section Red

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Degree-1 base change for every sheaf from finitely generated (`FGT`) sheaves.** -/
theorem bcSurj_one_of_fgt [CompactSpace (fib g s)]
    (hA : ∀ {Z : Scheme.{u}} (h : Z ⟶ fib g s), IsAffine Z → IsAffineHom h)
    (hF : ∀ F : EtSh Λ P, FGT Λ F → BCSurj Λ g s 1 F) (G : EtSh Λ P) : BCSurj Λ g s 1 G := by
  intro β
  obtain ⟨t, ht, W, hW, φ, hφ⟩ := exists_kill (fibι g s) hA G β
  let SK := ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ) (kernel.condition _)
  have hSK : SK.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
      mono_f := mono_kerι _
      epi_g := epi_cokπ φ }
  have hSK' := hSK.map_of_exact (pull (fibι g s) Λ)
  obtain ⟨β', hβ'⟩ := Ext.covariant_sequence_exact₂ (X := unitSh Λ (fib g s)) (hS := hSK') β hφ
  have hFK : FGT Λ (kernel (cokernel.π φ)) := ⟨t, ht, W, hW, Abelian.factorThruImage φ, epi_fti φ⟩
  obtain ⟨j, α', hα'⟩ := hF _ hFK β'
  refine ⟨j, α'.comp (Ext.mk₀ (kernel.ι (cokernel.π φ))) (add_zero 1), ?_⟩
  exact (Delta.bc_comp_mk₀ (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j
    (kernel.ι (cokernel.π φ)) 1 α').trans
    ((congrArg (fun γ => γ.comp (Ext.mk₀ ((pull (fibι g s) Λ).map (kernel.ι (cokernel.π φ)))) (add_zero 1))
      hα').trans hβ')

end Red

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2S1 =====
section

/-!
# S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes

* `opEt_ext` (maps into `opEt U` are unique), `toOpEt`, `opEtMap`, `freeMap_id`;
* `mvC_shortExact'`: the MV criterion with "surjective onto the fibre of `Z`" instead of "nonempty";
* `locC`, **`locC_shortExact`**: the one-point MV complex `Λ[D ×_P Uo] ⟶ Λ[D] ⊞ Λ[P ∖ z] ⟶ Λ[P]` for an etale `D`
  with one geometric point over `z` and all other points over `Uo` (`Uo ⊆ P ∖ z`);
* `IsLoc Λ F z β` (one-point MV class `ε_loc ∘ κ`), `locSpan Λ F` (the subgroup they generate);
* `exists_good_one`, **`split_step`** (a class dying on `U` differs from a one-point class at `z ∉ U` by a class
  dying on `U ∪ {z}`), **`mem_locSpan_of_dies`** (induction on `#(P ∖ U)`), **`mem_locSpan_P1`**:
  `H²(P¹, F) = locSpan` (with `claimD`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtPBC.GenGeo

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

/-- **Induction on `#(P ∖ U)`**: a class dying on a cofinite `U` (closed, Galois-trivial complement) lies in
`locSpan`. -/
theorem mem_locSpan_of_dies (F : EtSh Λ P) (n : ℕ) : ∀ (U : P.Opens) (β : Ext.{u} (freeSh Λ (etId P)) F 2),
    ((U : Set P)ᶜ).ncard = n → ((U : Set P)ᶜ).Finite → (∀ x ∈ (U : Set P)ᶜ, IsClosed ({x} : Set P)) →
    (∀ x ∈ (U : Set P)ᶜ, Subsingleton (Gal x)) →
    (Ext.mk₀ (freeMap Λ (toTop (opEt U)))).comp β (zero_add 2) = 0 → β ∈ locSpan Λ F := by
  induction n with
  | zero =>
    intro U β hn hf _ _ hβ
    have hU : ∀ x : P, x ∈ U := by
      intro x
      by_contra hx
      exact ((Set.ncard_pos hf).2 ⟨x, hx⟩).ne' hn
    have hmono : Mono (freeMap Λ (toTop (opEt U))) := by
      rw [mono_iff_stalk]
      intro x
      rw [ModuleCat.mono_iff_injective]
      exact stalk_freeMap_injective _ x (fun a b _ => Subsingleton.elim a b)
    have hepi : Epi (freeMap Λ (toTop (opEt U))) := by
      rw [epi_iff_stalk]
      intro x
      rw [ModuleCat.epi_iff_surjective]
      obtain ⟨t⟩ := nonempty_fib_opEt U x (hU x)
      exact stalk_freeMap_surjective _ x (fun _ => ⟨t, Subsingleton.elim _ _⟩)
    have := isIso_of_mono_of_epi (freeMap Λ (toTop (opEt U)))
    have h0 := congrArg (fun t => (Ext.mk₀ (inv (freeMap Λ (toTop (opEt U))))).comp t (zero_add 2)) hβ
    simp only [Ext.mk₀_comp_mk₀_assoc, IsIso.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_zero] at h0
    rw [h0]
    exact zero_mem _
  | succ n ih =>
    intro U β hn hf hc hG hβ
    obtain ⟨z, hz⟩ : ((U : Set P)ᶜ).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    have hf' : ((U : Set P)ᶜ \ {z}).Finite := hf.sdiff
    have hc' : ∀ x ∈ (U : Set P)ᶜ \ {z}, IsClosed ({x} : Set P) := fun x hx => hc x hx.1
    have hUpc : IsClosed ((U : Set P)ᶜ \ {z}) := by
      have h := hf'.isClosed_biUnion hc'
      rwa [Set.biUnion_of_singleton] at h
    let Up : P.Opens := ⟨((U : Set P)ᶜ \ {z})ᶜ, hUpc.isOpen_compl⟩
    have hUpS : (Up : Set P)ᶜ = (U : Set P)ᶜ \ {z} := compl_compl _
    have hUp : ∀ x : P, x ∈ Up ↔ x ∈ U ∨ x = z := fun x => by
      show x ∈ ((U : Set P)ᶜ \ {z})ᶜ ↔ x ∈ U ∨ x = z
      rw [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_compl_iff, Set.mem_singleton_iff, SetLike.mem_coe]
      tauto
    let Uz : P.Opens := ⟨{z}ᶜ, (hc z hz).isOpen_compl⟩
    have hUz : ∀ x : P, x ∈ Uz ↔ x ≠ z := fun x => Iff.rfl
    obtain ⟨γ, hγ, hγ0⟩ := split_step F β U Up Uz z hz hUp hUz hf hc (hG z hz) hβ
    have hn' : ((Up : Set P)ᶜ).ncard = n := by
      rw [hUpS, Set.ncard_sdiff_singleton_of_mem hz, hn]
      rfl
    have hmem := ih Up (β - γ) hn' (hUpS ▸ hf') (fun x hx => hc' x (hUpS ▸ hx))
      (fun x hx => hG x (hUpS ▸ hx).1) hγ0
    have h2 : γ ∈ locSpan Λ F := AddSubgroup.subset_closure ⟨z, hγ⟩
    have h3 := add_mem hmem h2
    rwa [sub_add_cancel] at h3

end Gen

section P1

end P1

end RamanujanPetersson.EtPBC.EtMV

end

end


