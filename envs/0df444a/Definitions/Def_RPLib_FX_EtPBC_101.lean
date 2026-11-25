-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_101
-- name    : RPLib_FX_EtPBC_101
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:00:17.319543+00:00
-- url     : https://prove2.me/theorems/31ef6ce9-d587-5b8b-9c94-4e25ada72fb4
-- title:
--   Proper base change for the projective line, library file 101
-- statement:
--   File 101 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
--   * `S4.Def_RP_EtPBC_A_FinGenA`: S4-EtPBC-A, M4(A): finitely many generating sections over AFFINE etale `P`-schemes
--   * `S4.Def_RP_EtPBC_A_PushKill`: S4-EtPBC-A, R4-T3c: effacement through an etale neighbourhood by a pushout
--   * `S4.Def_RP_EtPBC_A_NInd`: S4-EtPBC-A, M4(C,D,F): noetherian induction on supports
--   * `S4.Def_RP_EtPBC_A_EmbQ`: S4-EtPBC-A, R3 (degree `q` of M4): closure properties of `BCSurj q`, noetherian induction for a predicate
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_032
import Definitions.Def_RPLib_FX_EtPBC_089

/-!
# Proper base change for the projective line, library file 101

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
* `S4.Def_RP_EtPBC_A_FinGenA`: S4-EtPBC-A, M4(A): finitely many generating sections over AFFINE etale `P`-schemes
* `S4.Def_RP_EtPBC_A_PushKill`: S4-EtPBC-A, R4-T3c: effacement through an etale neighbourhood by a pushout
* `S4.Def_RP_EtPBC_A_NInd`: S4-EtPBC-A, M4(C,D,F): noetherian induction on supports
* `S4.Def_RP_EtPBC_A_EmbQ`: S4-EtPBC-A, R3 (degree `q` of M4): closure properties of `BCSurj q`, noetherian induction for a predicate
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_CovAs6b =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover

Over `R'` (via `σ : C →ₐ[A] R'`) the charts are `Pres (gmap (tsC σ Bᵢ) gCᵢ)` and the overlap is
`Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀))`.
* `psi0`: `presMap (bcS R' φ₀)` followed by `presCongr`; `psi0_alg`, `psi0_tmul`, `psi0_X`, `psi0_away`.
* `isoN`, `psi1`: `presMap (bcS R' φ₁)`, `presCongr`, then `presIso` of the pushed substitution data;
  `psi1_alg`, `psi1_tmul`, `psi1_X`, `psi1_away`.
* `ctheta0`, `ctheta1`: compatibility of residue maps with `psi0`/`psi1` from values on constants and variables.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section Psi

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S] {R' : Type u} [CommRing R']
  [Algebra A R'] {B₀ B₁ N : Type u} [CommRing B₀] [Algebra A B₀] [CommRing B₁] [Algebra A B₁] [CommRing N]
  [Algebra A N] (φ₀ : B₀ →ₐ[A] N) (φ₁ : B₁ →ₐ[A] N) {C : Subalgebra A S} (σ : C →ₐ[A] R') {r₀ r₁ : ℕ}
  (gC₀ : Fin r₀ → MvPolynomial (Fin r₀) (C ⊗[A] B₀)) (gC₁ : Fin r₁ → MvPolynomial (Fin r₁) (C ⊗[A] B₁))

variable (uC : Fin r₀ → MvPolynomial (Fin r₁) (C ⊗[A] N)) (vC : Fin r₁ → MvPolynomial (Fin r₀) (C ⊗[A] N))
  (H : (∀ j, MvPolynomial.bind₁ uC (gmap (bcC φ₀ C) gC₀ j) ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
    (∀ i, MvPolynomial.bind₁ vC (gmap (bcC φ₁ C) gC₁ i) ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀))) ∧
    (∀ i, MvPolynomial.bind₁ uC (vC i) - MvPolynomial.X i ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
    (∀ j, MvPolynomial.bind₁ vC (uC j) - MvPolynomial.X j ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀))))

theorem psi1_tmul (r : R') (b : B₁) :
    psi1 φ₀ φ₁ σ gC₀ gC₁ uC vC H (algebraMap (R' ⊗[A] B₁) (Pres (gmap (tsC σ B₁) gC₁)) (r ⊗ₜ b)) =
      algebraMap (R' ⊗[A] N) (Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀))) (r ⊗ₜ φ₁ b) :=
  psi1_alg φ₀ φ₁ σ gC₀ gC₁ uC vC H (r ⊗ₜ b)

end Psi

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_FinGenA =====
section

/-!
# S4-EtPBC-A, M4(A): finitely many generating sections over AFFINE etale `P`-schemes

* **`exists_affine_le`**: every etale neighbourhood of a geometric point is refined by one with affine total space;
* `exists_repG_aff`, `exists_pullRepG_aff`, `exists_fg_aff`: the representations of `FinGen` over affines;
* **`bcSurj_of_fg_aff`**: `BCSurj 0` for `G` from `BCSurj 0` for the subsheaves `ker (coker φ)` generated by finitely
  many sections `φ : ∐ Λ[W x] ⟶ G` with every `(W x).left` affine.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Gen

end Gen

section Red

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Reduction to subsheaves generated by finitely many sections over affines** (`P_s` compact). -/
theorem bcSurj_of_fg_aff [CompactSpace (fib g s)] (G : EtSh Λ P)
    (h : ∀ (t : Finset (fib g s)) (W : fib g s → P.Etale), (∀ x, IsAffine (W x).left) → ∀ (φ : (∐ fun x : t => freeSh Λ (W x.1)) ⟶ G),
      BCSurj Λ g s 0 (kernel (cokernel.π φ))) :
    BCSurj Λ g s 0 G := by
  intro β
  obtain ⟨t, W, z, hW, hz⟩ := exists_fg_aff (fibι g s) G (Ext.addEquiv₀ β)
  let φ : (∐ fun x : t => freeSh Λ (W x.1)) ⟶ G := Sigma.desc fun x => (freeEquiv Λ (W x.1) G).symm (z x.1)
  have hp : Ext.addEquiv₀ β ≫ (pull (fibι g s) Λ).map (cokernel.π φ) = 0 := hz (cokernel.π φ) fun x hx => by
    have e0 : (freeEquiv Λ (W x) G).symm (z x) ≫ cokernel.π φ = 0 :=
      (congrArg (· ≫ cokernel.π φ)
        (Sigma.ι_desc (fun x : t => (freeEquiv Λ (W x.1) G).symm (z x.1)) ⟨x, hx⟩).symm).trans
        ((Category.assoc _ _ _).trans ((congrArg (Sigma.ι (fun x : t => freeSh Λ (W x.1)) ⟨x, hx⟩ ≫ ·) (cokernel.condition φ)).trans comp_zero))
    have e := freeEquiv_comp Λ (W x) ((freeEquiv Λ (W x) G).symm (z x)) (cokernel.π φ)
    rw [e0, map_zero, AddEquiv.apply_symm_apply] at e
    exact e.symm
  let b' : unitSh Λ (fib g s) ⟶ (pull (fibι g s) Λ).obj (kernel (cokernel.π φ)) :=
    kernel.lift _ (Ext.addEquiv₀ β) hp ≫ (PreservesKernel.iso (pull (fibι g s) Λ) (cokernel.π φ)).inv
  have hb' : b' ≫ (pull (fibι g s) Λ).map (kernel.ι (cokernel.π φ)) = Ext.addEquiv₀ β := by
    simp only [b', Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]
  obtain ⟨j, α', hα'⟩ := h t W hW φ (Ext.mk₀ b')
  refine ⟨j, α'.comp (Ext.mk₀ (kernel.ι (cokernel.π φ))) (add_zero 0), ?_⟩
  exact (Delta.bc_comp_mk₀ (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j
    (kernel.ι (cokernel.π φ)) 0 α').trans
    ((congrArg (fun γ => γ.comp (Ext.mk₀ ((pull (fibι g s) Λ).map (kernel.ι (cokernel.π φ)))) (add_zero 0)) hα').trans
      ((Ext.mk₀_comp_mk₀ _ _).trans ((congrArg Ext.mk₀ hb').trans (Ext.mk₀_addEquiv₀_apply β))))

end Red

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_PushKill =====
section

/-!
# S4-EtPBC-A, R4-T3c: effacement through an etale neighbourhood by a pushout

Abstract part: an adjunction `Rl ⊣ R` (`Rl = f_!`, `R = f^*`) with `Rl` preserving monomorphisms, functors
`L : C ⥤ D` (`ι^*`), `L'' : C' ⥤ D` (`ι'^*`) and `κ : R ⋙ L'' ≅ L`. For a mono `m : R G ⟶ H` the pushout
`E = Rl H ⊔_{Rl R G} G` (along the counit) receives a mono `pushI : G ⟶ E`, and `L(pushI)` factors through
`L''(m)` (`pushI_fac`, from the triangle identity). Hence a class killed by `L''(m)` is killed by `L(pushI)`
(`kill_pushI`).

Geometric part (**`exists_bc_of_push_kill`**): for `g : P ⟶ S`, an etale `f : P' ⟶ P` with a lift `ι'` of the
fibre inclusion and a mono `m : f^* G ⟶ H` on `P'`, every `β ∈ H^1(P_s, ι^* G)` killed by `ι'^*(m)` is the base
change of a germ, provided base change is surjective in degree `0` for every sheaf on `P` (G1). No change of
the base `S` is needed: the effacement `G ⟶ E` lives on `P` (`f_!` preserves monos, `LshEt`).
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.PushKill

universe w v₁ u₁ v₂ u₂ v₃ u₃

section Abstract

end Abstract

section Geo

open AlgebraicGeometry RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Effacement through an etale `P' ⟶ P`**: a degree-one fibre class killed by a mono on `P'` comes from a
germ, given base change surjectivity in degree `0` for every sheaf on `P`. -/
theorem exists_bc_of_push_kill (hQ : ∀ Q : EtSh Λ P, BCSurj Λ g s 0 Q) {P' : Scheme.{u}} (f : P' ⟶ P)
    [Etale f] (ι' : fib g s ⟶ P') (hι : ι' ≫ f = fibι g s) {G : EtSh Λ P} {H : EtSh Λ P'}
    (m : (pull f Λ).obj G ⟶ H) [Mono m]
    (β : Ext.{u} (unitSh Λ (fib g s)) ((pull (fibι g s) Λ).obj G) 1)
    (hβ : (β.comp (Ext.mk₀ ((liftIso g s f ι' hι).inv.app G)) (add_zero 1)).comp
      (Ext.mk₀ ((pull ι' Λ).map m)) (add_zero 1) = 0) :
    ∃ (j : Nbhd s) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 1),
      Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j G 1 α = β := by
  exact Delta.exists_bc_of_kill (Cech.cokSC_shortExact (pushI (lshPullAdj f Λ) m)) (q := 0) (hQ _) β
    (kill_pushI (lshPullAdj f Λ) (liftIso g s f ι' hι) m β hβ)

end Geo

end RamanujanPetersson.EtPBC.PushKill

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

variable (Λ) in
/-- **The generic step** (to be proved at the generic point of a component of `Z`). -/
def GenStep : Prop :=
  ∀ (Z : Set P), IsClosed Z → Z.Nonempty → ∀ F : EtSh Λ P, FGT Λ F → (∀ x ∉ Z, IsZero (stalk Λ F x)) →
    ∃ (V : P.Opens) (H : EtSh Λ P) (φ : F ⟶ H), BCSurj Λ g s 0 H ∧ ((V : Set P) ∩ Z).Nonempty ∧
      ∀ x ∈ (V : Set P) ∩ Z, Mono (((geomPtAt x).stalkF Λ).map φ)

end RamanujanPetersson.EtPBC

end

end

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

theorem genStep_eq (g : P ⟶ S) (s : GeomPt S) : GenStep Λ g s = GenStepP Λ (BCSurj Λ g s 0) := rfl

end RamanujanPetersson.EtPBC

end

end


