-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_064
-- name    : RPLib_FX_EtPBC_064
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:39:15.00393+00:00
-- url     : https://prove2.me/theorems/00ff90a3-0976-5985-aa57-39bde83c1717
-- title:
--   Proper base change for the projective line, library file 064
-- statement:
--   File 064 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovAs5d`: S4-EtPBC-A, R4-T2 (A3 assembly, As5d): substitution data descend to a f.g. subalgebra
--   * `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
--   * `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_DescG4`: S4-EtPBC-A, R4-T1d (part 1): the sheets `V ⟶ U₀`
--   * `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
--   * `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_029
import Definitions.Def_RPLib_FX_EtPBC_053
import Definitions.Def_RPLib_FX_EtPBC_054

/-!
# Proper base change for the projective line, library file 064

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovAs5d`: S4-EtPBC-A, R4-T2 (A3 assembly, As5d): substitution data descend to a f.g. subalgebra
* `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
* `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
* `S4.Def_RP_EtPBC_A_DescG4`: S4-EtPBC-A, R4-T1d (part 1): the sheets `V ⟶ U₀`
* `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
* `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_CovAs5d =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As5d): substitution data descend to a f.g. subalgebra

* `subst_map`: the four substitution memberships (`hu hv huv hvu` of `presIso`) push along any ring map.
* `mem_push`, `gmap_tiC_bcC`, `gmap_tvC_bcC`: bookkeeping for `tiC`, `tvC`, `bcC`.
* **`desc_subst`**: substitution data `uC vC` between square systems `G₀ G₁` over `C₀ ⊗ B` whose memberships hold
  over `S ⊗ B` (after `tvC`) already satisfy them over `C ⊗ B` for a f.g. `C ≥ C₀` (two `desc_mem` calls, joined
  at `C₁ ⊔ C₂`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section SubstMap

end SubstMap

section Desc

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B : Type u} [CommRing B] [Algebra A B]

set_option maxHeartbeats 400000 in
/-- **Substitution data descend to a f.g. subalgebra.** -/
theorem desc_subst [Module.Flat A S] {r₀ r₁ : ℕ} (C₀ : Subalgebra A S) (hC₀ : C₀.FG)
    (G₀ : Fin r₀ → MvPolynomial (Fin r₀) (C₀ ⊗[A] B)) (G₁ : Fin r₁ → MvPolynomial (Fin r₁) (C₀ ⊗[A] B))
    (uC : Fin r₀ → MvPolynomial (Fin r₁) (C₀ ⊗[A] B)) (vC : Fin r₁ → MvPolynomial (Fin r₀) (C₀ ⊗[A] B))
    (hu : ∀ j, MvPolynomial.bind₁ (fun k => MvPolynomial.map (tvC B C₀) (uC k)) (gmap (tvC B C₀) G₀ j) ∈
      Ideal.span (Set.range (gmap (tvC B C₀) G₁)))
    (hv : ∀ i, MvPolynomial.bind₁ (fun k => MvPolynomial.map (tvC B C₀) (vC k)) (gmap (tvC B C₀) G₁ i) ∈
      Ideal.span (Set.range (gmap (tvC B C₀) G₀)))
    (huv : ∀ i, MvPolynomial.bind₁ (fun k => MvPolynomial.map (tvC B C₀) (uC k))
      (MvPolynomial.map (tvC B C₀) (vC i)) - MvPolynomial.X i ∈ Ideal.span (Set.range (gmap (tvC B C₀) G₁)))
    (hvu : ∀ j, MvPolynomial.bind₁ (fun k => MvPolynomial.map (tvC B C₀) (vC k))
      (MvPolynomial.map (tvC B C₀) (uC j)) - MvPolynomial.X j ∈ Ideal.span (Set.range (gmap (tvC B C₀) G₀))) :
    ∃ (C : Subalgebra A S) (h : C₀ ≤ C), C.FG ∧
      (∀ j, MvPolynomial.bind₁ (fun k => MvPolynomial.map (tiC B h) (uC k)) (gmap (tiC B h) G₀ j) ∈
        Ideal.span (Set.range (gmap (tiC B h) G₁))) ∧
      (∀ i, MvPolynomial.bind₁ (fun k => MvPolynomial.map (tiC B h) (vC k)) (gmap (tiC B h) G₁ i) ∈
        Ideal.span (Set.range (gmap (tiC B h) G₀))) ∧
      (∀ i, MvPolynomial.bind₁ (fun k => MvPolynomial.map (tiC B h) (uC k))
        (MvPolynomial.map (tiC B h) (vC i)) - MvPolynomial.X i ∈ Ideal.span (Set.range (gmap (tiC B h) G₁))) ∧
      (∀ j, MvPolynomial.bind₁ (fun k => MvPolynomial.map (tiC B h) (vC k))
        (MvPolynomial.map (tiC B h) (uC j)) - MvPolynomial.X j ∈ Ideal.span (Set.range (gmap (tiC B h) G₀))) := by
  classical
  obtain ⟨C₁, h₁, hC₁, hz₁⟩ := desc_mem (B := B) C₀ hC₀ G₁
    (Sum.elim (fun j : Fin r₀ => MvPolynomial.bind₁ uC (G₀ j))
      (fun i : Fin r₁ => MvPolynomial.bind₁ uC (vC i) - MvPolynomial.X i))
    (by
      rintro (j | i)
      · show MvPolynomial.map (tvC B C₀) (MvPolynomial.bind₁ uC (G₀ j)) ∈
          Ideal.span (Set.range (gmap (tvC B C₀) G₁))
        rw [MvPolynomial.map_bind₁]
        exact hu j
      · show MvPolynomial.map (tvC B C₀) (MvPolynomial.bind₁ uC (vC i) - MvPolynomial.X i) ∈
          Ideal.span (Set.range (gmap (tvC B C₀) G₁))
        rw [map_sub, MvPolynomial.map_bind₁, MvPolynomial.map_X]
        exact huv i)
  obtain ⟨C₂, h₂, hC₂, hz₂⟩ := desc_mem (B := B) C₀ hC₀ G₀
    (Sum.elim (fun i : Fin r₁ => MvPolynomial.bind₁ vC (G₁ i))
      (fun j : Fin r₀ => MvPolynomial.bind₁ vC (uC j) - MvPolynomial.X j))
    (by
      rintro (i | j)
      · show MvPolynomial.map (tvC B C₀) (MvPolynomial.bind₁ vC (G₁ i)) ∈
          Ideal.span (Set.range (gmap (tvC B C₀) G₀))
        rw [MvPolynomial.map_bind₁]
        exact hv i
      · show MvPolynomial.map (tvC B C₀) (MvPolynomial.bind₁ vC (uC j) - MvPolynomial.X j) ∈
          Ideal.span (Set.range (gmap (tvC B C₀) G₀))
        rw [map_sub, MvPolynomial.map_bind₁, MvPolynomial.map_X]
        exact hvu j)
  have k₁ : C₁ ≤ C₁ ⊔ C₂ := le_sup_left
  have k₂ : C₂ ≤ C₁ ⊔ C₂ := le_sup_right
  refine ⟨C₁ ⊔ C₂, h₁.trans k₁, hC₁.sup hC₂, fun j => ?_, fun i => ?_, fun i => ?_, fun j => ?_⟩
  · have e : MvPolynomial.map (tiC B (h₁.trans k₁)) (MvPolynomial.bind₁ uC (G₀ j)) ∈
        Ideal.span (Set.range (gmap (tiC B (h₁.trans k₁)) G₁)) := mem_push h₁ k₁ G₁ (hz₁ (Sum.inl j))
    rw [MvPolynomial.map_bind₁] at e
    exact e
  · have e : MvPolynomial.map (tiC B (h₁.trans k₁)) (MvPolynomial.bind₁ vC (G₁ i)) ∈
        Ideal.span (Set.range (gmap (tiC B (h₁.trans k₁)) G₀)) := mem_push h₂ k₂ G₀ (hz₂ (Sum.inl i))
    rw [MvPolynomial.map_bind₁] at e
    exact e
  · have e : MvPolynomial.map (tiC B (h₁.trans k₁)) (MvPolynomial.bind₁ uC (vC i) - MvPolynomial.X i) ∈
        Ideal.span (Set.range (gmap (tiC B (h₁.trans k₁)) G₁)) := mem_push h₁ k₁ G₁ (hz₁ (Sum.inr i))
    rw [map_sub, MvPolynomial.map_bind₁, MvPolynomial.map_X] at e
    exact e
  · have e : MvPolynomial.map (tiC B (h₁.trans k₁)) (MvPolynomial.bind₁ vC (uC j) - MvPolynomial.X j) ∈
        Ideal.span (Set.range (gmap (tiC B (h₁.trans k₁)) G₀)) := mem_push h₂ k₂ G₀ (hz₂ (Sum.inr j))
    rw [map_sub, MvPolynomial.map_bind₁, MvPolynomial.map_X] at e
    exact e

end Desc

section BCg

end BCg

end RamanujanPetersson.EtPBC.Cov

end

end

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

theorem psi1_alg (x : R' ⊗[A] B₁) :
    psi1 φ₀ φ₁ σ gC₀ gC₁ uC vC H (algebraMap (R' ⊗[A] B₁) (Pres (gmap (tsC σ B₁) gC₁)) x) =
      algebraMap (R' ⊗[A] N) (Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀))) (bcS R' φ₁ x) := by
  unfold psi1
  rw [RingHom.comp_apply, presMap_algebraMap]
  exact (isoN φ₀ φ₁ σ gC₀ gC₁ uC vC H).commutes (bcS R' φ₁ x)

end Psi

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Alg =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`

`A = Γ(V)`, `B₀ = Γ(Y, Y₀)`, `B₁ = Γ(Y, Y₁)`, `N = Γ(Y, Y₀ ⊓ Y₁)`:
* `A[X]`-structures `algX0` (via `t`), `algX1` (via `s`), `algXN` (via `t`); `A`-structures `algA0`, `algA1`, `algAN`
  (structure maps of `Y ⟶ V`); towers `tow0`, `tow1`, `towN`; `res_struct`.
* `φY0 : B₀ →ₐ[A[X]] N`, `φY1 : B₁ →ₐ[A] N` (restrictions); `hts_Y`, `hs0_Y`, `hs1_Y`, `hz0_Y`, `hz1_Y`.
* **`exists_etale_idem_Y`**: chart elements idempotent mod `p` and agreeing mod `p` on the overlap come from an
  idempotent of `R' ⊗_A secAlg φY0 φY1` after an etale `R'` with a prime over `p` with the same residue field.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace HomogeneousLocalization
open RamanujanPetersson.EtCompact
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN

attribute [local instance] tow0 tow1 towN

theorem hts_Y : algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) Polynomial.X *
    φY1 K gV π (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X) = 1 := by
  rw [algXN_X, algX1_X]
  exact trans_Y K gV π

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_CovGl2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`

Chart algebras `E₀`, `E₁`, `E₀₁` over `R' ⊗ Γ(Y₀)`, `R' ⊗ Γ(Y₁)`, `R' ⊗ Γ(Y₀₁)`, glued by localizations `ψ₀`, `ψ₁` (the
data of `CoverLift`), give a relative gluing datum **`glD`** over the chart cover `covV`; its glued scheme maps to
`Y_{V'}` by **`toBase`**, which is finite and etale when `E₀`, `E₁` are.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

theorem unit1 : IsUnit (φY1 K gV π (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X)) :=
  IsUnit.of_mul_eq_one_right _ (hts_Y K gV π)

section FinEt

end FinEt

section Et

end Et

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG4 =====
section

/-!
# S4-EtPBC-A, R4-T1d (part 1): the sheets `V ⟶ U₀`

For `ν : M`, the evaluations `evR U ν : B(U) → CU V U`, `f ↦ f ν`, glue (along the affine opens of `X`, as in
Mathlib's `Scheme.Hom.toNormalization`) to the **sheet** `sheet ν : V ⟶ U₀` over `X`:
`ι_sheet` (its restriction to `V.hom⁻¹ U`), `sheet_toU0`, and `sheetE ν : V ⟶ U0E` in `X.Etale`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Sheet

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] [Surjective V.hom] {Λ : Type u} [CommRing Λ]
  {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M] {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem sheet_toU0 (ν : M) : sheet V a b hab hS e he ν ≫ toU0 V a b hab hS e he = V.hom := by
  refine Scheme.Cover.hom_ext (V.left.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top X) V.hom.base.1)) _ _ fun U ↦ ?_
  refine (ι_sheet_assoc V a b hab hS e he ν U _).trans ?_
  simp only [Category.assoc]
  rw [toU0, cover_toBase, ← Spec.map_comp_assoc, alphaU_evR]
  simp
  rfl

end Sheet

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG5 =====
section

/-!
# S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`

* `sheet_cover`: the sheets `sheetE ν : V ⟶ U0E` cover `U0E` (every prime of `B(U)` comes from a sheet).
* `cU_kL`, `cval_dif_sheet`, `dif_sheet`: if `gi ≫ sheetE i = gj ≫ sheetE j` then `dif gi gj = j - i`
  (pointwise: the pair `(gi, gj)` lands in `Spec (C ⊗ C)` over an affine `U`, and `key_sheet`).
* `exists_sigma`: the sections `e + a(ν)` on the sheets glue to `σ ∈ E(U₀)`; `b_sigma`: `b σ` is the pull-back of `q`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Gen

end Gen

section Pt

end Pt

section Cover

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] [Surjective V.hom] {Λ : Type u} [CommRing Λ]
  {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M] {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

@[reassoc]
theorem tauU_sheet (ν : M) (U : X.AffineZariskiSite) :
    tauU V U ≫ sheet V a b hab hS e he ν = Spec.map (CommRingCat.ofHom (evR V a b hab hS e he U ν)) ≫
      (glD (coequifibered_alphaU V a b hab hS e he)).cover.f U :=
  (Category.assoc (U.2.preimage V.hom).isoSpec.inv (V.hom ⁻¹ᵁ U.1).ι (sheet V a b hab hS e he ν)).trans <|
    (whisker_eq _ (ι_sheet V a b hab hS e he ν U)).trans <| (Category.assoc _ _ _).symm.trans <|
      (eq_whisker (IsAffineOpen.isoSpec_inv_toSpecΓ _) _).trans (Category.id_comp _)

/-- The key computation at a point of a pair of maps over `U` identified by the sheets `i` and `j`. -/
theorem cU_kL (i j : M) (U : X.AffineZariskiSite) {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ V.left)
    (h : g₁ ≫ vh V = g₂ ≫ vh V) (hg₁ : ∀ z, vh V (g₁ z) ∈ U.1) (hg₂ : ∀ z, vh V (g₂ z) ∈ U.1)
    (hsh : g₁ ≫ sheet V a b hab hS e he i = g₂ ≫ sheet V a b hab hS e he j) (z : Z) :
    cU U.2.fromSpec (tauU V U) (htauU V U) a b hab hS e he (kL V U g₁ g₂ h hg₁ hg₂ z) = j - i := by
  obtain ⟨φK, hφK⟩ : ∃ φK : CommRingCat.of (CU V U ⊗[Γ(X, U.1)] CU V U) ⟶ Γ(Z, ⊤),
      Z.toSpecΓ ≫ Spec.map φK = kL V U g₁ g₂ h hg₁ hg₂ := ⟨_, toSpecΓ_factor _⟩
  have hsh' : kL V U g₁ g₂ h hg₁ hg₂ ≫ Spec.map (CommRingCat.ofHom (j1 Γ(X, U.1) (CU V U)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (evR V a b hab hS e he U i)) =
      kL V U g₁ g₂ h hg₁ hg₂ ≫ Spec.map (CommRingCat.ofHom (j2 Γ(X, U.1) (CU V U)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (evR V a b hab hS e he U j)) := by
    have : IsOpenImmersion ((glD (coequifibered_alphaU V a b hab hS e he)).cover.f U) :=
      (glD (coequifibered_alphaU V a b hab hS e he)).cover.map_prop U
    refine (cancel_mono ((glD (coequifibered_alphaU V a b hab hS e he)).cover.f U)).1 ?_
    exact (comp_aux (tauU_sheet V a b hab hS e he i U)
        ((eq_whisker (kL_j1 V U g₁ g₂ h hg₁ hg₂) (tauU V U)).trans (liftU_fac V U g₁ hg₁))).trans
      (hsh.trans (comp_aux (tauU_sheet V a b hab hS e he j U)
        ((eq_whisker (kL_j2 V U g₁ g₂ h hg₁ hg₂) (tauU V U)).trans (liftU_fac V U g₂ hg₂))).symm)
  rw [← hφK] at hsh'
  simp only [Category.assoc, ← Spec.map_comp] at hsh'
  have h3 := eq_of_toSpecΓ hsh'
  have hkey : ∀ f : (datA V a b hab hS e he U).B, φK.hom (j1 Γ(X, U.1) (CU V U) (f.1 i)) =
      φK.hom (j2 Γ(X, U.1) (CU V U) (f.1 j)) := fun f => congrArg (fun φ => φ.hom f) h3
  have hP : ∀ x, x ∈ PrimeSpectrum.asIdeal (kL V U g₁ g₂ h hg₁ hg₂ z) ↔
      φK.hom x ∈ PrimeSpectrum.asIdeal (Z.toSpecΓ z) := by
    intro x
    rw [← hφK, Scheme.Hom.comp_apply]
    rfl
  have hε : (datA V a b hab hS e he U).ε
      (cU U.2.fromSpec (tauU V U) (htauU V U) a b hab hS e he (kL V U g₁ g₂ h hg₁ hg₂ z)) ∉
      PrimeSpectrum.asIdeal (kL V U g₁ g₂ h hg₁ hg₂ z) :=
    (fib_not_mem (cU U.2.fromSpec (tauU V U) (htauU V U) a b hab hS e he)
      (isLocallyConstant_cU U.2.fromSpec (tauU V U) (htauU V U) a b hab hS e he) _ _).2 rfl
  have hk : φK.hom ((datA V a b hab hS e he U).ε
      (cU U.2.fromSpec (tauU V U) (htauU V U) a b hab hS e he (kL V U g₁ g₂ h hg₁ hg₂ z))) ≠ 0 :=
    fun h0 => hε ((hP _).2 (by rw [h0]; exact Ideal.zero_mem _))
  have hj := (datA V a b hab hS e he U).key_sheet φK.hom i j _ hkey hk
  rw [hj]
  abel

end Cover

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree

* `dg W`: the diagonal of `W ×_P W` (clopen: `isClopen_dg`); `dsec Λ W`: its indicator section of `Λ_W`;
* `shapφ Λ W : Λ[W] ⟶ π_* Λ_W` is the map given by `dsec` (`shapφ_taut`);
* `cval_S`: values of `Σ_a l_a · τ_a^* dsec` along a sheet;
* **`isIso_shapφ`**, **`shapIso`**: `shapφ` is an isomorphism (stalkwise: `stalk_inj`, `stalk_surj`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

section Dg

end Dg

section Iso

variable (Λ : Type u) [CommRing Λ] (W : P.Etale) [IsSeparated W.hom]

variable [QuasiCompact W.hom]

/-- **`Λ[W] ⟶ π_* Λ_W` is an isomorphism** for `W` separated, quasi-compact etale of constant degree. -/
theorem isIso_shapφ (n : ℕ) (hn : ∀ y : P, Nat.card ((geomPtAt y).point.fiber.obj W) = n) :
    IsIso (shapφ Λ W) := by
  refine (isIso_iff_stalk Λ _).2 fun x => ?_
  have : Mono (((geomPtAt x).stalkF Λ).map (shapφ Λ W)) :=
    (ModuleCat.mono_iff_injective _).2 (stalk_inj Λ W x)
  have : Epi (((geomPtAt x).stalkF Λ).map (shapφ Λ W)) :=
    (ModuleCat.epi_iff_surjective _).2 (stalk_surj Λ W n hn x)
  exact isIso_of_mono_of_epi _

end Iso

end RamanujanPetersson.EtPBC.EtShap

end

end


