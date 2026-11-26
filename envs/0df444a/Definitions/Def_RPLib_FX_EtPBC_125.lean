-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_125
-- name    : RPLib_FX_EtPBC_125
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:04:49.968607+00:00
-- url     : https://prove2.me/theorems/0c34e72d-5187-5965-a2a2-7cb30b41e275
-- title:
--   Proper base change for the projective line, library file 125
-- statement:
--   File 125 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovAs5e`: S4-EtPBC-A, R4-T2 (A3 assembly, As5e): the two-chart package descends to one f.g. subalgebra
--   * `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_074
import Definitions.Def_RPLib_FX_EtPBC_112

/-!
# Proper base change for the projective line, library file 125

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovAs5e`: S4-EtPBC-A, R4-T2 (A3 assembly, As5e): the two-chart package descends to one f.g. subalgebra
* `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_CovAs5e =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As5e): the two-chart package descends to one f.g. subalgebra

**`desc_pack`**: square systems `g₀` over `S ⊗ B₀`, `g₁` over `S ⊗ B₁` with etale and finite witnesses, and
substitution data `u v` over `S ⊗ N` between their base changes along `bcS S φᵢ = id_S ⊗ φᵢ`, all come from data
`gC₀ gC₁ uC vC` over one f.g. `C ≤ S` (`gmap (tvC _ C) gCᵢ = gᵢ`, `map (tvC N C) ∘ uC = u`, ...), for which the
witnesses and the substitution memberships (between `gmap (bcC φᵢ C) gCᵢ`) already hold over `C`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section BcS

end BcS

section Congr

end Congr

section Pack

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B₀ B₁ N : Type u} [CommRing B₀] [Algebra A B₀] [CommRing B₁] [Algebra A B₁] [CommRing N] [Algebra A N]
  (φ₀ : B₀ →ₐ[A] N) (φ₁ : B₁ →ₐ[A] N)

set_option maxHeartbeats 400000 in
/-- **The two-chart package descends to one f.g. subalgebra.** -/
theorem desc_pack [Module.Flat A S] {r₀ r₁ : ℕ} (g₀ : Fin r₀ → MvPolynomial (Fin r₀) (S ⊗[A] B₀))
    (g₁ : Fin r₁ → MvPolynomial (Fin r₁) (S ⊗[A] B₁))
    (u : Fin r₀ → MvPolynomial (Fin r₁) (S ⊗[A] N)) (v : Fin r₁ → MvPolynomial (Fin r₀) (S ⊗[A] N))
    (hu : ∀ j, MvPolynomial.bind₁ u (gmap (bcS S φ₀) g₀ j) ∈ Ideal.span (Set.range (gmap (bcS S φ₁) g₁)))
    (hv : ∀ i, MvPolynomial.bind₁ v (gmap (bcS S φ₁) g₁ i) ∈ Ideal.span (Set.range (gmap (bcS S φ₀) g₀)))
    (huv : ∀ i, MvPolynomial.bind₁ u (v i) - MvPolynomial.X i ∈ Ideal.span (Set.range (gmap (bcS S φ₁) g₁)))
    (hvu : ∀ j, MvPolynomial.bind₁ v (u j) - MvPolynomial.X j ∈ Ideal.span (Set.range (gmap (bcS S φ₀) g₀)))
    (hJ₀ : ∃ w, jdet g₀ * w - 1 ∈ Ideal.span (Set.range g₀))
    (hF₀ : ∀ j, ∃ q : Polynomial (S ⊗[A] B₀), q.Monic ∧
      Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range g₀))
    (hJ₁ : ∃ w, jdet g₁ * w - 1 ∈ Ideal.span (Set.range g₁))
    (hF₁ : ∀ j, ∃ q : Polynomial (S ⊗[A] B₁), q.Monic ∧
      Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range g₁)) :
    ∃ (C : Subalgebra A S), C.FG ∧ ∃ (gC₀ : Fin r₀ → MvPolynomial (Fin r₀) (C ⊗[A] B₀))
      (gC₁ : Fin r₁ → MvPolynomial (Fin r₁) (C ⊗[A] B₁))
      (uC : Fin r₀ → MvPolynomial (Fin r₁) (C ⊗[A] N)) (vC : Fin r₁ → MvPolynomial (Fin r₀) (C ⊗[A] N)),
      (gmap (tvC B₀ C) gC₀ = g₀ ∧ gmap (tvC B₁ C) gC₁ = g₁ ∧
        (fun j => MvPolynomial.map (tvC N C) (uC j)) = u ∧ (fun i => MvPolynomial.map (tvC N C) (vC i)) = v) ∧
      ((∃ w, jdet gC₀ * w - 1 ∈ Ideal.span (Set.range gC₀)) ∧
        (∀ j, ∃ q : Polynomial (C ⊗[A] B₀), q.Monic ∧
          Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range gC₀)) ∧
        (∃ w, jdet gC₁ * w - 1 ∈ Ideal.span (Set.range gC₁)) ∧
        (∀ j, ∃ q : Polynomial (C ⊗[A] B₁), q.Monic ∧
          Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range gC₁))) ∧
      (∀ j, MvPolynomial.bind₁ uC (gmap (bcC φ₀ C) gC₀ j) ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
      (∀ i, MvPolynomial.bind₁ vC (gmap (bcC φ₁ C) gC₁ i) ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀))) ∧
      (∀ i, MvPolynomial.bind₁ uC (vC i) - MvPolynomial.X i ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
      (∀ j, MvPolynomial.bind₁ vC (uC j) - MvPolynomial.X j ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀))) := by
  classical
  obtain ⟨Ca, hCa, la⟩ := exists_lift_polys (B := B₀) g₀
  choose ga hga using la
  obtain ⟨Cb, hCb, lb⟩ := exists_lift_polys (B := B₁) g₁
  choose gb hgb using lb
  obtain ⟨Cc, hCc, lc⟩ := exists_lift_polys (B := N) u
  choose uc huc using lc
  obtain ⟨Cd, hCd, ld⟩ := exists_lift_polys (B := N) v
  choose vd hvd using ld
  obtain ⟨C₀, hC₀, ha, hb, hc, hd⟩ : ∃ C₀ : Subalgebra A S, C₀.FG ∧ Ca ≤ C₀ ∧ Cb ≤ C₀ ∧ Cc ≤ C₀ ∧ Cd ≤ C₀ :=
    ⟨Ca ⊔ Cb ⊔ Cc ⊔ Cd, ((hCa.sup hCb).sup hCc).sup hCd, le_sup_left.trans (le_sup_left.trans le_sup_left),
      le_sup_right.trans (le_sup_left.trans le_sup_left), le_sup_right.trans le_sup_left, le_sup_right⟩
  obtain ⟨G0, eG0⟩ : ∃ G0 : Fin r₀ → MvPolynomial (Fin r₀) (C₀ ⊗[A] B₀), gmap (tvC B₀ C₀) G0 = g₀ :=
    ⟨gmap (tiC B₀ ha) ga, funext fun j => (map_tvC_tiC ha (ga j)).trans (hga j)⟩
  obtain ⟨G1, eG1⟩ : ∃ G1 : Fin r₁ → MvPolynomial (Fin r₁) (C₀ ⊗[A] B₁), gmap (tvC B₁ C₀) G1 = g₁ :=
    ⟨gmap (tiC B₁ hb) gb, funext fun j => (map_tvC_tiC hb (gb j)).trans (hgb j)⟩
  obtain ⟨U, eU⟩ : ∃ U : Fin r₀ → MvPolynomial (Fin r₁) (C₀ ⊗[A] N),
      (fun j => MvPolynomial.map (tvC N C₀) (U j)) = u :=
    ⟨fun j => MvPolynomial.map (tiC N hc) (uc j), funext fun j => (map_tvC_tiC hc (uc j)).trans (huc j)⟩
  obtain ⟨V, eV⟩ : ∃ V : Fin r₁ → MvPolynomial (Fin r₀) (C₀ ⊗[A] N),
      (fun i => MvPolynomial.map (tvC N C₀) (V i)) = v :=
    ⟨fun i => MvPolynomial.map (tiC N hd) (vd i), funext fun i => (map_tvC_tiC hd (vd i)).trans (hvd i)⟩
  exact desc_pack_aux φ₀ φ₁ g₀ g₁ u v hu hv huv hvu hJ₀ hF₀ hJ₁ hF₁ C₀ hC₀ G0 G1 U V eG0 eG1 eU eV

end Pack

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4d =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Pc

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

set_option backward.isDefEq.respectTransparency false in
theorem clsD_sec_key {T : P.Etale} (s : chEt c φ ⟶ T)
    (Y : H Λ ((res (toD1 c φ a).left Λ).obj (unitSh Λ (chEt c φ).left)) 1) :
    (extFree Λ (W1 c φ a) (freeSh Λ T) 1).symm (Y.comp (Ext.mk₀ ((res (toD1 c φ a).left Λ).map
      (secMap Λ s) ≫ (resCompIso Λ (toD1 c φ a)).hom.app (freeSh Λ T))) (add_zero 1)) =
      thetaM Λ (toD1 c φ a ≫ s) 1 (Y.comp (Ext.mk₀ (unitResIso (toD1 c φ a).left Λ).inv) (add_zero 1)) := by
  rw [thetaM_eq, secMap_res, ← unitResIso_hom, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.inv_hom_id_assoc]

end Pc

end RamanujanPetersson.EtPBC.EtMV

end

end


