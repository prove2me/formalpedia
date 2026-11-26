-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_182
-- name    : RPLib_FX_EtPBC_182
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:08:35.866066+00:00
-- url     : https://prove2.me/theorems/74c7a14d-766c-52a2-bec3-b39bdafdf0fa
-- title:
--   Proper base change for the projective line, library file 182
-- statement:
--   File 182 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovAs6d`: S4-EtPBC-A, R4-T2 (A3 assembly, As6d): the completed cover descends to one finitely generated `C ≤ S`
--   * `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_125
import Definitions.Def_RPLib_FX_EtPBC_175

/-!
# Proper base change for the projective line, library file 182

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovAs6d`: S4-EtPBC-A, R4-T2 (A3 assembly, As6d): the completed cover descends to one finitely generated `C ≤ S`
* `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_CovAs6d =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As6d): the completed cover descends to one finitely generated `C ≤ S`

**`desc_cover`** (any flat `A`-algebra `S`; in the application `S = Â`): a two-chart cover over `S ⊗ Bᵢ` glued over
`S ⊗ N` (the shape of `hat_lift`) is, over one finitely generated `C ≤ S`, given by square systems `gCᵢ` with etale
and finite witnesses and substitution data `uC vC`, together with ring isomorphisms from the base-changed
presentations to the charts and the overlap, compatible with the structure maps and the gluing maps on variables.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section DescCover

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B₀ B₁ N : Type u} [CommRing B₀] [Algebra A B₀] [CommRing B₁] [Algebra A B₁] [CommRing N] [Algebra A N]
  (φ₀ : B₀ →ₐ[A] N) (φ₁ : B₁ →ₐ[A] N)

set_option maxHeartbeats 800000 in
/-- **Descent of the completed cover to a finitely generated subalgebra.** -/
theorem desc_cover [Module.Flat A S] {Eh₀ Eh₁ Eh : Type u} [CommRing Eh₀] [CommRing Eh₁] [CommRing Eh]
    (t₀ : B₀) (t₁ : B₁)
    (hf₀ : IsAwayMap (bcS S φ₀) ((1 : S) ⊗ₜ[A] t₀)) (hf₁ : IsAwayMap (bcS S φ₁) ((1 : S) ⊗ₜ[A] t₁))
    (hu₀ : IsUnit (bcS S φ₀ ((1 : S) ⊗ₜ[A] t₀))) (hu₁ : IsUnit (bcS S φ₁ ((1 : S) ⊗ₜ[A] t₁)))
    (b₀ : S ⊗[A] B₀ →+* Eh₀) (b₁ : S ⊗[A] B₁ →+* Eh₁) (bN : S ⊗[A] N →+* Eh) (q₀ : Eh₀ →+* Eh)
    (q₁ : Eh₁ →+* Eh) (het₀ : b₀.Etale) (het₁ : b₁.Etale) (hfi₀ : b₀.Finite) (hfi₁ : b₁.Finite)
    (hq₀ : q₀.comp b₀ = bN.comp (bcS S φ₀)) (hq₁ : q₁.comp b₁ = bN.comp (bcS S φ₁))
    (aw₀ : IsAwayMap q₀ (b₀ ((1 : S) ⊗ₜ[A] t₀))) (aw₁ : IsAwayMap q₁ (b₁ ((1 : S) ⊗ₜ[A] t₁))) :
    ∃ (C : Subalgebra A S), C.FG ∧ ∃ (r₀ r₁ : ℕ) (gC₀ : Fin r₀ → MvPolynomial (Fin r₀) (C ⊗[A] B₀))
      (gC₁ : Fin r₁ → MvPolynomial (Fin r₁) (C ⊗[A] B₁))
      (uC : Fin r₀ → MvPolynomial (Fin r₁) (C ⊗[A] N)) (vC : Fin r₁ → MvPolynomial (Fin r₀) (C ⊗[A] N)),
      ((∃ w, jdet gC₀ * w - 1 ∈ Ideal.span (Set.range gC₀)) ∧
        (∀ j, ∃ q : Polynomial (C ⊗[A] B₀), q.Monic ∧
          Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range gC₀)) ∧
        (∃ w, jdet gC₁ * w - 1 ∈ Ideal.span (Set.range gC₁)) ∧
        (∀ j, ∃ q : Polynomial (C ⊗[A] B₁), q.Monic ∧
          Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range gC₁))) ∧
      ((∀ j, MvPolynomial.bind₁ uC (gmap (bcC φ₀ C) gC₀ j) ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
        (∀ i, MvPolynomial.bind₁ vC (gmap (bcC φ₁ C) gC₁ i) ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀))) ∧
        (∀ i, MvPolynomial.bind₁ uC (vC i) - MvPolynomial.X i ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
        (∀ j, MvPolynomial.bind₁ vC (uC j) - MvPolynomial.X j ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀)))) ∧
      ∃ (E₀ : Pres (gmap (tvC B₀ C) gC₀) ≃+* Eh₀) (E₁ : Pres (gmap (tvC B₁ C) gC₁) ≃+* Eh₁)
        (EN : Pres (gmap (tvC N C) (gmap (bcC φ₀ C) gC₀)) ≃+* Eh),
        (∀ a, E₀ (algebraMap (S ⊗[A] B₀) (Pres (gmap (tvC B₀ C) gC₀)) a) = b₀ a) ∧
        (∀ a, E₁ (algebraMap (S ⊗[A] B₁) (Pres (gmap (tvC B₁ C) gC₁)) a) = b₁ a) ∧
        (∀ a, EN (algebraMap (S ⊗[A] N) (Pres (gmap (tvC N C) (gmap (bcC φ₀ C) gC₀))) a) = bN a) ∧
        (∀ j, q₀ (E₀ (Ideal.Quotient.mk _ (MvPolynomial.X j))) = EN (Ideal.Quotient.mk _ (MvPolynomial.X j))) ∧
        (∀ j, q₁ (E₁ (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
          EN (Ideal.Quotient.mk _ (MvPolynomial.map (tvC N C) (vC j)))) := by
  obtain ⟨r₀, r₁, g₀, g₁, e₀, e₁, eN₀, eN₁, u, v, hu, hv, huv, hvu, ⟨hJ₀, hF₀, hJ₁, hF₁⟩, ⟨he₀, he₁, hN₀, -⟩,
    ⟨hM₀, hM₁, hI⟩⟩ := two_chart_pres (bcS S φ₀) (bcS S φ₁) _ _ hf₀ hf₁ hu₀ hu₁ b₀ b₁ bN q₀ q₁ het₀ het₁
      hfi₀ hfi₁ hq₀ hq₁ aw₀ aw₁
  obtain ⟨C, hC, gC₀, gC₁, uC, vC, ⟨e0, e1, -, ev⟩, hW, H1, H2, H3, H4⟩ :=
    desc_pack φ₀ φ₁ g₀ g₁ u v hu hv huv hvu hJ₀ hF₀ hJ₁ hF₁
  subst e0 e1 ev
  have hN : gmap (tvC N C) (gmap (bcC φ₀ C) gC₀) = gmap (bcS S φ₀) (gmap (tvC B₀ C) gC₀) :=
    gmap_tvC_bcC φ₀ C gC₀
  refine ⟨C, hC, r₀, r₁, gC₀, gC₁, uC, vC, hW, ⟨H1, H2, H3, H4⟩, e₀, e₁, (presCongr hN).toRingEquiv.trans eN₀,
    he₀, he₁, fun a => ?_, fun j => ?_, fun j => ?_⟩
  · rw [RingEquiv.trans_apply]
    exact (congrArg eN₀ ((presCongr hN).commutes a)).trans (hN₀ a)
  · rw [RingEquiv.trans_apply, ← hM₀, presMap_X]
    rfl
  · rw [RingEquiv.trans_apply, ← hM₁, presMap_X, ← hI, presIso_mk, MvPolynomial.bind₁_X_right]
    rfl

end DescCover

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
theorem clsD_sec_tb {T : P.Etale} (s : chEt c φ ⟶ T) (c' : Λ) :
    (hS.extClass.comp (Ext.mk₀ (freeMap Λ (isoT c φ hUz).inv)) (add_zero 1)).comp
      (thetaM Λ (toD1 c φ a ≫ s) 1 (resLE (toWa c a φ).left 1 (xiA a hN Λ hΛ c'))) (show 1 + 1 = 2 from rfl) =
    (pcD c φ a hN hΛ hUz hS c').comp (Ext.mk₀ (freeMap Λ s)) (add_zero 2) := by
  rw [thetaM_comp, pcD_eq, Ext.comp_assoc_of_third_deg_zero]

end Pc

end RamanujanPetersson.EtPBC.EtMV

end

end


