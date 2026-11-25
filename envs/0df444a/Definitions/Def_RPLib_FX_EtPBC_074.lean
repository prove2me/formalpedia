-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_074
-- name    : RPLib_FX_EtPBC_074
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:42:27.760438+00:00
-- url     : https://prove2.me/theorems/1ce47a1e-b337-5fb9-85f3-0a9495b977d6
-- title:
--   Proper base change for the projective line, library file 074
-- statement:
--   File 074 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovAs5e`: S4-EtPBC-A, R4-T2 (A3 assembly, As5e): the two-chart package descends to one f.g. subalgebra
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_064

/-!
# Proper base change for the projective line, library file 074

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovAs5e`: S4-EtPBC-A, R4-T2 (A3 assembly, As5e): the two-chart package descends to one f.g. subalgebra
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
/-- The descent step of `desc_pack` from data over `C₀`. -/
theorem desc_pack_aux [Module.Flat A S] {r₀ r₁ : ℕ} (g₀ : Fin r₀ → MvPolynomial (Fin r₀) (S ⊗[A] B₀))
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
      Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range g₁))
    (C₀ : Subalgebra A S) (hC₀ : C₀.FG) (G0 : Fin r₀ → MvPolynomial (Fin r₀) (C₀ ⊗[A] B₀))
    (G1 : Fin r₁ → MvPolynomial (Fin r₁) (C₀ ⊗[A] B₁)) (U : Fin r₀ → MvPolynomial (Fin r₁) (C₀ ⊗[A] N))
    (V : Fin r₁ → MvPolynomial (Fin r₀) (C₀ ⊗[A] N)) (eG0 : gmap (tvC B₀ C₀) G0 = g₀)
    (eG1 : gmap (tvC B₁ C₀) G1 = g₁) (eU : (fun j => MvPolynomial.map (tvC N C₀) (U j)) = u)
    (eV : (fun i => MvPolynomial.map (tvC N C₀) (V i)) = v) :
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
  subst eG0 eG1 eU eV
  obtain ⟨C₁, h₁, hC₁, hJc₀, hFc₀⟩ := desc_chart (B := B₀) C₀ hC₀ G0 hJ₀ hF₀
  obtain ⟨C₂, h₂, hC₂, hJc₁, hFc₁⟩ := desc_chart (B := B₁) C₀ hC₀ G1 hJ₁ hF₁
  obtain ⟨C₃, h₃, hC₃, s₁, s₂, s₃, s₄⟩ := desc_subst (B := N) C₀ hC₀ (gmap (bcC φ₀ C₀) G0)
    (gmap (bcC φ₁ C₀) G1) U V
    (fun j => by rw [gmap_tvC_bcC φ₀ C₀ G0, gmap_tvC_bcC φ₁ C₀ G1]; exact hu j)
    (fun i => by rw [gmap_tvC_bcC φ₀ C₀ G0, gmap_tvC_bcC φ₁ C₀ G1]; exact hv i)
    (fun i => by rw [gmap_tvC_bcC φ₁ C₀ G1]; exact huv i)
    (fun j => by rw [gmap_tvC_bcC φ₀ C₀ G0]; exact hvu j)
  obtain ⟨D, hD, k₁, k₂, k₃⟩ : ∃ D : Subalgebra A S, D.FG ∧ C₁ ≤ D ∧ C₂ ≤ D ∧ C₃ ≤ D :=
    ⟨C₁ ⊔ C₂ ⊔ C₃, (hC₁.sup hC₂).sup hC₃, le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left,
      le_sup_right⟩
  have key₀ : gmap (tiC N k₃) (gmap (tiC N h₃) (gmap (bcC φ₀ C₀) G0)) =
      gmap (bcC φ₀ D) (gmap (tiC B₀ (h₁.trans k₁)) G0) :=
    (gmap_tiC_tiC h₃ k₃ (gmap (bcC φ₀ C₀) G0)).trans (gmap_tiC_bcC φ₀ (h₃.trans k₃) G0)
  have key₁ : gmap (tiC N k₃) (gmap (tiC N h₃) (gmap (bcC φ₁ C₀) G1)) =
      gmap (bcC φ₁ D) (gmap (tiC B₁ (h₁.trans k₁)) G1) :=
    (gmap_tiC_tiC h₃ k₃ (gmap (bcC φ₁ C₀) G1)).trans (gmap_tiC_bcC φ₁ (h₃.trans k₃) G1)
  obtain ⟨Su, Sv, Suv, Svu⟩ := subst_congr key₁ key₀ _ _
    (subst_map (tiC N k₃) (gmap (tiC N h₃) (gmap (bcC φ₁ C₀) G1))
      (gmap (tiC N h₃) (gmap (bcC φ₀ C₀) G0)) (fun k => MvPolynomial.map (tiC N h₃) (U k))
      (fun k => MvPolynomial.map (tiC N h₃) (V k)) s₁ s₂ s₃ s₄)
  refine ⟨D, hD, gmap (tiC B₀ (h₁.trans k₁)) G0, gmap (tiC B₁ (h₁.trans k₁)) G1,
    fun j => MvPolynomial.map (tiC N k₃) (MvPolynomial.map (tiC N h₃) (U j)),
    fun i => MvPolynomial.map (tiC N k₃) (MvPolynomial.map (tiC N h₃) (V i)),
    ⟨gmap_tvC_tiC _ G0, gmap_tvC_tiC _ G1,
      funext fun j => (map_tvC_tiC (B := N) k₃ _).trans (map_tvC_tiC h₃ (U j)),
      funext fun i => (map_tvC_tiC (B := N) k₃ _).trans (map_tvC_tiC h₃ (V i))⟩,
    ⟨?_, ?_, ?_, ?_⟩, Su, Sv, Suv, Svu⟩
  · have e := hJ_map (tiC B₀ k₁) (gmap (tiC B₀ h₁) G0) hJc₀
    rw [gmap_tiC_tiC h₁ k₁ G0] at e
    exact e
  · have e := hF_map (tiC B₀ k₁) (gmap (tiC B₀ h₁) G0) hFc₀
    rw [gmap_tiC_tiC h₁ k₁ G0] at e
    exact e
  · have e := hJ_map (tiC B₁ k₂) (gmap (tiC B₁ h₂) G1) hJc₁
    rw [gmap_tiC_tiC h₂ k₂ G1] at e
    exact e
  · have e := hF_map (tiC B₁ k₂) (gmap (tiC B₁ h₂) G1) hFc₁
    rw [gmap_tiC_tiC h₂ k₂ G1] at e
    exact e

end Pack

end RamanujanPetersson.EtPBC.Cov

end

end


