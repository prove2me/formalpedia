-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_009
-- name    : RPLib_FX_EtPBC_009
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:37:23.143882+00:00
-- url     : https://prove2.me/theorems/9f1c162c-9bf4-5e37-babc-23445a572693
-- title:
--   Proper base change for the projective line, library file 009
-- statement:
--   File 009 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_GalTr`: S4-EtCompact (b3a): Galois actions on stalks along etale maps and isomorphisms of geometric points
--   * `S4.Def_RP_EtPBC_A_CovAs5a`: S4-EtPBC-A, R4-T2 (A3 assembly, As5a): lifting polynomials and memberships to a f.g. subalgebra
--   * `S4.Def_RP_EtPBC_A_Z3Clo`: S4-EtPBC-A, (Z) geometric layer 1: idempotent sections and clopen subsets of a scheme
--   * `S4.Def_RP_EtPBC_A_Xi`: S4-EtPBC-A, M2 F5: the germ `ξ_s(b)` of a section of a pullback
--   * `S4.Def_RP_EtPBC_A_FGS`: S4-EtPBC-A, R2(a,b): sections over compact etale objects, and local lifts on the whole fibre
--   * `S4.Def_RP_EtPBC_A_O2Ap1`: S4-EtPBC-A, O2 M6 (O2Ap1): approximating a function on an etale neighbourhood by a function from below
--   * `S4.Def_RP_EtPBC_A_O2MVo`: S4-EtPBC-A, O2 (MV route), MVo: Mayer-Vietoris for an open `U ⊆ P` and `W : P.Etale`
--   * `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
--   * `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
--   * `S4.Def_RP_EtPBC_A_O2D1`: S4-EtPBC-A, O2 (MV route), M3 step (3): classes of `H²(Spec A, g_* N)` die on a basic open
--   * `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
--   * `S4.Def_RP_EtPBC_A_O2M4b`: S4-EtPBC-A, O2 (MV route), M4 (b): every class of `H²(P¹, F)` is a Mayer-Vietoris class
--   * `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
--   * `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
--   * `S4.Def_RP_EtPBC_A_O2Km3`: S4-EtPBC-A, O2 M6 (O2Km3): an etale algebra over a PID splits into Dedekind domains
--   * `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
--   * `S4.Def_RP_EtPBC_A_O2N3`: S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map
--   * `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
--   * `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
--   * `S4.Def_RP_EtPBC_A_O2E5b`: S4-EtPBC-A, O2 C-plan S4d0b: `extFree` is natural in the etale object (degree 1)
--   * `S4.Def_RP_EtPBC_A_O2Km4`: S4-EtPBC-A, O2 M6 (O2Km4): `H¹` of an affine scheme whose ring is a product of Dedekind domains
--   * `S4.Def_RP_EtPBC_A_O2Gl1b`: S4-EtPBC-A, O2 GLOB (O2Gl1b): the algebra of stages S1-S2
--   * `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
--   * `S4.Def_RP_EtPBC_A_O2Km5`: S4-EtPBC-A, O2 M6 (O2Km5): global sections of an affine scheme etale over `Spec A`
--   * `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2T1`: S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps
--   * `S4.Def_RP_EtPBC_A_O2Th1a`: S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality
--   * `S4.Def_RP_EtPBC_A_O2T3`: S4-EtPBC-A, O2 S5c: sections after shrinking, and the graph splitting
--   * `S4.Def_RP_EtPBC_A_O2Gl2g`: S4-EtPBC-A, O2 GLOB (O2Gl2g): stage S4, the data `e`, `g`, `hHp`, `hHq` of `uk_diff` (pure algebra)
--   * `S4.Def_RP_EtPBC_A_O2Gl2c`: S4-EtPBC-A, O2 GLOB (O2Gl2c): stage S3, the live modification (pure algebra)
--   * `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
--   * `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
--   * `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
--   * `S4.Def_RP_EtPBC_A_O2Gl3e`: S4-EtPBC-A, O2 GLOB (O2Gl3e): the core step on the charts
--   * `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
--   * `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
--   * `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_001
import Definitions.Def_RPLib_FX_EtPBC_002
import Definitions.Def_RPLib_FX_EtPBC_003
import Definitions.Def_RPLib_FX_EtPBC_004

/-!
# Proper base change for the projective line, library file 009

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_GalTr`: S4-EtCompact (b3a): Galois actions on stalks along etale maps and isomorphisms of geometric points
* `S4.Def_RP_EtPBC_A_CovAs5a`: S4-EtPBC-A, R4-T2 (A3 assembly, As5a): lifting polynomials and memberships to a f.g. subalgebra
* `S4.Def_RP_EtPBC_A_Z3Clo`: S4-EtPBC-A, (Z) geometric layer 1: idempotent sections and clopen subsets of a scheme
* `S4.Def_RP_EtPBC_A_Xi`: S4-EtPBC-A, M2 F5: the germ `ξ_s(b)` of a section of a pullback
* `S4.Def_RP_EtPBC_A_FGS`: S4-EtPBC-A, R2(a,b): sections over compact etale objects, and local lifts on the whole fibre
* `S4.Def_RP_EtPBC_A_O2Ap1`: S4-EtPBC-A, O2 M6 (O2Ap1): approximating a function on an etale neighbourhood by a function from below
* `S4.Def_RP_EtPBC_A_O2MVo`: S4-EtPBC-A, O2 (MV route), MVo: Mayer-Vietoris for an open `U ⊆ P` and `W : P.Etale`
* `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
* `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
* `S4.Def_RP_EtPBC_A_O2D1`: S4-EtPBC-A, O2 (MV route), M3 step (3): classes of `H²(Spec A, g_* N)` die on a basic open
* `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
* `S4.Def_RP_EtPBC_A_O2M4b`: S4-EtPBC-A, O2 (MV route), M4 (b): every class of `H²(P¹, F)` is a Mayer-Vietoris class
* `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
* `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
* `S4.Def_RP_EtPBC_A_O2Km3`: S4-EtPBC-A, O2 M6 (O2Km3): an etale algebra over a PID splits into Dedekind domains
* `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
* `S4.Def_RP_EtPBC_A_O2N3`: S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map
* `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
* `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
* `S4.Def_RP_EtPBC_A_O2E5b`: S4-EtPBC-A, O2 C-plan S4d0b: `extFree` is natural in the etale object (degree 1)
* `S4.Def_RP_EtPBC_A_O2Km4`: S4-EtPBC-A, O2 M6 (O2Km4): `H¹` of an affine scheme whose ring is a product of Dedekind domains
* `S4.Def_RP_EtPBC_A_O2Gl1b`: S4-EtPBC-A, O2 GLOB (O2Gl1b): the algebra of stages S1-S2
* `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
* `S4.Def_RP_EtPBC_A_O2Km5`: S4-EtPBC-A, O2 M6 (O2Km5): global sections of an affine scheme etale over `Spec A`
* `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
* `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
* `S4.Def_RP_EtPBC_A_O2T1`: S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps
* `S4.Def_RP_EtPBC_A_O2Th1a`: S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality
* `S4.Def_RP_EtPBC_A_O2T3`: S4-EtPBC-A, O2 S5c: sections after shrinking, and the graph splitting
* `S4.Def_RP_EtPBC_A_O2Gl2g`: S4-EtPBC-A, O2 GLOB (O2Gl2g): stage S4, the data `e`, `g`, `hHp`, `hHq` of `uk_diff` (pure algebra)
* `S4.Def_RP_EtPBC_A_O2Gl2c`: S4-EtPBC-A, O2 GLOB (O2Gl2c): stage S3, the live modification (pure algebra)
* `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
* `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
* `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
* `S4.Def_RP_EtPBC_A_O2Gl3e`: S4-EtPBC-A, O2 GLOB (O2Gl3e): the core step on the charts
* `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
* `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
* `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtCompact_GalTr =====
section

/-!
# S4-EtCompact (b3a): Galois actions on stalks along etale maps and isomorphisms of geometric points

* `resFib_stalkAut`: the germ isomorphism `resFib g t : (res g F)_t ≅ F_(t ≫ g)` intertwines the action of an
  automorphism `τ` of `Spec Ω` over `U` on both sides;
* `autHom_ptIso`: across an isomorphism `e` of geometric points, `τ` on the target corresponds to
  `e.hom.left ≫ τ ≫ e.inv.left` on the source (`ptIso e`), and `stalkAut_ptIso` on stalks;
* for an open immersion `g` and `y : U`: `sepO g y : Ω_(g y) ≃ Ω_y` (behind `StkTr.mapPtIso`), the Galois transport
  `galTr g y : Gal (g y) → Gal y` (`galTrHom`, `galTr_left`), `resTrIso g y Λ F : (g^* F)_y ≅ F_(g y)` and
  **`stalkAut_resTr`**: `resTrIso` carries `galRep (g^* F) y (galTr σ)` to `galRep F (g y) σ`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTr

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

section Res

end Res

section Pt

variable {X : Scheme.{u}}

variable (Λ : Type u) [CommRing Λ]

/-- `autHom_ptIso` on stalk functors: `τ` on `t` and its conjugate on `s` correspond under `ptIsoSheafFiber`. -/
theorem stalkAut_ptIso {s t : GeomPt X} (e : CategoryTheory.Over.mk s.pt ≅ CategoryTheory.Over.mk t.pt)
    (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω)) (hτ : τ ≫ t.pt = t.pt)
    (hτs : (e.hom.left ≫ τ ≫ e.inv.left) ≫ s.pt = s.pt) :
    t.stalkAut Λ τ hτ ≫ (ptIsoSheafFiber Λ (GPtIso.ptIso e)).hom =
      (ptIsoSheafFiber Λ (GPtIso.ptIso e)).hom ≫ s.stalkAut Λ (e.hom.left ≫ τ ≫ e.inv.left) hτs := by
  change GrothendieckTopology.Point.Hom.sheafFiber (t.autHom τ hτ) ≫
      GrothendieckTopology.Point.Hom.sheafFiber (GPtIso.ptIso e).hom =
    GrothendieckTopology.Point.Hom.sheafFiber (GPtIso.ptIso e).hom ≫
      GrothendieckTopology.Point.Hom.sheafFiber (s.autHom (e.hom.left ≫ τ ≫ e.inv.left) hτs)
  rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, ← GrothendieckTopology.Point.Hom.sheafFiber_comp,
    autHom_ptIso e τ hτ hτs]

end Pt

section Open

end Open

end RamanujanPetersson.EtCompact.GalTr

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs5a =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As5a): lifting polynomials and memberships to a f.g. subalgebra

For a flat `A`-algebra `S` and an `A`-algebra `B`, with `tvC B C : C ⊗ B → S ⊗ B` and, for `C ≤ D`,
`tiC B h : C ⊗ B → D ⊗ B`:
* `exists_lift_polys`: finitely many polynomials over `S ⊗ B` come from one f.g. `C`;
* `exists_lift_monic`: a monic polynomial over `S ⊗ B` comes from a monic one over `C ⊗ B`;
* **`desc_mem`**: finitely many ideal memberships `x_k ∈ (g)` over `S ⊗ B` already hold over `C ⊗ B` for a f.g.
  `C ≥ C₀` (cofactors lifted by `exists_lift_polys`, the identities descended by `desc_mvPoly`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section Lift

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]

variable {B : Type u} [CommRing B] [Algebra A B]

/-- Finitely many polynomials over `S ⊗ B` come from `C ⊗ B` for one f.g. `C`. -/
theorem exists_lift_polys {ι σ : Type*} [Finite ι] (p : ι → MvPolynomial σ (S ⊗[A] B)) :
    ∃ C : Subalgebra A S, C.FG ∧ ∀ k, ∃ y, MvPolynomial.map (tvC B C) y = p k := by
  classical
  obtain ⟨C, hC, hz⟩ := exists_fg_lift (A := A) (S := S) (B := B) (ι := Σ k : ι, (p k).coeffs)
    (fun i => i.2.1)
  refine ⟨C, hC, fun k => ?_⟩
  have hs : ((p k).coeffs : Set (S ⊗[A] B)) ⊆ Set.range (tvC B C) := by
    intro c hc
    obtain ⟨x, hx⟩ := hz ⟨k, ⟨c, Finset.mem_coe.mp hc⟩⟩
    exact ⟨x, (tmap_id_apply C.val x).trans hx⟩
  obtain ⟨y, hy⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hs
  exact ⟨y, hy⟩

end Lift

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Clo =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 1: idempotent sections and clopen subsets of a scheme

* `basicOpen_inf_one_sub`, `basicOpen_sup_one_sub`: for an idempotent `e ∈ Γ(X, U)`, `D(e)` and `D(1 - e)` partition
  `U`; **`isClopen_basicOpen`**: `D(e)` is clopen for an idempotent `e ∈ Γ(X, ⊤)`.
* `exists_idem_of_disjoint`: for disjoint opens `U`, `V` the section of `Γ(X, U ⊔ V)` that is `1` on `U` and `0` on
  `V` (sheaf gluing `objSupIsoProdEqLocus`) is idempotent.
* **`exists_idem_basicOpen_eq`**: every clopen open `U` is `D(e)` for an idempotent `e ∈ Γ(X, ⊤)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable {X : Scheme.{u}}

/-- **Every clopen open is `D(e)`** for an idempotent global section `e`. -/
theorem exists_idem_basicOpen_eq (U : X.Opens) (hU : IsClosed (U : Set X)) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ X.basicOpen e = U := by
  let V : X.Opens := ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩
  have hUV : U ⊓ V = ⊥ := by
    ext x
    simp [V]
  have hUV' : (⊤ : X.Opens) ≤ U ⊔ V := by
    intro x _
    by_cases hx : x ∈ U
    · exact Or.inl hx
    · exact Or.inr hx
  obtain ⟨c, hc, hc₁, hc₂⟩ := exists_idem_of_disjoint U V hUV
  refine ⟨X.presheaf.map (homOfLE hUV').op c, ?_, ?_⟩
  · show _ * _ = _
    rw [← map_mul, hc.eq]
  · rw [Scheme.basicOpen_res, top_inf_eq]
    apply le_antisymm
    · have h2 : V ⊓ X.basicOpen c = ⊥ := by
        rw [← Scheme.basicOpen_res X c (homOfLE le_sup_right).op, hc₂, Scheme.basicOpen_zero]
      intro x hx
      by_contra hxU
      have hm : x ∈ V ⊓ X.basicOpen c := ⟨hxU, hx⟩
      rw [h2] at hm
      simp at hm
    · have h1 : U ⊓ X.basicOpen c = U := by
        rw [← Scheme.basicOpen_res X c (homOfLE le_sup_left).op, hc₁, Scheme.basicOpen_one]
      exact inf_eq_left.mp h1

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Xi =====
section

/-!
# S4-EtPBC-A, M2 F5: the germ `ξ_s(b)` of a section of a pullback

For `f : X ⟶ Y`, a geometric point `s` of `X`, a sheaf `G` on `Y` and `b : Λ_X ⟶ f^* G`:
* **`pullStalkIso_germ`**: the stalk isomorphism `(f^* G)_s ≅ G_{s ≫ f}` sends the germ of `η_G(z)` at `b'` to the germ
  of `z` at the corresponding fibre point of `s ≫ f`;
* `xi f s G b ∈ G_{s ≫ f}`: the image of the germ of `b(1)`; `xi_sub`, `germ_eq_zero_of_xi`;
* **`xi_bc`**: for `f = ι : P_s ⟶ P`, `ξ(u_v ≫ ι^* φ)` is the germ of `φ(1)` at the neighbourhood point.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Xi

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeomPt X)

/-- `ξ_s(b) = 0` kills the germ of `b(1)` at `s`. -/
theorem germ_eq_zero_of_xi (G : EtSh Λ Y) (b : unitSh Λ X ⟶ (pull f Λ).obj G) (h : xi f s G b = 0) :
    (s.point.toPresheafFiber (etId X) s.top ((pull f Λ).obj G).obj).hom (sc b (etId X)) = 0 := by
  have hinv := ConcreteCategory.congr_hom (Iso.hom_inv_id_app (pullStalkIso f Λ s) G)
    ((s.point.toPresheafFiber (etId X) s.top ((pull f Λ).obj G).obj).hom (sc b (etId X)))
  refine hinv.symm.trans ?_
  change ((pullStalkIso f Λ s).inv.app G).hom (xi f s G b) = 0
  rw [h]
  exact LinearMap.map_zero _

end Xi

section XiBC

end XiBC

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FGS =====
section

/-!
# S4-EtPBC-A, R2(a,b): sections over compact etale objects, and local lifts on the whole fibre

* `exists_affine_refine'`: finite affine refinement of a covering sieve of a COMPACT etale object;
* `exists_cover_lift`: for an epimorphism `S.g` and a global section `q` of `S.X₃` on a compact `Y`, an affine etale
  surjection `V ⟶ Y` and a section of `S.X₂` over `V` lifting `q`;
* `isAffine_nv1`: `V ×_Y V` is affine when `V` is affine and `V ⟶ Y` is an affine morphism;
* `exists_common_rep'`, `exists_fib_at`, `exists_pullRepS`: local representation of a section of `ι^* G` over `U`;
* **`exists_fg_sec`**: a section `d` of `ι^* G` over a compact `U` is killed by every `p : G ⟶ Q` that kills
  finitely many sections `z x ∈ G(W x)` over affines.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Refine

variable {Y : Scheme.{u}}

variable {Λ : Type u} [CommRing Λ]

/-- **Local lift of a global section along an epimorphism**, on one affine etale surjection. -/
theorem exists_cover_lift [CompactSpace Y] {S : ShortComplex (EtSh Λ Y)} (hS : S.ShortExact)
    (q : S.X₃.obj.obj (op (etId Y))) :
    ∃ (V : Y.Etale) (fV : V ⟶ etId Y) (_ : IsAffine V.left) (_ : Function.Surjective fV.left)
      (p' : S.X₂.obj.obj (op V)), (S.g.hom.app (op V)).hom p' = (S.X₃.obj.map fV.op).hom q := by
  have hls : Sheaf.IsLocallySurjective S.g := (Sheaf.isLocallySurjective_iff_epi' (φ := S.g)).2 hS.epi_g
  have hR := Presheaf.imageSieve_mem Y.smallEtaleTopology S.g.hom q
  have : CompactSpace (etId Y).left := ‹CompactSpace Y›
  obtain ⟨ι, _, Sk, g, haff, hg, hcov⟩ := exists_affine_refine' (etId Y) _ hR
  choose t ht using hg
  have ht' : ∀ k, (S.g.hom.app (op (Sk k))).hom (t k) = (S.X₃.obj.map (g k).op).hom q := ht
  obtain ⟨p', hp'⟩ := cop_glue Sk S.X₂ t
  refine ⟨cop Sk, copDesc g, isAffine_cop Sk, copDesc_surjective g hcov, p', ?_⟩
  refine sep_of_cover S.X₃ (copι Sk) (cop_cover Sk) _ _ fun k => ?_
  calc _ = (S.g.hom.app (op (Sk k))).hom ((S.X₂.obj.map (copι Sk k).op).hom p') := by
        rw [← ModuleCat.comp_apply, ← NatTrans.naturality, ModuleCat.comp_apply]
    _ = _ := by
        rw [hp' k, ht' k, ← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp, copι_desc]

end Refine

section Gen

end Gen

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Ap1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Ap1): approximating a function on an etale neighbourhood by a function from below

Pure algebra for Km DESIGN v3 (Rel): `O → O'` with `O' = O + t O'` (trivial residue extension along `t`, e.g.
`k[X] → B_w` for an etale neighbourhood), an `O`-algebra `S` (functions on `R`), an `O'`-algebra `Q` (functions on
the generic fibre of `W = D_o ×_P R`) and `f : S →ₐ[O] Q`; `hatS f = O'[f S] ⊆ Q`.
* `exists_pow_dense`: `x = c + t^n y` in `O'`;
* `hatS_dense`: every `q ∈ hatS f` is `f s + t^n x` with `x ∈ hatS f`;
* **`exists_approx`**: if `s ∈ hatS f` has an inverse `v` with `t^c v ∈ hatS f`, then `f u = s (1 - t z)` for some
  `u ∈ S`, `z ∈ hatS f`;
* `isIntegral_of_mem_hatS`: elements of `hatS f` are integral over `O'` when `S` is integral over `O`;
* `exists_crt`, **`exists_approx_crt`**: the same with `u` prescribed modulo finitely many pairwise coprime ideals
  of `S` that are coprime to every `(t^n)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Approx

variable {O O' S Q : Type*} [CommRing O] [CommRing O'] [CommRing S] [CommRing Q]
  [Algebra O O'] [Algebra O S] [Algebra O' Q] [Algebra O Q] [IsScalarTower O O' Q]
  (f : S →ₐ[O] Q) (t : O)

theorem mem_hatS (s : S) : f s ∈ hatS (O' := O') f := Algebra.subset_adjoin ⟨s, rfl⟩

theorem algebraMap_pow_mem_hatS (n : ℕ) : algebraMap O Q t ^ n ∈ hatS (O' := O') f := by
  rw [IsScalarTower.algebraMap_apply O O' Q]
  exact Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ _) n

theorem hatS_dense (h1 : ∀ x : O', ∃ c : O, ∃ y : O', x = algebraMap O O' c + algebraMap O O' t * y)
    (n : ℕ) {q : Q} (hq : q ∈ hatS (O' := O') f) :
    ∃ s : S, ∃ x ∈ hatS (O' := O') f, q = f s + algebraMap O Q t ^ n * x := by
  induction hq using Algebra.adjoin_induction with
  | mem q hq =>
    obtain ⟨s, rfl⟩ := hq
    exact ⟨s, 0, Subalgebra.zero_mem _, by rw [mul_zero, add_zero]⟩
  | algebraMap r =>
    obtain ⟨c, y, hy⟩ := exists_pow_dense t h1 n r
    refine ⟨algebraMap O S c, algebraMap O' Q y, Subalgebra.algebraMap_mem _ y, ?_⟩
    rw [hy, map_add, map_mul, map_pow, AlgHom.commutes, IsScalarTower.algebraMap_apply O O' Q c,
      IsScalarTower.algebraMap_apply O O' Q t]
  | add a b _ _ ha hb =>
    obtain ⟨s, x, hx, rfl⟩ := ha
    obtain ⟨s', x', hx', rfl⟩ := hb
    exact ⟨s + s', x + x', Subalgebra.add_mem _ hx hx', by rw [map_add]; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨s, x, hx, rfl⟩ := ha
    obtain ⟨s', x', hx', rfl⟩ := hb
    refine ⟨s * s', f s * x' + x * f s' + algebraMap O Q t ^ n * x * x', ?_, by rw [map_mul]; ring⟩
    exact Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (mem_hatS f s) hx')
      (Subalgebra.mul_mem _ hx (mem_hatS f s')))
      (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (algebraMap_pow_mem_hatS f t n) hx) hx')

theorem isIntegral_of_mem_hatS [Algebra.IsIntegral O S] {q : Q} (hq : q ∈ hatS (O' := O') f) :
    IsIntegral O' q := by
  have hle : hatS (O' := O') f ≤ integralClosure O' Q := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, rfl⟩
    exact (IsIntegral.map f (Algebra.IsIntegral.isIntegral (R := O) s)).tower_top
  exact hle hq

end Approx

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2MVo =====
section

/-!
# S4-EtPBC-A, O2 (MV route), MVo: Mayer-Vietoris for an open `U ⊆ P` and `W : P.Etale`

* `toTop W : W ⟶ etId P`, `toTop_ext`; the fibre of `etId P` is a singleton (`topPt`, `fpt_topPt`);
* `opEt U := opn (etId P) U`: its fibre over `x̄` is subsingleton, nonempty iff `x ∈ U` (`opPt`, `mem_of_fib_opEt`);
* `prd_fib_ext`; `prW_bijective` (`x ∈ U`), `prT_bijective` (`x ∉ U`) for `prd W (opEt U)`;
* **`mvOpen_shortExact`**: `0 → Λ[W ×_P U] → Λ[W] ⊞ Λ[U] → Λ[P] → 0` is short exact when every `x ∉ U` has exactly
  one fibre point of `W` over `x̄`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo

universe u

variable {P : Scheme.{u}}

theorem fpt_topPt (x : P) (a : (geomPtAt x).point.fiber.obj (etId P)) : (fpt x a : P) = x := by
  rw [Subsingleton.elim a (topPt x)]
  exact center_geomPtAt x

instance subsingleton_fib_opEt (U : P.Opens) (x : P) : Subsingleton ((geomPtAt x).point.fiber.obj (opEt U)) :=
  ⟨fun b b' => fib_opn_injective (etId P) U x (Subsingleton.elim _ _)⟩

theorem mem_of_fib_opEt (U : P.Opens) (x : P) (b : (geomPtAt x).point.fiber.obj (opEt U)) : x ∈ U := by
  have h1 := opnι_mem (etId P) U (fpt x b)
  rw [← fib_left_map, fpt_topPt] at h1
  exact h1

theorem nonempty_fib_opEt (U : P.Opens) (x : P) (hx : x ∈ U) :
    Nonempty ((geomPtAt x).point.fiber.obj (opEt U)) := by
  have hv : (opnι (etId P) U).left (⟨x, hx⟩ : U) = fpt x (topPt x) :=
    (Scheme.Opens.ι_apply U ⟨x, hx⟩).trans (fpt_topPt x (topPt x)).symm
  obtain ⟨b, -, -⟩ := exists_lift_fib (opnι (etId P) U) x (topPt x) (⟨x, hx⟩ : U) hv
  exact ⟨b⟩

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fl =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero

For an etale `e : U ⟶ X` and `V : U.Etale`:
* `res e` is additive and exact (left and right adjoint);
* **`lshFreeIso`**: `Λ[e ∘ V] ≅ e_! Λ[V]`.
For `W : P.Etale`:
* **`freeLshIso`**: `Λ[W] ≅ e_! Λ_W` (`e = W.hom`);
* **`extFree`**: `Ext_P(Λ[W], F) ≃ H(W, F|_W)`, with `extFree_comp_mk₀` (natural in `F`) and `ext_free_eq_zero`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ]

section Free

end Free

section GenFl

universe w₁ v₁ u₁ v₂ u₂

theorem extAdjIsoGen_apply {C : Type u₁} [Category.{v₁} C] [Abelian C] {hC : HasExt.{w₁} C}
    {D : Type u₂} [Category.{v₂} D] [Abelian D] {hD : HasExt.{w₁} D} [EnoughInjectives D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] [L.PreservesMonomorphisms] {A : D} {U : C} (e : A ≅ L.obj U) (B : D) (n : ℕ)
    (β : Ext.{w₁} A B n) :
    extAdjIsoGen adj e B n β = extAdjMap adj U B n ((Ext.mk₀ e.inv).comp β (zero_add n)) :=
  rfl

end GenFl

section Obj

variable {P : Scheme.{u}}

/-- `e ∘ (terminal object) ≅ W` for `e = W.hom`. -/
def etCompTop (W : P.Etale) : (etComp W.hom).obj (etId W.left) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl _) rfl

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fl2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`

* `extAdjMap_mk₀_comp`: the adjunction map on `Ext` is natural in the source;
* `lshFreeHom_natural`, `lshFreeInv_natural`: `Λ[e ∘ V] ≅ e_! Λ[V]` is natural in `V`;
* `toW W V : e ∘ V ⟶ W` (`e = W.hom`, `V : W.left.Etale`), `extFreeV : Ext_P(Λ[e ∘ V], F) ≃ Ext_W(Λ[V], F|_W)`;
* **`extFreeV_restrict`**: restricting `β ∈ Ext_P(Λ[W], F)` along `toW W V` is restricting `extFree β ∈ H(W, F|_W)`
  to `V`; **`restrict_eq_zero`**: if `extFree β` dies on `V`, then `β` dies on `e ∘ V`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe w v v' u₁ u₂ u

section Adj

end Adj

variable {Λ : Type u} [CommRing Λ]

section Nat

end Nat

section Obj

variable {P : Scheme.{u}}

/-- `e ∘ V ⟶ W` for `V : W.left.Etale` (`e = W.hom`). -/
def toW (W : P.Etale) (V : W.left.Etale) : (etComp W.hom).obj V ⟶ W :=
  (etComp W.hom).map (toTop V) ≫ (etCompTop W).hom

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2D1 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M3 step (3): classes of `H²(Spec A, g_* N)` die on a basic open

`Y = Spec A` (`A` a noetherian integrally closed domain of dimension `≤ 1`), `g = gen A` its generic point.
* `bOpen f = D(f)`, `rD Λ f : Λ[D(f)] ⟶ Λ_Y` (restriction to `D(f)`);
* `exists_bOpen_zero`: a global section of a sheaf with zero stalks at non-closed points and at the generic point
  vanishes on some `D(f)`, `f ≠ 0` (finite support, `f` = product of elements of the supporting primes);
* **`push_two_dies`**: under `H²(η, -) = 0` and `R²g_* = 0`, every `β ∈ H²(Y, g_* N)` dies on some `D(f)`, `f ≠ 0`
  (`β` comes from a global section of `R¹g_* N` along `presB`, `presA`; that section vanishes on some `D(f)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.GenFrac

variable {A : Type} [CommRing A] [IsDomain A] {Λ : Type} [CommRing Λ]

/-- **A global section with zero germs at non-closed points and at the generic point vanishes on some `D(f)`,
`f ≠ 0`.** -/
theorem exists_bOpen_zero [IsNoetherianRing A] {G : EtSh Λ (Spec (CommRingCat.of A))}
    (hG : ∀ y : Spec (CommRingCat.of A), ¬ IsClosed ({y} : Set (Spec (CommRingCat.of A))) → IsZero (Cech.Mx G y))
    (h0 : IsZero (Cech.Mx G (GenBr.genPt A)))
    (σ : G.obj.obj (op (etId (Spec (CommRingCat.of A))))) :
    ∃ f : A, f ≠ 0 ∧ (G.obj.map (toTop (opEt (bOpen f))).op).hom σ = 0 := by
  have : IsAffine (etId (Spec (CommRingCat.of A))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hfin := Cech.finite_supp G hG σ
  have hne : ∀ t ∈ hfin.toFinset, ∃ g : A, g ∈ t.asIdeal ∧ g ≠ 0 := by
    intro t ht
    have htS := hfin.mem_toFinset.1 ht
    have hbot : t.asIdeal ≠ ⊥ := by
      intro hb
      obtain ⟨y, a, hya, hne⟩ := htS
      have hty : t = GenBr.genPt A := PrimeSpectrum.ext hb
      have hy : y = GenBr.genPt A := (fpt_topPt y a).symm.trans (hya.trans hty)
      subst hy
      apply hne
      exact congrArg (fun φ => φ.hom σ)
        (h0.eq_of_tgt ((geomPtAt (GenBr.genPt A)).point.toPresheafFiber _ a G.obj) 0)
    obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    exact ⟨g, hg, hg0⟩
  choose! g hg hg0 using hne
  obtain ⟨P, hP⟩ : ∃ P : A, P = ∏ t ∈ hfin.toFinset, g t := ⟨_, rfl⟩
  have hPmem : ∀ t ∈ hfin.toFinset, P ∈ t.asIdeal := by
    intro t ht
    rw [hP]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem g ht) (hg t ht)
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact Finset.prod_ne_zero_iff.2 fun t ht => hg0 t ht
  refine ⟨P, hP0, ?_⟩
  apply Cech.eq_zero_of_germs
  intro x a
  rw [Cech.germ_map]
  apply Cech.germ_eq_zero_of_not_mem_supp
  intro hmem
  have hx : x ∈ bOpen P := mem_of_fib_opEt _ x a
  rw [mem_bOpen] at hx
  have h2 := hPmem _ (hfin.mem_toFinset.2 hmem)
  have heq : (Cech.fpt x ((geomPtAt x).point.fiber.map (toTop (opEt (bOpen P))) a) :
      Spec (CommRingCat.of A)) = x := fpt_topPt x _
  rw [heq] at h2
  exact hx h2

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2D3 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`

* `A1.exists_closed_mem`: a nonzero `f ∈ k[X]` is a unit at some closed point (`k` infinite);
* `two_dies_A1`: the `k[X]` instance of `two_dies` (`k = k̄`, `ℓ ≠ char k`, `ℓ^m Λ = 0`);
* `chartEt k`: the chart `A¹ ⟶ P¹` as an étale object; `chart_dies`: `β ∈ Ext²(Λ_{P¹}, F)` dies on
  `chart ∘ D(f)` (restrict to the chart with `extFree`, apply `two_dies_A1`, come back with `restrict_eq_zero`);
* `U' k f := chart ''ᵁ D(f)`, `toU'`: `opEt (U' k f) ⟶ chart ∘ D(f)` (open immersion lift);
* **`claimD`**: every `β ∈ Ext²(Λ[P¹], F)` dies on the open `U' k f` of `P¹` for some `f ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.CurveHn

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ]

instance isOpenImmersion_chartComp (f : k[X]) :
    IsOpenImmersion ((etComp (chartEt k).hom).obj (opEt (bOpen f))).hom :=
  show IsOpenImmersion (((bOpen f).ι ≫ 𝟙 _) ≫ chartA1 k) from inferInstance

theorem range_U'_sub (f : k[X]) :
    Set.range (U' k f).ι ⊆ Set.range ((etComp (chartEt k).hom).obj (opEt (bOpen f))).hom := by
  rintro _ ⟨z, rfl⟩
  have hz : ((U' k f).ι z : P1 k) ∈ ((chartA1 k) ''ᵁ (bOpen f) : Set (P1 k)) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨z, rfl⟩
  obtain ⟨x, hx, hxz⟩ := hz
  refine ⟨(⟨x, hx⟩ : bOpen f), ?_⟩
  rw [← hxz]
  rfl

/-- `opEt (chart ''ᵁ D(f)) ⟶ chart ∘ D(f)`. -/
def toU' (f : k[X]) : opEt (U' k f) ⟶ (etComp (chartEt k).hom).obj (opEt (bOpen f)) :=
  MorphismProperty.Over.homMk (IsOpenImmersion.lift _ (U' k f).ι (range_U'_sub k f))
    ((IsOpenImmersion.lift_fac _ _ _).trans (Category.comp_id _).symm)

section GenDies

universe w₁ v₁ u₁

end GenDies

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2M4b =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M4 (b): every class of `H²(P¹, F)` is a Mayer-Vietoris class

* `exists_good_opn`: an etale object `N` with chosen fibre points `n z` over a finite set `Zs` of closed points
  (Galois-trivial) has an open `V ⊆ N` whose geometric fibre over every `z ∈ Zs` is a singleton (remove the closed
  discrete set `N⁻¹(Zs) ∖ {fpt (n z)}`);
* `genPt_mem_U'`, `isClosed_of_not_mem_U'`, `finite_compl_U'`: `P¹ ∖ chart(D(f))` is a finite set of closed points;
* **`mv_two`** (M4): for every `β ∈ Ext²(Λ[P¹], F)` there are `f ≠ 0` and an MV-good `W` for the open `U' k f`
  with `β|_W = 0` and `β = ε ∘ κ`, `ε` the MV class of `0 → Λ[W ×_P U'] → Λ[W] ⊞ Λ[U'] → Λ → 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtPBC.GenGeo

section Shrink

universe u

end Shrink

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ]

theorem genPt_mem_U' (f : k[X]) (hf : f ≠ 0) : P1.genPt k ∈ U' k f := by
  have hmem : GenBr.genPt k[X] ∈ bOpen f := by
    refine (mem_bOpen f _).2 ?_
    change f ∉ (⊥ : Ideal k[X])
    rwa [Submodule.mem_bot]
  rw [← map_genPt k k[X] (chartA1 k)]
  exact Set.mem_image_of_mem _ hmem

theorem isClosed_of_not_mem_U' (f : k[X]) (hf : f ≠ 0) (x : P1 k) (hx : x ∉ U' k f) :
    IsClosed ({x} : Set (P1 k)) :=
  P1.isClosed_of_ne_genPt k x (fun h => hx (h ▸ genPt_mem_U' k f hf))

end RamanujanPetersson.EtPBC.EtMV

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

/-- **Shrinking to one point over `z`** and nothing else over a finite closed set `Zs ∋ z`. -/
theorem exists_good_one (Zs : Set P) (hZf : Zs.Finite) (hZc : ∀ x ∈ Zs, IsClosed ({x} : Set P))
    (z : P) (hz : z ∈ Zs) (hG : Subsingleton (Gal z)) (N : P.Etale) (n : (geomPtAt z).point.fiber.obj N) :
    ∃ V : N.left.Opens, Subsingleton ((geomPtAt z).point.fiber.obj (opn N V)) ∧
      Nonempty ((geomPtAt z).point.fiber.obj (opn N V)) ∧
      ∀ v : (opn N V).left, (opn N V).hom v ∉ Zs ∨ (opn N V).hom v = z := by
  let y : N.left := fpt z n
  have hy : N.hom y = z := fib_over z n
  let D : Set N.left := N.hom ⁻¹' Zs
  have hDe : D = ⋃ x ∈ Zs, N.hom ⁻¹' {x} := by
    ext t
    simp [D]
  have hDd : _root_.IsDiscrete D := by
    rw [hDe]
    exact _root_.IsDiscrete.biUnion hZf (fun x _ => N.hom.isDiscrete_preimage_singleton x)
      (fun x hx => (hZc x hx).preimage N.hom.continuous)
  have hZcl : IsClosed Zs := by
    have h := hZf.isClosed_biUnion hZc
    rwa [Set.biUnion_of_singleton] at h
  have hDc : IsClosed D := hZcl.preimage N.hom.continuous
  let S : Set N.left := D \ {y}
  have hSc : IsClosed S := isClosed_of_subset_discrete_closed Set.sdiff_subset hDd hDc
  let V : N.left.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  have hyV : y ∈ V := fun h => h.2 rfl
  have := hG
  have key : ∀ c : (geomPtAt z).point.fiber.obj (opn N V),
      fpt z ((geomPtAt z).point.fiber.map (opnι N V) c) = y := by
    intro c
    have h1 : fpt z ((geomPtAt z).point.fiber.map (opnι N V) c) ∈ V := opnι_mem N V (fpt z c)
    have h2 : fpt z ((geomPtAt z).point.fiber.map (opnι N V) c) ∉ S := h1
    have ht : N.hom (fpt z ((geomPtAt z).point.fiber.map (opnι N V) c)) = z := fib_over z _
    have htD : fpt z ((geomPtAt z).point.fiber.map (opnι N V) c) ∈ D := by
      show N.hom _ ∈ Zs
      rw [ht]
      exact hz
    by_contra hne
    exact h2 ⟨htD, hne⟩
  refine ⟨V, ⟨fun b b' => fib_opn_injective N V z (fiber_eq_of_pt z _ _ ((key b).trans (key b').symm))⟩, ?_, ?_⟩
  · obtain ⟨b, -, -⟩ := exists_lift_fib (opnι N V) z n (⟨y, hyV⟩ : V) (Scheme.Opens.ι_apply V ⟨y, hyV⟩)
    exact ⟨b⟩
  · intro v
    by_cases hv : (opn N V).hom v ∈ Zs
    · right
      have h1 : (opnι N V).left v ∈ V := opnι_mem N V v
      have hu : (opnι N V).left v = y := by
        by_contra hne
        exact h1 ⟨hv, hne⟩
      show N.hom ((opnι N V).left v) = z
      rw [hu, hy]
    · exact Or.inl hv

end Gen

section P1

end P1

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2S2 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die

* `prdMap d X : prd D₁ X ⟶ prd D X` for `d : D₁ ⟶ D`, `prdMap_prW`, `prdMap_prT`;
* **`locC_shrink`**: `ε_loc(D₁) ∘ Λ[prdMap d] = ε_loc(D)`; **`locCls_shrink`**: the class of `κ` through `D` is the
  class of its pullback through `D₁`; `opn_sub`, `opn_nonempty`, `opn_range`, **`isLoc_opn`** (an open of `D`
  containing the points over `z` gives the same class);
* **`mv_res_W`**, **`mv_res_U`**: `ε ∘ Λ[p₁]^* γ = 0`, `ε ∘ Λ[p₂]^* γ = 0` for any MV square; `loc_res_D`,
  `loc_res_U` (the one-point case).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

section Prd

end Prd

section Shrink

end Shrink

section Opn

variable (D : P.Etale) (V : D.left.Opens) (z : P)

theorem opn_sub (hD : Subsingleton ((geomPtAt z).point.fiber.obj D)) :
    Subsingleton ((geomPtAt z).point.fiber.obj (opn D V)) :=
  ⟨fun _ _ => fib_opn_injective D V z (Subsingleton.elim _ _)⟩

end Opn

section Res

end Res

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km3 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km3): an etale algebra over a PID splits into Dedekind domains

`C` a commutative ring whose localizations at maximal ideals are domains.
* `isReduced_of_loc`, `eq_of_le_max`: two minimal primes inside one maximal ideal agree;
* `isCoprime_minimalPrimes`, `iInf_minimalPrimes`;
* **`piEquiv h : C ≃+* Π p : minimalPrimes C, C ⧸ p`** (`piEquiv_apply` is `rfl`);
* **`isDomain_loc_of_etale`**: for `C` etale over a Jacobson PID `A` (not a field) every `C_m` is a domain;
* **`isDedekindDomain_quot`**: for a minimal prime `p` of such `C`, `C ⧸ p` is a Dedekind domain.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC.EtDed

section Dec

variable {C : Type*} [CommRing C] (h : ∀ (m : Ideal C) [m.IsMaximal], IsDomain (Localization.AtPrime m))

include h in
theorem isCoprime_minimalPrimes :
    Pairwise (Function.onFun IsCoprime (Subtype.val : minimalPrimes C → Ideal C)) := by
  intro p p' hne
  rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
  by_contra hne'
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne'
  exact hne (Subtype.ext (eq_of_le_max h p.2 p'.2 m hm (le_sup_left.trans hle) (le_sup_right.trans hle)))

include h in
theorem iInf_minimalPrimes : ⨅ p : minimalPrimes C, (p : Ideal C) = ⊥ := by
  have := isReduced_of_loc h
  rw [← sInf_eq_iInf']
  change sInf (⊥ : Ideal C).minimalPrimes = ⊥
  rw [Ideal.sInf_minimalPrimes]
  exact nilradical_eq_zero C

variable [IsNoetherianRing C]

/-- **`C ≅ Π_p C ⧸ p`** over the minimal primes. -/
def piEquiv : C ≃+* Π p : minimalPrimes C, C ⧸ (p : Ideal C) :=
  RingEquiv.ofBijective (RingHom.pi fun p : minimalPrimes C => Ideal.Quotient.mk (p : Ideal C))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have hmem : x ∈ ⨅ p : minimalPrimes C, (p : Ideal C) := by
        rw [Submodule.mem_iInf]
        intro p
        exact Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hx p)
      rw [iInf_minimalPrimes h] at hmem
      exact (Submodule.mem_bot C).1 hmem,
    fun y => by
      obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective (isCoprime_minimalPrimes h) y
      exact ⟨r, funext hr⟩⟩

theorem piEquiv_apply (x : C) (p : minimalPrimes C) : piEquiv h x p = Ideal.Quotient.mk (p : Ideal C) x := rfl

end Dec

section Et

end Et

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2P1 =====
section

/-!
# S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)

`B` Dedekind with fraction field `K`, `Bt = B[1/t]`, `(t)` prime.

* `locPt p hp`: the height-one prime `p Bt` of a localization; `valuation_locPt` (same valuation on `K`);
* `dvd_log_of_mem_maxUnram`: a root `α ∈ maxUnram Bt K` of `u ∈ K` gives `d ∣ log v_p(u)` for `t ∉ p`;
* `valuation_algebraMap_bot`, `root_mem_maxUnram_self`: `d ∣ log v(u)` at every height-one prime of `B` puts every
  `d`-th root of `u` in `maxUnram B K` (`root_mem_maxUnram_of_dvd` with `M = ⊥`, model `B`);
* `exists_root_unit`: `d`-th roots of units of `B` lie in `maxUnram B K`;
* **`root_mem_maxUnram_twist`**: for `α ∈ maxUnram Bt K` with `α ^ d = u`, there is `m : ℤ` such that every `d`-th root
  of `u t^m` lies in `maxUnram B K`.
-/

set_option autoImplicit false

open IsDedekindDomain

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer

section VC

variable {B Bt K : Type} [CommRing B] [IsDedekindDomain B] [CommRing Bt] [IsDedekindDomain Bt] [Algebra B Bt]
  (S : Submonoid B) [IsLocalization S Bt] (hS : S ≤ nonZeroDivisors B)
  [Field K] [Algebra B K] [Algebra Bt K] [IsScalarTower B Bt K] [IsFractionRing B K] [IsFractionRing Bt K]

theorem intValuation_locPt (p : HeightOneSpectrum B) (hp : Disjoint (S : Set B) p.asIdeal) (b : B) :
    (locPt S hS p hp).intValuation (algebraMap B Bt b) = p.intValuation b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hb' : algebraMap B Bt b ≠ 0 := fun h => hb (IsLocalization.injective Bt hS (h.trans (map_zero _).symm))
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hb,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hb']
  congr 3
  apply multiplicity_eq_of_emultiplicity_eq
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff,
    Set.singleton_subset_iff]
  show algebraMap B Bt b ∈ (p.asIdeal.map (algebraMap B Bt)) ^ n ↔ b ∈ p.asIdeal ^ n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← Ideal.map_pow, ← Ideal.mem_comap]
  have hprim : (p.asIdeal ^ n).IsPrimary := by
    refine Ideal.isPrimary_of_isMaximal_radical ?_
    rw [Ideal.radical_pow _ hn.ne', p.isPrime.radical]
    exact p.isMaximal
  have hdisj : Disjoint (S : Set B) ↑(p.asIdeal ^ n) :=
    hp.mono_right (Ideal.pow_le_self hn.ne')
  rw [show Ideal.comap (algebraMap B Bt) (Ideal.map (algebraMap B Bt) (p.asIdeal ^ n)) = p.asIdeal ^ n from
    IsLocalization.under_map_of_isPrimary_disjoint S Bt hprim hdisj]

end VC

section Root

end Root

section Twist

end Twist

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N3 =====
section

/-!
# S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map

* `kchar_transport` (field theory): two Kummer characters agree when the two groups act compatibly through
  embeddings `e : L → Ω`, `e' : L' → Ω` and one `σ ∈ Aut Ω`, `e ζ = e' ζ'` is fixed by `σ` and `e (γ^N) = e' (γ'^N)`;
* `val_add_smul`, `kumChi hζ γ c : τ ↦ (kchar γ τ).val • c` (an additive locally constant character when
  `N • c = 0`): `kumChi_mul`, `kumChi_isLocallyConstant`;
* `sepX g h`, `resMapX g h` for `h : g y = x` (`sepE`, `residueFieldMap` transported), `galTrX_apply`,
  `sepX_algebraMap`;
* **`resLE_kappaL_kum`** (NAT for Kummer classes): `resLE g 1 (κ (kumChi ζ γ c)) = κ (kumChi ζ' γ' c)` when
  `sepX (ζ) = ζ'` and `sepX (γ^N) = γ'^N` in `κ(η')^sep`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer

section KumTr

end KumTr

section KumChi

variable {K E : Type} [Field K] [Field E] [Algebra K E] {N : ℕ} [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N)
  {Λ : Type} [AddCommGroup Λ]

theorem kumChi_mul (hζΓ : ∀ σ ∈ (⊤ : Subgroup (E ≃ₐ[K] E)), σ ζ = ζ) {γ : Eˣ}
    (hγ : γ ∈ rad (⊤ : Subgroup (E ≃ₐ[K] E)) N) {c : Λ} (hc : N • c = 0) (a b : E ≃ₐ[K] E) :
    kumChi hζ γ c (a * b) = kumChi hζ γ c a + kumChi hζ γ c b := by
  unfold kumChi
  rw [show (⟨a * b, Subgroup.mem_top _⟩ : (⊤ : Subgroup (E ≃ₐ[K] E))) =
      ⟨a, Subgroup.mem_top _⟩ * ⟨b, Subgroup.mem_top _⟩ from rfl, kchar_mul hζ hζΓ hγ, val_add_smul hc]

theorem kumChi_isLocallyConstant [Algebra.IsIntegral K E] (γ : Eˣ) (c : Λ) : IsLocallyConstant (kumChi (K := K) hζ γ c) :=
  ((isLocallyConstant_kchar hζ (Γ := ⊤) γ).comp_continuous
    (Continuous.subtype_mk continuous_id (fun τ => Subgroup.mem_top τ))).comp (fun k : ZMod N => k.val • c)

end KumChi

section Sep

universe u

end Sep

section KumNat

end KumNat

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

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (Λ : Type) [AddCommGroup Λ]

variable {A K Λ}

variable {N : ℕ} [NeZero N] {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ ζ = ζ) {τ : (maxUnram A K)ˣ}
  (hτ : τ ∈ rad (⊤ : Subgroup (Pi1 A K)) N) (hΛ : ∀ x : Λ, N • x = 0)

/-- `c ↦ kumChi ζ τ c` as an additive map into the character group. -/
def kumTau : Λ →+ ChL A K Λ :=
  AddMonoidHom.mk' (fun c => ⟨kumChi hζ τ c, mem_ChL.2 ⟨kumChi_mul hζ hζΓ hτ (hΛ c), kumChi_isLocallyConstant hζ τ c⟩⟩)
    (fun _ _ => Subtype.ext (funext fun _ => smul_add _ _ _))

end ChL

section KappaLH

end KappaLH

section ResH

universe u

end ResH

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E5 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)

* generic: **`mapExact_comp_iso`**: for exact `Φ`, `Ψ`, `Φ'` and `τ : Φ ⋙ Ψ ≅ Φ'`, `Ψ(Φ ξ) ∘ τ_B = τ_A ∘ Φ' ξ`
  on `Ext¹` (enough injectives);
* for `m : W' ⟶ W` in `P.Etale`: `Etale m.left`, `etCompCompIso m`, `resCompIso Λ m : res W ⋙ res m ≅ res W'`;
* `diagSec Λ W : Λ_W ⟶ Λ[W]|_W` with `extFree_eq` (`extFree β = diagSec ∘ β|_W`) and `diagSec_sec`;
* **`diagSec_natural`**: `diagSec W' ≫ Λ[m]|_W' = unitRes m.left ≫ (diagSec W)|_W' ≫ (resCompIso m)_{Λ[W]}`.
`extFree_natural` is in O2E5b.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg

section Gen

universe w v₁ u₁ v₂ u₂ v₃ u₃

end Gen

section Nat

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {W W' : P.Etale} (m : W' ⟶ W)

/-- `etComp m.left ⋙ etComp W.hom ≅ etComp W'.hom` (identity on underlying schemes). -/
def etCompCompIso : etComp m.left ⋙ etComp W.hom ≅ etComp W'.hom :=
  NatIso.ofComponents
    (fun V => MorphismProperty.Over.isoMk (Iso.refl _)
      (by
        change 𝟙 _ ≫ V.hom ≫ W'.hom = (V.hom ≫ m.left) ≫ W.hom
        rw [Category.id_comp, Category.assoc, MorphismProperty.Over.w m]))
    (fun f => MorphismProperty.Over.Hom.ext
      (by exact (Category.comp_id _).trans (Category.id_comp _).symm))

variable (Λ) in
/-- **`res W.hom ⋙ res m.left ≅ res W'.hom`.** -/
def resCompIso : res W.hom Λ ⋙ res m.left Λ ≅ res W'.hom Λ :=
  haveI : (etComp m.left).IsContinuous W'.left.smallEtaleTopology W.left.smallEtaleTopology :=
    etComp_cont m.left
  haveI : (etComp W.hom).IsContinuous W.left.smallEtaleTopology P.smallEtaleTopology := etComp_cont W.hom
  haveI : (etComp W'.hom).IsContinuous W'.left.smallEtaleTopology P.smallEtaleTopology := etComp_cont W'.hom
  Functor.sheafPushforwardContinuousComp' (etCompCompIso m) (ModuleCat.{u} Λ)
    W'.left.smallEtaleTopology W.left.smallEtaleTopology P.smallEtaleTopology

theorem resCompIso_app (G : EtSh Λ P) (V : W'.left.Etale)
    (x : (((res m.left Λ).obj ((res W.hom Λ).obj G)).obj.obj (op V))) :
    (((resCompIso Λ m).hom.app G).hom.app (op V)).hom x =
      (G.obj.map ((etCompCompIso m).inv.app V).op).hom x :=
  rfl

end Nat

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E5b =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d0b: `extFree` is natural in the etale object (degree 1)

**`extFree_natural`**: for `m : W' ⟶ W` in `P.Etale` and `ξ : Ext¹_P(Λ[W], F)`,
`extFree W' (ξ ∘ Λ[m]) = (resHE m.left (extFree W ξ)) ∘ (resCompIso m)_F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg

section Gen

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {Cp : Type u₁} [Category.{v₁} Cp] [Abelian Cp] {hCp : HasExt.{w} Cp} [EnoughInjectives Cp]
  {Cw : Type u₂} [Category.{v₂} Cw] [Abelian Cw] {hCw : HasExt.{w} Cw}
  {Cw' : Type u₃} [Category.{v₃} Cw'] [Abelian Cw'] {hCw' : HasExt.{w} Cw'}

/-- Generic `extFree_natural`. -/
theorem extFree_natural_gen {L : Cw ⥤ Cp} {R : Cp ⥤ Cw} (adj : L ⊣ R) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] [L.PreservesMonomorphisms]
    {L' : Cw' ⥤ Cp} {R' : Cp ⥤ Cw'} (adj' : L' ⊣ R') [R'.Additive] [PreservesFiniteLimits R']
    [PreservesFiniteColimits R'] [L'.PreservesMonomorphisms]
    (Ψ : Cw ⥤ Cw') [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ] (τ : R ⋙ Ψ ≅ R')
    {A A' B : Cp} {U : Cw} {U' : Cw'} (e : A ≅ L.obj U) (e' : A' ≅ L'.obj U') (f : A' ⟶ A) (u : U' ⟶ Ψ.obj U)
    (h : adj'.homEquiv U' A' e'.inv ≫ R'.map f = u ≫ Ψ.map (adj.homEquiv U A e.inv) ≫ τ.hom.app A)
    (ξ : Ext.{w} A B 1) :
    ((extIsoLeft e'.symm B 1).trans (extAdjEquiv adj' U' B 1)) ((Ext.mk₀ f).comp ξ (zero_add 1)) =
      (mapExtU Ψ u (R.obj B) 1 (((extIsoLeft e.symm B 1).trans (extAdjEquiv adj U B 1)) ξ)).comp
        (Ext.mk₀ (τ.hom.app B)) (add_zero 1) := by
  rw [extAdj_eq_gen adj' e', extAdj_eq_gen adj e, mapExtU_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc,
    Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (by simp), mapExact_comp_iso R Ψ τ, Ext.mk₀_comp_mk₀_assoc, h]
  simp only [Category.assoc]

end Gen

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km4 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km4): `H¹` of an affine scheme whose ring is a product of Dedekind domains

* `piHom e k : Spec (R k) ⟶ X`, `piS e k : X.Etale` for a ring isomorphism `e : Γ(X, ⊤) ≃+* Π k, R k`;
  `cop_piS_hom`, `IsIso (cop (piS e)).hom` (via `sigmaSpec`);
* `kapS h Λ p χ = pr_p^* (extFreeU⁻¹ (κ(χ)))`: the Kummer class of a character `χ` of `π₁(Γ ⧸ p)` as a class
  in `H¹(X, Λ)` (`Γ = Γ(X, ⊤)` noetherian, localizations at maximal ideals domains, `p` a minimal prime);
  `kapS_apply`. The decomposition theorem `h1_exists_kappa` is in O2Km4b (split for the kernel budget).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur

universe u

section PiS

variable {X : Scheme.{u}} [IsAffine X] {ι : Type u} {R : ι → Type u} [∀ k, CommRing (R k)]
  (e : Γ(X, ⊤) ≃+* Π k, R k)

instance isOpenImmersion_piHom (k : ι) : IsOpenImmersion (piHom e k) := by
  unfold piHom
  infer_instance

/-- The pieces as etale `X`-schemes. -/
def piS (k : ι) : X.Etale := Scheme.Etale.mk (piHom e k)

theorem cop_piS_hom : (cop (piS e)).hom =
    sigmaSpec (fun k => CommRingCat.of (R k)) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.isoSpec.inv := by
  refine Sigma.hom_ext _ _ fun k => ?_
  have h1 : Sigma.ι (fun k => (piS e k).left) k ≫ (cop (piS e)).hom = piHom e k :=
    Sigma.ι_desc (fun k => (piS e k).hom) k
  have h2 := ι_sigmaSpec_assoc (fun k => CommRingCat.of (R k)) k
    (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.isoSpec.inv)
  exact h1.trans h2.symm

end PiS

section GenKap
universe w v₁ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {hC : HasExt.{w} C}

theorem precompSymmGen_apply {A B Z : C} (u : A ⟶ B) {M : Type u₂} {N : Type u₃} [AddCommGroup M]
    [AddCommGroup N] (e : Ext.{w} B Z 1 ≃+ N) (κ : M →+ N) (x : M) :
    precompSymmGen u e κ x = (Ext.mk₀ u).comp (e.symm (κ x)) (zero_add 1) :=
  rfl

end GenKap

section Kappa

end Kappa

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl1b =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl1b): the algebra of stages S1-S2

GLOB/REL PLAN v1, stages S1-S2 (pure algebra). `Q = Π_p Frac(G ⧸ p)` over the minimal primes of `G` (`G = Γ(W₁)`).
* `exists_pow_mul_mem_hatS` (Gen): if `L^N • y ∈ S` for every `y` and `L = t^e L'` with `L'` a unit in `O'`, then every
  `q ∈ O'[F Y]` has `t^N q ∈ hatS (F|_S)`;
* `mem_adjoin_map`: `O'`-algebra maps carry `O'[F₀ Y]` into `O'[ψ F₀ Y]`;
* `pow_mul_div_mem_range`: `x ∣ τ^e w₁`, `y ∣ τ^e' w₂` (`wᵢ` units) ⇒ `τ^(e+e') (x/y)^{±1}` are integral elements;
* `toPiQ`, `exists_toPiQ_update`: CRT over the pieces (`piEquiv`, O2Km3);
* **`exists_glob_approx`** (S1 + S2): `f u_S = t^N ũ (1 - t z)`, `ũ = (u₁ on p₀, 1 elsewhere)`, `z ∈ hatS`,
  `u_S ≡ r_i mod J_i`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Gen

variable {O O' Y Q : Type*} [CommRing O] [CommRing O'] [CommRing Y] [CommRing Q]
  [Algebra O O'] [Algebra O Y] [Algebra O' Q] [Algebra O Q] [IsScalarTower O O' Q]

theorem exists_pow_mul_mem_hatS (S : Subalgebra O Y) (F : Y →ₐ[O] Q) (t : O) {L L' : O} {e : ℕ}
    (hL : L = t ^ e * L') (hL' : IsUnit (algebraMap O O' L')) (hS : ∀ y : Y, ∃ N : ℕ, L ^ N • y ∈ S)
    {q : Q} (hq : q ∈ Algebra.adjoin O' (Set.range F)) :
    ∃ N : ℕ, algebraMap O Q t ^ N * q ∈ hatS (O' := O') (F.comp S.val) := by
  induction hq using Algebra.adjoin_induction with
  | mem q hq =>
    obtain ⟨y, rfl⟩ := hq
    obtain ⟨N, hN⟩ := hS y
    obtain ⟨w, hw⟩ := hL'.pow N
    have h1 : F (L ^ N • y) ∈ hatS (O' := O') (F.comp S.val) := mem_hatS (F.comp S.val) ⟨_, hN⟩
    have hw' : algebraMap O' Q (↑w⁻¹ : O') * algebraMap O Q L' ^ N = 1 := by
      rw [IsScalarTower.algebraMap_apply O O' Q L', ← map_pow, ← hw, ← map_mul, Units.inv_mul, map_one]
    have key : algebraMap O Q t ^ (e * N) * F y = algebraMap O' Q (↑w⁻¹ : O') * F (L ^ N • y) := by
      rw [map_smul, Algebra.smul_def, hL, mul_pow, map_mul]
      simp only [map_pow]
      rw [pow_mul]
      linear_combination (-((algebraMap O Q t ^ e) ^ N * F y)) * hw'
    exact ⟨e * N, key ▸ Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) h1⟩
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add a b _ _ ha hb =>
    obtain ⟨N₁, h₁⟩ := ha
    obtain ⟨N₂, h₂⟩ := hb
    refine ⟨N₁ + N₂, ?_⟩
    have e : algebraMap O Q t ^ (N₁ + N₂) * (a + b) = algebraMap O Q t ^ N₂ * (algebraMap O Q t ^ N₁ * a) +
        algebraMap O Q t ^ N₁ * (algebraMap O Q t ^ N₂ * b) := by ring
    rw [e]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (algebraMap_pow_mem_hatS _ t N₂) h₁)
      (Subalgebra.mul_mem _ (algebraMap_pow_mem_hatS _ t N₁) h₂)
  | mul a b _ _ ha hb =>
    obtain ⟨N₁, h₁⟩ := ha
    obtain ⟨N₂, h₂⟩ := hb
    refine ⟨N₁ + N₂, ?_⟩
    have e : algebraMap O Q t ^ (N₁ + N₂) * (a * b) =
        (algebraMap O Q t ^ N₁ * a) * (algebraMap O Q t ^ N₂ * b) := by ring
    rw [e]
    exact Subalgebra.mul_mem _ h₁ h₂

end Gen

section Frac

end Frac

section PiQ

end PiQ

section Glob

end Glob

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2a =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3

GLOB/REL PLAN v1, stage S3 (pure algebra).
* `isUnit_of_mul_eq_one_of_isIntegral`: `t z = 1` with `z` integral over `R ↪ K` makes `t` a unit (so `1 - t z ≠ 0`
  for `z ∈ hatS` when `t` is not a unit);
* `liveIdem`, `liveMod`: on a reduced Noetherian `Y` (`Y ≅ Π Y ⧸ Q`), `x' := v + (x - v) e_live` with `e_live` the
  idempotent of the pieces where `x` is not identically zero; `liveMod_notMem` / `mem_nonZeroDivisors_of_notMem`
  (`x'` is a non-zero-divisor when `v` is), `map_liveMod` (`κ x' = κ x` for every `κ` into a domain with `κ x ≠ 0`),
  `liveMod_mem_integralClosure`;
* `exists_glob_approx'`: `exists_glob_approx` with `N` chosen before the CRT targets `r`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Inv

end Inv

section Live

variable {Y : Type*} [CommRing Y] (h : ∀ (m : Ideal Y) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [IsNoetherianRing Y]

open Classical in
/-- The idempotent of the pieces where `x` is not identically zero. -/
def liveIdem (x : Y) : Y := (piEquiv h).symm fun Q => if x ∈ (Q : Ideal Y) then 0 else 1

open Classical in
theorem liveIdem_mk (x : Y) (Q : minimalPrimes Y) :
    Ideal.Quotient.mk (Q : Ideal Y) (liveIdem h x) = if x ∈ (Q : Ideal Y) then 0 else 1 := by
  have e := congrFun ((piEquiv h).apply_symm_apply (fun Q : minimalPrimes Y => if x ∈ (Q : Ideal Y) then
    (0 : Y ⧸ (Q : Ideal Y)) else 1)) Q
  rw [piEquiv_apply] at e
  exact e

include h in
theorem mem_nonZeroDivisors_of_notMem (y : Y) (hy : ∀ Q : minimalPrimes Y, y ∉ (Q : Ideal Y)) : y ∈ Y⁰ := by
  refine mem_nonZeroDivisors_iff_right.2 fun z hz => (piEquiv h).injective (funext fun Q => ?_)
  rw [piEquiv_apply, map_zero, Pi.zero_apply]
  have h1 : Ideal.Quotient.mk (Q : Ideal Y) z * Ideal.Quotient.mk (Q : Ideal Y) y = 0 := by
    rw [← map_mul, hz, map_zero]
  exact (mul_eq_zero.1 h1).resolve_right fun h0 => hy Q (Ideal.Quotient.eq_zero_iff_mem.1 h0)

end Live

section Glob'

end Glob'

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km5 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km5): global sections of an affine scheme etale over `Spec A`

`X` affine, `g : X ⟶ Spec A` etale.
* `gamAlg g : Algebra A Γ(X, ⊤)` (through `ΓSpecIso` and `g.appTop`), **`etale_gamAlg`**;
* `isNoetherianRing_gam`; for a Jacobson PID `A` (not a field): **`isDomain_loc_gam`** (localizations at maximal
  ideals are domains) and **`isDedekindDomain_gam`** (`Γ ⧸ p` is Dedekind for minimal primes `p`) — the hypotheses
  of `h1_exists_kappa` (O2Km4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

universe u

section Gam

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (CommRingCat.of A)) [Etale g]

theorem etale_gamAlg : @Algebra.Etale A Γ(X, ⊤) _ _ (gamAlg g) := by
  letI := gamAlg g
  rw [← RingHom.etale_algebraMap]
  have h1 : (g.appTop).hom.Etale := (HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 inferInstance
  exact ((HasRingHomProperty.isLocal_ringHomProperty @Etale).respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv g.appTop).2 h1

include g in
theorem isNoetherianRing_gam [IsNoetherianRing A] : IsNoetherianRing Γ(X, ⊤) := by
  letI := gamAlg g
  have := etale_gamAlg g
  exact Algebra.FiniteType.isNoetherianRing A Γ(X, ⊤)

end Gam

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree

* `shObj s`, `shι s`: a map `s : N ⟶ W` of etale `P`-schemes gives a sheet `N ⟶ N ×_P W` over `W`.
* `sheet_cover`: sheets that biject onto every geometric fibre cover `N ×_P W`; `sheet_sep`: distinct sheets
  do not meet; `shι_cancel`.
* **`push_epi`**: if `W` is quasi-compact separated etale over `P` with `n` points in every geometric fibre, then
  `push W.hom` preserves epimorphisms (stalk lifts on a splitting neighbourhood, glued over the sheets), and
  **`push_preservesFiniteColimits_of_deg`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

section Sheet

variable {W N : P.Etale}

/-- The sheet as a map of etale `W`-schemes into `N ×_P W`. -/
def shι (s : N ⟶ W) : shObj s ⟶ (etPull W.hom).obj N :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 _) s.left (sh_lift_w s)) (pullback.lift_snd _ _ _)

theorem shι_left (s : N ⟶ W) : (shι s).left = pullback.lift (𝟙 _) s.left (sh_lift_w s) := rfl

/-- Two maps into the sheets agree on `N` and on `W`. -/
theorem lift_eq {S : Scheme.{u}} {s s' : N ⟶ W} (a b : S ⟶ N.left)
    (hab : a ≫ pullback.lift (𝟙 N.left) s.left (sh_lift_w s) =
      b ≫ pullback.lift (𝟙 N.left) s'.left (sh_lift_w s')) :
    a = b ∧ a ≫ s.left = b ≫ s'.left := by
  have h1 := congrArg (· ≫ pullback.fst N.hom W.hom) hab
  have h2 := congrArg (· ≫ pullback.snd N.hom W.hom) hab
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at h1 h2
  exact ⟨h1, h2⟩

theorem shι_cancel (s : N ⟶ W) {Z : W.left.Etale} (g g' : Z ⟶ shObj s) (h : g ≫ shι s = g' ≫ shι s) :
    g = g' :=
  MorphismProperty.Over.Hom.ext (lift_eq (s := s) (s' := s) g.left g'.left (congrArg (fun φ => φ.left) h)).1

/-- **Distinct sheets do not meet.** -/
theorem sheet_sep {ι : Type*} (σ : ι → (N ⟶ W))
    (hsep : ∀ (S : Scheme.{u}) (g : S ⟶ N.left) (p q : ι), g ≫ (σ p).left = g ≫ (σ q).left → ∀ _ : S, p = q)
    {p q : ι} {Z : W.left.Etale} (gi : Z ⟶ shObj (σ p)) (gj : Z ⟶ shObj (σ q))
    (h : gi ≫ shι (σ p) = gj ≫ shι (σ q)) (z : Z.left) : p = q := by
  have hl := lift_eq (s := σ p) (s' := σ q) gi.left gj.left (congrArg (fun φ => φ.left) h)
  exact hsep Z.left gi.left p q (hl.2.trans (congrArg (· ≫ (σ q).left) hl.1.symm)) z

end Sheet

section Lift

variable {W N : P.Etale}

/-- A map into a sheet, as a map of etale `P`-schemes. -/
def upP {s : N ⟶ W} {V : W.left.Etale} (g : V ⟶ shObj s) : (etComp W.hom).obj V ⟶ N :=
  MorphismProperty.Over.homMk g.left (by
    show g.left ≫ N.hom = V.hom ≫ W.hom
    exact (congrArg (g.left ≫ ·) (sh_w s).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ W.hom) (MorphismProperty.Over.w g))))

/-- Restriction of a map into a sheet along `c : M ⟶ N`. -/
def dnW {s : N ⟶ W} {V : W.left.Etale} (g : V ⟶ shObj s) {M : P.Etale} (c : M ⟶ N)
    (h : M ⟶ (etComp W.hom).obj V) (hc : h ≫ upP g = c) : shObj (c ≫ s) ⟶ V :=
  MorphismProperty.Over.homMk h.left (by
    have h1 : h.left ≫ g.left = c.left := congrArg (fun φ => φ.left) hc
    show h.left ≫ V.hom = (c ≫ s).left
    exact (congrArg (h.left ≫ ·) (MorphismProperty.Over.w g).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ s.left) h1)))

theorem lift_comp_core {M : P.Etale} (c : M ⟶ N) (s : N ⟶ W) :
    c.left ≫ pullback.lift (𝟙 N.left) s.left (sh_lift_w s) =
      pullback.lift (𝟙 M.left) (c ≫ s).left (sh_lift_w (c ≫ s)) ≫
        pullback.lift (pullback.fst M.hom W.hom ≫ c.left) (pullback.snd M.hom W.hom)
          (by rw [Category.assoc, ← sh_w c, pullback.condition]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, Category.id_comp]
  · simp only [Category.assoc, pullback.lift_snd]
    rfl

theorem dnW_comp {s : N ⟶ W} {V : W.left.Etale} (g : V ⟶ shObj s) {M : P.Etale} (c : M ⟶ N)
    (h : M ⟶ (etComp W.hom).obj V) (hc : h ≫ upP g = c) :
    dnW g c h hc ≫ g ≫ shι s = shι (c ≫ s) ≫ (etPull W.hom).map c := by
  have h1 : h.left ≫ g.left = c.left := congrArg (fun φ => φ.left) hc
  apply MorphismProperty.Over.Hom.ext
  show h.left ≫ g.left ≫ (shι s).left = (shι (c ≫ s)).left ≫ ((etPull W.hom).map c).left
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (shι s).left) h1).trans (lift_comp_core c s))

variable (Λ : Type u) [CommRing Λ]

theorem compat_of {Y : Scheme.{u}} (F : EtSh Λ Y) {U : Y.Etale} {I : Type*} {V : I → Y.Etale}
    (f : ∀ i, V i ⟶ U) (s : F.obj.obj (op U)) (i j : I) (Z : Y.Etale) (gi : Z ⟶ V i) (gj : Z ⟶ V j)
    (h : gi ≫ f i = gj ≫ f j) :
    (F.obj.map gi.op).hom ((F.obj.map (f i).op).hom s) = (F.obj.map gj.op).hom ((F.obj.map (f j).op).hom s) := by
  rw [← mapc, ← mapc, h]

end Lift

end RamanujanPetersson.EtPBC.EtShap

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

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

section Dg

variable (W : P.Etale)

theorem isClopen_dg [IsSeparated W.hom] : IsClopen (dg W) :=
  ⟨(pullback.diagonal W.hom).isClosedEmbedding.isClosed_range,
    (pullback.diagonal W.hom).isOpenEmbedding.isOpen_range⟩

theorem pt_eq {T N : P.Etale} (g : N ⟶ T) (σ : T ⟶ W) (s : N ⟶ W) (v : N.left) :
    ((etPull W.hom).map σ).left (((etPull W.hom).map g).left ((shι s).left v)) =
      pullback.lift (g ≫ σ).left s.left (agr_w (g ≫ σ) s) v := by
  have h1 : (pullback.fst N.hom W.hom ≫ g.left) ≫ T.hom = pullback.snd N.hom W.hom ≫ W.hom := by
    rw [Category.assoc, sh_w, pullback.condition]
  have h2 : (pullback.fst T.hom W.hom ≫ σ.left) ≫ W.hom = pullback.snd T.hom W.hom ≫ W.hom := by
    rw [Category.assoc, sh_w, pullback.condition]
  have e : pullback.lift (𝟙 N.left) s.left (sh_lift_w s) ≫ pullback.lift _ _ h1 ≫ pullback.lift _ _ h2 =
      pullback.lift (g.left ≫ σ.left) s.left (agr_w (g ≫ σ) s) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
      exact (pullback.lift_fst _ _ _).symm
    · simp only [Category.assoc, pullback.lift_snd]
      exact (pullback.lift_snd _ _ _).symm
  exact congrArg (fun f => f v) e

end Dg

section Iso

end Iso

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T1 =====
section

/-!
# S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps

* `resFreeIso Λ e T : Λ_U[e⁻¹T] ≅ (Λ[T])|_U` for etale `e : U ⟶ X` (`pullFreeIso` + `pullIsoRes`);
* `resFreeIso_taut`: its value on the tautological section is the pullback of `taut T` along the counit;
* `graph m : etId W.left ⟶ e⁻¹T` for `m : W ⟶ T` in `P.Etale` (adjoint to `W ≅ etComp (etId) ⟶ T`);
* `secMap Λ m := diagSec Λ W ≫ (res W.hom Λ).map Λ[m] : Λ_W ⟶ (Λ[T])|_W`, `secMap_comp`;
* **`secMap_graph`**: `unitIso.hom ≫ secMap m = Λ[graph m] ≫ resFreeIso.hom`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg

universe u

section Res

end Res

section Graph

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} {W T : P.Etale}

/-- The graph of `m : W ⟶ T`, a section of `W ×_P T` over `W`. -/
def graph (m : W ⟶ T) : etId W.left ⟶ (etPull W.hom).obj T :=
  (etCompAdj W.hom).homEquiv (etId W.left) T ((etCompTop W).hom ≫ m)

theorem graph_counit (m : W ⟶ T) :
    (etComp W.hom).map (graph m) ≫ (etCompAdj W.hom).counit.app T = (etCompTop W).hom ≫ m := by
  exact ((etCompAdj W.hom).homEquiv_counit (g := graph m)).symm.trans (Equiv.symm_apply_apply _ _)

end Graph

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Th1a =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality

Fix `D₀ R : P.Etale` with `W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`.
For `τ : T ⟶ D₀` (any `T : P.Etale` over `D₀`):
* **`theta Λ D₀ R n hn τ : Ext¹_P(Λ[T], Λ[R]) ≃+ H¹(T ×_P R, Λ)`** (extension by zero to `D₀`, Shapiro for
  `W₀ ⟶ D₀`, pullback of free sheaves, `T ×_{D₀} W₀ ≅ T ×_P R`);
* **`theta_natural`**: for `m : T₁ ⟶ T₂` with `m ≫ τ₂ = τ₁`,
  `θ_{τ₁}(Λ[m]^* x) = resLE (wm R m) (θ_{τ₂} x)` (`wm R m : T₁ ×_P R ⟶ T₂ ×_P R`);
* `extFreeV_natural` (naturality of `extFreeV` in `V`), `shapExt_symm_natural`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.GalTrE

universe u

section ExtV

end ExtV

section ShapNat

end ShapNat

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} (D₀ R : P.Etale)

variable {D₀} in
/-- `T` as an etale `D₀`-scheme through `τ`. -/
def ovr {T : P.Etale} (τ : T ⟶ D₀) : D₀.left.Etale := Scheme.Etale.mk τ.left

variable {D₀} in
/-- `D₀ ∘ (T over D₀) ≅ T`. -/
def ovrIso {T : P.Etale} (τ : T ⟶ D₀) : (etComp D₀.hom).obj (ovr τ) ≅ T :=
  MorphismProperty.Over.isoMk (Iso.refl _)
    (by
      change 𝟙 _ ≫ T.hom = τ.left ≫ D₀.hom
      rw [Category.id_comp, MorphismProperty.Over.w τ])

variable {D₀} in
/-- `(T over D₀) ×_{D₀} W₀ ⟶ T ×_P R`. -/
def ιHom {T : P.Etale} (τ : T ⟶ D₀) :
    ((etPull ((etPull D₀.hom).obj R).hom).obj (ovr τ)).left ⟶ ((etPull T.hom).obj R).left :=
  pullback.lift (pullback.snd (ovr τ).hom ((etPull D₀.hom).obj R).hom ≫ pullback.fst R.hom D₀.hom)
    (pullback.fst (ovr τ).hom ((etPull D₀.hom).obj R).hom)
    (by
      have h1 : pullback.fst R.hom D₀.hom ≫ R.hom = pullback.snd R.hom D₀.hom ≫ D₀.hom := pullback.condition
      have h2 : pullback.fst (ovr τ).hom ((etPull D₀.hom).obj R).hom ≫ τ.left =
          pullback.snd (ovr τ).hom ((etPull D₀.hom).obj R).hom ≫ pullback.snd R.hom D₀.hom :=
        pullback.condition
      have h3 : τ.left ≫ D₀.hom = T.hom := MorphismProperty.Over.w τ
      rw [Category.assoc, h1, ← h3, ← Category.assoc, ← Category.assoc, h2])

variable {D₀} in
theorem ιHom_fst {T : P.Etale} (τ : T ⟶ D₀) :
    ιHom R τ ≫ pullback.fst R.hom T.hom =
      pullback.snd (ovr τ).hom ((etPull D₀.hom).obj R).hom ≫ pullback.fst R.hom D₀.hom :=
  pullback.lift_fst _ _ _

variable {D₀} in
theorem ιHom_snd {T : P.Etale} (τ : T ⟶ D₀) :
    ιHom R τ ≫ pullback.snd R.hom T.hom = pullback.fst (ovr τ).hom ((etPull D₀.hom).obj R).hom :=
  pullback.lift_snd _ _ _

variable {D₀}

/-- `T₁ ⟶ T₂` over `D₀`. -/
def ovrMap {T₁ T₂ : P.Etale} (m : T₁ ⟶ T₂) {τ₁ : T₁ ⟶ D₀} {τ₂ : T₂ ⟶ D₀} (h : m ≫ τ₂ = τ₁) :
    ovr τ₁ ⟶ ovr τ₂ :=
  MorphismProperty.Over.homMk m.left
    (by
      subst h
      rfl)

theorem ovrIso_natural {T₁ T₂ : P.Etale} (m : T₁ ⟶ T₂) {τ₁ : T₁ ⟶ D₀} {τ₂ : T₂ ⟶ D₀} (h : m ≫ τ₂ = τ₁) :
    (etComp D₀.hom).map (ovrMap m h) ≫ (ovrIso τ₂).hom = (ovrIso τ₁).hom ≫ m :=
  MorphismProperty.Over.Hom.ext (by exact (Category.comp_id _).trans (Category.id_comp _).symm)

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T3 =====
section

/-!
# S4-EtPBC-A, O2 S5c: sections after shrinking, and the graph splitting

* `exists_opn_pt`: an open of `N` whose only geometric point over a closed Galois-trivial `z` is a given one;
* **`isLoc_sec`**: a one-point class has a presentation `D` with a map `s : D ⟶ T` through a given point `t` of `T`;
* `isClosed_range_sec`, `secV σ`: a section `σ` of a separated etale `N` has closed range, with open complement;
* **`isIso_secSplit`**, `secSplitIso`: `Λ_X ⊞ Λ[N|secV σ] ≅ Λ[N]`, first summand `Λ[σ]`;
* `isSeparated_opn`; `isSeparated_etPull` (so the graph of `m : W ⟶ T` splits).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg

universe u

section PtOpn

variable {P : Scheme.{u}}

/-- **An open of `N` through one geometric point over `z`** and no other. -/
theorem exists_opn_pt (z : P) (hzc : IsClosed ({z} : Set P)) (hG : Subsingleton (Gal z)) (N : P.Etale)
    (n : (geomPtAt z).point.fiber.obj N) :
    ∃ V : N.left.Opens, Subsingleton ((geomPtAt z).point.fiber.obj (opn N V)) ∧
      Nonempty ((geomPtAt z).point.fiber.obj (opn N V)) ∧
      ∀ c : (geomPtAt z).point.fiber.obj (opn N V), (geomPtAt z).point.fiber.map (opnι N V) c = n := by
  have := hG
  let y : N.left := fpt z n
  let D : Set N.left := N.hom ⁻¹' {z}
  have hDd : _root_.IsDiscrete D := N.hom.isDiscrete_preimage_singleton z
  have hDc : IsClosed D := hzc.preimage N.hom.continuous
  let S : Set N.left := D \ {y}
  have hSc : IsClosed S := isClosed_of_subset_discrete_closed Set.sdiff_subset hDd hDc
  let V : N.left.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  have hyV : y ∈ V := fun h => h.2 rfl
  have key : ∀ c : (geomPtAt z).point.fiber.obj (opn N V),
      (geomPtAt z).point.fiber.map (opnι N V) c = n := by
    intro c
    apply fiber_eq_of_pt z
    have h1 : fpt z ((geomPtAt z).point.fiber.map (opnι N V) c) ∈ V := opnι_mem N V (fpt z c)
    have h2 : fpt z ((geomPtAt z).point.fiber.map (opnι N V) c) ∉ S := h1
    have ht : N.hom (fpt z ((geomPtAt z).point.fiber.map (opnι N V) c)) = z := fib_over z _
    by_contra hne
    exact h2 ⟨ht, hne⟩
  refine ⟨V, ⟨fun b b' => fib_opn_injective N V z ((key b).trans (key b').symm)⟩, ?_, key⟩
  obtain ⟨b, -, -⟩ := exists_lift_fib (opnι N V) z n (⟨y, hyV⟩ : V) (Scheme.Opens.ι_apply V ⟨y, hyV⟩)
  exact ⟨b⟩

end PtOpn

section SecSplit

end SecSplit

section Lift

end Lift

section GraphSplit

end GraphSplit

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2g =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2g): stage S4, the data `e`, `g`, `hHp`, `hHq` of `uk_diff` (pure algebra)

GLOB/REL PLAN v1, stage S4 (ring level, abstract rings). `G₂ = G₁[1/s]` (the Zariski shrink `W₂ → W₁`), `B₁ → G₁`,
`B₂ → G₂`, `ι : B₁ → B₂` compatible, `z ∈ Π_q Frac(G₁ ⧸ q)` integral over `B₁`, `μH T₂^N = x₁` with
`x₁ = T₁^N ũ (1 - T₁ z)` (`ũ = (u₁ on p₁, 1 elsewhere)`):
* `eq_comap_of_le_comap`: below a minimal prime of a localization lies exactly one minimal prime (its contraction);
* `exists_psi`, `psi_unique`, `psi_update`, `psi_update_ne`: the maps `Frac(G₁ ⧸ q₁) → Frac(G₂ ⧸ q)`;
* `exists_monic_he`: one monic `g ∈ B₂[X]` of positive degree killing every `-Ψ_q (z_{q₁})`;
* **`exists_S4_gen`**: `e q := -Ψ_q (z_{q₁ q})` and `g` with `he`, `hHp` (any compatible `Ψ`), `hHq`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Below

end Below

section Psi

variable {G₁ G₂ : Type} [CommRing G₁] [CommRing G₂]

theorem psi_update [DecidableEq (minimalPrimes G₁)] {p₁ p₁' : minimalPrimes G₁} (h : p₁' = p₁) {K : Type}
    [CommRing K] (Ψ : FractionRing (G₁ ⧸ (p₁' : Ideal G₁)) →+* K) (Ψ' : FractionRing (G₁ ⧸ (p₁ : Ideal G₁)) →+* K)
    (hΨ : ∀ a : G₁, Ψ (algebraMap _ _ (Ideal.Quotient.mk (p₁' : Ideal G₁) a)) =
      Ψ' (algebraMap _ _ (Ideal.Quotient.mk (p₁ : Ideal G₁) a)))
    (u : FractionRing (G₁ ⧸ (p₁ : Ideal G₁))) : Ψ (Function.update (1 : PiQ G₁) p₁ u p₁') = Ψ' u := by
  subst h
  rw [Function.update_self, psi_unique _ hΨ]

theorem psi_update_ne [DecidableEq (minimalPrimes G₁)] {p₁ q₁ : minimalPrimes G₁} (h : q₁ ≠ p₁) {K : Type}
    [CommRing K] (Ψ : FractionRing (G₁ ⧸ (q₁ : Ideal G₁)) →+* K) (u : FractionRing (G₁ ⧸ (p₁ : Ideal G₁))) :
    Ψ (Function.update (1 : PiQ G₁) p₁ u q₁) = 1 := by
  rw [Function.update_of_ne h, Pi.one_apply, map_one]

end Psi

section Monic

/-- **One monic `g` of positive degree** with `g(-Ψ_i (z_{q₁ i})) = 0` for all `i`. -/
theorem exists_monic_he {O' G B₂ I : Type} [CommRing O'] [CommRing G] [CommRing B₂] [Nontrivial B₂]
    [Algebra O' (PiQ G)] {K : I → Type} [∀ i, CommRing (K i)] (q₁ : I → minimalPrimes G)
    (Ψ : ∀ i, FractionRing (G ⧸ (q₁ i : Ideal G)) →+* K i) (ιh : O' →+* B₂) (β : ∀ i, B₂ →+* K i)
    (hβ : ∀ i b, Ψ i (algebraMap O' (PiQ G) b (q₁ i)) = β i (ιh b)) {z : PiQ G} (hz : IsIntegral O' z) :
    ∃ g : B₂[X], g.Monic ∧ 0 < g.natDegree ∧ ∀ i, g.eval₂ (β i) (-Ψ i (z (q₁ i))) = 0 := by
  obtain ⟨g₁, hm, hg⟩ := hz.neg
  refine ⟨g₁.map ιh * X, (hm.map ιh).mul monic_X, ?_, fun i => ?_⟩
  · rw [natDegree_mul_X (hm.map ιh).ne_zero]
    exact Nat.succ_pos _
  · let π : PiQ G →+* K i := (Ψ i).comp (Pi.evalRingHom _ (q₁ i))
    have e1 : (β i).comp ιh = π.comp (algebraMap O' (PiQ G)) := RingHom.ext fun b => (hβ i b).symm
    have e2 : -Ψ i (z (q₁ i)) = π (-z) := by
      show _ = Ψ i ((-z) (q₁ i))
      rw [Pi.neg_apply, map_neg]
    rw [eval₂_mul, eval₂_X, eval₂_map, e1, e2, ← hom_eval₂, hg, map_zero, zero_mul]

end Monic

section S4Gen

end S4Gen

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2c =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2c): stage S3, the live modification (pure algebra)

GLOB/REL PLAN v1, stage S3 (algebra assembly). After S2, `f u_S = t^N ũ (1 - t z)` in `Π_q Frac(G ⧸ q)`:
* `one_sub_mul_ne_zero`: `1 - t z` has no zero coordinate when `O' ↪ Frac(G ⧸ q)` and `t` is not a unit of `O'`
  (`z` is integral over `O'`, so `t z_q = 1` would make `t` a unit: `isUnit_of_mul_eq_one_of_isIntegral`);
* **`exists_live`**: `y := liveMod u_S 1` is a non-zero-divisor of `Y`, integral over `O`, has the same image as
  `u_S` in `Π_q Frac(G ⧸ q)`, and divides some `c₀ ∈ O ∖ 0` (`exists_dvd_algebraMap`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section S3

variable {O O' S G : Type*} [CommRing O] [CommRing O'] [CommRing S] [CommRing G]
  [Algebra O O'] [Algebra O S] [Algebra O' (PiQ G)] [Algebra O (PiQ G)] [IsScalarTower O O' (PiQ G)]
  (f : S →ₐ[O] PiQ G) (t : O)

/-- `1 - t z` has no zero coordinate. -/
theorem one_sub_mul_ne_zero [Algebra.IsIntegral O S]
    (hinj : ∀ q : minimalPrimes G, Function.Injective fun b : O' => algebraMap O' (PiQ G) b q)
    (ht : ¬ IsUnit (algebraMap O O' t)) {z : PiQ G} (hz : z ∈ hatS (O' := O') f) (q : minimalPrimes G) :
    (1 - algebraMap O (PiQ G) t * z) q ≠ 0 := by
  intro h0
  let ev : PiQ G →+* FractionRing (G ⧸ (q : Ideal G)) := Pi.evalRingHom _ q
  let _ : Algebra O' (FractionRing (G ⧸ (q : Ideal G))) := (ev.comp (algebraMap O' (PiQ G))).toAlgebra
  let evA : PiQ G →ₐ[O'] FractionRing (G ⧸ (q : Ideal G)) := { ev with commutes' := fun _ => rfl }
  have hzi : IsIntegral O' (z q) := (isIntegral_of_mem_hatS f hz).map evA
  have e : (algebraMap O (PiQ G) t * z) q = 1 := by
    rw [Pi.sub_apply, Pi.one_apply, sub_eq_zero] at h0
    exact h0.symm
  have h1 : algebraMap O' (FractionRing (G ⧸ (q : Ideal G))) (algebraMap O O' t) * z q = 1 := by
    rw [Pi.mul_apply, IsScalarTower.algebraMap_apply O O' (PiQ G)] at e
    exact e
  exact ht (isUnit_of_mul_eq_one_of_isIntegral (hinj q) hzi h1)

end S3

section Live

variable {O Y G : Type*} [CommRing O] [IsDomain O] [CommRing Y] [Algebra O Y] [CommRing G]
  (hY : ∀ (m : Ideal Y) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing Y]

/-- The coordinates of `t^N ũ (1 - t z)` are nonzero. -/
theorem coord_ne_zero {a b c : PiQ G} (ha : ∀ q, a q ≠ 0) (hb : ∀ q, b q ≠ 0) (hc : ∀ q, c q ≠ 0) (N : ℕ)
    (q : minimalPrimes G) : (a ^ N * b * c) q ≠ 0 := by
  rw [Pi.mul_apply, Pi.mul_apply, Pi.pow_apply]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (ha q)) (hb q)) (hc q)

end Live

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T6 =====
section

/-!
# S4-EtPBC-A, O2 S5f: geometry of graphs of sections

For `m : W ⟶ T` in `P.Etale`, `graph m : etId W.left ⟶ (etPull W.hom).obj T` (lib O2T1):
* `graph_fst`, `graph_snd`, `graph_left_eq_sec` (it is EGeoB's `sec m`), **`graph_cover`** (points over `fpt d`
  lie on graphs of sections through every fibre point);
* `graphMeet m m'` (where the graphs meet), closed for separated `T`; `graph_meet_eq`, **`not_mem_graphMeet`**
  (graphs of sections through different fibre points do not meet at `fpt d`), `disjoint_graph`;
* `pullMap d`, **`graph_natural`**, **`graphMeet_natural`** (meeting loci pull back along `d : W' ⟶ W`);
* `eq_fpt_of_over`: `fpt d` is the only point over `z` when the fibre over `z` is a singleton.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

section GraphGeo

variable {P : Scheme.{u}} {W' W T : P.Etale}

set_option backward.isDefEq.respectTransparency false in
theorem graph_fst (m : W ⟶ T) : (graph m).left ≫ pullback.fst T.hom W.hom = m.left := by
  have h := congrArg (fun f => f.left) (graph_counit m)
  rw [← Category.id_comp m.left]
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem graph_snd (m : W ⟶ T) : (graph m).left ≫ pullback.snd T.hom W.hom = 𝟙 W.left :=
  MorphismProperty.Over.w (graph m)

/-- Where the graph of `m` meets the graph of `m'`. -/
def graphMeet (m m' : W ⟶ T) : Set W.left := (graph m).left ⁻¹' Set.range (graph m').left

set_option backward.isDefEq.respectTransparency false in
theorem graph_meet_eq (m m' : W ⟶ T) {v u : W.left} (h : (graph m).left v = (graph m').left u) :
    v = u ∧ m.left v = m'.left u := by
  have k1 : pullback.snd T.hom W.hom ((graph m).left v) = v :=
    (Scheme.Hom.comp_apply (graph m).left (pullback.snd T.hom W.hom) v).symm.trans (by rw [graph_snd]; try rfl)
  have k2 : pullback.snd T.hom W.hom ((graph m').left u) = u :=
    (Scheme.Hom.comp_apply (graph m').left (pullback.snd T.hom W.hom) u).symm.trans (by rw [graph_snd]; try rfl)
  have k3 : pullback.fst T.hom W.hom ((graph m).left v) = m.left v :=
    (Scheme.Hom.comp_apply (graph m).left (pullback.fst T.hom W.hom) v).symm.trans (by rw [graph_fst]; try rfl)
  have k4 : pullback.fst T.hom W.hom ((graph m').left u) = m'.left u :=
    (Scheme.Hom.comp_apply (graph m').left (pullback.fst T.hom W.hom) u).symm.trans (by rw [graph_fst]; try rfl)
  exact ⟨k1.symm.trans ((congrArg (fun x => pullback.snd T.hom W.hom x) h).trans k2),
    k3.symm.trans ((congrArg (fun x => pullback.fst T.hom W.hom x) h).trans k4)⟩

theorem disjoint_graph {m m' : W ⟶ T} (h : ∀ v, v ∉ graphMeet m m') :
    Disjoint (Set.range (graph m).left) (Set.range (graph m').left) := by
  rw [Set.disjoint_left]
  rintro _ ⟨v, rfl⟩ ⟨u, hu⟩
  exact h v ⟨u, hu⟩

end GraphGeo

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gd =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes

* `graph_left_eq_of_fib`: sections with the same value at a geometric point have meeting graphs there;
* `mem_graph_of_card`: if disjoint graphs of sections `τ i : W ⟶ T` are at least as many as the points of every
  geometric fibre of `T` (finite), every point of `W ×_P T` lies on one of the graphs;
* `isZero_freeSh_of_isEmpty`, `ext_eq_zero_of_isZero`;
* **`isLoc_free_good`**: for `T` quasi-compact separated etale over `P` and `z = c (X = a)` a point where the fibre of
  `T` is as large as any fibre (a good point: constant degree near `z`), every one-point class at `z` with
  coefficients `Λ[T]` is in the subgroup generated by the point classes `PtCls` (the residual of `isLoc_free_decomp`
  is EMPTY).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtDed

universe u w

section GoodGeo

variable {P : Scheme.{u}} {W T : P.Etale}

set_option backward.isDefEq.respectTransparency false in
/-- Sections with the same value at a geometric point have graphs meeting there. -/
theorem graph_left_eq_of_fib (x : P) (d : (geomPtAt x).point.fiber.obj W) (m m' : W ⟶ T)
    (h : (geomPtAt x).point.fiber.map m d = (geomPtAt x).point.fiber.map m' d) :
    (graph m).left (fpt x d) = (graph m').left (fpt x d) := by
  have key : fl x d ≫ (graph m).left = fl x d ≫ (graph m').left := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, graph_fst, graph_fst]
      exact congrArg (fun a => fl x a) h
    · rw [Category.assoc, Category.assoc, graph_snd, graph_snd]
  exact (Scheme.Hom.comp_apply (fl x d) (graph m).left _).symm.trans
    ((congrArg (fun f => f (default : Spec (CommRingCat.of (geomPtAt x).Ω))) key).trans
      (Scheme.Hom.comp_apply _ _ _))

end GoodGeo

section Zero

end Zero

section GenZero

universe w' v₁ u₁ v₂ u₂ v₃ u₃

variable {C' : Type u₁} [Category.{v₁} C'] [Abelian C'] {hC : HasExt.{w'} C'}
  {D' : Type u₂} [Category.{v₂} D'] [Abelian D'] {hD : HasExt.{w'} D'}

theorem comp_symm_eq_zero_gen {X0 Y0 W : D'} (Y : Ext.{w'} X0 Y0 1) (hY : IsZero Y0) (g : Y0 ⟶ W)
    {A0 A1 B : C'} (A : Ext.{w'} A0 A1 1) (e : Ext.{w'} A1 B 1 ≃+ Ext.{w'} X0 W 1) :
    A.comp (e.symm (Y.comp (Ext.mk₀ g) (add_zero 1))) (show 1 + 1 = 2 from rfl) = 0 := by
  rw [ext_eq_zero_of_isZero Y hY, Ext.zero_comp, map_zero, Ext.comp_zero]

end GenZero

section Good

end Good

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals

REL PLAN v2 (s126) + s128 fix. At a bad point `c(b)` (`G = (X - C b)^m G_b`, `G_b(b) ≠ 0`, `c(b) ∉ U₀`), the chart
`D' := D_{G_b} = chEt c (locF G_b)` satisfies the hypotheses of `bad_term_zero'` (O2Bd5):
* fibres: **`subsingleton_fib_of_mono`**, **`nonempty_fib_of_mem`** (generic);
* **`bad_pt`**, **`badCh_r₁`** (`hDr₁`), **`badCh_r`** (`hDr`), **`badCh_D'`** (`hD'`), **`badCh_hUo`**, **`isAffine_badCh`**,
  **`badCh_hta`** (`hta`), **`badCh_n`** (`hDn`);
* CRT ideals `J b := (X - C b) S`: **`span_coprime_pow`** (`hJt`), **`pairwise_span_coprime`** (`hJ`) of `exists_S23_chart`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Cech

section Fib

variable {P : Scheme.{0}}

/-- A point over `x` gives a nonempty geometric fibre. -/
theorem nonempty_fib_of_mem (D : P.Etale) (x : P) (v : D.left) (hv : D.hom v = x) :
    Nonempty ((geomPtAt x).point.fiber.obj D) := by
  obtain ⟨e, -, -⟩ := exists_lift_fib (toTop D) x (topPt x) v (hv.trans (fpt_topPt x (topPt x)).symm)
  exact ⟨e⟩

end Fib

section BadCh

end BadCh

section BadCh2

end BadCh2

section JAlg

end JAlg

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl3e =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl3e): the core step on the charts

* **`exists_psi_away`** (generic): in a localization `G₂ = G₁[1/s]`, a minimal prime `p₁ ≤ σ⁻¹ p₂` gives the field map
  `Ψ : Frac(G₁ ⧸ p₁) → Frac(G₂ ⧸ p₂)` compatible with `σ`;
* **`core_chart`**: `core₁₂` (O2Gl3d) at `D₂ := chEt c (φ₁ ≫ locF (φ₁.hom c₀'))`, `dm := toDF`, `T' := D_G ×_P U₀`
  (`G` generic with `g₀ ∣ G`), `m := mG`, `c_Y := Σ_Q kapS Q (kumD β_Q)`, taking the output of `exists_S4H` (O2Gl2k)
  and roots `β_Q` of `H` as hypotheses; `p₂` (exists_piece_toDF), its uniqueness (piece_unique_away), `Ψ`, the
  radicals `γ₂` (exists_gam) and `χ` (exists_chi) are produced inside.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section PsiAway

variable {G₁ G₂ : Type} [CommRing G₁] [CommRing G₂]

/-- The field map `Ψ` along a localization (`p₁ ≤ σ⁻¹ p₂` forces `p₁ = σ⁻¹ p₂`). -/
theorem exists_psi_away (σ : G₁ →+* G₂) (s : G₁) (hloc : letI := σ.toAlgebra; IsLocalization.Away s G₂)
    (p₁ : minimalPrimes G₁) (p₂ : minimalPrimes G₂) (κ : G₁ →+* G₂ ⧸ p₂.1)
    (hκ : RingHom.ker κ = Ideal.comap σ p₂.1) (h : p₁.1 ≤ RingHom.ker κ) :
    ∃ Ψ : FractionRing (G₁ ⧸ p₁.1) →+* FractionRing (G₂ ⧸ p₂.1),
      ∀ a : G₁, Ψ (algebraMap _ _ (Ideal.Quotient.mk p₁.1 a)) = algebraMap _ _ (Ideal.Quotient.mk p₂.1 (σ a)) := by
  let _ : Algebra G₁ G₂ := σ.toAlgebra
  have _ := hloc
  have _ : p₁.1.IsPrime := p₁.2.1.1
  have _ : p₂.1.IsPrime := p₂.2.1.1
  have e : p₁.1 = p₂.1.comap (algebraMap G₁ G₂) :=
    eq_comap_of_le_comap (Submonoid.powers s) p₂.2 (h.trans_eq hκ)
  exact exists_psi σ p₁.1 p₂.1 e.symm

end PsiAway

section CoreChart

end CoreChart

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2b =====
section

/-!
# S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section TB2b

variable {Λ : Type u} [CommRing Λ]

@[reassoc]
theorem graph_left_fst {P : Scheme.{u}} {V T : P.Etale} (m : V ⟶ T) :
    (graph m).left ≫ pullback.fst T.hom V.hom = m.left := by
  have h : (graph m).left ≫ pullback.fst T.hom V.hom = 𝟙 _ ≫ m.left :=
    congrArg (fun φ => φ.left) (graph_counit m)
  rw [Category.id_comp] at h
  exact h

end TB2b

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB3 =====
section

/-!
# S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`

* `pullH Λ g n κ := u ∘ g^*κ ∘ u⁻¹ ∈ H^n(X, Λ)` for `κ ∈ H^n(Y, Λ)` and any `g : X ⟶ Y` (`u := pullUnit Λ g`);
* `secMap_id`, `diagSec_pull` (the KEY identity at `m = 𝟙`);
* **`thetaM_pull`**: `Λ[f⁻¹W] ⟶ f^*Λ[W]` followed by `f^*(thetaM m 1 κ)` equals
  `thetaM (f⁻¹ m) 1 (pullH f_W 1 κ)` followed by `Λ[f⁻¹T] ⟶ f^*Λ[T]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenAlg

universe u

section TB3

variable {Λ : Type u} [CommRing Λ]

/-- `Φ'(ξ) = Ψ(Φ ξ)` on `Ext¹` for `Φ' = Φ ⋙ Ψ`. -/
theorem mapExact_compF {C D E : Type*} [Category C] [Abelian C] [HasExt.{u} C] [EnoughInjectives C]
    [Category D] [Abelian D] [HasExt.{u} D] [Category E] [Abelian E] [HasExt.{u} E]
    (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (Ψ : D ⥤ E) [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ]
    [(Φ ⋙ Ψ).Additive] [PreservesFiniteLimits (Φ ⋙ Ψ)] [PreservesFiniteColimits (Φ ⋙ Ψ)]
    {A B : C} (ξ : Ext.{u} A B 1) :
    ξ.mapExactFunctor (Φ ⋙ Ψ) = (ξ.mapExactFunctor Φ).mapExactFunctor Ψ := by
  have h := mapExact_comp_iso Φ Ψ (Iso.refl (Φ ⋙ Ψ)) ξ
  simp only [Iso.refl_hom, NatTrans.id_app] at h
  exact ((Ext.mk₀_id_comp _).symm.trans h.symm).trans (Ext.comp_mk₀_id _)

section GenPL

universe w' v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

end GenPL

end TB3

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7a =====
section

/-!
# S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
* `Delta.bcImg`: the germ image `{β | ∃ j α, bc j α = β}` is an additive subgroup (cofiltered `J`);
* `etPullId`: `etPull (𝟙 X) ≅ 𝟭`; `pushId`: `push (𝟙 X) ≅ 𝟭`; `pushEquiv e` for an isomorphism `e`;
* **`pull_isEquivalence`**: `e^*` is an equivalence for an isomorphism `e`;
* **`pull_ext_bijective`**: `e^*` is bijective on `Ext^n`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact

universe u

section L7a

variable {Λ : Type u} [CommRing Λ]

/-- `(etPull (𝟙 X)).obj V ≅ V`. -/
def etPullIdC {X : Scheme.{u}} (V : X.Etale) : (etPull (𝟙 X)).obj V ≅ V where
  hom := MorphismProperty.Over.homMk (pullback.fst V.hom (𝟙 X))
    (by exact (pullback.condition).trans (Category.comp_id _)) trivial
  inv := MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) V.hom (by simp))
    (by exact pullback.lift_snd _ _ _) trivial
  hom_inv_id := MorphismProperty.Over.Hom.ext (fst_lift_id V)
  inv_hom_id := MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

end L7a

end RamanujanPetersson.EtPBC.EtMV

end

end


