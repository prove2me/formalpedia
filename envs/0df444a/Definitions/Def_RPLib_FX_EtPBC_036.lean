-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_036
-- name    : RPLib_FX_EtPBC_036
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:38:38.8623+00:00
-- url     : https://prove2.me/theorems/a6e8a05b-503d-5512-b91a-da630079b7bd
-- title:
--   Proper base change for the projective line, library file 036
-- statement:
--   File 036 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovAs5a`: S4-EtPBC-A, R4-T2 (A3 assembly, As5a): lifting polynomials and memberships to a f.g. subalgebra
--   * `S4.Def_RP_EtPBC_A_CovAs5b`: S4-EtPBC-A, R4-T2 (A3 assembly, As5b): monic families and base change along `φ` at the level of `C`
--   * `S4.Def_RP_EtPBC_A_CovAs5c`: S4-EtPBC-A, R4-T2 (A3 assembly, As5c): one chart descends to a f.g. subalgebra
--   * `S4.Def_RP_EtPBC_A_CovAs5d`: S4-EtPBC-A, R4-T2 (A3 assembly, As5d): substitution data descend to a f.g. subalgebra
--   * `S4.Def_RP_EtPBC_A_Z3Y`: S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
--   * `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
--   * `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
--   * `S4.Def_RP_EtPBC_A_DescG4`: S4-EtPBC-A, R4-T1d (part 1): the sheets `V ⟶ U₀`
--   * `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
--   * `S4.Def_RP_EtPBC_A_O2N4`: S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)
--   * `S4.Def_RP_EtPBC_A_O2UK1`: S4-EtPBC-A, O2 M6 (O2UK1): `1 + t e` is a `d`-th power over an etale neighbourhood (ring level)
--   * `S4.Def_RP_EtPBC_A_O2UK2b`: S4-EtPBC-A, O2 M6 (O2UK2b): the `d`-th root of `1 + t e` on the pieces over an etale `B → B'`
--   * `S4.Def_RP_EtPBC_A_O2Bd2`: S4-EtPBC-A, O2 REL (O2Bd2): `H = 1 + t_i e` on every piece at a bad point
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_ArtinApprox_03
import Definitions.Def_RPLib_FX_EtPBC_024
import Definitions.Def_RPLib_FX_EtPBC_031

/-!
# Proper base change for the projective line, library file 036

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovAs5a`: S4-EtPBC-A, R4-T2 (A3 assembly, As5a): lifting polynomials and memberships to a f.g. subalgebra
* `S4.Def_RP_EtPBC_A_CovAs5b`: S4-EtPBC-A, R4-T2 (A3 assembly, As5b): monic families and base change along `φ` at the level of `C`
* `S4.Def_RP_EtPBC_A_CovAs5c`: S4-EtPBC-A, R4-T2 (A3 assembly, As5c): one chart descends to a f.g. subalgebra
* `S4.Def_RP_EtPBC_A_CovAs5d`: S4-EtPBC-A, R4-T2 (A3 assembly, As5d): substitution data descend to a f.g. subalgebra
* `S4.Def_RP_EtPBC_A_Z3Y`: S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
* `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
* `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
* `S4.Def_RP_EtPBC_A_DescG4`: S4-EtPBC-A, R4-T1d (part 1): the sheets `V ⟶ U₀`
* `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
* `S4.Def_RP_EtPBC_A_O2N4`: S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)
* `S4.Def_RP_EtPBC_A_O2UK1`: S4-EtPBC-A, O2 M6 (O2UK1): `1 + t e` is a `d`-th power over an etale neighbourhood (ring level)
* `S4.Def_RP_EtPBC_A_O2UK2b`: S4-EtPBC-A, O2 M6 (O2UK2b): the `d`-th root of `1 + t e` on the pieces over an etale `B → B'`
* `S4.Def_RP_EtPBC_A_O2Bd2`: S4-EtPBC-A, O2 REL (O2Bd2): `H = 1 + t_i e` on every piece at a bad point
-/

set_option autoImplicit false

set_option linter.defProp false

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

theorem map_tiC_tiC {σ : Type*} {C D E : Subalgebra A S} (h : C ≤ D) (h' : D ≤ E)
    (y : MvPolynomial σ (C ⊗[A] B)) :
    MvPolynomial.map (tiC B h') (MvPolynomial.map (tiC B h) y) = MvPolynomial.map (tiC B (h.trans h')) y := by
  rw [MvPolynomial.map_map,
    show (tiC B h').comp (tiC B h) = tiC B (h.trans h') from RingHom.ext fun x => tiC_tiC h h' x]

set_option maxHeartbeats 400000 in
/-- **Finitely many ideal memberships descend to a f.g. subalgebra.** -/
theorem desc_mem [Module.Flat A S] {ι σ : Type*} [Fintype ι] {r : ℕ} (C₀ : Subalgebra A S) (hC₀ : C₀.FG)
    (g : Fin r → MvPolynomial σ (C₀ ⊗[A] B)) (x : ι → MvPolynomial σ (C₀ ⊗[A] B))
    (hx : ∀ k, MvPolynomial.map (tvC B C₀) (x k) ∈
      Ideal.span (Set.range fun j => MvPolynomial.map (tvC B C₀) (g j))) :
    ∃ (C : Subalgebra A S) (h : C₀ ≤ C), C.FG ∧ ∀ k,
      MvPolynomial.map (tiC B h) (x k) ∈ Ideal.span (Set.range fun j => MvPolynomial.map (tiC B h) (g j)) := by
  classical
  choose c hc using fun k => Ideal.mem_span_range_iff_exists_fun.mp (hx k)
  obtain ⟨C₁, hC₁, hl⟩ := exists_lift_polys (B := B) (fun kj : ι × Fin r => c kj.1 kj.2)
  choose c' hc' using hl
  have h₀ : C₀ ≤ C₀ ⊔ C₁ := le_sup_left
  have h₁ : C₁ ≤ C₀ ⊔ C₁ := le_sup_right
  let Qp : ι → MvPolynomial σ ((C₀ ⊔ C₁ : Subalgebra A S) ⊗[A] B) := fun k =>
    ∑ j, MvPolynomial.map (tiC B h₁) (c' (k, j)) * MvPolynomial.map (tiC B h₀) (g j) -
      MvPolynomial.map (tiC B h₀) (x k)
  have hQ : ∀ k, MvPolynomial.map (tvC B (C₀ ⊔ C₁)) (Qp k) = 0 := fun k => by
    simp only [Qp, map_sub, map_sum, map_mul, map_tvC_tiC, hc']
    rw [sub_eq_zero]
    exact hc k
  obtain ⟨C, h, hC, hz⟩ := desc_mvPoly (B := B) (C₀ ⊔ C₁) (hC₀.sup hC₁) (Finset.univ.image Qp)
    (fun q hq => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hq
      exact hQ k)
  refine ⟨C, h₀.trans h, hC, fun k => ?_⟩
  have e := hz (Qp k) (Finset.mem_image_of_mem Qp (Finset.mem_univ k))
  have e' : MvPolynomial.map (tiC B h) (Qp k) = 0 := e
  simp only [Qp, map_sub, map_sum, map_mul, map_tiC_tiC] at e'
  rw [sub_eq_zero] at e'
  rw [← e']
  exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun j => MvPolynomial.map (tiC B (h₁.trans h)) (c' (k, j)), rfl⟩

end Lift

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs5b =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As5b): monic families and base change along `φ` at the level of `C`

* `exists_lift_monics`: finitely many monic polynomials over `S ⊗ B` come from monic ones over `C ⊗ B`, `C` f.g.
* `bcC φ C = id_C ⊗ φ : C ⊗ B → C ⊗ N`; `tvC_bcC`, `tiC_bcC` and their polynomial forms `map_tvC_bcC`,
  `map_tiC_bcC`: `bcC` commutes with `tvC` (to `S`) and with `tiC` (to a larger `D`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section LiftB

end LiftB

section BC

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B N : Type u} [CommRing B] [Algebra A B] [CommRing N] [Algebra A N] (φ : B →ₐ[A] N)

theorem map_tiC_bcC {σ : Type*} {C D : Subalgebra A S} (h : C ≤ D) (y : MvPolynomial σ (C ⊗[A] B)) :
    MvPolynomial.map (tiC N h) (MvPolynomial.map (bcC φ C) y) =
      MvPolynomial.map (bcC φ D) (MvPolynomial.map (tiC B h) y) := by
  rw [MvPolynomial.map_map, MvPolynomial.map_map,
    show (tiC N h).comp (bcC φ C) = (bcC φ D).comp (tiC B h) from RingHom.ext fun x => tiC_bcC φ h x]

end BC

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs5c =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As5c): one chart descends to a f.g. subalgebra

**`desc_chart`**: if a square system `gC` over `C₀ ⊗ B` becomes etale-and-finite presented over `S ⊗ B` (witnesses
`hJ`, `hF` for `gmap (tvC B C₀) gC`), then the witnesses already exist over `C ⊗ B` for a f.g. `C ≥ C₀` (for the
system `gmap (tiC B h) gC`). Helpers `gmap_tvC_tiC`, `gmap_tiC_tiC`, `polymap_tvC_tiC`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section Chart

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B : Type u} [CommRing B] [Algebra A B]

theorem gmap_tiC_tiC {r : ℕ} {C D E : Subalgebra A S} (h : C ≤ D) (h' : D ≤ E)
    (gC : Fin r → MvPolynomial (Fin r) (C ⊗[A] B)) :
    gmap (tiC B h') (gmap (tiC B h) gC) = gmap (tiC B (h.trans h')) gC :=
  funext fun j => map_tiC_tiC h h' (gC j)

end Chart

end RamanujanPetersson.EtPBC.Cov

end

end

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

theorem mem_push {r : ℕ} {C D E : Subalgebra A S} (h : C ≤ D) (h' : D ≤ E)
    (g : Fin r → MvPolynomial (Fin r) (C ⊗[A] B)) {x : MvPolynomial (Fin r) (C ⊗[A] B)}
    (hx : MvPolynomial.map (tiC B h) x ∈ Ideal.span (Set.range (gmap (tiC B h) g))) :
    MvPolynomial.map (tiC B (h.trans h')) x ∈ Ideal.span (Set.range (gmap (tiC B (h.trans h')) g)) := by
  have e := span_map_mem (tiC B h') (gmap (tiC B h) g) hx
  rw [map_tiC_tiC, gmap_tiC_tiC] at e
  exact e

end Desc

section BCg

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B N : Type u} [CommRing B] [Algebra A B] [CommRing N] [Algebra A N] (φ : B →ₐ[A] N)

theorem gmap_tiC_bcC {r : ℕ} {C D : Subalgebra A S} (h : C ≤ D) (gC : Fin r → MvPolynomial (Fin r) (C ⊗[A] B)) :
    gmap (tiC N h) (gmap (bcC φ C) gC) = gmap (bcC φ D) (gmap (tiC B h) gC) :=
  funext fun j => map_tiC_bcC φ h (gC j)

end BCg

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Y =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`

For `π : Y ⟶ P¹_V` (`V` affine):
* `isAffineOpen_Qc`, `isAffineOpen_Yc`: the charts `Qᵢ` of `P¹_V` and `Yᵢ = π⁻¹ Qᵢ` are affine;
* `σY i j : Γ(V)[X] → Γ(Y, Yᵢ)` (`X ↦ π^*(Xⱼ/Xᵢ)`), **`finite_σY`** (`π` finite);
* `pull_res` (restriction commutes with pullback), **`basicOpen_tY`**, **`basicOpen_sY`**: `D(t) = D(s) = Y₀ ⊓ Y₁`;
* **`trans_Y`**: `t|_{Y₀₁} · s|_{Y₀₁} = 1`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization
open RamanujanPetersson.EtCompact

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K))

variable {Y : Scheme.{u}} (π : Y ⟶ PV K gV)

/-- **`Γ(Yᵢ)` is finite over `Γ(V)[X]`.** -/
theorem finite_σY [IsAffine V] [IsFinite π] (i j : Fin 2) (hij : i ≠ j) : (σY K gV π i j).Finite :=
  finite_app_of_surj π (isAffineOpen_Qc K gV i) _ (surj_chart K gV i j hij)

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG1 =====
section

/-!
# S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart

For a short exact sequence `0 → F →a E →b Q → 0` of etale sheaves on `X`, an etale `V` and `e ∈ E(V)` whose
restrictions along any two maps `W ⟶ V` have the same image in `Q`:
* `dif a b hab hS e he W w₁ w₂ ∈ F(W)` with `a (dif) = w₁^* e - w₂^* e` (`f_dif`, unique: `dif_eq`);
  `dif_self`, `dif_add` (cocycle), `dif_map` (naturality); `he_of_glob` (the hypothesis from a global section).
* Charts: `σ : Spec A ⟶ X` etale, `τ : Spec C ⟶ V` over `σ` (`hτ`), `C` etale over `A`. `etS σ R` (= `Spec R` as
  an etale `X`-object for an etale `A`-algebra `R`), `homS σ φ`, `kmap σ τ hτ φ : etS σ R ⟶ V`, `homS_kmap`,
  `cval_comap`.
* For `F = M_X` (`M` finite): `cU` (the values of `dif` on `Spec (C ⊗[A] C)`), `cU_diag`, `cU_coc`, and
  **`datU : Datum A C M`** (`DescB.mkDatum`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Dif

end Dif

section Chart

variable {X : Scheme.{u}} {A : Type u} [CommRing A] (σ : Spec (CommRingCat.of A) ⟶ X) [Etale σ]

variable {C : Type u} [CommRing C] [Algebra A C] [Algebra.Etale A C] {V : X.Etale}
  (τ : Spec (CommRingCat.of C) ⟶ V.left)
  (hτ : τ ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ σ)

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

variable {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q) (hab : a ≫ b = 0)
  (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

/-- **The descent datum on the chart** (`M` finite). -/
def datU [Fintype M] [DecidableEq M] : Datum A C M :=
  mkDatum (cU σ τ hτ a b hab hS e he) (isLocallyConstant_cU σ τ hτ a b hab hS e he)
    (cU_diag σ τ hτ a b hab hS e he) (cU_coc σ τ hτ a b hab hS e he)

theorem datU_ε [Fintype M] [DecidableEq M] (ν : M) :
    (datU σ τ hτ a b hab hS e he).ε ν = DescA.fib (cU σ τ hτ a b hab hS e he)
      (isLocallyConstant_cU σ τ hτ a b hab hS e he) ν := rfl

end Chart

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG2 =====
section

/-!
# S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens

* Cross-chart maps `homX σ σ' ρA hσ φ hφ : etS σ' R' ⟶ etS σ R` (for `Spec ρA ≫ σ = σ'`), `homX_kmap`,
  `cval_comapX`; **`datU_compat`**: `psiMap ρA φC hφC (datU ...).ε m = (datU' ...).ε m`.
* On affine opens `U` of `X` (for `V` etale over `X` with `V.hom` affine): `CU V U = Γ(V, V.hom⁻¹ U)` as an etale
  `Γ(X, U)`-algebra, the chart datum `datA`, restriction maps `mapU`, the functor
  **`FU : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat`**, `alphaU : 𝒪_X ⟶ FU` and **`coequifibered_alphaU`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Cross

variable {X : Scheme.{u}} {A A' : Type u} [CommRing A] [CommRing A'] (σ : Spec (CommRingCat.of A) ⟶ X) [Etale σ]
  (σ' : Spec (CommRingCat.of A') ⟶ X) [Etale σ'] (ρA : A →+* A')
  (hσ : Spec.map (CommRingCat.ofHom ρA) ≫ σ = σ')

variable {C C' : Type u} [CommRing C] [Algebra A C] [Algebra.Etale A C] [CommRing C'] [Algebra A' C']
  [Algebra.Etale A' C'] {V : X.Etale}
  (τ : Spec (CommRingCat.of C) ⟶ V.left) (hτ : τ ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ σ)
  (τ' : Spec (CommRingCat.of C') ⟶ V.left)
  (hτ' : τ' ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A' C')) ≫ σ')
  (φC : C →+* C') (hφC : ∀ x, φC (algebraMap A C x) = algebraMap A' C' (ρA x))
  (hτφ : Spec.map (CommRingCat.ofHom φC) ≫ τ = τ')

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

include hσ hτφ in
/-- **Compatibility of the chart data** across charts. -/
theorem datU_compat [Fintype M] [DecidableEq M] (m : M) :
    psiMap ρA φC hφC ((datU σ τ hτ a b hab hS e he).ε m) = (datU σ' τ' hτ' a b hab hS e he).ε m := by
  rw [datU_ε, datU_ε]
  exact fib_map _ _ _ _ _ (cU_compat σ σ' ρA hσ τ hτ τ' hτ' φC hφC hτφ a b hab hS e he) m

end Cross

section Pres

end Pres

section Glue

variable {X : Scheme.{u}}

variable (V : X.Etale) [IsAffineHom V.hom]

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M] {E Q : EtSh Λ X}
  (a : constSh Λ X M ⟶ E) (b : E ⟶ Q) (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact)
  (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

/-- The descent datum on the affine open `U`. -/
def datA (U : X.AffineZariskiSite) : Datum Γ(X, U.1) (CU V U) M :=
  datU U.2.fromSpec (tauU V U) (htauU V U) a b hab hS e he

theorem compatU {U U' : X.AffineZariskiSite} (h : U'.1 ≤ U.1) (m : M) :
    psiMap (rhoX h) (phiV V h) (hphiV V h) ((datA V a b hab hS e he U).ε m) =
      (datA V a b hab hS e he U').ε m :=
  datU_compat U.2.fromSpec U'.2.fromSpec (rhoX h) (U.2.map_fromSpec U'.2 (homOfLE h).op)
    (tauU V U) (htauU V U) (tauU V U') (htauU V U') (phiV V h) (hphiV V h)
    ((U.2.preimage V.hom).map_fromSpec (U'.2.preimage V.hom) (homOfLE (Scheme.Hom.preimage_mono V.hom h)).op)
    a b hab hS e he m

/-- The restriction map of descended algebras. -/
def mapU {U U' : X.AffineZariskiSite} (h : U'.1 ≤ U.1) :
    (datA V a b hab hS e he U).B →+* (datA V a b hab hS e he U').B :=
  mapBL _ _ (rhoX h) (phiV V h) (hphiV V h) (compatU V a b hab hS e he h)

theorem mapU_apply {U U' : X.AffineZariskiSite} (h : U'.1 ≤ U.1) (f : (datA V a b hab hS e he U).B) (ν : M) :
    (mapU V a b hab hS e he h f).1 ν = phiV V h (f.1 ν) := rfl

theorem mapU_algebraMap {U U' : X.AffineZariskiSite} (h : U'.1 ≤ U.1) (x : Γ(X, U.1)) :
    mapU V a b hab hS e he h (algebraMap Γ(X, U.1) (datA V a b hab hS e he U).B x) =
      algebraMap Γ(X, U'.1) (datA V a b hab hS e he U').B (rhoX h x) :=
  mapB_algebraMap _ _ _ _ (hphiV V h) (psiMap (rhoX h) (phiV V h) (hphiV V h))
    (psiMap_j1 (rhoX h) (phiV V h) (hphiV V h)) (psiMap_j2 (rhoX h) (phiV V h) (hphiV V h))
    (compatU V a b hab hS e he h) x

/-- **The presheaf of descended algebras** on the affine opens of `X`. -/
def FU : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (datA V a b hab hS e he U.unop).B
  map {U U'} i := CommRingCat.ofHom (mapU V a b hab hS e he
    (Scheme.AffineZariskiSite.toOpens_mono (leOfHom i.unop)))
  map_id U := CommRingCat.hom_ext (RingHom.ext fun f => Subtype.ext (funext fun ν => pmap_id _ (f.1 ν)))
  map_comp {U₁ U₂ U₃} i j := CommRingCat.hom_ext (RingHom.ext fun f => Subtype.ext (funext fun ν =>
    pmap_comp (Scheme.Hom.preimage_mono V.hom (Scheme.AffineZariskiSite.toOpens_mono (leOfHom i.unop)))
      (Scheme.Hom.preimage_mono V.hom (Scheme.AffineZariskiSite.toOpens_mono (leOfHom j.unop))) _ (f.1 ν)))

theorem FU_map {U U' : X.AffineZariskiSiteᵒᵖ} (i : U ⟶ U') :
    (FU V a b hab hS e he).map i = CommRingCat.ofHom (mapU V a b hab hS e he
      (Scheme.AffineZariskiSite.toOpens_mono (leOfHom i.unop))) := rfl

/-- The structure map `𝒪_X ⟶ FU`. -/
def alphaU : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ FU V a b hab hS e he where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop.1) (datA V a b hab hS e he U.unop).B)
  naturality {U U'} i := CommRingCat.hom_ext (RingHom.ext fun x =>
    (mapU_algebraMap V a b hab hS e he (Scheme.AffineZariskiSite.toOpens_mono (leOfHom i.unop)) x).symm)

theorem alphaU_app (U : X.AffineZariskiSite) (x : Γ(X, U.1)) :
    ((alphaU V a b hab hS e he).app (op U)).hom x = algebraMap Γ(X, U.1) (datA V a b hab hS e he U).B x := rfl

/-- **`FU` is quasi-coherent**: `FU (D(r)) = FU(U)[1/r]`. -/
theorem coequifibered_alphaU : (alphaU V a b hab hS e he).Coequifibered := by
  refine Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr fun U r => ?_
  have h : (U.basicOpen r).1 ≤ U.1 := Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le r)
  exact isLocalizationAway_B (datA V a b hab hS e he U) (datA V a b hab hS e he (U.basicOpen r))
    (rhoX h) (phiV V h) (hphiV V h) r (U.2.isLocalization_of_eq_basicOpen r (homOfLE h) rfl)
    ((U.2.preimage V.hom).isLocalization_of_eq_basicOpen (V.hom.app U.1 r)
      (homOfLE (Scheme.Hom.preimage_mono V.hom h)) (Scheme.preimage_basicOpen V.hom r))
    (compatU V a b hab hS e he h)

end Glue

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG3 =====
section

/-!
# S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective

* Generic (any coequifibered `α : 𝒪_X ⟶ F` on affine opens): `glD H` (the relative gluing data),
  `cover_toBase` (`Spec F(U) ⟶ U₀ ⟶ X` is `Spec α_U ≫ U.fromSpec`), `prop_toBase` (a Zariski-local property holds
  for `toBase` once it holds for every `Spec α_U`), `isFinite_toBase`, `etale_toBase`, `surjective_toBase`.
* For `V` etale and surjective over `X` with `V.hom` affine: `surj_comap`, the instance
  `Module.FaithfullyFlat Γ(X, U) (CU V U)`, and for the descended presheaf `FU`:
  **`U0`**, **`toU0`** `: U0 ⟶ X` with `IsFinite`, `Etale`, `Surjective`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Base

end Base

section Cover

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom]

variable [Surjective V.hom] {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M]
  {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q) (hab : a ≫ b = 0)
  (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

/-- **The descended cover** `U₀`. -/
def U0 : Scheme.{u} := (glD (coequifibered_alphaU V a b hab hS e he)).glued

/-- Its structure map. -/
def toU0 : U0 V a b hab hS e he ⟶ X := (glD (coequifibered_alphaU V a b hab hS e he)).toBase

end Cover

end RamanujanPetersson.EtPBC.DescG

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

/-- Evaluation at `ν`: `B(U) → CU V U`. -/
def evR (U : X.AffineZariskiSite) (ν : M) : (datA V a b hab hS e he U).B →+* CU V U where
  toFun f := f.1 ν
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evR_apply (U : X.AffineZariskiSite) (ν : M) (f : (datA V a b hab hS e he U).B) :
    evR V a b hab hS e he U ν f = f.1 ν := rfl

theorem alphaU_evR (U : X.AffineZariskiSite) (ν : M) :
    (alphaU V a b hab hS e he).app (op U) ≫ CommRingCat.ofHom (evR V a b hab hS e he U ν) = V.hom.app U.1 := by
  ext x
  rfl

end Sheet

end RamanujanPetersson.EtPBC.DescG

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

end Live

section Glob'

variable {O O' S G : Type*} [CommRing O] [CommRing O'] [CommRing S] [CommRing G]
  [Algebra O O'] [Algebra O S] [Algebra O' (PiQ G)] [Algebra O (PiQ G)] [IsScalarTower O O' (PiQ G)]
  (f : S →ₐ[O] PiQ G) (t : O)

/-- `exists_glob_approx` with `N` chosen before the CRT targets `r` (so `r i := t^N` is allowed). -/
theorem exists_glob_approx' [DecidableEq (minimalPrimes G)]
    (hG : ∀ (m : Ideal G) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing G]
    (h1 : ∀ x : O', ∃ c : O, ∃ y : O', x = algebraMap O O' c + algebraMap O O' t * y)
    {ι : Type*} [Finite ι] (J : ι → Ideal S) (hJ : Pairwise fun i j => IsCoprime (J i) (J j))
    (hJt : ∀ (n : ℕ) (i : ι), IsCoprime (Ideal.span {algebraMap O S t ^ n}) (J i))
    (hgen : ∀ x : G, ∃ N : ℕ, algebraMap O (PiQ G) t ^ N * toPiQ x ∈ hatS (O' := O') f)
    (τG : G) (hτ : toPiQ τG = algebraMap O (PiQ G) t) (ht : ∀ p, toPiQ τG p ≠ 0)
    (p₀ : minimalPrimes G) {u₁ : FractionRing (G ⧸ (p₀ : Ideal G))} (hu₁ : u₁ ≠ 0) {j : ℕ}
    (hj₁ : ∃ a, algebraMap (G ⧸ (p₀ : Ideal G)) _ a = toPiQ τG p₀ ^ j * u₁)
    (hj₂ : ∃ b, algebraMap (G ⧸ (p₀ : Ideal G)) _ b = toPiQ τG p₀ ^ j * u₁⁻¹) :
    ∃ N : ℕ, ∀ r : ι → S, ∃ uS : S, (∀ i, uS - r i ∈ J i) ∧ ∃ z ∈ hatS (O' := O') f,
      f uS = algebraMap O (PiQ G) t ^ N * Function.update (1 : PiQ G) p₀ u₁ * (1 - algebraMap O (PiQ G) t * z) := by
  have hũ : Function.update (1 : PiQ G) p₀ u₁ * Function.update (1 : PiQ G) p₀ u₁⁻¹ = 1 := by
    funext p
    by_cases hp : p = p₀
    · subst hp; simp [mul_inv_cancel₀ hu₁]
    · simp [Function.update_of_ne hp]
  have hτu : IsUnit (algebraMap O (PiQ G) t) := by
    rw [← hτ, Pi.isUnit_iff]; exact fun p => (ht p).isUnit
  obtain ⟨T, hT⟩ := hτu
  obtain ⟨N₁, h₁⟩ := exists_mem_hatS_update f t hG hgen τG hτ p₀ u₁ hj₁
  obtain ⟨N₂, h₂⟩ := exists_mem_hatS_update f t hG hgen τG hτ p₀ u₁⁻¹ hj₂
  have hs : algebraMap O (PiQ G) t ^ (N₁ + N₂) * Function.update (1 : PiQ G) p₀ u₁ ∈ hatS (O' := O') f := by
    rw [add_comm, pow_add, mul_assoc]; exact Subalgebra.mul_mem _ (algebraMap_pow_mem_hatS f t N₂) h₁
  have hv' : algebraMap O (PiQ G) t ^ (N₁ + N₂) * Function.update (1 : PiQ G) p₀ u₁⁻¹ ∈ hatS (O' := O') f := by
    rw [pow_add, mul_assoc]; exact Subalgebra.mul_mem _ (algebraMap_pow_mem_hatS f t N₁) h₂
  have hsv : (algebraMap O (PiQ G) t ^ (N₁ + N₂) * Function.update (1 : PiQ G) p₀ u₁) *
      (((T⁻¹ : (PiQ G)ˣ) : PiQ G) ^ (N₁ + N₂) * Function.update (1 : PiQ G) p₀ u₁⁻¹) = 1 := by
    rw [← hT]
    calc (↑T ^ (N₁ + N₂) * Function.update (1 : PiQ G) p₀ u₁) *
          (((T⁻¹ : (PiQ G)ˣ) : PiQ G) ^ (N₁ + N₂) * Function.update (1 : PiQ G) p₀ u₁⁻¹)
        = (↑T * ((T⁻¹ : (PiQ G)ˣ) : PiQ G)) ^ (N₁ + N₂) *
          (Function.update (1 : PiQ G) p₀ u₁ * Function.update (1 : PiQ G) p₀ u₁⁻¹) := by ring
      _ = 1 := by rw [Units.mul_inv, one_pow, hũ, one_mul]
  have hv : algebraMap O (PiQ G) t ^ (2 * (N₁ + N₂)) *
      (((T⁻¹ : (PiQ G)ˣ) : PiQ G) ^ (N₁ + N₂) * Function.update (1 : PiQ G) p₀ u₁⁻¹) ∈ hatS (O' := O') f := by
    have e : algebraMap O (PiQ G) t ^ (2 * (N₁ + N₂)) *
        (((T⁻¹ : (PiQ G)ˣ) : PiQ G) ^ (N₁ + N₂) * Function.update (1 : PiQ G) p₀ u₁⁻¹) =
        algebraMap O (PiQ G) t ^ (N₁ + N₂) * Function.update (1 : PiQ G) p₀ u₁⁻¹ := by
      rw [← hT]
      calc ↑T ^ (2 * (N₁ + N₂)) * (((T⁻¹ : (PiQ G)ˣ) : PiQ G) ^ (N₁ + N₂) * Function.update (1 : PiQ G) p₀ u₁⁻¹)
          = ↑T ^ (N₁ + N₂) * Function.update (1 : PiQ G) p₀ u₁⁻¹ *
            (↑T * ((T⁻¹ : (PiQ G)ˣ) : PiQ G)) ^ (N₁ + N₂) := by ring
        _ = _ := by rw [Units.mul_inv, one_pow, mul_one]
    rw [e]; exact hv'
  refine ⟨N₁ + N₂, fun r => ?_⟩
  obtain ⟨uS, hJu, z, hz, hfu⟩ := exists_approx_crt f t h1 J r hJ hJt hs hsv hv
  exact ⟨uS, hJu, z, hz, hfu⟩

end Glob'

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N4 =====
section

/-!
# S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)

* `algebraMap_residueFieldIso_inv_residueFieldMap` (category level): for `φ : R ⟶ S` and `y : Spec S`,
  `R → κ(φ y) → κ(y)` equals `R → S → κ(y)`;
* `resMapX_spec`, `resMapX_toGen`: `resMapX (Spec.map φ) h (toGen A a) = toGen A' (φ a)`;
* `resMapX_fracIso`: for `ψ : K → K'` extending `φ`, `resMapX (fracIso A K k) = fracIso A' K' (ψ k)`;
* `sepX_genEmb_algebraMap`: `sepX (genEmb (k)) = genEmb (ψ k)` for `k ∈ K`;
* **`resLE_kappaL_kum_field`**: NAT for Kummer classes along `Spec.map φ` when `ζ` and `γ^N` come from `K`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer

section Cat

universe u

end Cat

section Gen

variable {A K A' K' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing A'] [IsDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K']
  (φ : CommRingCat.of A ⟶ CommRingCat.of A') [Etale (Spec.map φ)] (h : Spec.map φ (genPt A') = genPt A)

theorem sepX_genEmb_algebraMap (ψ : K →+* K')
    (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (φ.hom a)) (k : K) :
    sepX (Spec.map φ) h (genEmb A K (algebraMap K (maxUnram A K) k)) =
      genEmb A' K' (algebraMap K' (maxUnram A' K') (ψ k)) := by
  rw [genEmb_algebraMap, sepX_algebraMap, resMapX_fracIso φ h ψ hψ, genEmb_algebraMap]

end Gen

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2UK1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UK1): `1 + t e` is a `d`-th power over an etale neighbourhood (ring level)

Km DESIGN v3 step UK, ring level. Let `χ : B → K` be a point with `χ t = 0`, `d` a unit of `B`, and `g ∈ B[X]` monic of
degree `n > 0`. In the coordinates `y_0 … y_{n-1}` of `B[X] ⧸ (g)`, the equation `(Σ y_i X^i)^d = 1 + t X` is the
system `ukF g d t` (coefficients of the remainder mod `g`). At `y₀ = (1, 0, …, 0)` its Jacobian is `d · 1`
(`uk_jac`, computed with dual numbers, `aeval_dual`) and its value is `-t · (X mod g)`, divisible by `det² = d^{2n}`.
* **`uk_root`** (Tougeron, `tougeron_nbhd_strong`): there are an etale `B → B'` with a point `χ'` over `χ` and
  `y : Fin n → B'` such that `(Σ y_i e^i)^d = 1 + t e` for every root `e` of `g` in every `B'`-algebra.
* `exists_monic_of_isIntegral`: an integral element has a monic equation of positive degree.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC.Cov

universe u v

section Dual

end Dual

section UK

variable {B : Type u} [CommRing B]

/-- **`1 + t e` is a `d`-th power over an etale neighbourhood of `χ`**, uniformly in the roots `e` of `g`. -/
theorem uk_root {K : Type u} [Field K] (χ : B →+* K) {g : B[X]} (hg : g.Monic) (hn : 0 < g.natDegree)
    {t : B} (ht : χ t = 0) {d : ℕ} (hd : IsUnit (d : B)) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra B B') (_ : Algebra.Etale B B') (χ' : B' →+* K)
      (y : Fin g.natDegree → B'), (∀ a, χ' (algebraMap B B' a) = χ a) ∧
      ∀ (S : Type v) [CommRing S] [Algebra B S] [Algebra B' S] [IsScalarTower B B' S] (e : S),
        aeval e g = 0 → (∑ i : Fin g.natDegree, algebraMap B' S (y i) * e ^ (i : ℕ)) ^ d =
          1 + algebraMap B S t * e := by
  have : Nontrivial B := χ.domain_nontrivial
  have hjac := uk_jac g hg hn d t
  have hmin : tmin (ukF g d t) (fun k => k) (ukY0 hn) = Matrix.diagonal fun _ => (d : B) := by
    ext k j
    simp only [tmin, Matrix.of_apply]
    rw [(hjac j k).2, Matrix.diagonal_apply]
    rcases eq_or_ne j k with h | h
    · simp [h]
    · simp [h, Ne.symm h]
  have hdet : (tmin (ukF g d t) (fun k => k) (ukY0 hn)).det = (d : B) ^ g.natDegree := by
    rw [hmin, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨u, hu⟩ := hd
  let e : Fin g.natDegree → B := fun j => -(t * (X %ₘ g).coeff j) * ((u⁻¹ : Bˣ) : B) ^ (2 * g.natDegree)
  have hf : ∀ j, MvPolynomial.eval (ukY0 hn) (ukF g d t j) =
      (tmin (ukF g d t) (fun k => k) (ukY0 hn)).det ^ 2 * e j := by
    intro j
    rw [(hjac j j).1, hdet, ← hu, ← pow_mul, mul_comm g.natDegree 2]
    simp only [e]
    rw [mul_left_comm, ← mul_pow, Units.mul_inv, one_pow, mul_one]
  have he : ∀ j, χ (e j) = 0 := fun j => by simp [e, ht]
  obtain ⟨B', i1, i2, i3, χ', y', d', hχ', hy', -, -, -⟩ :=
    tougeron_nbhd_strong χ (ukF g d t) (fun k => k) (ukY0 hn) e hf he
  refine ⟨B', i1, i2, i3, χ', y', hχ', fun S _ _ _ _ e he => ?_⟩
  have := uk_eval g hg d t ((IsScalarTower.toAlgHom B B' S).comp (MvPolynomial.aeval y'))
    (fun j => by rw [AlgHom.comp_apply, hy' j, map_zero]) e he
  simpa using this

end UK

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2UK2b =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UK2b): the `d`-th root of `1 + t e` on the pieces over an etale `B → B'`

`D = Spec B` etale over `P` (through `hB`), `X R : P.Etale`, `W := (D ×_P X) ×_P R`; `wD : W ⟶ D`,
`bW : B ⟶ Γ(W)`, `bK p : B →+* Frac(Γ(W) ⧸ p)`.
* `wm_wD`: `wm (prdMap d X) ≫ wD D X = wD D₁ X ≫ d.left`;
* `uk_root'`: O2UK1 `uk_root` with an explicit ring map `ι : B ⟶ B'` (`Spec ι` etale);
* **`exists_pow_of_uk`**: for `D₁ ⟶ Spec B'` and a piece `p₁` of `W₁ := (D₁ ×_P X) ×_P R`, every `Ψ` compatible with
  `wm (prdMap d X)` sends `1 + t e` (`e` a root of `g` over `B`) to a `d`-th power.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.GenGeo

universe u

section WD

end WD

section Ring

end Ring

section UK

variable {B : CommRingCat.{u}} {K : Type u} [Field K]

/-- **`uk_root` with an explicit ring map.** -/
theorem uk_root' (χ : B →+* K) {g : B[X]} (hg : g.Monic) (hn : 0 < g.natDegree) {t : B} (ht : χ t = 0) {d : ℕ}
    (hd : IsUnit (d : B)) :
    ∃ (B' : CommRingCat.{u}) (ι : B ⟶ B') (_ : Etale (Spec.map ι)) (χ' : B' →+* K) (y : Fin g.natDegree → B'),
      χ'.comp ι.hom = χ ∧ ∀ (S : Type u) [CommRing S] (σ : B' →+* S) (e : S), g.eval₂ (σ.comp ι.hom) e = 0 →
        (∑ i : Fin g.natDegree, σ (y i) * e ^ (i : ℕ)) ^ d = 1 + σ (ι t) * e := by
  obtain ⟨B', _, _, hE, χ', y, hχ', hy⟩ := uk_root χ hg hn ht hd
  have hEt : (algebraMap B B').Etale := RingHom.etale_algebraMap.2 hE
  refine ⟨CommRingCat.of B', CommRingCat.ofHom (algebraMap B B'),
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 hEt, χ', y, RingHom.ext hχ', fun S _ σ e he => ?_⟩
  letI : Algebra B' S := σ.toAlgebra
  letI : Algebra B S := (σ.comp (algebraMap B B')).toAlgebra
  haveI : IsScalarTower B B' S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact hy S e ((aeval_def e g).trans he)

end UK

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Bd2 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Bd2): `H = 1 + t_i e` on every piece at a bad point

REL PLAN v2 (s126), file R2. At a bad point `a_i` (chart `D' = chEt c φ'` with `d : D' ⟶ D_{g₀}`, `φ'(X - C a)` a
unit), the unit `H` of `Y_G` with `H ρ(t)^N = ρ(y)`, `y = liveMod uS t^N`, `uS - t^N ∈ (X - C a_i) S`:
* **`liveMod_eq_add`** (generic): `liveMod uS t^N = t^N + r s` with `s` integral when `uS - t^N ∈ r S`;
* **`exists_bad_genC`** (generic): `exists_bad_genB` (O2Bd1) from the `liveMod` form;
* **`exists_bad_e`**: the `e`, `g`, `he`, `hHq` inputs of `uk_kill_glob` (O2UKd3) at `D'` with `m := mG`, `t := φ'(X - C a_i)`;
* **`exists_S4H'`**: `exists_S4H` (O2Gl2k) also returning the relation `H ρ(t)^N = ρ(y)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section BadAlg

variable {O Y G' B' : Type} [CommRing O] [CommRing Y] [CommRing G'] [CommRing B'] [Algebra O Y]
  (hY : ∀ (m : Ideal Y) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing Y]

/-- `exists_bad_genB` from the `liveMod` form of the relation. -/
theorem exists_bad_genC (aY : O →+* Y) (hAY : algebraMap O Y = aY)
    (φ' : O →+* B') (bW' : B' →+* G') (κ : Y →+* G') (hκ : ∀ o, κ (aY o) = bW' (φ' o))
    (β : ∀ q : minimalPrimes G', B' →+* FractionRing (G' ⧸ q.1))
    (hβ : ∀ q b, β q b = algebraMap (G' ⧸ q.1) _ (Ideal.Quotient.mk q.1 (bW' b)))
    {t r : O} {N : ℕ} (ht : IsUnit (φ' t)) (uS : integralClosure O Y)
    (hu : uS - algebraMap O (integralClosure O Y) t ^ N ∈ Ideal.span {algebraMap O (integralClosure O Y) r})
    {Hc : G'} (hH : Hc * bW' (φ' t) ^ N = κ (liveMod hY (uS : Y) (aY t ^ N))) [Nontrivial B'] :
    ∃ e : ∀ q : minimalPrimes G', FractionRing (G' ⧸ q.1), ∃ g : B'[X], g.Monic ∧ 0 < g.natDegree ∧
      (∀ q, g.eval₂ (β q) (e q) = 0) ∧
      ∀ q : minimalPrimes G', algebraMap (G' ⧸ q.1) (FractionRing (G' ⧸ q.1)) (Ideal.Quotient.mk q.1 Hc) =
        1 + β q (φ' r) * e q := by
  subst hAY
  obtain ⟨s, hs, hy⟩ := liveMod_eq_add hY uS hu
  rw [hy] at hH
  exact exists_bad_genB φ' bW' κ hκ β hβ ht.unit ht.unit_spec.symm hs hH

end BadAlg

section BadChart

end BadChart

end RamanujanPetersson.EtPBC.EtKum

end

end


