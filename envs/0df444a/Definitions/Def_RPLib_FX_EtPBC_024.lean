-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_024
-- name    : RPLib_FX_EtPBC_024
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:14:56.020126+00:00
-- url     : https://prove2.me/theorems/481f724c-0e7a-5608-9aad-f233ce5aa5b2
-- title:
--   Proper base change for the projective line, library file 024
-- statement:
--   File 024 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovAs5c`: S4-EtPBC-A, R4-T2 (A3 assembly, As5c): one chart descends to a f.g. subalgebra
--   * `S4.Def_RP_EtPBC_A_CovAs5d`: S4-EtPBC-A, R4-T2 (A3 assembly, As5d): substitution data descend to a f.g. subalgebra
--   * `S4.Def_RP_EtPBC_A_CovAs6a`: S4-EtPBC-A, R4-T2 (A3 assembly, As6a): pushing the descended package along `σ : C →ₐ[A] R'`
--   * `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
--   * `S4.Def_RP_EtPBC_A_Z3P1b`: S4-EtPBC-A, (Z) geometric layer 4 (G-a): the transition `t s = 1` on the overlap of the two charts of `P¹_K`
--   * `S4.Def_RP_EtPBC_A_DescA`: S4-EtPBC-A, R4-T1a: descent of a torsor under a finite group along a flat cover (algebra)
--   * `S4.Def_RP_EtPBC_A_DescB`: S4-EtPBC-A, R4-T1b (algebra part): descent data from locally constant functions, and localization
--   * `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
--   * `S4.Def_RP_EtPBC_A_DescC`: S4-EtPBC-A, R4-T1d (algebra): sheets of the descended algebra
--   * `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_019
import Definitions.Def_RPLib_FX_EtPBC_020
import Definitions.Def_RPLib_FX_EtPBC_021

/-!
# Proper base change for the projective line, library file 024

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovAs5c`: S4-EtPBC-A, R4-T2 (A3 assembly, As5c): one chart descends to a f.g. subalgebra
* `S4.Def_RP_EtPBC_A_CovAs5d`: S4-EtPBC-A, R4-T2 (A3 assembly, As5d): substitution data descend to a f.g. subalgebra
* `S4.Def_RP_EtPBC_A_CovAs6a`: S4-EtPBC-A, R4-T2 (A3 assembly, As6a): pushing the descended package along `σ : C →ₐ[A] R'`
* `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
* `S4.Def_RP_EtPBC_A_Z3P1b`: S4-EtPBC-A, (Z) geometric layer 4 (G-a): the transition `t s = 1` on the overlap of the two charts of `P¹_K`
* `S4.Def_RP_EtPBC_A_DescA`: S4-EtPBC-A, R4-T1a: descent of a torsor under a finite group along a flat cover (algebra)
* `S4.Def_RP_EtPBC_A_DescB`: S4-EtPBC-A, R4-T1b (algebra part): descent data from locally constant functions, and localization
* `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
* `S4.Def_RP_EtPBC_A_DescC`: S4-EtPBC-A, R4-T1d (algebra): sheets of the descended algebra
* `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
-/

set_option autoImplicit false

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

theorem gmap_tvC_tiC {r : ℕ} {C D : Subalgebra A S} (h : C ≤ D)
    (gC : Fin r → MvPolynomial (Fin r) (C ⊗[A] B)) :
    gmap (tvC B D) (gmap (tiC B h) gC) = gmap (tvC B C) gC :=
  funext fun j => map_tvC_tiC h (gC j)

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

end Desc

section BCg

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B N : Type u} [CommRing B] [Algebra A B] [CommRing N] [Algebra A N] (φ : B →ₐ[A] N)

theorem gmap_tvC_bcC {r : ℕ} (C : Subalgebra A S) (gC : Fin r → MvPolynomial (Fin r) (C ⊗[A] B)) :
    gmap (tvC N C) (gmap (bcC φ C) gC) =
      gmap (Algebra.TensorProduct.map (AlgHom.id A S) φ : S ⊗[A] B →+* S ⊗[A] N) (gmap (tvC B C) gC) :=
  funext fun j => map_tvC_bcC φ C (gC j)

end BCg

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs6a =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As6a): pushing the descended package along `σ : C →ₐ[A] R'`

`tsC σ B = σ ⊗ id_B : C ⊗ B → R' ⊗ B`; `tsC_bcC`, `map_tsC_bcC`, `gmap_tsC_bcC`: `tsC` commutes with base change
along `φ` (`bcC φ C` over `C`, `bcS R' φ` over `R'`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section TsC

end TsC

section TsCBC

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S] {R' : Type u} [CommRing R']
  [Algebra A R'] {B N : Type u} [CommRing B] [Algebra A B] [CommRing N] [Algebra A N] (φ : B →ₐ[A] N)

theorem gmap_tsC_bcC {r : ℕ} {C : Subalgebra A S} (σ : C →ₐ[A] R')
    (gC : Fin r → MvPolynomial (Fin r) (C ⊗[A] B)) :
    gmap (tsC σ N) (gmap (bcC φ C) gC) = gmap (bcS R' φ) (gmap (tsC σ B) gC) :=
  funext fun j => map_tsC_bcC φ σ (gC j)

end TsCBC

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

/-- The overlap map of chart 0 over `R'`. -/
def psi0 : Pres (gmap (tsC σ B₀) gC₀) →+* Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀)) :=
  ((presCongr (gmap_tsC_bcC φ₀ σ gC₀).symm).toRingEquiv : _ →+* _).comp
    (presMap (bcS R' φ₀) (gmap (tsC σ B₀) gC₀))

theorem psi0_alg (x : R' ⊗[A] B₀) :
    psi0 φ₀ σ gC₀ (algebraMap (R' ⊗[A] B₀) (Pres (gmap (tsC σ B₀) gC₀)) x) =
      algebraMap (R' ⊗[A] N) (Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀))) (bcS R' φ₀ x) := by
  unfold psi0
  rw [RingHom.comp_apply, presMap_algebraMap]
  exact (presCongr (gmap_tsC_bcC φ₀ σ gC₀).symm).commutes (bcS R' φ₀ x)

theorem psi0_X (j : Fin r₀) :
    psi0 φ₀ σ gC₀ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = Ideal.Quotient.mk _ (MvPolynomial.X j) := by
  unfold psi0
  rw [RingHom.comp_apply, presMap_mk, MvPolynomial.map_X]
  rfl

theorem psi0_away [Module.Flat A R'] (t : B₀) (h : IsAwayMap (φ₀ : B₀ →+* N) t) :
    IsAwayMap (psi0 φ₀ σ gC₀) (algebraMap (R' ⊗[A] B₀) (Pres (gmap (tsC σ B₀) gC₀)) ((1 : R') ⊗ₜ[A] t)) :=
  presMap_away_equiv (bcS R' φ₀) ((1 : R') ⊗ₜ[A] t) (away_bc (S := R') φ₀ t h) (gmap (tsC σ B₀) gC₀)
    (presCongr (gmap_tsC_bcC φ₀ σ gC₀).symm).toRingEquiv

end Psi

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3P1b =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 4 (G-a): the transition `t s = 1` on the overlap of the two charts of `P¹_K`

* `x01 = X₀ X₁`, `tr0`, `tr1`: the restrictions `K[X₀,X₁]_(Xᵢ) → K[X₀,X₁]_(X₀X₁)` (Mathlib `awayMap`);
  `tr_mul`: `tr0 (X₁/X₀) * tr1 (X₀/X₁) = 1`.
* `c0 = Spec tr0 ≫ ch 0`, `c1 = Spec tr1 ≫ ch 1`, `c0_eq_c1` (both are `Proj.awayι (X₀X₁)`), `top_le_c0`.
* `appLE_injective_of_eq`: for an open immersion `f` with image `W`, `f.appLE W ⊤` is injective.
* **`coord_mul_coord`**: `coord 0 1 |_W * coord 1 0 |_W = 1` on `W = chU 0 ⊓ chU 1`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K]

theorem top_le_c0 : (⊤ : (Spec (CommRingCat.of (Away (gr K) (x01 K)))).Opens) ≤ c0 K ⁻¹ᵁ (chU K 0 ⊓ chU K 1) := by
  intro x _
  refine ⟨⟨(Spec.map (CommRingCat.ofHom (tr0 K))).base x, trivial, rfl⟩, ?_⟩
  rw [c0_eq_c1]
  exact ⟨(Spec.map (CommRingCat.ofHom (tr1 K))).base x, trivial, rfl⟩

theorem res0 : (Scheme.ΓSpecIso _).inv ≫ ((ch K 0).appIso ⊤).inv ≫
    (Proj (gr K)).presheaf.map (homOfLE inf_le_left : chU K 0 ⊓ chU K 1 ⟶ chU K 0).op ≫
      (c0 K).appLE (chU K 0 ⊓ chU K 1) ⊤ (top_le_c0 K) =
    CommRingCat.ofHom (tr0 K) ≫ (Scheme.ΓSpecIso _).inv :=
  res_aux (ch K 0) _ (c0 K) rfl _ inf_le_left _

theorem res1 : (Scheme.ΓSpecIso _).inv ≫ ((ch K 1).appIso ⊤).inv ≫
    (Proj (gr K)).presheaf.map (homOfLE inf_le_right : chU K 0 ⊓ chU K 1 ⟶ chU K 1).op ≫
      (c0 K).appLE (chU K 0 ⊓ chU K 1) ⊤ (top_le_c0 K) =
    CommRingCat.ofHom (tr1 K) ≫ (Scheme.ΓSpecIso _).inv :=
  res_aux (ch K 1) _ (c0 K) (c0_eq_c1 K) _ inf_le_right _

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_DescA =====
section

/-!
# S4-EtPBC-A, R4-T1a: descent of a torsor under a finite group along a flat cover (algebra)

`A → C` an algebra, `N` a finite abelian group, and a descent datum `D : Datum A C N`: complete orthogonal
idempotents `ε ν ∈ C ⊗ C` (the indicator functions of the values `ν` of a locally constant `N`-valued cocycle on
`Spec (C ⊗ C)`), trivial on the diagonal (`diag`) and satisfying the cocycle identity
`ε¹³_ν = ∑_α ε¹²_α ε²³_(ν - α)` in `C ⊗ C ⊗ C` (`cocycle`).

* `B D`: the `A`-subalgebra of `N → C` of the `f` with `f ν ⊗ 1 = ∑_m ε_m (1 ⊗ f (ν + m))` (functions on the
  trivial torsor `N × Spec C` that descend), `mem_B_iff` (`B = ker delta`).
* `delta'`, `key1`, `eq_sum_of_delta'`, `gOf`, `lmul'_gOf`, `delta'_gOf`, `cocycle'`: the base change of `delta`
  along `C` has kernel `N → C` (multiplication `m12` gives the retraction).
* **`theta_bijective`** (`C` flat over `A`): `C ⊗[A] B ≅ (N → C)`, `c ⊗ f ↦ c f`; `thetaEquiv`.
* With `C` faithfully flat: **`finite_B`**, **`etale_B`**, and `exists_prime_over` (`Spec B → Spec A` is onto).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.DescA

universe u

open TensorProduct

section Maps

end Maps

namespace Datum

variable {A C N : Type u} [CommRing A] [CommRing C] [Algebra A C] [AddCommGroup N] [Fintype N]
  [DecidableEq N] (D : Datum A C N)

theorem delta'_gOf (h : N → C) : D.delta' (D.gOf h) = 0 := by
  funext ν
  simp only [delta', LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, sub_eq_zero, gOf, map_sum,
    map_mul, e12_j1]
  -- RHS: ∑ m, e23 ε_m * ∑ k, e13 ε_k * J (h (ν + m - k)), reindex `k = α + m`
  have hre : ∀ m, e23 A C (D.ε m) * ∑ k, e13 A C (D.ε k) * e13 A C (j1 A C (h (ν + m - k))) =
      ∑ α, e23 A C (D.ε m) * e13 A C (D.ε (α + m)) * e13 A C (j1 A C (h (ν - α))) := by
    intro m
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (-m)) _ _ fun k => ?_
    simp only [Equiv.coe_addRight, neg_add_cancel_right]
    rw [mul_assoc]
    congr 3
    abel
  rw [Finset.sum_congr rfl fun m _ => hre m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_mul, D.cocycle']

section Tensor

theorem comm_delta (x : C ⊗[A] (N → C)) :
    TensorProduct.piRightHom A A C (fun _ : N => C ⊗[A] C) (D.delta.lTensor C x) =
      D.delta' (TensorProduct.piRightHom A A C (fun _ : N => C) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c f =>
    funext ν
    simp only [LinearMap.lTensor_tmul, TensorProduct.piRightHom_tmul, delta, delta', LinearMap.coe_mk,
      AddHom.coe_mk, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tmul_sub, tmul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem theta_injective [Module.Flat A C] : Function.Injective D.theta := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  set x' := D.B.val.toLinearMap.lTensor C x with hx'
  set g := TensorProduct.piRightHom A A C (fun _ : N => C) x' with hg
  have hδ : D.delta' g = 0 := by
    rw [hg, ← comm_delta, hx', ← LinearMap.lTensor_comp_apply,
      (D.exact_val).linearMap_comp_eq_zero, LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero]
  have hm : ∀ ν, Algebra.TensorProduct.lmul' A (g ν) = 0 := fun ν => by
    rw [hg, ← theta_eq, hx, Pi.zero_apply]
  have hg0 : g = 0 := by
    funext ν
    rw [D.eq_sum_of_delta' g hδ ν]
    simp only [hm, map_zero, mul_zero, Finset.sum_const_zero, Pi.zero_apply]
  have hx'0 : x' = 0 := by
    have := (TensorProduct.piRight A A C (fun _ : N => C)).injective
      (a₁ := x') (a₂ := 0) (by simp only [TensorProduct.piRight_apply, map_zero]; exact hg0)
    exact this
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := C) D.B.val.toLinearMap
    (fun a b h => Subtype.ext h) (by rw [map_zero]; exact hx'0)

theorem theta_surjective [Module.Flat A C] : Function.Surjective D.theta := by
  intro h
  set x' := (TensorProduct.piRight A A C (fun _ : N => C)).symm (D.gOf h) with hx'
  have hpx : TensorProduct.piRightHom A A C (fun _ : N => C) x' = D.gOf h := by
    rw [hx', ← TensorProduct.piRight_apply, LinearEquiv.apply_symm_apply]
  have h0 : D.delta.lTensor C x' = 0 := by
    apply (TensorProduct.piRight A A C (fun _ : N => C ⊗[A] C)).injective
    rw [map_zero, TensorProduct.piRight_apply, comm_delta, hpx, delta'_gOf]
  obtain ⟨x, hx⟩ := (Module.Flat.lTensor_exact C D.exact_val x').mp h0
  refine ⟨x, funext fun ν => ?_⟩
  rw [theta_eq, hx, hpx, lmul'_gOf]

theorem theta_bijective [Module.Flat A C] : Function.Bijective D.theta := ⟨D.theta_injective, D.theta_surjective⟩

/-- `C ⊗[A] B ≅ (N → C)`: the descended algebra trivialises over `C`. -/
def thetaEquiv [Module.Flat A C] : C ⊗[A] D.B ≃ₐ[C] (N → C) := AlgEquiv.ofBijective D.theta D.theta_bijective

end Tensor

section FF

variable [Module.FaithfullyFlat A C]

theorem finite_B : Module.Finite A D.B := by
  haveI : Module.Finite C (C ⊗[A] D.B) := Module.Finite.equiv D.thetaEquiv.symm.toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat C

theorem etale_B : Algebra.Etale A D.B := by
  haveI : Algebra.Etale C (C ⊗[A] D.B) := Algebra.Etale.of_equiv D.thetaEquiv.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat C

end FF

end Datum

end RamanujanPetersson.EtPBC.DescA

end

end

-- ===== S4.Def_RP_EtPBC_A_DescB =====
section

/-!
# S4-EtPBC-A, R4-T1b (algebra part): descent data from locally constant functions, and localization

* `fib c hc ν`: for `c : PrimeSpectrum R → N` locally constant, the idempotent of the clopen `{c = ν}`
  (`fib_not_mem`: `fib c hc ν ∉ P ↔ c P = ν`); `idem_ext` (idempotents are determined by their primes),
  `fib_mul_ne`, `fib_sum`, `fib_map` (naturality along ring maps).
* **`mkDatum c hc hdiag hcoc : Datum A C N`** from a locally constant `c` on `Spec (C ⊗[A] C)` that vanishes on the
  diagonal and satisfies the cocycle identity pointwise.
* `mapB`: the map of descended algebras induced by compatible maps; `mapB_id`, `mapB_comp`, `mapB_algebraMap`.
* `psiMap ρA φC hφC : C ⊗[A] C →+* C' ⊗[A'] C'`; `psiMap_ker` (kernel is `r`-power torsion when `A'`, `C'` are the
  localizations away from `r`).
* **`isLocalizationAway_B`**: then `D'.B` is the localization of `D.B` away from `r` (input of `Coequifibered`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.DescA

universe u

open TensorProduct

section Idem

section Orth

end Orth

end Idem

section Mk

end Mk

section Map

variable {A C A' C' A'' C'' : Type u} [CommRing A] [CommRing C] [Algebra A C] [CommRing A'] [CommRing C']
  [Algebra A' C'] [CommRing A''] [CommRing C''] [Algebra A'' C''] {N : Type u} [AddCommGroup N] [Fintype N]
  [DecidableEq N]

/-- **Localization**: if `A'`, `C'` are the localizations of `A`, `C` away from `r` and the data are compatible,
then `D'.B` is the localization of `D.B` away from `r`. -/
theorem isLocalizationAway_B (D : Datum A C N) (D' : Datum A' C' N) (ρA : A →+* A') (φC : C →+* C')
    (hφC : ∀ a, φC (algebraMap A C a) = algebraMap A' C' (ρA a)) (r : A)
    (hA : letI := ρA.toAlgebra; IsLocalization.Away r A')
    (hC : letI := φC.toAlgebra; IsLocalization.Away (algebraMap A C r) C')
    (hε : ∀ m, psiMap ρA φC hφC (D.ε m) = D'.ε m) :
    letI := (mapBL D D' ρA φC hφC hε).toAlgebra
    IsLocalization.Away (algebraMap A D.B r) D'.B := by
  letI : Algebra D.B D'.B := (mapBL D D' ρA φC hφC hε).toAlgebra
  have hr : IsUnit (ρA r) := by
    letI : Algebra A A' := ρA.toAlgebra
    haveI : IsLocalization.Away r A' := hA
    exact IsLocalization.Away.algebraMap_isUnit r
  have hφr : ∀ n : ℕ, φC (algebraMap A C r ^ n) = algebraMap A' C' (ρA r ^ n) := fun n => by
    simp only [map_pow, hφC]
  have hBr : ∀ n : ℕ, algebraMap D.B D'.B (algebraMap A D.B r ^ n) = algebraMap A' D'.B (ρA r ^ n) :=
    fun n => Subtype.ext (funext fun _ => hφr n)
  have hcommon : ∀ k : N → ℕ, ∃ K : ℕ, ∀ ν, k ν ≤ K := fun k =>
    ⟨∑ ν, k ν, fun ν => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ ν)⟩
  letI : Algebra C C' := φC.toAlgebra
  haveI : IsLocalization.Away (algebraMap A C r) C' := hC
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    show IsUnit (algebraMap D.B D'.B (algebraMap A D.B r ^ n))
    rw [hBr]
    exact (hr.pow n).map _
  · intro g
    have hs : ∀ ν, ∃ (c : C) (k : ℕ), g.1 ν * algebraMap A' C' (ρA r ^ k) = φC c := by
      intro ν
      obtain ⟨⟨c, ⟨_, k, rfl⟩⟩, hck⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A C r)) (g.1 ν)
      exact ⟨c, k, by rw [← hφr]; exact hck⟩
    choose c k hck using hs
    obtain ⟨K, hkK⟩ := hcommon k
    let f₀ : N → C := fun ν => algebraMap A C r ^ (K - k ν) * c ν
    have hf₀ : ∀ ν, φC (f₀ ν) = algebraMap A' C' (ρA r ^ K) * g.1 ν := by
      intro ν
      show φC (algebraMap A C r ^ (K - k ν) * c ν) = _
      rw [map_mul, hφr, ← hck, ← pow_sub_mul_pow (ρA r) (hkK ν), map_mul]
      ring
    have e1 : ∀ y : C', j1 A' C' (algebraMap A' C' (ρA r ^ K) * y) =
        algebraMap A' (C' ⊗[A'] C') (ρA r ^ K) * j1 A' C' y := fun y => by
      rw [map_mul, AlgHom.commutes]
    have e2 : ∀ y : C', j2 A' C' (algebraMap A' C' (ρA r ^ K) * y) =
        algebraMap A' (C' ⊗[A'] C') (ρA r ^ K) * j2 A' C' y := fun y => by
      rw [map_mul, AlgHom.commutes]
    have hδ : ∀ ν, psiMap ρA φC hφC (D.delta f₀ ν) = 0 := by
      intro ν
      show psiMap ρA φC hφC (j1 A C (f₀ ν) - ∑ m, D.ε m * j2 A C (f₀ (ν + m))) = 0
      rw [map_sub, map_sum, psiMap_j1, hf₀, e1, (mem_B D' _).mp g.2 ν, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [map_mul, hε, psiMap_j2, hf₀, e2]
      ring
    have hn : ∀ ν, ∃ n : ℕ, algebraMap A (C ⊗[A] C) (r ^ n) * D.delta f₀ ν = 0 :=
      fun ν => psiMap_ker ρA φC hφC r hA hC _ (hδ ν)
    choose n hn using hn
    obtain ⟨M, hnM⟩ := hcommon n
    have hfB : (r ^ M) • f₀ ∈ D.B := by
      rw [D.mem_B_iff, map_smul]
      funext ν
      rw [Pi.smul_apply, Algebra.smul_def, ← pow_sub_mul_pow r (hnM ν), map_mul, mul_assoc, hn ν,
        mul_zero]
      rfl
    refine ⟨⟨⟨(r ^ M) • f₀, hfB⟩, ⟨algebraMap A D.B r ^ (M + K), M + K, rfl⟩⟩, ?_⟩
    show g * algebraMap D.B D'.B (algebraMap A D.B r ^ (M + K)) = algebraMap D.B D'.B ⟨(r ^ M) • f₀, hfB⟩
    rw [hBr]
    apply Subtype.ext
    funext ν
    show g.1 ν * algebraMap A' C' (ρA r ^ (M + K)) = φC ((r ^ M) • f₀ ν)
    simp only [Algebra.smul_def, map_mul, hf₀, hφC, map_pow, pow_add]
    ring
  · intro x y hxy
    have h : ∀ ν, ∃ n : ℕ, algebraMap A C r ^ n * (x.1 ν - y.1 ν) = 0 := by
      intro ν
      have e : algebraMap C C' (x.1 ν - y.1 ν) = 0 := by
        show φC (x.1 ν - y.1 ν) = 0
        rw [map_sub, sub_eq_zero]
        exact congrFun (congrArg Subtype.val hxy) ν
      obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
        (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap A C r)) C' _).mp e
      exact ⟨n, hn⟩
    choose n hn using h
    obtain ⟨M, hnM⟩ := hcommon n
    refine ⟨⟨algebraMap A D.B r ^ M, M, rfl⟩, ?_⟩
    apply Subtype.ext
    funext ν
    show algebraMap A C r ^ M * x.1 ν = algebraMap A C r ^ M * y.1 ν
    rw [← sub_eq_zero, ← mul_sub, ← pow_sub_mul_pow _ (hnM ν), mul_assoc, hn ν, mul_zero]

end Map

end RamanujanPetersson.EtPBC.DescA

end

end

-- ===== S4.Def_RP_EtPBC_A_LshEt =====
section

/-!
# S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`

For an etale `e : U ⟶ X`, a geometric point `x` of `X` and a module `J`, the restriction
`res e (x_* J)` of the skyscraper sheaf is assembled from the skyscraper sheaves `l_* J` at the
lifts `l` of `x` along `e` (`pr`, `assemble`, `assemble_pr`, `hom_ext_pr`). Hence:
* `injective_res_sky`: `res e (x_* J)` is injective for `J` injective;
* `res e` preserves injective objects (every injective is a retract of its god sheaf);
* **`lsh e Λ = e_!` preserves monomorphisms** (Mathlib's
  `preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite
open RamanujanPetersson.EtCompact

noncomputable section

namespace RamanujanPetersson.EtSheaves.LshEt

universe u

variable {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] (x : GeomPt X)

variable {Λ : Type u} [CommRing Λ] (J : ModuleCat.{u} Λ)

/-- **`res e (x_* J)` is injective** for an injective module `J`. -/
theorem injective_res_sky [Injective J] : Injective ((res e Λ).obj (x.point.skyscraperSheaf J)) where
  factors {A B} g f _ := by
    have hl : ∀ l, Injective ((liftPt e x l).point.skyscraperSheaf J) := fun l =>
      Injective.injective_of_adjoint (liftPt e x l).point.skyscraperSheafAdjunction _
    choose h hh using fun l => by
      haveI := hl l
      exact Injective.factors (g ≫ pr e x J l) f
    refine ⟨assemble e x J h, hom_ext_pr e x J fun l => ?_⟩
    rw [Category.assoc, assemble_pr, hh]

end RamanujanPetersson.EtSheaves.LshEt

end

end

-- ===== S4.Def_RP_EtPBC_A_DescC =====
section

/-!
# S4-EtPBC-A, R4-T1d (algebra): sheets of the descended algebra

For a descent datum `D : Datum A C N`:
* `D.evB ν : D.B →+* C` (`f ↦ f ν`, the `ν`-th sheet);
* **`exists_sheet_prime`** [FaithfullyFlat]: every prime of `D.B` is pulled back from a prime of `C` along some sheet;
* `eps_j1`, **`key_sheet`** [Flat]: if a ring map `ψ : C ⊗[A] C → R` identifies the sheets `i` (through `j1`) and `j`
  (through `j2`) and `ψ (D.ε k) ≠ 0`, then `j = i + k`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.DescA.Datum

open TensorProduct

universe u

variable {A C N : Type u} [CommRing A] [CommRing C] [Algebra A C] [AddCommGroup N] [Fintype N]
  [DecidableEq N] (D : Datum A C N)

theorem exists_sheet_prime [Module.FaithfullyFlat A C] (Q : PrimeSpectrum D.B) :
    ∃ ν : N, ∃ P : PrimeSpectrum C, PrimeSpectrum.comap (D.evB ν) P = Q := by
  obtain ⟨Q', hQ'⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := D.B) (B := D.B ⊗[A] C) Q
  let e : D.B ⊗[A] C ≃+* (N → C) :=
    (Algebra.TensorProduct.comm A D.B C).toRingEquiv.trans D.thetaEquiv.toRingEquiv
  have hev : ∀ f : D.B, e.symm f.1 = algebraMap D.B (D.B ⊗[A] C) f := fun f => by
    rw [RingEquiv.symm_apply_eq]
    funext ν
    show f.1 ν = D.theta (Algebra.TensorProduct.comm A D.B C (f ⊗ₜ 1)) ν
    rw [Algebra.TensorProduct.comm_tmul, D.theta_tmul, one_mul]
  obtain ⟨⟨ν, P⟩, hP⟩ := (PrimeSpectrum.sigmaToPi_bijective (fun _ : N => C)).2
    (PrimeSpectrum.comap e.symm.toRingHom Q')
  refine ⟨ν, P, PrimeSpectrum.ext ?_⟩
  rw [← hQ']
  have h1 : P.asIdeal.comap (Pi.evalRingHom (fun _ : N => C) ν) = Q'.asIdeal.comap e.symm.toRingHom :=
    congrArg PrimeSpectrum.asIdeal hP
  show P.asIdeal.comap (D.evB ν) = Q'.asIdeal.comap (algebraMap D.B (D.B ⊗[A] C))
  calc P.asIdeal.comap (D.evB ν)
      = (P.asIdeal.comap (Pi.evalRingHom (fun _ : N => C) ν)).comap D.B.val.toRingHom := by
        rw [Ideal.comap_comap]
        rfl
    _ = (Q'.asIdeal.comap e.symm.toRingHom).comap D.B.val.toRingHom := by rw [h1]
    _ = Q'.asIdeal.comap (algebraMap D.B (D.B ⊗[A] C)) := by
        rw [Ideal.comap_comap]
        congr 1
        exact RingHom.ext hev

/-- **The sheets are distinct**: if `ψ` identifies sheet `i` with sheet `j` and `ψ (ε k) ≠ 0`, then `j = i + k`. -/
theorem key_sheet [Module.Flat A C] {R : Type u} [CommRing R] (ψ : C ⊗[A] C →+* R) (i j k : N)
    (h : ∀ f : D.B, ψ (j1 A C (f.1 i)) = ψ (j2 A C (f.1 j))) (hk : ψ (D.ε k) ≠ 0) : j = i + k := by
  by_contra hne
  have hB : ∀ f : D.B, ψ (D.ε k) * ψ (j2 A C (f.1 j)) = ψ (D.ε k) * ψ (j2 A C (f.1 (i + k))) :=
    fun f => by
      rw [← h f]
      exact D.eps_j1 ψ k i f
  let L : (N → C) →+ R :=
    { toFun := fun φ => ψ (D.ε k) * ψ (j2 A C (φ j)) - ψ (D.ε k) * ψ (j2 A C (φ (i + k)))
      map_zero' := by simp
      map_add' := fun φ φ' => by
        simp only [Pi.add_apply, map_add]
        ring }
  have hL : ∀ t : C ⊗[A] D.B, L (D.theta t) = 0 := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c f =>
      show ψ (D.ε k) * ψ (j2 A C (D.theta (c ⊗ₜ f) j)) -
        ψ (D.ε k) * ψ (j2 A C (D.theta (c ⊗ₜ f) (i + k))) = 0
      rw [D.theta_tmul, D.theta_tmul, map_mul, map_mul, map_mul, map_mul]
      linear_combination ψ (j2 A C c) * hB f
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  obtain ⟨t, ht⟩ := D.theta_bijective.2 (Pi.single j (1 : C))
  have h0 := hL t
  rw [ht] at h0
  have hne' : i + k ≠ j := fun h' => hne h'.symm
  have h1 : L (Pi.single j (1 : C)) = ψ (D.ε k) := by
    show ψ (D.ε k) * ψ (j2 A C ((Pi.single j (1 : C) : N → C) j)) -
      ψ (D.ε k) * ψ (j2 A C ((Pi.single j (1 : C) : N → C) (i + k))) = ψ (D.ε k)
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne', map_one, map_one, map_zero, map_zero, mul_one,
      mul_zero, sub_zero]
  exact hk (h1.symm.trans h0)

end RamanujanPetersson.EtPBC.DescA.Datum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N1a =====
section

/-!
# S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`

For an etale `g : U ⟶ X` and `y : U` (generalizing `GalTr`, which treats open immersions):
* `eE g y`: the geometric points `ȳ ≫ g` and `(g y)‾` are isomorphic (`κ(y)/κ(g y)` is finite separable, so
  `κ(y)^sep` is a separable closure of `κ(g y)`); `sepE g y : κ(g y)^sep ≃ κ(y)^sep`;
* `galTrE g y : Gal y →* Gal (g y)` (conjugation by `sepE`, `galTrE_left`);
* `resTrIsoE g y Λ F : (g^* F)_ȳ ≅ F_(g y)‾`, natural (`resTrIsoE_natural`) and **Galois equivariant**
  (`galRep_resTrE`: `galRep (g^* F) y σ` corresponds to `galRep F (g y) (galTrE σ)`);
* `unitRes g Λ : Λ_U ⟶ g^* Λ_X` (the section `1` goes to the restriction of `1`), `resTrIsoE_unitRes`
  (`1 ↦ 1` on stalks), **`isIso_unitRes`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTr
  RamanujanPetersson.EtCompact.GGerm RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) (y : U)

variable [Etale g]

variable (Λ : Type u) [CommRing Λ]

/-! ### `Λ_U ⟶ g^* Λ_X` -/

theorem unitRes_oneStalk (x : U) :
    (((geomPtAt x).stalkF Λ).map (unitRes g Λ)).hom (oneStalk Λ x) =
      (resTrIsoE g x Λ (unitSh Λ X)).inv.hom (oneStalk Λ (g x)) := by
  rw [← resTrIsoE_unitRes g Λ x]
  exact (congrArg (fun φ => ModuleCat.Hom.hom φ _) (resTrIsoE g x Λ (unitSh Λ X)).hom_inv_id).symm

end RamanujanPetersson.EtCompact.GalTrE

end

end


