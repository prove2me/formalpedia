-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_012
-- name    : RPLib_FX_EtPBC_012
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:24:23.526469+00:00
-- url     : https://prove2.me/theorems/32ff9732-0d37-5aae-8d98-a945b7980e34
-- title:
--   Proper base change for the projective line, library file 012
-- statement:
--   File 012 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovAs5b`: S4-EtPBC-A, R4-T2 (A3 assembly, As5b): monic families and base change along `φ` at the level of `C`
--   * `S4.Def_RP_EtPBC_A_CovAs6a`: S4-EtPBC-A, R4-T2 (A3 assembly, As6a): pushing the descended package along `σ : C →ₐ[A] R'`
--   * `S4.Def_RP_EtPBC_A_Z3Clo`: S4-EtPBC-A, (Z) geometric layer 1: idempotent sections and clopen subsets of a scheme
--   * `S4.Def_RP_EtPBC_A_Z3P1a`: S4-EtPBC-A, (Z) geometric layer 3 (G-a): the two affine charts of `P¹_K = Proj K[X₀, X₁]` and their coordinates
--   * `S4.Def_RP_EtPBC_A_Z3P1b`: S4-EtPBC-A, (Z) geometric layer 4 (G-a): the transition `t s = 1` on the overlap of the two charts of `P¹_K`
--   * `S4.Def_RP_EtPBC_A_Z3Gen`: S4-EtPBC-A, (Z) geometric layer 5 (G-b algebra): one generator for a chart of `P¹`, and pushouts
--   * `S4.Def_RP_EtPBC_A_Z2H1`: S4-EtPBC-A, (Z2a-c): `H¹` over the two charts, Artin-Rees, lifting mod `I^n`
--   * `S4.Def_RP_EtPBC_A_Z2Et`: S4-EtPBC-A, (Z2e): an idempotent on the fibre becomes a global idempotent after an etale neighbourhood
--   * `S4.Def_RP_EtPBC_A_Z2Pi0`: S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood
--   * `S4.Def_RP_EtPBC_A_Delta`: S4-EtPBC-A, L1e: the δ-functor lemma for base change maps on germs
--   * `S4.Def_RP_EtPBC_A_LocRep`: S4-EtPBC-A, M2 F6a: local representation of a section of `ι^* π_* C`
--   * `S4.Def_RP_EtPBC_A_DescA`: S4-EtPBC-A, R4-T1a: descent of a torsor under a finite group along a flat cover (algebra)
--   * `S4.Def_RP_EtPBC_A_DescB`: S4-EtPBC-A, R4-T1b (algebra part): descent data from locally constant functions, and localization
--   * `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
--   * `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
--   * `S4.Def_RP_EtPBC_A_DeltaS`: S4-EtPBC-A, L1e': surjectivity of base change along short exact sequences (the epi four-lemma)
--   * `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
--   * `S4.Def_RP_EtPBC_A_FGS`: S4-EtPBC-A, R2(a,b): sections over compact etale objects, and local lifts on the whole fibre
--   * `S4.Def_RP_EtPBC_A_EmbQ`: S4-EtPBC-A, R3 (degree `q` of M4): closure properties of `BCSurj q`, noetherian induction for a predicate
--   * `S4.Def_RP_EtPBC_A_O2a`: S4-EtPBC-A, O2a: base change surjectivity passes to quotients in the top degree
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_002

/-!
# Proper base change for the projective line, library file 012

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovAs5b`: S4-EtPBC-A, R4-T2 (A3 assembly, As5b): monic families and base change along `φ` at the level of `C`
* `S4.Def_RP_EtPBC_A_CovAs6a`: S4-EtPBC-A, R4-T2 (A3 assembly, As6a): pushing the descended package along `σ : C →ₐ[A] R'`
* `S4.Def_RP_EtPBC_A_Z3Clo`: S4-EtPBC-A, (Z) geometric layer 1: idempotent sections and clopen subsets of a scheme
* `S4.Def_RP_EtPBC_A_Z3P1a`: S4-EtPBC-A, (Z) geometric layer 3 (G-a): the two affine charts of `P¹_K = Proj K[X₀, X₁]` and their coordinates
* `S4.Def_RP_EtPBC_A_Z3P1b`: S4-EtPBC-A, (Z) geometric layer 4 (G-a): the transition `t s = 1` on the overlap of the two charts of `P¹_K`
* `S4.Def_RP_EtPBC_A_Z3Gen`: S4-EtPBC-A, (Z) geometric layer 5 (G-b algebra): one generator for a chart of `P¹`, and pushouts
* `S4.Def_RP_EtPBC_A_Z2H1`: S4-EtPBC-A, (Z2a-c): `H¹` over the two charts, Artin-Rees, lifting mod `I^n`
* `S4.Def_RP_EtPBC_A_Z2Et`: S4-EtPBC-A, (Z2e): an idempotent on the fibre becomes a global idempotent after an etale neighbourhood
* `S4.Def_RP_EtPBC_A_Z2Pi0`: S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood
* `S4.Def_RP_EtPBC_A_Delta`: S4-EtPBC-A, L1e: the δ-functor lemma for base change maps on germs
* `S4.Def_RP_EtPBC_A_LocRep`: S4-EtPBC-A, M2 F6a: local representation of a section of `ι^* π_* C`
* `S4.Def_RP_EtPBC_A_DescA`: S4-EtPBC-A, R4-T1a: descent of a torsor under a finite group along a flat cover (algebra)
* `S4.Def_RP_EtPBC_A_DescB`: S4-EtPBC-A, R4-T1b (algebra part): descent data from locally constant functions, and localization
* `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
* `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
* `S4.Def_RP_EtPBC_A_DeltaS`: S4-EtPBC-A, L1e': surjectivity of base change along short exact sequences (the epi four-lemma)
* `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
* `S4.Def_RP_EtPBC_A_FGS`: S4-EtPBC-A, R2(a,b): sections over compact etale objects, and local lifts on the whole fibre
* `S4.Def_RP_EtPBC_A_EmbQ`: S4-EtPBC-A, R3 (degree `q` of M4): closure properties of `BCSurj q`, noetherian induction for a predicate
* `S4.Def_RP_EtPBC_A_O2a`: S4-EtPBC-A, O2a: base change surjectivity passes to quotients in the top degree
-/

set_option autoImplicit false

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

theorem tvC_bcC (C : Subalgebra A S) (x : C ⊗[A] B) :
    tvC N C (bcC φ C x) = (Algebra.TensorProduct.map (AlgHom.id A S) φ) (tvC B C x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    first
      | rfl
      | simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end BC

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

theorem tsC_bcC {C : Subalgebra A S} (σ : C →ₐ[A] R') (x : C ⊗[A] B) :
    tsC σ N (bcC φ C x) = bcS R' φ (tsC σ B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    first
      | rfl
      | simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end TsCBC

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

/-- **`D(e)` is clopen** for an idempotent global section `e`. -/
theorem isClopen_basicOpen {e : Γ(X, ⊤)} (he : IsIdempotentElem e) : IsClopen (X.basicOpen e : Set X) := by
  refine ⟨?_, (X.basicOpen e).isOpen⟩
  have h1 := basicOpen_sup_one_sub e
  have h2 := basicOpen_inf_one_sub he
  have hc : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    constructor
    · intro hx hx'
      have hm : x ∈ X.basicOpen e ⊓ X.basicOpen (1 - e) := ⟨hx, hx'⟩
      rw [h2] at hm
      simp at hm
    · intro hx
      have hm : x ∈ X.basicOpen e ⊔ X.basicOpen (1 - e) := by rw [h1]; trivial
      rcases hm with h | h
      · exact h
      · exact absurd h hx
  rw [hc]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3P1a =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 3 (G-a): the two affine charts of `P¹_K = Proj K[X₀, X₁]` and their coordinates

* `gr K`: the grading of `K[X₀, X₁]`, `x_mem`; `ch K i : Spec K[X₀,X₁]_(Xᵢ) ⟶ P¹` (Mathlib `Proj.awayι`),
  `chU K i := ch K i ''ᵁ ⊤` (`= D₊(Xᵢ)`, affine: `isAffineOpen_chU`).
* `coord K i j ∈ Γ(P¹, chU K i)`: the coordinate `Xⱼ/Xᵢ` (transported by `appIso`).
* **`basicOpen_coord`**: `D(coord K i j) = chU K i ⊓ D₊(Xⱼ)` (Mathlib `Proj.awayι_preimage_basicOpen`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K]

/-- **`D(Xⱼ/Xᵢ) = D₊(Xᵢ) ⊓ D₊(Xⱼ)`.** -/
theorem basicOpen_coord (i j : Fin 2) :
    (Proj (gr K)).basicOpen (coord K i j) = chU K i ⊓ Proj.basicOpen (gr K) (X j) := by
  rw [coord, ← Scheme.image_basicOpen, basicOpen_eq_of_affine,
    ← Proj.awayι_preimage_basicOpen (gr K) (x_mem K i) one_pos (x_mem K j) one_pos,
    Scheme.Hom.image_preimage_eq_opensRange_inf, chU, Scheme.Hom.image_top_eq_opensRange]

end RamanujanPetersson.EtPBC.Z3

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

theorem c0_eq_c1 : c0 K = c1 K :=
  (c0_eq_awayι K).trans
    (Proj.SpecMap_awayMap_awayι (gr K) (x_mem K 1) one_pos (x_mem K 0) (mul_comm _ _ : x01 K = X 1 * X 0)).symm

theorem image_c0 : c0 K ''ᵁ ⊤ = chU K 0 ⊓ chU K 1 := by
  rw [Scheme.Hom.image_top_eq_opensRange, opensRange_congr (c0_eq_awayι K), Proj.opensRange_awayι,
    chU_eq, chU_eq, ← Proj.basicOpen_mul]

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Gen =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 5 (G-b algebra): one generator for a chart of `P¹`, and pushouts

* `adjoin_X_zero`, **`away_adjoin`**: `K[X₀,X₁]_(Xᵢ)` is generated over the degree-`0` part by `Xⱼ/Xᵢ`;
  `away_surj_eval`: `K[X] → K[X₀,X₁]_(Xᵢ)`, `X ↦ Xⱼ/Xᵢ`, is surjective.
* `surj_eval₂_comp`, `surj_eval₂_map`: transport of "generated by one element" along surjections.
* **`pushout_surj`**: in a pushout square of commutative rings `B ⊗_R C`, if `B` is generated over `R` by `e`,
  then the pushout is generated over `C` by the image of `e`.
-/

set_option autoImplicit false

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

section Poly

end Poly

variable (K : Type u) [Field K]

/-- **`K[X₀,X₁]_(Xᵢ)` is generated by `Xⱼ/Xᵢ`.** -/
theorem away_adjoin (i j : Fin 2) (hij : i ≠ j) :
    Algebra.adjoin (gr K 0) {Away.isLocalizationElem (x_mem K i) (x_mem K j)} = ⊤ := by
  rw [eq_top_iff, ← Away.adjoin_mk_prod_pow_eq_top (x_mem K i) (Fin 2) X (adjoin_X_zero K) (fun _ => 1)
    (x_mem K), Algebra.adjoin_le_iff]
  rintro _ ⟨a, ai, hai, hle, rfl⟩
  have hs : ai i + ai j = a := by
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two] at hai hij ⊢ <;> omega
  have hp : ∏ k, (X k : MvPolynomial (Fin 2) K) ^ ai k = X i ^ ai i * X j ^ ai j := by
    fin_cases i <;> fin_cases j <;> simp [Fin.prod_univ_two, mul_comm] at hij ⊢
  subst hs
  rw [SetLike.mem_coe]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle j) with h0 | h1
  · convert (Algebra.adjoin (gr K 0) {Away.isLocalizationElem (x_mem K i) (x_mem K j)}).one_mem using 1
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, HomogeneousLocalization.val_one, ← Localization.mk_one, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [hp, h0, OneMemClass.coe_one, one_mul, mul_one, pow_zero, add_zero]
  · convert Algebra.self_mem_adjoin_singleton (gr K 0) (Away.isLocalizationElem (x_mem K i) (x_mem K j)) using 1
    apply HomogeneousLocalization.val_injective
    simp only [Away.isLocalizationElem, Away.val_mk]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [hp, h1, OneMemClass.coe_one, one_mul]
    ring

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z2H1 =====
section

/-!
# S4-EtPBC-A, (Z2a-c): `H¹` over the two charts, Artin-Rees, lifting mod `I^n`

Two-chart data as in `Z1.twoChart_fg`: `φ₀ : M₀ →ₗ[A[X]] N`, `φ₁ : M₁ →ₗ[A] N` with `X • φ₁ (X • m) = φ₁ m`.
`W := φ₀(M₀) + φ₁(M₁)` (`chartIm`), so that `H¹ = N / W`.

* **`h1_span`**: if `M₁` is finite over `A[X]`, every `y ∈ N` is `X^k • φ₁ b` and every `φ₁ m` is moved into the
  image of `φ₀` by a power of `X`, then `N = U + W` with `U` finite over `A` (`H¹` is finite over `A`).
* **`artinRees_sup`**: `N = U + W` with `U` finite, `A` noetherian: `∃ c, ∀ n, I^(n+c) N ∩ W ≤ I^n W`.
* **`lift_twoChart`**: `∃ c, ∀ n a b, φ₀ a - φ₁ b ∈ I^(n+c) N → ∃ a' b', φ₀ a' = φ₁ b'` with `a' ≡ a`, `b' ≡ b`
  mod `I^n`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Z2

universe u v w w'

variable {A : Type u} [CommRing A]

section Span

variable {M₀ : Type v} {M₁ : Type w} {N : Type w'}
  [AddCommGroup M₀] [Module A[X] M₀] [Module A M₀] [IsScalarTower A A[X] M₀]
  [AddCommGroup M₁] [Module A[X] M₁] [Module A M₁] [IsScalarTower A A[X] M₁]
  [AddCommGroup N] [Module A[X] N] [Module A N] [IsScalarTower A A[X] N]

omit [Module A[X] M₁] [IsScalarTower A A[X] M₁] in
theorem mem_chartIm₀ (φ₀ : M₀ →ₗ[A[X]] N) (φ₁ : M₁ →ₗ[A] N) (a : M₀) : φ₀ a ∈ chartIm φ₀ φ₁ :=
  Submodule.mem_sup_left (LinearMap.mem_range_self (φ₀.restrictScalars A) a)

omit [Module A[X] M₁] [IsScalarTower A A[X] M₁] in
theorem mem_chartIm₁ (φ₀ : M₀ →ₗ[A[X]] N) (φ₁ : M₁ →ₗ[A] N) (b : M₁) : φ₁ b ∈ chartIm φ₀ φ₁ :=
  Submodule.mem_sup_right (LinearMap.mem_range_self φ₁ b)

end Span

section ArtinRees

end ArtinRees

section Lift

variable {M₀ : Type v} {M₁ : Type w} {N : Type w'}
  [AddCommGroup M₀] [Module A[X] M₀] [Module A M₀] [IsScalarTower A A[X] M₀]
  [AddCommGroup M₁] [Module A[X] M₁] [Module A M₁] [IsScalarTower A A[X] M₁]
  [AddCommGroup N] [Module A[X] N] [Module A N] [IsScalarTower A A[X] N]

omit [Module A[X] M₁] [IsScalarTower A A[X] M₁] in
/-- `I • W = φ₀(I M₀) + φ₁(I M₁)`. -/
theorem mem_smul_chartIm (J : Ideal A) (φ₀ : M₀ →ₗ[A[X]] N) (φ₁ : M₁ →ₗ[A] N) {y : N}
    (hy : y ∈ J • chartIm φ₀ φ₁) :
    ∃ (a : M₀) (b : M₁), a ∈ (J • ⊤ : Submodule A M₀) ∧ b ∈ (J • ⊤ : Submodule A M₁) ∧ y = φ₀ a + φ₁ b := by
  rw [chartIm, Submodule.smul_sup, LinearMap.range_eq_map, LinearMap.range_eq_map, ← Submodule.map_smul'',
    ← Submodule.map_smul''] at hy
  obtain ⟨y₀, ⟨a, ha, rfl⟩, y₁, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
  exact ⟨a, b, ha, hb, rfl⟩

end Lift
end RamanujanPetersson.EtPBC.Z2
end

end

-- ===== S4.Def_RP_EtPBC_A_Z2Et =====
section

/-!
# S4-EtPBC-A, (Z2e): an idempotent on the fibre becomes a global idempotent after an etale neighbourhood

* `fibre_idem`: let `ρ : T →+* F`, `e : Fin (n+1) → T` complete orthogonal idempotents and primes `P' i` such that
  every prime of `F` pulls back to a prime containing `e (last n)` and equal to `P' i` whenever it misses
  `e i.castSucc`. If `ρ y` is idempotent, then `ρ y = ρ e'` for an idempotent `e'` (a sum of some `e i`).
* **`exists_etale_idem`** (with Mathlib's 00UL): `E` finite over `R`, `p` prime, `ρ : E →ₐ[R] F`, `F` a
  `κ(p)`-algebra, `ρ y` idempotent. Then there are an etale `R → R'` and a prime `P` over `p` with `κ(p) ≅ κ(P)`
  and an idempotent `e' ∈ R' ⊗ E` with `(R' → κ(P) ≅ κ(p) → F) ⊗ ρ` sending `e'` to `ρ y`.
-/

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z2

universe u v w

section Fibre

variable {T : Type v} {F : Type w} [CommRing T] [CommRing F]

/-- An idempotent of the fibre that comes from `T` is the image of a sum of the `e i`. -/
theorem fibre_idem (ρ : T →+* F) {n : ℕ} (e : Fin (n + 1) → T) (he : CompleteOrthogonalIdempotents e)
    (P' : Fin n → Ideal T) [∀ i, (P' i).IsPrime]
    (H : ∀ Q : Ideal F, Q.IsPrime → e (Fin.last n) ∈ Q.comap ρ ∧
      ∀ i, e i.castSucc ∉ Q.comap ρ → Q.comap ρ = P' i)
    (y : T) (hy : IsIdempotentElem (ρ y)) :
    ∃ e' : T, IsIdempotentElem e' ∧ ρ e' = ρ y := by
  classical
  have hidem : ∀ j, IsIdempotentElem (ρ (e j)) := fun j => (he.idem j).map ρ
  let S : Finset (Fin n) := Finset.univ.filter fun i => y - 1 ∈ P' i
  refine ⟨∑ i ∈ S, e i.castSucc, ?_, ?_⟩
  · exact (he.toOrthogonalIdempotents.embedding Fin.castSuccEmb).isIdempotentElem_sum
  have hlast : ρ (e (Fin.last n) * y) = 0 := by
    have h0 : ρ (e (Fin.last n)) = 0 :=
      eq_zero_of_idem_mem_primes (hidem _) fun Q hQ => (H Q hQ).1
    rw [map_mul, h0, zero_mul]
  have hin : ∀ i ∈ S, ρ (e i.castSucc * y) = ρ (e i.castSucc) := by
    intro i hi
    have hiS : y - 1 ∈ P' i := (Finset.mem_filter.1 hi).2
    have hz : ρ (e i.castSucc) * (1 - ρ y) = 0 := by
      refine eq_zero_of_idem_mem_primes ((hidem _).mul hy.one_sub) fun Q hQ => ?_
      by_cases hQe : e i.castSucc ∈ Q.comap ρ
      · exact Q.mul_mem_right _ (Ideal.mem_comap.1 hQe)
      · have hQP := (H Q hQ).2 i hQe
        have : 1 - y ∈ Q.comap ρ := by
          rw [hQP]; simpa using (P' i).neg_mem hiS
        rw [Ideal.mem_comap, map_sub, map_one] at this
        exact Q.mul_mem_left _ this
    rw [map_mul]
    linear_combination -hz
  have hout : ∀ i ∉ S, ρ (e i.castSucc * y) = 0 := by
    intro i hi
    have hiS : y - 1 ∉ P' i := fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [map_mul]
    refine eq_zero_of_idem_mem_primes ((hidem _).mul hy) fun Q hQ => ?_
    by_cases hQe : e i.castSucc ∈ Q.comap ρ
    · exact Q.mul_mem_right _ (Ideal.mem_comap.1 hQe)
    · have hQP := (H Q hQ).2 i hQe
      have hyy : y * (y - 1) ∈ Q.comap ρ := by
        rw [Ideal.mem_comap, map_mul, map_sub, map_one, mul_sub, mul_one, hy.eq, sub_self]
        exact Q.zero_mem
      rw [hQP] at hyy
      have hyP : y ∈ P' i := ((Ideal.IsPrime.mem_or_mem inferInstance hyy).resolve_right hiS)
      rw [← hQP] at hyP
      exact Q.mul_mem_left _ (Ideal.mem_comap.1 hyP)
  calc ρ (∑ i ∈ S, e i.castSucc) = ∑ i ∈ S, ρ (e i.castSucc) := map_sum ρ _ _
    _ = ∑ i : Fin n, ρ (e i.castSucc * y) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => y - 1 ∈ P' i)]
        rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i => ¬ y - 1 ∈ P' i)
          (fun i hi => hout i (by simpa [S] using (Finset.mem_filter.1 hi).2)), add_zero]
        exact Finset.sum_congr rfl fun i hi => (hin i hi).symm
    _ = ∑ j : Fin (n + 1), ρ (e j * y) := by rw [Fin.sum_univ_castSucc, hlast, add_zero]
    _ = ρ y := by rw [← map_sum, ← Finset.sum_mul, he.complete, one_mul]

end Fibre

section Etale

end Etale

end RamanujanPetersson.EtPBC.Z2

end

end

-- ===== S4.Def_RP_EtPBC_A_Z2Pi0 =====
section

/-!
# S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood

Algebraic form of the `π₀` lemma: `A` noetherian, `p` prime, chart algebras `B₀` (over `A[t]`), `B₁` (over `A[s]`),
both finite over `A[X]`, overlap algebra `N`, `φ₀ : B₀ →ₐ[A[X]] N`, `φ₁ : B₁ →ₐ[A] N`.

* `secAlg φ₀ φ₁`: the global sections `{(a, b) | φ₀ a = φ₁ b}` as an `A`-subalgebra of `B₀ × B₁`;
  `secAlg_finite`: it is finite over `A` (Z1, `twoChart_fg`).
* `fibreMap p φ₀ φ₁ : secAlg →ₐ[A] κ(p) ⊗ B₀ × κ(p) ⊗ B₁` and `fibreUnit p B₀ B₁`.
* `includeRight_eq_of_sub_mem`: `x ≡ y mod p B` gives `1 ⊗ x = 1 ⊗ y` in `κ(p) ⊗ B`.
* **`exists_etale_idem_twoChart`**: chart elements `ε₀`, `ε₁` idempotent mod `p` and agreeing mod `p` on the overlap
  come, after an etale `A → A'` with a prime `P` over `p` and `κ(p) ≅ κ(P)`, from an idempotent of `A' ⊗ secAlg`.
-/

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z2

universe u v w w'

variable {A : Type u} [CommRing A]

section Fib

end Fib

section TwoChart

variable {B₀ : Type v} {B₁ : Type w} {N : Type w'}
  [CommRing B₀] [Algebra A[X] B₀] [Algebra A B₀] [IsScalarTower A A[X] B₀]
  [CommRing B₁] [Algebra A[X] B₁] [Algebra A B₁] [IsScalarTower A A[X] B₁]
  [CommRing N] [Algebra A[X] N] [Algebra A N] [IsScalarTower A A[X] N]

omit [Algebra A[X] B₁] [IsScalarTower A A[X] B₁] in
theorem fibreMap_fst (p : Ideal A) [p.IsPrime] (φ₀ : B₀ →ₐ[A[X]] N) (φ₁ : B₁ →ₐ[A] N) (y : secAlg φ₀ φ₁) :
    (fibreMap p φ₀ φ₁ y).1 = (Algebra.TensorProduct.includeRight : B₀ →ₐ[A] p.ResidueField ⊗[A] B₀) y.1.1 :=
  rfl

omit [Algebra A[X] B₁] [IsScalarTower A A[X] B₁] in
theorem fibreMap_snd (p : Ideal A) [p.IsPrime] (φ₀ : B₀ →ₐ[A[X]] N) (φ₁ : B₁ →ₐ[A] N) (y : secAlg φ₀ φ₁) :
    (fibreMap p φ₀ φ₁ y).2 = (Algebra.TensorProduct.includeRight : B₁ →ₐ[A] p.ResidueField ⊗[A] B₁) y.1.2 :=
  rfl

end TwoChart

end RamanujanPetersson.EtPBC.Z2

end

end

-- ===== S4.Def_RP_EtPBC_A_Delta =====
section

/-!
# S4-EtPBC-A, L1e: the δ-functor lemma for base change maps on germs

Abstract setting: an exact functor `L : C ⥤ D` of abelian categories, `C` with enough injectives, a cofiltered
system `A : J ⥤ C` (the free sheaves `Λ[g⁻¹ V]` of the etale neighbourhoods `V` of a geometric point), an object
`B : D` (the unit sheaf of the fibre) and compatible maps `u j : B ⟶ L (A j)`. The base change map at `j` is
`bc j : Ext^q(A j, F) → Ext^q(B, L F)`, `α ↦ u j ∘ L α`, and `res a` restricts classes along `a : j' ⟶ j`.

**`injAt_all`**: if base change is injective on germs in degree `0` for all `F` (`InjAt 0`) and surjective on germs
in every degree for all `F` (`SurjAt q`), then it is injective on germs in every degree. The proof embeds `F` into
an injective object and uses the long exact `Ext` sequences, `Ext^(q+1)(-, I) = 0` and the compatibility of
`Ext.mapExactFunctor` with composition and extension classes.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {J : Type u₃} [Category.{v₃} J]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (A : J ⥤ C) (B : D) (u : ∀ j, B ⟶ L.obj (A.obj j))

theorem bc_apply (j : J) (F : C) (q : ℕ) (α : Ext (A.obj j) F q) :
    bc L A B u j F q α = (Ext.mk₀ (u j)).comp (α.mapExactFunctor L) (zero_add q) := rfl

/-- Restriction of classes along `a : j' ⟶ j`. -/
def res {j j' : J} (a : j' ⟶ j) (F : C) (q : ℕ) : Ext (A.obj j) F q →+ Ext (A.obj j') F q where
  toFun α := (Ext.mk₀ (A.map a)).comp α (zero_add q)
  map_zero' := Ext.comp_zero _ _ _ _ _
  map_add' _ _ := Ext.comp_add _ _ _ _

theorem res_apply {j j' : J} (a : j' ⟶ j) (F : C) (q : ℕ) (α : Ext (A.obj j) F q) :
    res A a F q α = (Ext.mk₀ (A.map a)).comp α (zero_add q) := rfl

theorem res_comp {j j' j'' : J} (a : j' ⟶ j) (b : j'' ⟶ j') (F : C) (q : ℕ) (α : Ext (A.obj j) F q) :
    res A (b ≫ a) F q α = res A b F q (res A a F q α) := by
  rw [res_apply, res_apply, res_apply, Functor.map_comp, Ext.mk₀_comp_mk₀_assoc]

theorem res_comp_right {j j' : J} (a : j' ⟶ j) {F G : C} {n m p : ℕ} (x : Ext (A.obj j) F n)
    (y : Ext F G m) (h : n + m = p) : res A a G p (x.comp y h) = (res A a F n x).comp y h :=
  (Ext.comp_assoc _ _ _ (zero_add n) h (by omega)).symm

variable {L A B u}

theorem bc_res (hu : ∀ {j j' : J} (a : j' ⟶ j), u j' ≫ L.map (A.map a) = u j) {j j' : J} (a : j' ⟶ j)
    (F : C) (q : ℕ) (α : Ext (A.obj j) F q) :
    bc L A B u j' F q (res A a F q α) = bc L A B u j F q α := by
  rw [bc_apply, bc_apply, res_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, hu]

variable (L A B u)

theorem bc_comp_mk₀ (j : J) {F G : C} (f : F ⟶ G) (q : ℕ) (α : Ext (A.obj j) F q) :
    bc L A B u j G q (α.comp (Ext.mk₀ f) (add_zero q)) =
      (bc L A B u j F q α).comp (Ext.mk₀ (L.map f)) (add_zero q) := by
  rw [bc_apply, bc_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

theorem bc_comp_extClass (j : J) {S : ShortComplex C} (hS : S.ShortExact) (q : ℕ)
    (α : Ext (A.obj j) S.X₃ q) :
    bc L A B u j S.X₁ (q + 1) (α.comp hS.extClass rfl) =
      (bc L A B u j S.X₃ q α).comp (hS.map_of_exact L).extClass rfl := by
  rw [bc_apply, bc_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add q) rfl (by omega)).symm

/-- Base change is injective on germs in degree `q` for `F`. -/
def InjAt (q : ℕ) (F : C) : Prop :=
  ∀ (j : J) (α : Ext (A.obj j) F q), bc L A B u j F q α = 0 → ∃ (j' : J) (a : j' ⟶ j), res A a F q α = 0

/-- Base change is surjective on germs in degree `q` for `F`. -/
def SurjAt (q : ℕ) (F : C) : Prop :=
  ∀ β : Ext B (L.obj F) q, ∃ (j : J) (α : Ext (A.obj j) F q), bc L A B u j F q α = β

end RamanujanPetersson.EtPBC.Delta

end

end

-- ===== S4.Def_RP_EtPBC_A_LocRep =====
section

/-!
# S4-EtPBC-A, M2 F6a: local representation of a section of `ι^* π_* C`

For `ι : X ⟶ P`, `π : Y ⟶ P`, `G = π_* C` (`C = constSh Λ Y M`) and `b : Λ_X ⟶ ι^* G`:
* `germ_elem`: germs along an arrow of the category of elements;
* **`exists_pullRep`**: near any geometric point `y` of `X` there are `W`, an etale `U ⟶ ι⁻¹ W` through `y` and
  `z ∈ C(π⁻¹ W)` with `b(1)|_U = η(z)|_U`;
* **`xi_of_pullRep`**: for such a representation, `ξ_{y'}(b)` at every geometric point `y'` through `U` is the germ
  of `z` at the corresponding point.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.Supp

universe u

/-- Two sections with the same germ agree on a common etale neighbourhood. -/
theorem exists_common_rep {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}} (Φ : (Z.smallEtaleTopology).Point)
    (F : (Z.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ) {j₁ j₀ : Φ.fiber.Elements} (x₁ : F.obj (op j₁.1)) (x₀ : F.obj (op j₀.1))
    (h : (Φ.toPresheafFiber j₁.1 j₁.2 F).hom x₁ = (Φ.toPresheafFiber j₀.1 j₀.2 F).hom x₀) :
    ∃ (U : Z.Etale) (f₁ : U ⟶ j₁.1) (f₀ : U ⟶ j₀.1) (_ : Φ.fiber.obj U),
      (F.map f₁.op).hom x₁ = (F.map f₀.op).hom x₀ := by
  have e4 := (germ_elem Φ F (IsCofiltered.minToLeft j₁ j₀) x₁).trans
    (h.trans (germ_elem Φ F (IsCofiltered.minToRight j₁ j₀) x₀).symm)
  obtain ⟨U, f, u, -, hs⟩ := (Φ.toPresheafFiber_eq_iff' (IsCofiltered.min j₁ j₀).1
    (IsCofiltered.min j₁ j₀).2 _ _).1 e4
  refine ⟨U, f ≫ (IsCofiltered.minToLeft j₁ j₀).1, f ≫ (IsCofiltered.minToRight j₁ j₀).1, u, ?_⟩
  have c1 := ConcreteCategory.congr_hom (F.map_comp (IsCofiltered.minToLeft j₁ j₀).1.op f.op) x₁
  have c0 := ConcreteCategory.congr_hom (F.map_comp (IsCofiltered.minToRight j₁ j₀).1.op f.op) x₀
  exact c1.trans (hs.trans c0.symm)

end RamanujanPetersson.EtPBC

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

theorem eps_mul_sum (k : N) (X : N → C ⊗[A] C) : D.ε k * ∑ m, D.ε m * X m = D.ε k * X k := by
  rw [Finset.mul_sum, Finset.sum_eq_single k]
  · rw [← mul_assoc, D.mul_self]
  · intro m _ hm
    rw [← mul_assoc, D.mul_ne k m (Ne.symm hm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem sum_mul_sum (X Y : N → C ⊗[A] C) :
    (∑ m, D.ε m * X m) * (∑ k, D.ε k * Y k) = ∑ m, D.ε m * (X m * Y m) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  calc D.ε m * X m * (∑ k, D.ε k * Y k) = X m * (D.ε m * ∑ k, D.ε k * Y k) := by ring
    _ = X m * (D.ε m * Y m) := by rw [D.eps_mul_sum]
    _ = D.ε m * (X m * Y m) := by ring

theorem cocycle' (α : N) : ∑ m, e23 A C (D.ε m) * e13 A C (D.ε (α + m)) = e12 A C (D.ε α) := by
  have h1 : ∀ m, e23 A C (D.ε m) * e13 A C (D.ε (α + m)) = e12 A C (D.ε α) * e23 A C (D.ε m) := by
    intro m
    rw [D.cocycle, Finset.mul_sum, Finset.sum_eq_single α]
    · rw [add_sub_cancel_left, mul_left_comm, ← map_mul, D.mul_self]
    · intro γ _ hγ
      rw [mul_left_comm, ← map_mul, D.mul_ne m (α + m - γ), map_zero, mul_zero]
      intro hm
      apply hγ
      rw [eq_sub_iff_add_eq, add_comm α m] at hm
      exact add_left_cancel hm
    · intro h
      exact absurd (Finset.mem_univ α) h
  rw [Finset.sum_congr rfl fun m _ => h1 m, ← Finset.mul_sum, ← map_sum, D.sum_eq, map_one, mul_one]

section Tensor

end Tensor

section FF

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

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {N : Type u} [AddCommGroup N] [Fintype N]
  [DecidableEq N]

/-- The descent datum of a locally constant `N`-valued cocycle on `Spec (C ⊗[A] C)`. -/
def mkDatum (c : PrimeSpectrum (C ⊗[A] C) → N) (hc : IsLocallyConstant c)
    (hdiag : ∀ P : PrimeSpectrum C,
      c (PrimeSpectrum.comap (Algebra.TensorProduct.lmul' A : C ⊗[A] C →ₐ[A] C).toRingHom P) = 0)
    (hcoc : ∀ P : PrimeSpectrum (C ⊗[A] (C ⊗[A] C)),
      c (PrimeSpectrum.comap (e13 A C).toRingHom P) =
        c (PrimeSpectrum.comap (e12 A C).toRingHom P) + c (PrimeSpectrum.comap (e23 A C).toRingHom P)) :
    Datum A C N where
  ε := fib c hc
  mul_self ν := fib_isIdem c hc ν
  mul_ne _ _ h := fib_mul_ne c hc h
  sum_eq := fib_sum c hc
  diag ν := by
    have hi : IsIdempotentElem (Algebra.TensorProduct.lmul' A (fib c hc ν)) := (fib_isIdem c hc ν).map _
    split_ifs with h
    · subst h
      exact eq_one_of_idem hi fun P => (fib_algMap_not_mem _ c hc 0 P).mpr (hdiag P)
    · exact eq_zero_of_idem hi fun P => by
        by_contra h'
        exact h (((fib_algMap_not_mem _ c hc ν P).mp h').symm.trans (hdiag P))
  cocycle ν := by
    have hg : ∀ α, IsIdempotentElem (e12 A C (fib c hc α) * e23 A C (fib c hc (ν - α))) := fun α =>
      ((fib_isIdem c hc α).map _).mul ((fib_isIdem c hc _).map _)
    have ho : ∀ α β, α ≠ β → (e12 A C (fib c hc α) * e23 A C (fib c hc (ν - α))) *
        (e12 A C (fib c hc β) * e23 A C (fib c hc (ν - β))) = 0 := fun α β hαβ => by
      calc _ = e12 A C (fib c hc α * fib c hc β) *
            (e23 A C (fib c hc (ν - α)) * e23 A C (fib c hc (ν - β))) := by rw [map_mul]; ring
        _ = 0 := by rw [fib_mul_ne c hc hαβ, map_zero, zero_mul]
    refine (idem_ext (isIdem_sum_orth _ hg ho) ((fib_isIdem c hc ν).map _) fun P => ?_).symm
    rw [not_mem_sum_orth _ hg ho P, fib_algMap_not_mem, hcoc P]
    simp only [not_mem_mul, fib_algMap_not_mem]
    constructor
    · rintro ⟨α, h1, h2⟩
      rw [h1, h2]
      abel
    · intro h
      exact ⟨_, rfl, by rw [← h]; abel⟩

@[simp] theorem mkDatum_ε (c : PrimeSpectrum (C ⊗[A] C) → N) (hc : IsLocallyConstant c) (hdiag) (hcoc)
    (ν : N) : (mkDatum c hc hdiag hcoc).ε ν = fib c hc ν := rfl

end Mk

section Map

variable {A C A' C' A'' C'' : Type u} [CommRing A] [CommRing C] [Algebra A C] [CommRing A'] [CommRing C']
  [Algebra A' C'] [CommRing A''] [CommRing C''] [Algebra A'' C''] {N : Type u} [AddCommGroup N] [Fintype N]
  [DecidableEq N]

theorem psiMap_tmul (ρA : A →+* A') (φC : C →+* C')
    (hφC : ∀ a, φC (algebraMap A C a) = algebraMap A' C' (ρA a)) (c d : C) :
    psiMap ρA φC hφC (c ⊗ₜ d) = φC c ⊗ₜ φC d := by
  show (φC c ⊗ₜ[A'] (1 : C')) * ((1 : C') ⊗ₜ φC d) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem psiMap_j1 (ρA : A →+* A') (φC : C →+* C')
    (hφC : ∀ a, φC (algebraMap A C a) = algebraMap A' C' (ρA a)) (c : C) :
    psiMap ρA φC hφC (j1 A C c) = j1 A' C' (φC c) := by
  show psiMap ρA φC hφC (c ⊗ₜ 1) = φC c ⊗ₜ 1
  rw [psiMap_tmul, map_one]

theorem psiMap_j2 (ρA : A →+* A') (φC : C →+* C')
    (hφC : ∀ a, φC (algebraMap A C a) = algebraMap A' C' (ρA a)) (c : C) :
    psiMap ρA φC hφC (j2 A C c) = j2 A' C' (φC c) := by
  show psiMap ρA φC hφC (1 ⊗ₜ c) = 1 ⊗ₜ φC c
  rw [psiMap_tmul, map_one]

end Map

end RamanujanPetersson.EtPBC.DescA

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

/-- The map of etale `X`-objects induced by an `A`-algebra map. -/
def homS {R R' : Type u} [CommRing R] [Algebra A R] [Algebra.Etale A R] [CommRing R'] [Algebra A R']
    [Algebra.Etale A R'] (φ : R →ₐ[A] R') : etS σ R' ⟶ etS σ R :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    show Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)) ≫ σ =
      Spec.map (CommRingCat.ofHom (algebraMap A R')) ≫ σ
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact φ.commutes x) trivial

theorem homS_left {R R' : Type u} [CommRing R] [Algebra A R] [Algebra.Etale A R] [CommRing R'] [Algebra A R']
    [Algebra.Etale A R'] (φ : R →ₐ[A] R') :
    (homS σ φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

variable {C : Type u} [CommRing C] [Algebra A C] [Algebra.Etale A C] {V : X.Etale}
  (τ : Spec (CommRingCat.of C) ⟶ V.left)
  (hτ : τ ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ σ)

/-- `Spec R ⟶ Spec C ⟶ V` for an `A`-algebra map `C → R`. -/
def kmap {R : Type u} [CommRing R] [Algebra A R] [Algebra.Etale A R] (φ : C →ₐ[A] R) : etS σ R ⟶ V :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ τ) (by
    show (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ τ) ≫ V.hom =
      Spec.map (CommRingCat.ofHom (algebraMap A R)) ≫ σ
    rw [Category.assoc, hτ, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact φ.commutes x) trivial

theorem kmap_left {R : Type u} [CommRing R] [Algebra A R] [Algebra.Etale A R] (φ : C →ₐ[A] R) :
    (kmap σ τ hτ φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ τ := rfl

theorem homS_kmap {R R' : Type u} [CommRing R] [Algebra A R] [Algebra.Etale A R] [CommRing R'] [Algebra A R']
    [Algebra.Etale A R'] (ψ : R →ₐ[A] R') (φ : C →ₐ[A] R) :
    homS σ ψ ≫ kmap σ τ hτ φ = kmap σ τ hτ (ψ.comp φ) := by
  apply MorphismProperty.Over.Hom.ext
  show Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ τ =
    Spec.map (CommRingCat.ofHom (ψ.comp φ).toRingHom) ≫ τ
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

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

/-- The map of etale `X`-objects across two charts. -/
def homX {R R' : Type u} [CommRing R] [Algebra A R] [Algebra.Etale A R] [CommRing R'] [Algebra A' R']
    [Algebra.Etale A' R'] (φ : R →+* R') (hφ : ∀ x, φ (algebraMap A R x) = algebraMap A' R' (ρA x)) :
    etS σ' R' ⟶ etS σ R :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
    show Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)) ≫ σ =
      Spec.map (CommRingCat.ofHom (algebraMap A' R')) ≫ σ'
    subst hσ
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext x
    exact hφ x) trivial

theorem homX_left {R R' : Type u} [CommRing R] [Algebra A R] [Algebra.Etale A R] [CommRing R'] [Algebra A' R']
    [Algebra.Etale A' R'] (φ : R →+* R') (hφ : ∀ x, φ (algebraMap A R x) = algebraMap A' R' (ρA x)) :
    (homX σ σ' ρA hσ φ hφ).left = Spec.map (CommRingCat.ofHom φ) := rfl

variable {C C' : Type u} [CommRing C] [Algebra A C] [Algebra.Etale A C] [CommRing C'] [Algebra A' C']
  [Algebra.Etale A' C'] {V : X.Etale}
  (τ : Spec (CommRingCat.of C) ⟶ V.left) (hτ : τ ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ σ)
  (τ' : Spec (CommRingCat.of C') ⟶ V.left)
  (hτ' : τ' ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A' C')) ≫ σ')
  (φC : C →+* C') (hφC : ∀ x, φC (algebraMap A C x) = algebraMap A' C' (ρA x))
  (hτφ : Spec.map (CommRingCat.ofHom φC) ≫ τ = τ')

include hτφ in
theorem homX_kmap {R R' : Type u} [CommRing R] [Algebra A R] [Algebra.Etale A R] [CommRing R'] [Algebra A' R']
    [Algebra.Etale A' R'] (φ : R →+* R') (hφ : ∀ x, φ (algebraMap A R x) = algebraMap A' R' (ρA x))
    (ψ : C →ₐ[A] R) (ψ' : C' →ₐ[A'] R') (h : ∀ c, φ (ψ c) = ψ' (φC c)) :
    homX σ σ' ρA hσ φ hφ ≫ kmap σ τ hτ ψ = kmap σ' τ' hτ' ψ' := by
  apply MorphismProperty.Over.Hom.ext
  show Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ τ =
    Spec.map (CommRingCat.ofHom ψ'.toRingHom) ≫ τ'
  subst hτφ
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext c
  exact h c

end Cross

section Pres

end Pres

section Glue

end Glue

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_DeltaS =====
section

/-!
# S4-EtPBC-A, L1e': surjectivity of base change along short exact sequences (the epi four-lemma)

Same abstract setting as `Delta`. For a short exact sequence `0 → X₁ → X₂ → X₃ → 0`:

* `surjAt_zero_of_ses`: surjectivity in degree `0` for `X₂` and injectivity in degree `0` for `X₃` give surjectivity
  in degree `0` for `X₁` (no `δ` term: `Ext^0(B, L X₁) → Ext^0(B, L X₂)` is injective);
* `surjAt_succ_of_ses`: surjectivity in degree `q + 1` for `X₂`, injectivity in degree `q + 1` and surjectivity in
  degree `q` for `X₃` give surjectivity in degree `q + 1` for `X₁`.

Used to reduce surjectivity for all sheaves to a cogenerating class (`X₁ ↪ X₂` with `X₂` in the class).
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {J : Type u₃} [Category.{v₃} J]
  {L : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {A : J ⥤ C} {B : D} {u : ∀ j, B ⟶ L.obj (A.obj j)}

theorem bc_comp_f_g (j : J) {S : ShortComplex C} (q : ℕ) (β : Ext B (L.obj S.X₁) q) (α : Ext (A.obj j) S.X₂ q)
    (h : bc L A B u j S.X₂ q α = β.comp (Ext.mk₀ (L.map S.f)) (add_zero q)) :
    bc L A B u j S.X₃ q (α.comp (Ext.mk₀ S.g) (add_zero q)) = 0 := by
  rw [bc_comp_mk₀, h, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← L.map_comp, S.zero, L.map_zero,
    Ext.mk₀_zero, Ext.comp_zero]

end RamanujanPetersson.EtPBC.Delta

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

/-- Restriction maps of a skyscraper sheaf on components. -/
@[reassoc]
theorem s_map_π {Y : Scheme.{u}} (Φ : GrothendieckTopology.Point.{u} Y.smallEtaleTopology) {W W' : (Y.Etale)ᵒᵖ}
    (g : W ⟶ W') (c : Φ.fiber.obj W'.unop) :
    (Φ.skyscraperSheaf J).obj.map g ≫ sπ J Φ W' c = sπ J Φ W (Φ.fiber.map g.unop c) :=
  (Pi.map'_comp_π _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem r_map_π {W W' : (U.Etale)ᵒᵖ} (g : W ⟶ W') (b : x.point.fiber.obj ((etComp e).obj W'.unop)) :
    ((res e Λ).obj (x.point.skyscraperSheaf J)).obj.map g ≫ rπ e x J W' b =
      rπ e x J W (x.point.fiber.map ((etComp e).map g.unop) b) :=
  s_map_π J x.point ((etComp e).op.map g) b

end RamanujanPetersson.EtSheaves.LshEt

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

end Refine

/-- Common refinement of two germ representatives, compatible with the fibre element of the second. -/
theorem exists_common_rep' {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}} (Φ : (Z.smallEtaleTopology).Point)
    (F : (Z.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ) {j₁ j₀ : Φ.fiber.Elements} (x₁ : F.obj (op j₁.1)) (x₀ : F.obj (op j₀.1))
    (h : (Φ.toPresheafFiber j₁.1 j₁.2 F).hom x₁ = (Φ.toPresheafFiber j₀.1 j₀.2 F).hom x₀) :
    ∃ (U : Z.Etale) (f₁ : U ⟶ j₁.1) (f₀ : U ⟶ j₀.1) (u : Φ.fiber.obj U), Φ.fiber.map f₀ u = j₀.2 ∧
      (F.map f₁.op).hom x₁ = (F.map f₀.op).hom x₀ := by
  have e4 := (germ_elem Φ F (IsCofiltered.minToLeft j₁ j₀) x₁).trans
    (h.trans (germ_elem Φ F (IsCofiltered.minToRight j₁ j₀) x₀).symm)
  obtain ⟨U, f, u, hu, hs⟩ := (Φ.toPresheafFiber_eq_iff' (IsCofiltered.min j₁ j₀).1
    (IsCofiltered.min j₁ j₀).2 _ _).1 e4
  refine ⟨U, f ≫ (IsCofiltered.minToLeft j₁ j₀).1, f ≫ (IsCofiltered.minToRight j₁ j₀).1, u, ?_, ?_⟩
  · rw [Functor.map_comp_apply, hu]
    exact (IsCofiltered.minToRight j₁ j₀).2
  · have c1 := ConcreteCategory.congr_hom (F.map_comp (IsCofiltered.minToLeft j₁ j₀).1.op f.op) x₁
    have c0 := ConcreteCategory.congr_hom (F.map_comp (IsCofiltered.minToRight j₁ j₀).1.op f.op) x₀
    exact c1.trans (hs.trans c0.symm)

section Gen

end Gen

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

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {J : Type u₃} [Category.{v₃} J]
  {L : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {A : J ⥤ C} {B : D} {u : ∀ j, B ⟶ L.obj (A.obj j)}

/-- Surjectivity on germs for a zero object. -/
theorem surjAt_of_isZero [IsCofiltered J] (q : ℕ) {X : C} (hX : IsZero X) : SurjAt L A B u q X := by
  intro β
  obtain ⟨j⟩ : Nonempty J := IsCofiltered.nonempty
  refine ⟨j, 0, ?_⟩
  rw [map_zero]
  have hLX : IsZero (L.obj X) := L.map_isZero hX
  rw [← Ext.comp_mk₀_id β, hLX.eq_of_src (𝟙 _) 0, Ext.mk₀_zero, Ext.comp_zero]

/-- **Surjectivity on germs passes to binary biproducts.** -/
theorem surjAt_biprod [IsCofiltered J] (hu : ∀ {j j' : J} (a : j' ⟶ j), u j' ≫ L.map (A.map a) = u j)
    (q : ℕ) {X₁ X₂ : C} (h₁ : SurjAt L A B u q X₁) (h₂ : SurjAt L A B u q X₂) :
    SurjAt L A B u q (X₁ ⊞ X₂) := by
  intro β
  obtain ⟨j₁, α₁, hα₁⟩ := h₁ (β.comp (Ext.mk₀ (L.map biprod.fst)) (add_zero q))
  obtain ⟨j₂, α₂, hα₂⟩ := h₂ (β.comp (Ext.mk₀ (L.map biprod.snd)) (add_zero q))
  refine ⟨IsCofiltered.min j₁ j₂,
    (res A (IsCofiltered.minToLeft j₁ j₂) X₁ q α₁).comp (Ext.mk₀ biprod.inl) (add_zero q) +
    (res A (IsCofiltered.minToRight j₁ j₂) X₂ q α₂).comp (Ext.mk₀ biprod.inr) (add_zero q), ?_⟩
  rw [map_add, bc_comp_mk₀, bc_comp_mk₀, bc_res hu, bc_res hu, hα₁, hα₂, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, ← L.map_comp, ← L.map_comp,
    ← Ext.comp_add, ← Ext.mk₀_add, ← L.map_add, biprod.total, L.map_id, Ext.comp_mk₀_id]

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2a =====
section

/-!
# S4-EtPBC-A, O2a: base change surjectivity passes to quotients in the top degree

* `Delta.surjAt_of_epi`: for `0 → X₁ → X₂ → X₃ → 0`, surjectivity in degree `q` for `X₂` gives surjectivity in
  degree `q` for `X₃` when `Ext^(q+1)(B, L X₁) = 0` (covariant exact sequence, no germ argument for `X₁`);
* `bcSurj_of_epi`: the same for base change germs along an epimorphism `G ⟶ H` of sheaves;
* **`bcSurj_two_of_epi`**: on `P¹_S` at a `K`-rational geometric point (`K = K̄`, `ℓ ≠ char K`, `ℓ^m Λ = 0`),
  `BCSurj 2` passes to quotients (`H³` of the fibre vanishes for every sheaf).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {J : Type u₃} [Category.{v₃} J]
  {L : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {A : J ⥤ C} {B : D} {u : ∀ j, B ⟶ L.obj (A.obj j)}

/-- **Surjectivity passes to quotients** when the next `Ext` of the kernel vanishes. -/
theorem surjAt_of_epi {S : ShortComplex C} (hSE : S.ShortExact) (q : ℕ) (hS : SurjAt L A B u q S.X₂)
    (h0 : ∀ e : Ext B (L.obj S.X₁) (q + 1), e = 0) : SurjAt L A B u q S.X₃ := by
  intro β
  obtain ⟨β₂, hβ₂⟩ := Ext.covariant_sequence_exact₃ (X := B) (hSE.map_of_exact L) (x₃ := β) rfl (h0 _)
  obtain ⟨j, α, hα⟩ := hS β₂
  refine ⟨j, α.comp (Ext.mk₀ S.g) (add_zero q), ?_⟩
  rw [bc_comp_mk₀, hα]
  exact hβ₂

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

section Epi

universe u

end Epi

section P1Two

end P1Two

end RamanujanPetersson.EtPBC

end

end


