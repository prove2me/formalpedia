-- Prove2me | Definitions.Def_OAIErdos3B069
-- name    : OAIErdos3B069
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T17:12:43.068409+00:00
-- url     : https://prove2.me/theorems/2193347a-fdf3-46f7-813d-1d6d50a23ed9
-- title:
--   OpenAI Erdős-3 split, definitions bundle 70 of 214
-- statement:
--   Definitions bundle 70 of 214 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B068`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 70 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.ControlledSymbolFactorizationAtFast.mono`, `OAI.Erdos3.NilpotentLieFiltration.controlledProjectionBudget`, `OAI.Erdos3.NilpotentLieFiltration.controlledProjectionDimensionInput`, `OAI.Erdos3.NilpotentLieFiltration.controlledProjectionDimensionInput_nonneg`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlledProjectionBudget_power`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlledProjectionUniformBudget_power`, `OAI.Erdos3.NilpotentLieFiltration.exists_symbolFactorizationIn_projection_pullback`, `OAI.Erdos3.NilpotentLieFiltration.le_controlledProjectionDimensionInput`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolProjection`, `OAI.Erdos3.RationalFilteredNilmanifold.optionNativeCommonFastTop_quotient_kernel_eq_zero`, `OAI.Erdos3.RationalFilteredNilmanifold.optionNativeCommonPivotQuotientFast_graded_top_kernel`, `OAI.Erdos3.RationalFilteredNilmanifold.optionNativeCommonPivotQuotientFast_top_kernel_eq_zero`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPairProjection`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPairProjection_adapted_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPairProjection_false`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPairProjection_jointOrbitSymbol`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPairProjection_layer_surjective`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPairProjection_layers`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPairProjection_native_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPairProjection_piRealOrbit_log`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPairProjection_true`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPivotProductQuotientMap`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPivotProductQuotientMap_fst`, `OAI.Erdos3.RationalFilteredNilmanifold.optionPivotProductQuotientMap_snd`, `OAI.Erdos3.RationalFilteredNilmanifold.pairFrequency_optionPairProjection`, `OAI.Erdos3.RationalFilteredNilmanifold.realification_optionPairProjection_false`, `OAI.Erdos3.RationalFilteredNilmanifold.realification_optionPairProjection_true`, `OAI.Erdos3.realificationLieSubalgebra_comap`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B066

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realificationLieSubalgebra_comap {L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (U : LieSubalgebra ℚ M) (φ : L →ₗ⁅ℚ⁆ M) :
    realificationLieSubalgebra (U.comap φ) =
      (realificationLieSubalgebra U).comap (realificationLieHom φ) := by
  apply LieSubalgebra.toSubmodule_injective
  exact realification_comap U.toSubmodule φ.toLinearMap

namespace NilpotentLieFiltration

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (f : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

noncomputable def realSymbolProjection (w : σ → ℕ) :
    F.RealPolynomialSymbolGroup w →* G.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.filteredPolynomialSymbolMap G φ hφ w)

theorem exists_symbolFactorizationIn_projection_pullback
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hfactor : G.SymbolFactorizationIn f ν hG T
      (F.realSymbolProjection G φ hφ (fun _ => 1) X) p l U) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (((p + 2) ^ 10 + 2) ^ 36) ∧ l ∣ m ∧
      F.SymbolFactorizationIn e ω hF T X (((p + 2) ^ 10 + 2) ^ 18 + p) m
        (U.comap (F.associatedGradedMap G φ hφ)) := by
  classical
  let w : σ → ℕ := fun _ => 1
  let B := F.polynomialSymbolBasis e ω hF w
  let C := G.polynomialSymbolBasis f ν hG w
  let ψ := F.filteredPolynomialSymbolMap G φ hφ w
  have hψ : Function.Surjective ψ :=
    F.filteredPolynomialSymbolMap_surjective G φ hφ w hsurj
  have himage : (⊤ : LieSubalgebra ℚ (F.PolynomialSymbol w)).map ψ = ⊤ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨x, rfl⟩ := hψ y
      exact ⟨x, trivial, rfl⟩
  have hb : ∀ j i, RationalHeightLE (B.repr (B j) i) H := by
    intro j i
    simp only [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact rationalHeightLE_one hH
    · exact rationalHeightLE_zero hH
  obtain ⟨S, m, hm, hmp, hlm, hsolve, hslow, hgrid⟩ :=
    NilpotentLieBCHGroup.exists_controlled_fast_lift
      (F.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (G.polynomialSymbol_lowerCentralSeries_eq_bot w) B C
      (fun z => z.val.1) (fun z => z.val.1) ⊤ B B.span_eq
      (fun _ _ _ => trivial) ψ
      (fun i j hij => F.filteredPolynomialSymbolMap_monomial_blocks
        G e ω hF f ν hG φ hφ w j i hij)
      hH hl hb
      (fun i j => F.filteredPolynomialSymbolMap_basis_height
        G e ω hF f ν hG φ hφ w hH hentries j i)
      hp hrows hcols hHp hlp
  simp only [Basis.equivFun_apply] at hslow hgrid
  let lift := NilpotentLieBCHGroup.realLinearCoordinateLift
    (hL := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w) S
  have hright (g : G.RealPolynomialSymbolGroup w) :
      F.realSymbolProjection G φ hφ w (lift g) = g := by
    apply (hsolve g ?_).2
    change g.coord ∈ ((⊤ : LieSubalgebra ℚ (F.PolynomialSymbol w)).map ψ).toSubmodule.baseChange ℝ
    rw [himage]
    simp
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := hfactor
  dsimp only [SymbolSlowBound, SymbolRationalGrid] at hE hR
  let middle := (lift E)⁻¹ * X * (lift R)⁻¹
  have hmiddle : F.realSymbolProjection G φ hφ w middle = P := by
    dsimp only [middle]
    rw [map_mul, map_mul, map_inv, map_inv, hright, hright, ← hprod]
    group
  refine ⟨m, hm, hmp, hlm, lift E, middle, lift R, ?_, ?_, ?_, ?_⟩
  · dsimp only [middle]; group
  · have h := hslow (monomialScale T) (monomialScale_pos T hT)
      (Real.exp p) (Real.exp_pos p).le E (by with_reducible exact hE)
    simp only [← Real.exp_add] at h
    dsimp only [SymbolSlowBound]
    with_reducible exact h
  · apply hgrid R
    with_reducible exact hR
  · rw [← F.symbolPointwiseSubalgebra_comap G e ω hF f ν hG φ hφ w U,
      realificationLieSubalgebra_comap]
    change (F.realSymbolProjection G φ hφ w middle).coord ∈
      realificationLieSubalgebra (G.symbolPointwiseSubalgebra f ν hG w U)
    rw [hmiddle]
    with_reducible exact hP

end NilpotentLieFiltration
end Erdos3

end

section

universe v

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]

def optionPairProjection (j : ι) :
    (∀ i : Option ι, optionLieSpace L₀ L i) →ₗ⁅ℚ⁆ PairAlgebra L₀ (L j) :=
  liePiMap (fun b => by
    cases b
    · exact liePiEval (some j)
    · exact liePiEval none)

@[simp] theorem optionPairProjection_true (j : ι)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    optionPairProjection j x true = x none := rfl

@[simp] theorem optionPairProjection_false (j : ι)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    optionPairProjection j x false = x (some j) := rfl

@[simp] theorem pairFrequency_optionPairProjection (j : ι)
    (η : L₀ →ₗ[ℚ] ℚ) (θ : L j →ₗ[ℚ] ℚ)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    pairFrequency η θ (optionPairProjection j x) = η (x none) + θ (x (some j)) := by
  rw [pairFrequency_apply, optionPairProjection_true, optionPairProjection_false]

@[simp] theorem realification_optionPairProjection_true (j : ι)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) :
    realificationLieHom (liePiEval true) (realificationLieHom (optionPairProjection j) x) =
      realificationLieHom (liePiEval none) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp <;> rfl
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

@[simp] theorem realification_optionPairProjection_false (j : ι)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) :
    realificationLieHom (liePiEval false) (realificationLieHom (optionPairProjection j) x) =
      realificationLieHom (liePiEval (some j)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp <;> rfl
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

variable [Fintype ι] {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (j : ι)

theorem optionPairProjection_layers (k : ℕ)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i)
    (hx : x ∈ (optionProduct D₀ D).filtration.layer k) :
    optionPairProjection j x ∈ (pi (pairModels D₀ (D j))).filtration.layer k := by
  apply (mem_pi_layer (fun b => (pairModels D₀ (D j) b).filtration) k _).mpr
  intro b
  cases b
  · exact (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k x).mp hx (some j)
  · exact (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k x).mp hx none

theorem optionPairProjection_layer_surjective (k : ℕ) (x : PairAlgebra L₀ (L j))
    (hx : x ∈ (pi (pairModels D₀ (D j))).filtration.layer k) :
    ∃ y ∈ (optionProduct D₀ D).filtration.layer k, optionPairProjection j y = x := by
  classical
  let y : ∀ i : Option ι, optionLieSpace L₀ L i
    | none => x true
    | some i => Pi.single (M := L) j (x false) i
  refine ⟨y, ?_, ?_⟩
  · apply (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k y).mpr
    intro i
    cases i with
    | none =>
      exact (mem_pi_layer (fun b => (pairModels D₀ (D j) b).filtration) k x).mp hx true
    | some i =>
      by_cases hij : i = j
      · subst i
        change Pi.single (M := L) j (x false) j ∈ (D j).filtration.layer k
        erw [Pi.single_eq_same]
        exact (mem_pi_layer (fun b => (pairModels D₀ (D j) b).filtration) k x).mp hx false
      · change Pi.single (M := L) j (x false) i ∈ (D i).filtration.layer k
        erw [Pi.single_eq_of_ne hij]
        exact Submodule.zero_mem _
  · funext b
    cases b
    · exact Pi.single_eq_same (M := L) j (x false)
    · rfl

theorem optionPairProjection_piRealOrbit_log {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w) :
    VectorPolynomial.map
      ((realificationLieHom (optionPairProjection j)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log =
        (pairOrbit D₀ (D j) (g none) (g (some j))).log := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  apply ((Pi.basis (fun b => (pairModels D₀ (D j) b).basis)).baseChange ℝ).repr.injective
  ext ⟨b, k⟩
  rw [realification_pi_basis_repr, realification_pi_basis_repr]
  change ((pairModels D₀ (D j) b).basis.baseChange ℝ).repr
    (realificationLieHom (liePiEval b) (realificationLieHom (optionPairProjection j)
      (coefficients (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log α))) k =
    ((pairModels D₀ (D j) b).basis.baseChange ℝ).repr
      (realificationLieHom (liePiEval b)
        (coefficients (pairOrbit D₀ (D j) (g none) (g (some j))).log α)) k
  have hpair := piRealOrbit_coefficient (fun b => (pairModels D₀ (D j) b).filtration)
    (fun b => by cases b; exact g (some j); exact g none) α b
  change realificationLieHom (liePiEval b)
    (coefficients (pairOrbit D₀ (D j) (g none) (g (some j))).log α) = _ at hpair
  rw [hpair]
  cases b
  · rw [realification_optionPairProjection_false]
    exact congrArg (fun x => ((D j).basis.baseChange ℝ).repr x k)
      (piRealOrbit_coefficient (fun i => (optionFactors D₀ D i).filtration) g α (some j))
  · rw [realification_optionPairProjection_true]
    exact congrArg (fun x => (D₀.basis.baseChange ℝ).repr x k)
      (piRealOrbit_coefficient (fun i => (optionFactors D₀ D i).filtration) g α none)

variable {α β σ : Type*}
  (e : Basis α ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) (ω : α → ℕ)
  (hF : ∀ k, (optionProduct D₀ D).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ ω i}))
  (b : Basis β ℚ (PairAlgebra L₀ (L j))) (ν : β → ℕ)
  (hG : ∀ k, (pi (pairModels D₀ (D j))).filtration.layer k =
    Submodule.span ℚ (b '' {i | k ≤ ν i}))

theorem optionPairProjection_jointOrbitSymbol {w : σ → ℕ}
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w) :
    (optionProduct D₀ D).filtration.realSymbolProjection
      (pi (pairModels D₀ (D j))).filtration
      (optionPairProjection j) (optionPairProjection_layers D₀ D j) w
      ((optionProduct D₀ D).filtration.realPolynomialSymbolHom e ω hF w
        ⟨⟨(piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log,
          (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).property⟩⟩) =
      pairOrbitSymbol D₀ (D j) (g none) (g (some j)) b ν hG := by
  apply NilpotentLieBCHGroup.ext
  have h := (optionProduct D₀ D).filtration.realFilteredPolynomialSymbolMap_polynomial
    (pi (pairModels D₀ (D j))).filtration
    (optionPairProjection j) (optionPairProjection_layers D₀ D j)
    e ω hF b ν hG w
    ⟨(piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log,
      (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).property⟩
  change _ = (pi (pairModels D₀ (D j))).filtration.realSymbolOfPolynomial b ν hG w
    (pairOrbit D₀ (D j) (g none) (g (some j))).log
  exact h.trans (congrArg
    ((pi (pairModels D₀ (D j))).filtration.realSymbolOfPolynomial b ν hG w)
    (optionPairProjection_piRealOrbit_log D₀ D j g))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {J : Type*} [Fintype J] {L : Type u} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  {s d₀ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))

theorem optionPairProjection_native_logHeight (j : J)
    (x : ∀ i : Option J, optionLieSpace L M i) {p : ℝ}
    (hx : ∀ k, rationalLogHeight ((optionProduct D E).basis.repr x k) ≤ p) :
    ∀ k, rationalLogHeight ((pi (pairModels D (E j))).basis.repr
      (optionPairProjection j x) k) ≤ p := by
  intro k
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ b : Bool, Fin (Bool.rec (d j) d₀ b))).symm k = z
  rcases z with ⟨b, i⟩
  cases b
  · change rationalLogHeight ((E j).basis.repr (x (some j)) i) ≤ p
    exact (congrArg rationalLogHeight
      (productFinBasis_repr_component (optionFactors D E) x (some j) i)).le.trans (hx _)
  · change rationalLogHeight (D.basis.repr (x none) i) ≤ p
    exact (congrArg rationalLogHeight
      (productFinBasis_repr_component (optionFactors D E) x none i)).le.trans (hx _)

theorem optionPairProjection_adapted_logHeight {α β : Type*}
    (j : J) (e : Basis α ℚ (∀ i : Option J, optionLieSpace L M i))
    (b : Basis β ℚ (PairAlgebra L (M j))) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ i : Bool, Fin (Bool.rec (d j) d₀ i)) : ℝ) ≤ p)
    (he : ∀ i k, rationalLogHeight ((optionProduct D E).basis.repr (e i) k) ≤ p)
    (hb : ∀ i k, rationalLogHeight (b.repr ((pi (pairModels D (E j))).basis i) k) ≤ p) :
    ∀ i k, rationalLogHeight (b.repr (optionPairProjection j (e i)) k) ≤ (p + 3) ^ 4 := by
  intro i k
  have hp' : 0 ≤ p + 1 := by linarith
  have hcoord := rational_basis_coordinates_logHeight (pi (pairModels D (E j))).basis b
    hp' (by simpa only [Fintype.card_fin] using hdim.trans (show p ≤ p + 1 by linarith))
    (ceil_exp_le_exp_add_one hp)
    (fun i k => rationalHeightLE_ceil_exp (hb i k)) (optionPairProjection j (e i))
    (fun k => (optionPairProjection_native_logHeight D E j (e i) (he i) k).trans
      (by linarith)) k
  convert hcoord using 1
  ring

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

noncomputable def controlledProjectionBudget (p : ℝ) : ℝ :=
  (((p + 2) ^ 10 + 2) ^ 36) + (((p + 2) ^ 10 + 2) ^ 18 + p) +
    (preimageBasisBudget p + 1)

variable {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (f : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

theorem exists_controlledProjectionBudget_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → controlledProjectionBudget p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ :=
    Polynomial.X + (Polynomial.X + (Polynomial.X + 3) ^ 7 + 2) ^ 4 + 1
  let P : Polynomial ℕ :=
    ((Polynomial.X + 2) ^ 10 + 2) ^ 36 +
      (((Polynomial.X + 2) ^ 10 + 2) ^ 18 + Polynomial.X) +
      ((Q + Q * ((Q + 2) ^ 7 + Q)) + 1)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, Q, controlledProjectionBudget, preimageBasisBudget, sparseGeneratorBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def controlledProjectionDimensionInput (s : ℕ) (p : ℝ) : ℝ :=
  2 * ((p + (s + 2)) ^ (s + 2)) ^ 2 + p + 1

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem ControlledSymbolFactorizationAtFast.mono {η : L →ₗ[ℚ] ℚ}
    {T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)}
    {p q : ℝ} {U : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.ControlledSymbolFactorizationAtFast e ω hF η T X p U)
    (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.ControlledSymbolFactorizationAtFast e ω hF η T X q U := by
  obtain ⟨m, E, P, R, v, hm, hmp, hprod, hE, hR, hv, hgraded, hheight, hzero, hP⟩ := h
  exact ⟨m, E, P, R, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    F.symbolSlowBound_mono e ω hF _ T hT (Real.exp_le_exp.mpr hpq) E hE,
    hR, hv, hgraded, fun i j => (hheight i j).trans hpq, hzero, hP⟩

variable {κ M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (G : NilpotentLieFiltration M s)
    (f : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

theorem le_controlledProjectionDimensionInput (s : ℕ) (p : ℝ) :
    p ≤ controlledProjectionDimensionInput s p := by
  unfold controlledProjectionDimensionInput
  nlinarith [sq_nonneg ((p + (s + 2)) ^ (s + 2))]

theorem controlledProjectionDimensionInput_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ controlledProjectionDimensionInput s p :=
  hp.trans (le_controlledProjectionDimensionInput s p)

theorem exists_controlledProjectionUniformBudget_power (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      controlledProjectionBudget (controlledProjectionDimensionInput s p) ≤ (p + C) ^ C := by
  obtain ⟨a, _, ha⟩ := exists_controlledProjectionBudget_power
  let P : Polynomial ℕ :=
    (2 * ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)) ^ 2 +
      Polynomial.X + 1 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  apply (ha _ (controlledProjectionDimensionInput_nonneg s hp)).trans
  simpa [P, controlledProjectionDimensionInput, Polynomial.eval₂_pow] using hbound p hp

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionPivotQuotientStrong
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} {L : Type u} {M : J → Type u} {Y : Type*}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)

noncomputable def optionPivotProductQuotientMap :
    (∀ i : Option J, optionLieSpace L M i) →ₗ⁅ℚ⁆
      (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) × (∀ j, M j) :=
  ((lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)).comp
    (liePiEval none)).prod (liePiMap (fun j => liePiEval (some j)))

@[simp] theorem optionPivotProductQuotientMap_fst
    (x : ∀ i : Option J, optionLieSpace L M i) :
    (optionPivotProductQuotientMap D π eta js x).1 =
      lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js) (x none) := rfl

@[simp] theorem optionPivotProductQuotientMap_snd
    (x : ∀ i : Option J, optionLieSpace L M i) (j : J) :
    (optionPivotProductQuotientMap D π eta js x).2 j = x (some j) := rfl

variable [Fintype J]

variable (U : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)

variable (theta : ∀ j, M j →ₗ[ℚ] ℚ)
  (hzero : ∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer U s →
    realifyFunctional ((pairFrequency (eta j) (theta j)).comp
      (optionPairProjection j).toLinearMap) x = 0)

variable {κ κQ : Type*}
  (e : Basis κ ℚ (∀ i : Option J, optionLieSpace L M i)) (μ : κ → ℕ)
  (hH : ∀ k, (optionProduct D E).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (q : Basis κQ ℚ ((L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) × (∀ j, M j)))
  (ν : κQ → ℕ)
  (hQ : ∀ k, (D.filtration.pivotProductQuotientFiltration π eta js
    (NilpotentLieFiltration.pi (fun j => (E j).filtration))).layer k =
      Submodule.span ℚ (q '' {i | k ≤ ν i}))
  (hU : BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e μ hH)
    μ U.toSubmodule)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} [Fintype J] {L : Type u} {M : J → Type u} {Y : Type*}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  {σ κ κQ : Type*} [Fintype σ] [Fintype κ] [Fintype κQ]
  (e : Basis κ ℚ (∀ i : Option J, optionLieSpace L M i)) (μ : κ → ℕ)
  (hF : ∀ k, (optionProduct D E).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (q : Basis κQ ℚ ((L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) × (∀ j, M j)))
  (ν : κQ → ℕ)
  (hQ : ∀ k, (D.filtration.pivotProductQuotientFiltration π eta js
    (NilpotentLieFiltration.pi (fun j => (E j).filtration))).layer k =
      Submodule.span ℚ (q '' {i | k ≤ ν i}))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} [Fintype J] {L Y : Type u} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal π eta js, π x = 0)
  (U : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
  (theta : ∀ j, M j →ₗ[ℚ] ℚ)
  (hzero : ∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer U s →
    realifyFunctional ((pairFrequency (eta j) (theta j)).comp
      (optionPairProjection j).toLinearMap) x = 0)

include hzero in

theorem optionNativeCommonFastTop_quotient_kernel_eq_zero
    (y : ∀ i : Option J,
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i)
    (hy : y ∈ ((optionProduct D E).filtration.gradedRefiltrationLayer U s).map
      (optionMarkedLieMap (L := M)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js))).toLinearMap)
    (hmark : optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker) y = 0) :
    y = 0 := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hπ : π (x none) = 0 := congrFun hmark none
  have hpartner (j : J) : x (some j) = 0 := congrFun hmark (some j)
  have hmem : x none ∈ D.filtration.pivotAnnihilatorIdeal π eta js := by
    apply (D.filtration.mem_pivotAnnihilatorIdeal π eta js (x none)).mpr
    refine ⟨?_, hπ, ?_⟩
    · exact (mem_pi_layer (fun i => (optionFactors D E i).filtration) s x).mp
        ((optionProduct D E).filtration.gradedRefiltrationLayer_le U s hx) none
    · intro j _
      have hz := (optionProduct D E).filtration.frequency_zero_on_refilteredLayer_of_real
        U ((pairFrequency (eta j) (theta j)).comp (optionPairProjection j).toLinearMap)
        s (hzero j) x hx
      simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap, pairFrequency_apply,
        optionPairProjection_true, optionPairProjection_false] at hz
      have hp : (x (some j) : M j) = (0 : M j) := hpartner j
      rw [hp, map_zero, add_zero] at hz
      exact hz
  funext i
  cases i with
  | none => exact (lieQuotientMap_eq_zero
      (D.filtration.pivotAnnihilatorIdeal π eta js) (x none)).mpr hmem
  | some j => exact hpartner j

variable {dQ : ℕ}
  (Q : RationalFilteredNilmanifold
    (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) s dQ)
  (hQ : Q.filtration = D.filtration.pivotQuotientFiltration π eta js)
  {κ κQ : Type*}
  (e : Basis κ ℚ (∀ i : Option J, optionLieSpace L M i)) (μ : κ → ℕ)
  (hSource : ∀ k, (optionProduct D E).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (c : Basis κQ ℚ (∀ i : Option J,
    optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i))
  (ν : κQ → ℕ)
  (hTarget : ∀ k, (optionProduct Q E).filtration.layer k =
    Submodule.span ℚ (c '' {i | k ≤ ν i}))
  (hU : BasisGradedSubmodule
    ((optionProduct D E).filtration.associatedGradedBasis e μ hSource) μ U.toSubmodule)

include hzero e μ hSource c ν hTarget hU in

theorem optionNativeCommonPivotQuotientFast_top_kernel_eq_zero
    (y : ∀ i : Option J,
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i)
    (hy : y ∈ (optionProduct Q E).filtration.gradedRefiltrationLayer
      (optionNativeCommonPivotQuotientFast D E π eta js Q hQ U) s)
    (hmark : optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker) y = 0) :
    y = 0 := by
  rw [optionNativeCommonPivotQuotientFast_layer_eq
    D E π eta js Q hQ U e μ hSource c ν hTarget hU s] at hy
  exact optionNativeCommonFastTop_quotient_kernel_eq_zero
    D E π eta js hker U theta hzero y hy hmark

include hzero e μ hSource c ν hTarget hU in

theorem optionNativeCommonPivotQuotientFast_graded_top_kernel
    (G : NilpotentLieFiltration (∀ i : Option J, optionLieSpace Y M i) s)
    (hmarked : ∀ k, ∀ y ∈ (optionProduct Q E).filtration.layer k,
      optionMarkedLieMap (L := M)
        (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker) y ∈
          G.layer k) :
    ∀ a ∈ optionNativeCommonPivotQuotientFast D E π eta js Q hQ U,
      basisGradeProjection
        ((optionProduct Q E).filtration.associatedGradedBasis c ν hTarget) ν s a = a →
      (optionProduct Q E).filtration.associatedGradedMap G
        (optionMarkedLieMap (L := M)
          (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker))
        hmarked a = 0 → a = 0 := by
  apply ((optionProduct Q E).filtration.graded_top_kernel_iff_refiltered_top_kernel
    G c ν hTarget
    (optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker))
    hmarked (optionNativeCommonPivotQuotientFast D E π eta js Q hQ U)).mpr
  exact optionNativeCommonPivotQuotientFast_top_kernel_eq_zero
    D E π eta js hker U theta hzero Q hQ e μ hSource c ν hTarget hU

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration
open scoped TensorProduct

variable {J : Type v} [Fintype J] {L Y : Type u} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ dQ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal π eta js, π x = 0)
  (Q : RationalFilteredNilmanifold
    (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) s dQ)
  (hQ : Q.filtration = D.filtration.pivotQuotientFiltration π eta js)
  (Fmark : NilpotentLieFiltration Y s)
  (hstrong : ∀ k, ∀ y ∈ Fmark.layer k, ∃ x ∈ D.filtration.layer k, π x = y)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end


