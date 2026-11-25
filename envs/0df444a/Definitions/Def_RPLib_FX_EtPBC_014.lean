-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_014
-- name    : RPLib_FX_EtPBC_014
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T18:41:42.367161+00:00
-- url     : https://prove2.me/theorems/f6f28e20-0ca2-5592-9b83-b63a28e3b753
-- title:
--   Proper base change for the projective line, library file 014
-- statement:
--   File 014 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovAR`: S4-EtPBC-A, R4-T2 (A2c-1b): uniform relations of `p` on the base charts (Artin-Rees)
--   * `S4.Def_RP_EtPBC_A_CovAs1`: S4-EtPBC-A, R4-T2 (A3 assembly, As1): base change of the chart data along a flat algebra
--   * `S4.Def_RP_EtPBC_A_CovPr13`: S4-EtPBC-A, R4-T2 (A3m): the residue data on tensor charts (no presentations)
--   * `S4.Def_RP_EtPBC_A_CovG1`: S4-EtPBC-A, R4-T2 (A2a): sections of `O(d)` of a two-chart cover and their lifting along transitions
--   * `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
--   * `S4.Def_RP_EtPBC_A_CovG3`: S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`
--   * `S4.Def_RP_EtPBC_A_CovFil2`: S4-EtPBC-A, R4-T2 (A2c-1e): the `p`-adic filtration on sections of `O(d)` is the `p`-power filtration
--   * `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
--   * `S4.Def_RP_EtPBC_A_Z1Two`: S4-EtPBC-A, (Z1): sections over the two charts of `P¹_A` form a finite `A`-module
--   * `S4.Def_RP_EtPBC_A_CovLim5`: S4-EtPBC-A, R4-T2 (A2c-2f): multiplication by `T₀`, `T₁` on compatible families; completed generation
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
--   * `S4.Def_RP_EtPBC_A_Z3Gen`: S4-EtPBC-A, (Z) geometric layer 5 (G-b algebra): one generator for a chart of `P¹`, and pushouts
--   * `S4.Def_RP_EtPBC_A_CovGl1`: S4-EtPBC-A, R4-T2 (G1c, part 2a): localization squares are pushouts
--   * `S4.Def_RP_EtPBC_A_Delta`: S4-EtPBC-A, L1e: the δ-functor lemma for base change maps on germs
--   * `S4.Def_RP_EtPBC_A_DescA`: S4-EtPBC-A, R4-T1a: descent of a torsor under a finite group along a flat cover (algebra)
--   * `S4.Def_RP_EtPBC_A_DescB`: S4-EtPBC-A, R4-T1b (algebra part): descent data from locally constant functions, and localization
--   * `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
--   * `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
--   * `S4.Def_RP_EtPBC_A_DeltaS`: S4-EtPBC-A, L1e': surjectivity of base change along short exact sequences (the epi four-lemma)
--   * `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
--   * `S4.Def_RP_EtPBC_A_T3dA`: S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension
--   * `S4.Def_RP_EtPBC_A_O2MV`: S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves
--   * `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
--   * `S4.Def_RP_EtPBC_A_O2M2`: S4-EtPBC-A, O2 (MV route), M2: local vanishing of cohomology classes
--   * `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
--   * `S4.Def_RP_EtPBC_A_O2E1`: S4-EtPBC-A, O2 C-plan S4a: rings of finite type and unramified over a Dedekind domain
--   * `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
--   * `S4.Def_RP_EtPBC_A_O2PPTc`: S4-EtPBC-A, O2 GLOB (O2PPTc): transfer of a piece Kummer class along a shrink `D₁ ⟶ D`
--   * `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_006
import Definitions.Def_RPLib_FX_EtPBC_007
import Definitions.Def_RPLib_FX_EtPBC_010
import Definitions.Def_RPLib_FX_EtPBC_011
import Definitions.Def_RPLib_FX_EtPBC_012

/-!
# Proper base change for the projective line, library file 014

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovAR`: S4-EtPBC-A, R4-T2 (A2c-1b): uniform relations of `p` on the base charts (Artin-Rees)
* `S4.Def_RP_EtPBC_A_CovAs1`: S4-EtPBC-A, R4-T2 (A3 assembly, As1): base change of the chart data along a flat algebra
* `S4.Def_RP_EtPBC_A_CovPr13`: S4-EtPBC-A, R4-T2 (A3m): the residue data on tensor charts (no presentations)
* `S4.Def_RP_EtPBC_A_CovG1`: S4-EtPBC-A, R4-T2 (A2a): sections of `O(d)` of a two-chart cover and their lifting along transitions
* `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
* `S4.Def_RP_EtPBC_A_CovG3`: S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`
* `S4.Def_RP_EtPBC_A_CovFil2`: S4-EtPBC-A, R4-T2 (A2c-1e): the `p`-adic filtration on sections of `O(d)` is the `p`-power filtration
* `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
* `S4.Def_RP_EtPBC_A_Z1Two`: S4-EtPBC-A, (Z1): sections over the two charts of `P¹_A` form a finite `A`-module
* `S4.Def_RP_EtPBC_A_CovLim5`: S4-EtPBC-A, R4-T2 (A2c-2f): multiplication by `T₀`, `T₁` on compatible families; completed generation
* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
* `S4.Def_RP_EtPBC_A_Z3Gen`: S4-EtPBC-A, (Z) geometric layer 5 (G-b algebra): one generator for a chart of `P¹`, and pushouts
* `S4.Def_RP_EtPBC_A_CovGl1`: S4-EtPBC-A, R4-T2 (G1c, part 2a): localization squares are pushouts
* `S4.Def_RP_EtPBC_A_Delta`: S4-EtPBC-A, L1e: the δ-functor lemma for base change maps on germs
* `S4.Def_RP_EtPBC_A_DescA`: S4-EtPBC-A, R4-T1a: descent of a torsor under a finite group along a flat cover (algebra)
* `S4.Def_RP_EtPBC_A_DescB`: S4-EtPBC-A, R4-T1b (algebra part): descent data from locally constant functions, and localization
* `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
* `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
* `S4.Def_RP_EtPBC_A_DeltaS`: S4-EtPBC-A, L1e': surjectivity of base change along short exact sequences (the epi four-lemma)
* `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
* `S4.Def_RP_EtPBC_A_T3dA`: S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension
* `S4.Def_RP_EtPBC_A_O2MV`: S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves
* `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
* `S4.Def_RP_EtPBC_A_O2M2`: S4-EtPBC-A, O2 (MV route), M2: local vanishing of cohomology classes
* `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
* `S4.Def_RP_EtPBC_A_O2E1`: S4-EtPBC-A, O2 C-plan S4a: rings of finite type and unramified over a Dedekind domain
* `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
* `S4.Def_RP_EtPBC_A_O2PPTc`: S4-EtPBC-A, O2 GLOB (O2PPTc): transfer of a piece Kummer class along a shrink `D₁ ⟶ D`
* `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovAR =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1b): uniform relations of `p` on the base charts (Artin-Rees)

For `α : Fin g → R` and `ιB : R → B`:
* **`RelV p α ιB n`**: vectors `w` with entries in `p^n B` and `∑ αᵢ wᵢ = 0`; `muB`, `mem_smul_top_pi`, `mem_relV_iff`;
* **`relV_transport`**: a chart-0 relation is `t₀^f` times a chart-1 relation on the overlap `N`;
* **`relV_uniform`** (Artin-Rees, `B₀` noetherian): one bound `F` such that for every `n` the relations `RelV n` are
  `p^(n-n')`-combinations of finitely many relations in `RelV n'` (`n' ≤ n`) whose transition exponents are `≤ F`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section RelV

variable {R : Type u} [CommRing R] (p : Ideal R) {g : ℕ} (α : Fin g → R)

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] (φ₀ : B₀ →+* N) (φ₁ : B₁ →+* N)
  (t₀ : B₀) (t₁ : B₁) (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁)

/-- **Uniform relations** (Artin-Rees): one bound `F` on the transition exponents of finitely many generating
relations, for every `n`. -/
theorem relV_uniform [IsNoetherianRing B₀] (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))
    (hts : φ₀ t₀ * φ₁ t₁ = 1) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) :
    ∃ F : ℕ, ∀ n, ∃ n' ≤ n, ∃ (L : ℕ) (ρ0 : Fin L → Fin g → B₀) (ρ1 : Fin L → Fin g → B₁) (f : Fin L → ℕ),
      (∀ l, f l ≤ F) ∧ (∀ l, ρ0 l ∈ RelV p α ιB₀ n') ∧ (∀ l, ρ1 l ∈ RelV p α ιB₁ n') ∧
      (∀ l i, φ₀ (ρ0 l i) = φ₀ t₀ ^ f l * φ₁ (ρ1 l i)) ∧
      ∀ w ∈ RelV p α ιB₀ n, ∃ β : Fin L → B₀, (∀ l, β l ∈ (p ^ (n - n')).map ιB₀) ∧
        w = ∑ l, β l • ρ0 l := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (p.map ιB₀) (LinearMap.ker (muB α ιB₀))
  have hfg : ∀ k : ℕ, ∃ (L : ℕ) (s : Fin L → Fin g → B₀), Submodule.span B₀ (Set.range s) =
      (p.map ιB₀) ^ k • (⊤ : Submodule B₀ (Fin g → B₀)) ⊓ LinearMap.ker (muB α ιB₀) :=
    fun k => Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian _)
  choose L s hs using hfg
  have hsm : ∀ k l, s k l ∈ RelV p α ιB₀ k := by
    intro k l
    rw [mem_relV_iff, ← hs k]
    exact Submodule.subset_span ⟨l, rfl⟩
  choose f ρ1 hρ1 hρ using fun k (l : Fin (L k)) =>
    relV_transport p α φ₀ φ₁ t₀ t₁ ιB₀ ιB₁ hφ₁ hu₁ hts hιB k (s k l) (hsm k l)
  refine ⟨(Finset.range (c + 1)).sup fun k => Finset.univ.sup (f k), fun n => ?_⟩
  obtain ⟨n', hn'⟩ : ∃ n', n' = min n c := ⟨_, rfl⟩
  have hn'c : n' ≤ c := hn' ▸ min_le_right _ _
  refine ⟨n', hn' ▸ min_le_left _ _, L n', s n', ρ1 n', f n', fun l => ?_, hsm n', hρ1 n', hρ n',
    fun w hw => ?_⟩
  · exact le_trans (Finset.le_sup (f := f n') (Finset.mem_univ l))
      (Finset.le_sup (f := fun k => Finset.univ.sup (f k)) (Finset.mem_range.2 (by omega)))
  · rw [mem_relV_iff] at hw
    by_cases hnc : n ≤ c
    · have e : n' = n := hn'.trans (min_eq_left hnc)
      have hw' : w ∈ Submodule.span B₀ (Set.range (s n')) := by
        rw [hs n', e]
        exact hw
      obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun B₀).1 hw'
      refine ⟨β, fun l => ?_, hβ.symm⟩
      rw [e, Nat.sub_self, pow_zero, Ideal.one_eq_top, Ideal.map_top]
      exact Submodule.mem_top
    · have e : n' = c := hn'.trans (min_eq_right (by omega))
      have hw' : w ∈ (p.map ιB₀) ^ (n - n') • Submodule.span B₀ (Set.range (s n')) := by
        rw [hs n', e, ← hc n (by omega)]
        exact hw
      obtain ⟨a, ha, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ _ _).1 hw'
      refine ⟨fun l => a l, fun l => ?_, ?_⟩
      · rw [Ideal.map_pow]
        exact ha l
      · rw [← hsum, Finsupp.sum_fintype a (fun l c => c • s n' l) (fun l => zero_smul _ _)]

end RelV

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As1): base change of the chart data along a flat algebra

* `tmap_id_left`: `map id φ` on `S ⊗[A] B` is `φ.lTensor S`.
* **`away_bc`**: for `S` flat over `A`, `IsAwayMap φ t` gives `IsAwayMap (map id φ) (1 ⊗ t)`.
* `tmul_one_mul_one`: `x * y = 1` gives `(1 ⊗ x) * (1 ⊗ y) = 1`.
* `hat_complete`, `hat_jac`: the completion `Â` is `p Â`-adically complete and `p Â ≤ jacobson ⊥` (`p` f.g.).
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section BC

variable {A S B N : Type u} [CommRing A] [CommRing S] [Algebra A S] [CommRing B] [Algebra A B] [CommRing N]
  [Algebra A N]

/-- **Base change of an away map along a flat algebra.** -/
theorem away_bc [Module.Flat A S] (φ : B →ₐ[A] N) (t : B) (h : IsAwayMap (φ : B →+* N) t) :
    IsAwayMap (Algebra.TensorProduct.map (AlgHom.id A S) φ : S ⊗[A] B →+* S ⊗[A] N) ((1 : S) ⊗ₜ[A] t) := by
  refine ⟨fun y => ?_, fun a ha => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp only [map_zero, mul_zero]⟩
    | tmul s n =>
      obtain ⟨k, b, hb⟩ := h.1 n
      have hb' : φ t ^ k * n = φ b := hb
      refine ⟨k, s ⊗ₜ[A] b, ?_⟩
      simp only [RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hb']
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨k₁, a₁, e₁⟩ := h₁
      obtain ⟨k₂, a₂, e₂⟩ := h₂
      refine ⟨k₁ + k₂, ((1 : S) ⊗ₜ[A] t) ^ k₂ * a₁ + ((1 : S) ⊗ₜ[A] t) ^ k₁ * a₂, ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, ← e₁, ← e₂, pow_add]
      ring
  · have hex := Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map φ.toLinearMap)
    have ha' : φ.toLinearMap.lTensor S a = 0 := by
      rw [← tmap_id_left]
      exact ha
    obtain ⟨w, rfl⟩ := (hex a).1 ha'
    exact away_bc_ker φ t h w

end BC

section Hat

end Hat

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr13 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3m): the residue data on tensor charts (no presentations)

Over `A` with `χ : A →+* K`: `Ah` (the completion, residue `res`), `R'` (residue `χ'`, a section `s : K →+* R'`), a
chart `B`, a target `Q` with `ν : K →+* Q`, `βQ : B →+* Q` (`βQ ∘ algebraMap = ν ∘ χ`).
* `Jt B χ' = (ker χ') (R' ⊗ B)`; `tmul_mem_Jt`;
* **`kap`** `: R' ⊗[A] B →+* Q`, `r ⊗ b ↦ ν (χ' r) * βQ b` (`kap_tmul`), `Jt_le_ker_kap`;
* **`lamQ`** `: Ah ⊗[A] B →+* (R' ⊗[A] B) ⧸ Jt`, `â ⊗ b ↦ s (res â) ⊗ b` (`lamQ_tmul`), `lamQ_map`, `I_le_ker_lamQ`;
* `kap_map` (the two residues agree on `C ⊗ B`), **`exists_sec`** (the section for `resid_ker_pm`).
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Tens

end Tens

section Lam

variable {K A R' B Ah : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing Ah] [Algebra A Ah] (χ : A →+* K) (χ' : R' →+* K) (res : Ah →+* K) (s : K →+* R')
  (hres : ∀ a, res (algebraMap A Ah a) = χ a) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a) (hs : ∀ k, χ' (s k) = k)

/-- `Ah ⊗[A] B → (R' ⊗[A] B) ⧸ Jt`, `â ⊗ b ↦ s (res â) ⊗ b`. -/
def lamQ : Ah ⊗[A] B →+* (R' ⊗[A] B) ⧸ Jt B χ' :=
  (Algebra.TensorProduct.productMap (lamL (B := B) χ χ' res s hres hχ' hs)
    ((Ideal.Quotient.mkₐ A (Jt B χ')).comp Algebra.TensorProduct.includeRight)).toRingHom

end Lam

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovG1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2a): sections of `O(d)` of a two-chart cover and their lifting along transitions

* `TwoCov.u` (the coordinate `t` on the overlap), **`TwoCov.sec C d`**: the pairs `(x₀, x₁)` with
  `ψ₀ x₀ = u^d ψ₁ x₁` (global sections of `O(d)`);
* `TwoCovHom.u_map`, **`TwoCovHom.secMap`**: a transition maps sections to sections;
* **`TwoCovHom.secMap_surj`**: if every element of `ker ρ` is `ψ₀ k₀ - u^d ψ₁ k₁` with `kᵢ ∈ ker ρᵢ`, sections lift;
* **`TwoCovHom.hker_of_gens`**: that hypothesis from generators `ψ₀ (g j)` of `ker ρ` whose multiples split.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Sec

variable {b₀ b₁ n : Type u} [CommRing b₀] [CommRing b₁] [CommRing n] {φb₀ : b₀ →+* n} {φb₁ : b₁ →+* n}
  {τ₀ : b₀} {τ₁ : b₁} (C : TwoCov φb₀ φb₁ τ₀ τ₁)

theorem TwoCov.mem_sec (d : ℕ) (x : C.E₀ × C.E₁) : x ∈ C.sec d ↔ C.ψ₀ x.1 = C.u ^ d * C.ψ₁ x.2 :=
  Iff.rfl

end Sec

section Hom

variable {B₀ B₁ N b₀ b₁ n : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing b₀] [CommRing b₁]
  [CommRing n] {φ₀ : B₀ →+* N} {φ₁ : B₁ →+* N} {t₀ : B₀} {t₁ : B₁} {φb₀ : b₀ →+* n} {φb₁ : b₁ →+* n} {τ₀ : b₀}
  {τ₁ : b₁} {π₀ : B₀ →+* b₀} {π₁ : B₁ →+* b₁} {π : N →+* n} {C' : TwoCov φ₀ φ₁ t₀ t₁}
  {C : TwoCov φb₀ φb₁ τ₀ τ₁} (H : TwoCovHom π₀ π₁ π C' C)

theorem TwoCovHom.u_map (hτ₀ : π₀ t₀ = τ₀) : H.ρ C'.u = C.u := by
  have e₁ : H.ρ (C'.ψ₀ (C'.a₀ t₀)) = C.ψ₀ (H.ρ₀ (C'.a₀ t₀)) := RingHom.congr_fun H.d₀ _
  have e₂ : H.ρ₀ (C'.a₀ t₀) = C.a₀ (π₀ t₀) := RingHom.congr_fun H.c₀ _
  change H.ρ (C'.ψ₀ (C'.a₀ t₀)) = C.ψ₀ (C.a₀ τ₀)
  rw [e₁, e₂, hτ₀]

end Hom

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovG2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions

For a two-chart cover `C` with ring maps `ιᵢ : R → Eᵢ` (agreeing on the overlap) and an ideal `I` of the overlap:
* **`TwoCov.Good C ι₀ I m y e`**: `E₀` is generated over `R[t]` by `m` modulo `ψ₀⁻¹ I`, and `ψ₀ mᵢ ≡ u^{eᵢ} ψ₁ yᵢ`
  modulo `I` (transition exponents `eᵢ`);
* **`TwoCov.h1_mod`**: then `H¹(O(d)) = 0` modulo `I` for `d ≥ max eᵢ`;
* **`TwoCov.good_zero`**: `Good` holds (any `I`, `I = ⊥` included) when `E₀` is finite over `R[t]`;
* **`TwoCovHom.good_lift`**: `Good` lifts along a transition with the SAME exponents (so `d` is uniform);
* **`TwoCovHom.hker_of_h1`**, **`TwoCovHom.secMap_surj_of_h1`**: `H¹ = 0` modulo `I'` and a kernel generated by
  `q` with `q · I' = 0` give the kernel hypothesis of `secMap_surj`: sections lift.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Good

variable {b₀ b₁ n : Type u} [CommRing b₀] [CommRing b₁] [CommRing n] {φb₀ : b₀ →+* n} {φb₁ : b₁ →+* n}
  {τ₀ : b₀} {τ₁ : b₁} (C : TwoCov φb₀ φb₁ τ₀ τ₁) {R : Type u} [CommRing R] (ι₀ : R →+* C.E₀) (I : Ideal C.E)

variable {C I} {d : ℕ}

theorem TwoCov.PI_congr {x x' : C.E₀} (hx : C.ψ₀ (x - x') ∈ I) (h' : C.PI I d x') : C.PI I d x := by
  have := TwoCov.PI_add (TwoCov.PI_of_mem (d := d) hx) h'
  rwa [sub_add_cancel] at this

theorem TwoCov.PI_zero : C.PI I d 0 :=
  TwoCov.PI_of_mem (by rw [map_zero]; exact I.zero_mem)

theorem TwoCov.PI_sum {r : ℕ} (f : Fin r → C.E₀) (h : ∀ i, C.PI I d (f i)) : C.PI I d (∑ i, f i) :=
  Finset.sum_induction f (C.PI I d) (fun _ _ => TwoCov.PI_add) TwoCov.PI_zero (fun i _ => h i)

end Good

section Zero

end Zero

section Lift

end Lift

section Ker

variable {B₀ B₁ N b₀ b₁ n : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing b₀] [CommRing b₁]
  [CommRing n] {φ₀ : B₀ →+* N} {φ₁ : B₁ →+* N} {t₀ : B₀} {t₁ : B₁} {φb₀ : b₀ →+* n} {φb₁ : b₁ →+* n} {τ₀ : b₀}
  {τ₁ : b₁} {π₀ : B₀ →+* b₀} {π₁ : B₁ →+* b₁} {π : N →+* n} {C' : TwoCov φ₀ φ₁ t₀ t₁}
  {C : TwoCov φb₀ φb₁ τ₀ τ₁} (H : TwoCovHom π₀ π₁ π C' C) {R : Type u} [CommRing R]
  (ι₀' : R →+* C'.E₀) (ι₁' : R →+* C'.E₁) (hι' : C'.ψ₀.comp ι₀' = C'.ψ₁.comp ι₁') (q : Ideal R)
  (hq₀ : ∀ α ∈ q, H.ρ₀ (ι₀' α) = 0) (hq₁ : ∀ α ∈ q, H.ρ₁ (ι₁' α) = 0)
  (hkρ : RingHom.ker H.ρ ≤ q.map (C'.ψ₀.comp ι₀')) (I' : Ideal C'.E)
  (hqI : ∀ α ∈ q, ∀ i ∈ I', C'.ψ₀ (ι₀' α) * i = 0) (d : ℕ)
  (h1 : ∀ z : C'.E, ∃ (x₀ : C'.E₀) (x₁ : C'.E₁), z - (C'.ψ₀ x₀ - C'.u ^ d * C'.ψ₁ x₁) ∈ I')

include hι' hq₀ hq₁ hkρ hqI h1

/-- **The kernel hypothesis of `secMap_surj`** from `H¹ = 0` modulo `I'` and `q · I' = 0`. -/
theorem TwoCovHom.hker_of_h1 :
    ∀ δ ∈ RingHom.ker H.ρ, ∃ k₀ ∈ RingHom.ker H.ρ₀, ∃ k₁ ∈ RingHom.ker H.ρ₁,
      δ = C'.ψ₀ k₀ - C'.u ^ d * C'.ψ₁ k₁ := by
  let Q : C'.E → Prop := fun δ => ∃ k₀ ∈ RingHom.ker H.ρ₀, ∃ k₁ ∈ RingHom.ker H.ρ₁,
    δ = C'.ψ₀ k₀ - C'.u ^ d * C'.ψ₁ k₁
  have hQadd : ∀ a b, Q a → Q b → Q (a + b) := by
    rintro a b ⟨k₀, hk₀, k₁, hk₁, rfl⟩ ⟨l₀, hl₀, l₁, hl₁, rfl⟩
    refine ⟨k₀ + l₀, Ideal.add_mem _ hk₀ hl₀, k₁ + l₁, Ideal.add_mem _ hk₁ hl₁, ?_⟩
    rw [map_add, map_add]
    ring
  have hmain : ∀ δ ∈ q.map (C'.ψ₀.comp ι₀'), ∀ c, Q (c * δ) := by
    intro δ hδ
    change δ ∈ Submodule.span C'.E _ at hδ
    induction hδ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨α, hα, rfl⟩ := hx
      intro c
      obtain ⟨x₀, x₁, hx⟩ := h1 c
      have e : C'.ψ₀ (ι₀' α) = C'.ψ₁ (ι₁' α) := RingHom.congr_fun hι' α
      refine ⟨ι₀' α * x₀, ?_, ι₁' α * x₁, ?_, ?_⟩
      · rw [RingHom.mem_ker, map_mul, hq₀ α hα, zero_mul]
      · rw [RingHom.mem_ker, map_mul, hq₁ α hα, zero_mul]
      · have h0 := hqI α hα _ hx
        rw [map_mul, map_mul, ← e]
        change c * C'.ψ₀ (ι₀' α) = _
        linear_combination h0
    | zero =>
      intro c
      exact ⟨0, Ideal.zero_mem _, 0, Ideal.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      intro c
      rw [mul_add]
      exact hQadd _ _ (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      rw [smul_eq_mul, ← mul_assoc]
      exact hx (c * a)
  intro δ hδ
  have := hmain δ (hkρ hδ) 1
  rwa [one_mul] at this

end Ker

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovG3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`

Charts `Bᵢ` with ring maps `ιBᵢ : R → Bᵢ` (agreeing in `N`) and `Jᵢ = p Bᵢ`, `JN = p N`:
* level maps **`lι₀`**, **`lι₁`** (`R → Eᵢ` at level `k`), **`lI`** (the ideal `p E`), `lι_compat`, `lhv`;
* along a transition: `lρι₀`, **`ker_ρ`** (`ker ρ = p^(k+1) E'`), `lq₀`, `lq₁`, `lqI` (`p^(k+1) · p E' = 0`), `lI_comap`;
* **`good_tower`**: generators with the same exponents at every level of `tower`;
* **`secMap_surj_tower`**: one `d₀` such that `secMap (towerHom k) d` is surjective for all `k` and `d ≥ d₀`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lv

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (p : Ideal R)

variable {k : ℕ} {C' : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ (k + 1)} {C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k}
  (H : TwoCovHom (down J₀ k) (down J₁ k) (down JN k) C' C)

theorem lρι₁ : H.ρ₁.comp (lι₁ ιB₁ C') = lι₁ ιB₁ C := by
  ext α
  have := RingHom.congr_fun H.c₁ (Ideal.Quotient.mk (J₁ ^ (k + 1 + 1)) (ιB₁ α))
  simpa only [lι₁, RingHom.comp_apply, Ideal.Quotient.factor_mk] using this

theorem ker_ρ (hJ₀ : J₀ = p.map ιB₀) :
    RingHom.ker H.ρ = (p ^ (k + 1)).map (C'.ψ₀.comp (lι₀ ιB₀ C')) := by
  subst hJ₀
  rw [H.k, H.k₀, Ideal.Quotient.factor_ker, Ideal.map_map, Ideal.map_map, ← Ideal.map_pow ιB₀ p (k + 1),
    Ideal.map_map]
  rfl

theorem lq₀ (hJ₀ : J₀ = p.map ιB₀) : ∀ α ∈ p ^ (k + 1), H.ρ₀ (lι₀ ιB₀ C' α) = 0 := by
  intro α hα
  have hm : ιB₀ α ∈ J₀ ^ (k + 1) := by
    rw [hJ₀, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hα
  have h0 : Ideal.Quotient.mk (J₀ ^ (k + 1)) (ιB₀ α) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
  rw [← RingHom.comp_apply, lρι₀ ιB₀ H]
  simp only [lι₀, RingHom.comp_apply]
  rw [h0, map_zero]

end Lv

section Tower

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFil2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1e): the `p`-adic filtration on sections of `O(d)` is the `p`-power filtration

* `FilProp`: every section of `O(d)` with entries in `p^(j+1)` is `∑ αᵢ yᵢ` with `yᵢ` sections with entries in `p^j`;
* `fil_step`: `FilProp` at one level `k` for `d ≥ d₀ + F` (from uniform `H¹` vanishing and uniform relations);
* **`fil_tower`**: one `d₂` with `FilProp` at every level of the tower and every `d ≥ d₂`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lv

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (p : Ideal R)

/-- Sections of `O(d)` with entries in `p^(j+1)` are `p`-combinations of sections with entries in `p^j`. -/
def FilProp {g : ℕ} (α : Fin g → R) {k : ℕ} (C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k) (d : ℕ) : Prop :=
  ∀ (j : ℕ) (x : C.E₀ × C.E₁), x ∈ C.sec d → x.1 ∈ (p ^ (j + 1)).map (lι₀ ιB₀ C) →
    x.2 ∈ (p ^ (j + 1)).map (lι₁ ιB₁ C) →
    ∃ y : Fin g → C.E₀ × C.E₁, (∀ i, y i ∈ C.sec d) ∧ (∀ i, (y i).1 ∈ (p ^ j).map (lι₀ ιB₀ C)) ∧
      (∀ i, (y i).2 ∈ (p ^ j).map (lι₁ ιB₁ C)) ∧
      x = ∑ i, (lι₀ ιB₀ C (α i) * (y i).1, lι₁ ιB₁ C (α i) * (y i).2)

end Lv

section Tower

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers

* `dep_choice`, `seq_choice`: sequences by choice along `ℕ`;
* `ker_ρ₀`, `ker_ρ₁`: the kernels of a transition are `p^(k+1)` on the charts; `mem_of_ρ₀`, `mem_of_ρ₁`: an element whose
  image has entries in `p^n` (`n ≤ k+1`) has entries in `p^n`;
* **`Gam C H d`**: compatible families of sections of `O(d)` along a tower `C`, `H`; **`exists_gam`**: every level-`0`
  section lifts when all transitions are surjective on sections.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Ker

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (p : Ideal R) {k : ℕ}
  {C' : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ (k + 1)} {C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k}
  (H : TwoCovHom (down J₀ k) (down J₁ k) (down JN k) C' C)

theorem ker_ρ₀ (hJ₀ : J₀ = p.map ιB₀) : RingHom.ker H.ρ₀ = (p ^ (k + 1)).map (lι₀ ιB₀ C') := by
  subst hJ₀
  rw [H.k₀, Ideal.Quotient.factor_ker, Ideal.map_map, ← Ideal.map_pow ιB₀ p (k + 1), Ideal.map_map]
  rfl

theorem ker_ρ₁ (hJ₁ : J₁ = p.map ιB₁) : RingHom.ker H.ρ₁ = (p ^ (k + 1)).map (lι₁ ιB₁ C') := by
  subst hJ₁
  rw [H.k₁, Ideal.Quotient.factor_ker, Ideal.map_map, ← Ideal.map_pow ιB₁ p (k + 1), Ideal.map_map]
  rfl

end Ker

section Fam

end Fam

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z1Two =====
section

/-!
# S4-EtPBC-A, (Z1): sections over the two charts of `P¹_A` form a finite `A`-module

Algebraic form of "`H⁰(P¹_A, 𝓕)` is finite over `A` for a coherent `𝓕`" (`A` noetherian), with `𝓕` given by
a finite `A[t]`-module `M₀`, a finite `A[s]`-module `M₁` (both written as `A[X]`-modules) and `A`-linear maps
`φ₀ : M₀ → N`, `φ₁ : M₁ → N` into the module over the overlap, where `X` acts on `N` as `t` and
`t • φ₁ (s • m) = φ₁ m`.

* `xTors M`: the `X`-power torsion; **`xTors_fg`**: it is finite over `A` for `M` finite over `A[X]`.
* `pow_smul_iter`, **`exists_refl`**: `X^D • φ₁ (c • w) = q • φ₁ w` with `deg q ≤ D` when `deg c ≤ D`.
* `twoChart φ₀ φ₁ := {(a, b) | φ₀ a = φ₁ b}` and **`twoChart_fg`**: it is finite over `A`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Z1

universe u v w w'

variable {A : Type u} [CommRing A]

/-- **The `X`-power torsion of a finite `A[X]`-module is finite over `A`** (`A` noetherian). -/
theorem xTors_fg [IsNoetherianRing A] (M : Type v) [AddCommGroup M] [Module A[X] M] [Module A M]
    [IsScalarTower A A[X] M] [Module.Finite A[X] M] : ((xTors (A := A) M).restrictScalars A).FG := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton M := Module.subsingleton A[X] M
    refine ⟨∅, le_antisymm (by simp) fun x _ => ?_⟩
    rw [Subsingleton.elim x 0]
    exact zero_mem _
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (xTors (A := A) M) : (xTors (A := A) M).FG)
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero G fun g hg => hG ▸ Submodule.subset_span hg
  have : Module.Finite A (degreeLT A k) := Module.Finite.equiv (degreeLTEquiv A k).symm
  let Φ : (G → degreeLT A k) →ₗ[A] M :=
    { toFun := fun c => ∑ g : G, (c g : A[X]) • (g : M)
      map_add' := fun c c' => by
        simp only [Pi.add_apply, Submodule.coe_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        simp only [Pi.smul_apply, Submodule.coe_smul, smul_assoc, RingHom.id_apply, Finset.smul_sum] }
  refine Submodule.FG.of_le (T := LinearMap.range Φ) ?_ ?_
  · rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · intro m hm
    have hm' : m ∈ Submodule.span A[X] (G : Set M) := hG ▸ hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.1 hm'
    refine LinearMap.mem_range.2 ⟨fun g => ⟨c g %ₘ X ^ k, mem_degreeLT.2 ?_⟩, ?_⟩
    · have h := degree_modByMonic_lt (c g) (monic_X_pow (R := A) k)
      rwa [degree_X_pow] at h
    · rw [← hc]
      refine Finset.sum_congr rfl fun g _ => ?_
      show (c g %ₘ X ^ k) • (g : M) = c g • (g : M)
      conv_rhs => rw [← modByMonic_add_div (c g) (X ^ k)]
      rw [add_smul, mul_comm, mul_smul, hk g g.2, smul_zero, add_zero]

section TwoChart

end TwoChart

end RamanujanPetersson.EtPBC.Z1

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim5 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2f): multiplication by `T₀`, `T₁` on compatible families; completed generation

* `mT₀`, `mT₁`: multiplication of a family by `T₀ = (1, s)` and `T₁ = (t, 1)`; `ρ₀_t`, `ρ₁_s`; `mT₀_mem`, `mT₁_mem`;
* **`gam_struct`**: finitely many `τⱼ ∈ Gam (e+1)` such that every `x ∈ Gam (e+2)` is
  `T₀ (∑ aⱼ τⱼ) + T₁ (∑ a'ⱼ τⱼ)` (`R` noetherian and `p`-precomplete, `H¹(O(e)) = 0` at level `0`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section T

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

theorem ρ₁_s (k : ℕ) : (H k).ρ₁ ((C (k + 1)).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1 + 1)) t₁)) =
    (C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁) := by
  have e := RingHom.congr_fun (H k).c₁ (Ideal.Quotient.mk (J₁ ^ (k + 1 + 1)) t₁)
  simp only [RingHom.comp_apply] at e
  rw [e]
  exact congrArg (C k).a₁ (Ideal.Quotient.factor_mk _ _)

end T

section Struct

end Struct

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts

* **`hE`** `⊆ L₀ × L₁` (fractions `x / T₁ᵃ T₀ᵇ`, `x ∈ Gam (a + b)`); **`hψ₀ : hE₀ →+* hE`**, **`hψ₁ : hE₁ →+* hE`**;
* `ρ₀_fB`, `ρ₁_fB`, **`famB_mem`**: `(fB₀ b₀, fB₁ b₁) ∈ Gam d` when `φ₀ b₀ = φ₀ t₀ ^ d * φ₁ b₁`;
* **`liftN₀ : N →+* L₀`**, **`liftN₁ : N →+* L₁`** (from `N = B₀[1/t₀] = B₁[1/t₁]`), `liftN₀_φ₀`, `liftN₁_φ₁`,
  `liftN₀_inv`, `liftN₁_inv`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Hat2

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

/-- **`N = B₁[1/t₁] → L₁`.** -/
def liftN₁ (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁)) : N →+* L₁ C :=
  letI := φ₁.toAlgebra
  haveI := isLocalization_of_isAwayMap φ₁ t₁ hφ₁ hu₁
  IsLocalization.Away.lift t₁ (g := (jL₁ C).comp (fB₁ C)) (IsLocalization.Away.algebraMap_isUnit (sFm C))

end Hat2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat4 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts

* **`frac₀ d x hx : hE₀`**, `frac₀_val`, `frac₀_spec`, `hE₀_ext`, **`eq_frac₀`**, `frac₀_congr`, **`frac₀_T₀`**,
  `frac₀_add`, `frac₀_mul`; chart 1: `frac₁`, `frac₁_spec`, `hE₁_ext`, `eq_frac₁`, `frac₁_congr`, `frac₁_T₁`, `frac₁_add`,
  `frac₁_mul`;
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Frac

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))
  (hts : φ₀ t₀ * φ₁ t₁ = 1)

variable {C H}

variable (C) in
theorem isUnit_jL₁ (d : ℕ) : IsUnit (jL₁ C (sFm C ^ d)) := by
  rw [map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit (sFm C)).pow d

end Frac

end RamanujanPetersson.EtPBC.Cov

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

/-- **`K[X] ↠ K[X₀,X₁]_(Xᵢ)`, `X ↦ Xⱼ/Xᵢ`.** -/
theorem away_surj_eval (i j : Fin 2) (hij : i ≠ j) :
    Function.Surjective (Polynomial.eval₂RingHom
      ((fromZeroRingHom (gr K) (Submonoid.powers (X i))).comp (algebraMap K (gr K 0)))
      (Away.isLocalizationElem (x_mem K i) (x_mem K j))) := by
  apply surj_eval₂_comp _ (algebraMap_zero_surj K)
  intro y
  have hy : y ∈ Algebra.adjoin (gr K 0) {Away.isLocalizationElem (x_mem K i) (x_mem K j)} := by
    rw [away_adjoin K i j hij]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hy
  refine ⟨p, ?_⟩
  rw [Polynomial.coe_eval₂RingHom, Polynomial.aeval_def]
  rfl

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_CovGl1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 2a): localization squares are pushouts

`isLoc_of_away`: an `IsAwayMap ψ t` with `ψ t` a unit is a localization away from `t`. `isLoc_tmap`: its base change
`R' ⊗ B → R' ⊗ C` is a localization away from `1 ⊗ t`. **`isPushout_loc`**: a map `ψ : E → E'` of algebras over
`R' ⊗ B` and `R' ⊗ C`, compatible on pure tensors and a localization away from `1 ⊗ t`, gives a pushout square.
-/

set_option autoImplicit false

open CategoryTheory Limits TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

variable {A B C R' E E' : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing R'] [CommRing E]
  [CommRing E'] [Algebra A B] [Algebra A C] [Algebra A R'] [Algebra (R' ⊗[A] B) E] [Algebra (R' ⊗[A] C) E']

/-- **The base change of a localization away from `t`** is a localization away from `1 ⊗ t`. -/
theorem isLoc_tmap (φ : B →ₐ[A] C) (t : B) (hφ : IsAwayMap φ.toRingHom t) (ht : IsUnit (φ t)) :
    @IsLocalization.Away (R' ⊗[A] B) _ ((1 : R') ⊗ₜ[A] t) (R' ⊗[A] C) _
      (Algebra.TensorProduct.map (AlgHom.id A R') φ).toRingHom.toAlgebra := by
  letI : Algebra B C := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  haveI : IsLocalization (Submonoid.powers t) C := isLoc_of_away φ.toRingHom t hφ ht
  letI : Algebra (R' ⊗[A] B) (R' ⊗[A] C) := (Algebra.TensorProduct.map (AlgHom.id A R') φ).toRingHom.toAlgebra
  haveI : IsScalarTower R' (R' ⊗[A] B) (R' ⊗[A] C) := IsScalarTower.of_algebraMap_eq (fun r => by
    show r ⊗ₜ[A] (1 : C) = Algebra.TensorProduct.map (AlgHom.id A R') φ (r ⊗ₜ 1)
    simp only [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply])
  have H := IsLocalization.tensorProduct_tensorProduct_right A R' (Submonoid.powers t) C (RingHom.ext fun b => by
    show Algebra.TensorProduct.map (AlgHom.id A R') φ (1 ⊗ₜ b) = (1 : R') ⊗ₜ[A] φ b
    simp only [Algebra.TensorProduct.map_tmul, map_one])
  rw [Submonoid.map_powers] at H
  exact H

end RamanujanPetersson.EtPBC.Cov

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

variable {L A B u}

variable (L A B u)

variable {L A B u}

theorem injAt_of_ses [IsCofiltered J] (hu : ∀ {j j' : J} (a : j' ⟶ j), u j' ≫ L.map (A.map a) = u j)
    {S : ShortComplex C} (hSE : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (hI : InjAt L A B u q S.X₃) (hS : SurjAt L A B u q S.X₂) : InjAt L A B u (q + 1) S.X₁ := by
  intro j α hα
  obtain ⟨η, hη⟩ := Ext.covariant_sequence_exact₁ (X := A.obj j) (hS := hSE) α
    (Ext.eq_zero_of_injective _) rfl
  have h1 : (bc L A B u j S.X₃ q η).comp (hSE.map_of_exact L).extClass rfl = 0 := by
    rw [← bc_comp_extClass L A B u j hSE q η, hη]
    exact hα
  obtain ⟨β, hβ⟩ := Ext.covariant_sequence_exact₃ (X := B) (hS := hSE.map_of_exact L) _ rfl h1
  obtain ⟨j₁, γ, hγ⟩ := hS β
  have h2 : bc L A B u (IsCofiltered.min j j₁) S.X₃ q
      (res A (IsCofiltered.minToLeft j j₁) S.X₃ q η -
        res A (IsCofiltered.minToRight j j₁) S.X₃ q (γ.comp (Ext.mk₀ S.g) (add_zero q))) = 0 := by
    rw [map_sub, bc_res hu, bc_res hu, bc_comp_mk₀, hγ, ← hβ]
    exact sub_self _
  obtain ⟨j₃, c, hc⟩ := hI _ _ h2
  rw [map_sub, sub_eq_zero] at hc
  refine ⟨j₃, c ≫ IsCofiltered.minToLeft j j₁, ?_⟩
  rw [res_comp, ← hη, res_comp_right, res_comp_right, hc, res_comp_right, res_comp_right,
    Ext.comp_assoc_of_second_deg_zero, hSE.comp_extClass, Ext.comp_zero]

end RamanujanPetersson.EtPBC.Delta

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

/-- The functions on `N × Spec C` that descend to `Spec A`. -/
def B : Subalgebra A (N → C) where
  carrier := {f | ∀ ν, j1 A C (f ν) = ∑ m, D.ε m * j2 A C (f (ν + m))}
  mul_mem' {f g} hf hg ν := by
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    simp only [Pi.mul_apply, map_mul, hf ν, hg ν, D.sum_mul_sum]
  one_mem' ν := by
    simp only [Pi.one_apply, map_one, mul_one, D.sum_eq]
  add_mem' {f g} hf hg ν := by
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    simp only [Pi.add_apply, map_add, hf ν, hg ν, mul_add, Finset.sum_add_distrib]
  zero_mem' ν := by
    simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]
  algebraMap_mem' a ν := by
    simp only [Pi.algebraMap_apply, AlgHom.commutes, ← Finset.sum_mul, D.sum_eq, one_mul]

/-- The inverse of `g ↦ lmul' ∘ g` on `ker delta'`. -/
def gOf (h : N → C) : N → C ⊗[A] C := fun ν => ∑ k, D.ε k * j1 A C (h (ν - k))

section Tensor

end Tensor

section FF

variable [Module.FaithfullyFlat A C]

/-- Evaluation at `0` (the sheet of the given trivialisation). -/
def ev0 : D.B →ₐ[A] C := (Pi.evalAlgHom A (fun _ : N => C) 0).comp D.B.val

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

theorem mem_B (D : Datum A C N) (f : N → C) :
    f ∈ D.B ↔ ∀ ν, j1 A C (f ν) = ∑ m, D.ε m * j2 A C (f (ν + m)) := Iff.rfl

/-- The kernel of `psiMap` is `r`-power torsion when `A'` and `C'` are the localizations away from `r`. -/
theorem psiMap_ker (ρA : A →+* A') (φC : C →+* C')
    (hφC : ∀ a, φC (algebraMap A C a) = algebraMap A' C' (ρA a)) (r : A)
    (hA : letI := ρA.toAlgebra; IsLocalization.Away r A')
    (hC : letI := φC.toAlgebra; IsLocalization.Away (algebraMap A C r) C')
    (x : C ⊗[A] C) (hx : psiMap ρA φC hφC x = 0) :
    ∃ n : ℕ, algebraMap A (C ⊗[A] C) (r ^ n) * x = 0 := by
  letI : Algebra A A' := ρA.toAlgebra
  letI : Algebra C C' := φC.toAlgebra
  haveI : IsLocalization.Away r A' := hA
  haveI : IsLocalization.Away (algebraMap A C r) C' := hC
  let Tr := Localization.Away (algebraMap A (C ⊗[A] C) r)
  let g0 : A →+* Tr := (algebraMap (C ⊗[A] C) Tr).comp (algebraMap A (C ⊗[A] C))
  have hu0 : IsUnit (g0 r) := IsLocalization.Away.algebraMap_isUnit (algebraMap A (C ⊗[A] C) r)
  let g1 : C →+* Tr := (algebraMap (C ⊗[A] C) Tr).comp (j1 A C).toRingHom
  let g2 : C →+* Tr := (algebraMap (C ⊗[A] C) Tr).comp (j2 A C).toRingHom
  have hg1 : ∀ a, g1 (algebraMap A C a) = g0 a := fun a => by
    show algebraMap (C ⊗[A] C) Tr (j1 A C (algebraMap A C a)) = _
    rw [AlgHom.commutes]
    rfl
  have hg2 : ∀ a, g2 (algebraMap A C a) = g0 a := fun a => by
    show algebraMap (C ⊗[A] C) Tr (j2 A C (algebraMap A C a)) = _
    rw [AlgHom.commutes]
    rfl
  have hu1 : IsUnit (g1 (algebraMap A C r)) := by rw [hg1]; exact hu0
  have hu2 : IsUnit (g2 (algebraMap A C r)) := by rw [hg2]; exact hu0
  let lam : A' →+* Tr := IsLocalization.Away.lift r hu0
  have hlam : ∀ a, lam (algebraMap A A' a) = g0 a := fun a => IsLocalization.Away.lift_eq (S := A') r hu0 a
  let l1 : C' →+* Tr := IsLocalization.Away.lift (algebraMap A C r) hu1
  let l2 : C' →+* Tr := IsLocalization.Away.lift (algebraMap A C r) hu2
  have hl1 : ∀ c, l1 (φC c) = g1 c := fun c => IsLocalization.Away.lift_eq (S := C') (algebraMap A C r) hu1 c
  have hl2 : ∀ c, l2 (φC c) = g2 c := fun c => IsLocalization.Away.lift_eq (S := C') (algebraMap A C r) hu2 c
  have hl : ∀ (l : C' →+* Tr) (g : C →+* Tr), (∀ c, l (φC c) = g c) →
      (∀ a, g (algebraMap A C a) = g0 a) → ∀ a', l (algebraMap A' C' a') = lam a' := by
    intro l g hlg hg a'
    have : (l.comp (algebraMap A' C')).comp (algebraMap A A') = lam.comp (algebraMap A A') := by
      ext a
      simp only [RingHom.comp_apply]
      rw [hlam]
      show l (algebraMap A' C' (ρA a)) = g0 a
      rw [← hφC, hlg, hg]
    exact RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers r) this) a'
  letI : Algebra A' Tr := lam.toAlgebra
  let L1 : C' →ₐ[A'] Tr := { toRingHom := l1, commutes' := hl l1 g1 hl1 hg1 }
  let L2 : C' →ₐ[A'] Tr := { toRingHom := l2, commutes' := hl l2 g2 hl2 hg2 }
  have key : ∀ y : C ⊗[A] C,
      Algebra.TensorProduct.productMap L1 L2 (psiMap ρA φC hφC y) = algebraMap (C ⊗[A] C) Tr y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      rw [psiMap_tmul, Algebra.TensorProduct.productMap_apply_tmul]
      show l1 (φC c) * l2 (φC d) = _
      rw [hl1, hl2]
      show algebraMap (C ⊗[A] C) Tr (j1 A C c) * algebraMap (C ⊗[A] C) Tr (j2 A C d) = _
      rw [← map_mul]
      congr 1
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add]
  have h0 : algebraMap (C ⊗[A] C) Tr x = 0 := by rw [← key, hx, map_zero]
  obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap A (C ⊗[A] C) r)) Tr x).mp h0
  exact ⟨n, by rw [map_pow]; exact hm⟩

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

variable {C : Type u} [CommRing C] [Algebra A C] [Algebra.Etale A C] {V : X.Etale}
  (τ : Spec (CommRingCat.of C) ⟶ V.left)
  (hτ : τ ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ σ)

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

theorem cval_comap {R R' : Type u} [CommRing R] [Algebra A R] [Algebra.Etale A R] [CommRing R']
    [Algebra A R'] [Algebra.Etale A R'] (φ : R →ₐ[A] R') (c : (constSh Λ X M).obj.obj (op (etS σ R)))
    (P : PrimeSpectrum R') :
    cval c (PrimeSpectrum.comap φ.toRingHom P) = cval (((constSh Λ X M).obj.map (homS σ φ).op).hom c) P :=
  (cval_map (homS σ φ) c P).symm

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

theorem cval_comapX {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} {R R' : Type u} [CommRing R] [Algebra A R]
    [Algebra.Etale A R] [CommRing R'] [Algebra A' R'] [Algebra.Etale A' R'] (φ : R →+* R')
    (hφ : ∀ x, φ (algebraMap A R x) = algebraMap A' R' (ρA x)) (c : (constSh Λ X M).obj.obj (op (etS σ R)))
    (P : PrimeSpectrum R') :
    cval c (PrimeSpectrum.comap φ P) = cval (((constSh Λ X M).obj.map (homX σ σ' ρA hσ φ hφ).op).hom c) P :=
  (cval_map (homX σ σ' ρA hσ φ hφ) c P).symm

variable {C C' : Type u} [CommRing C] [Algebra A C] [Algebra.Etale A C] [CommRing C'] [Algebra A' C']
  [Algebra.Etale A' C'] {V : X.Etale}
  (τ : Spec (CommRingCat.of C) ⟶ V.left) (hτ : τ ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ σ)
  (τ' : Spec (CommRingCat.of C') ⟶ V.left)
  (hτ' : τ' ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A' C')) ≫ σ')
  (φC : C →+* C') (hφC : ∀ x, φC (algebraMap A C x) = algebraMap A' C' (ρA x))
  (hτφ : Spec.map (CommRingCat.ofHom φC) ≫ τ = τ')

theorem psiMap_algebraMap (x : A) :
    psiMap ρA φC hφC (algebraMap A (C ⊗[A] C) x) = algebraMap A' (C' ⊗[A'] C') (ρA x) := by
  rw [Algebra.TensorProduct.algebraMap_apply, psiMap_tmul, hφC, map_one,
    Algebra.TensorProduct.algebraMap_apply]

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

/-- **Epi four-lemma, degree `0`.** -/
theorem surjAt_zero_of_ses [IsCofiltered J] (hu : ∀ {j j' : J} (a : j' ⟶ j), u j' ≫ L.map (A.map a) = u j)
    {S : ShortComplex C} (hSE : S.ShortExact)
    (hS : SurjAt L A B u 0 S.X₂) (hI : InjAt L A B u 0 S.X₃) : SurjAt L A B u 0 S.X₁ := by
  intro β
  obtain ⟨j, α₂, hα₂⟩ := hS (β.comp (Ext.mk₀ (L.map S.f)) (add_zero 0))
  obtain ⟨j', a, ha⟩ := hI j _ (bc_comp_f_g j 0 β α₂ hα₂)
  rw [res_comp_right] at ha
  obtain ⟨α₁, hα₁⟩ := Ext.covariant_sequence_exact₂ (X := A.obj j') hSE _ ha
  refine ⟨j', α₁, ?_⟩
  have hm : Mono (L.map S.f) := (hSE.map_of_exact L).mono_f
  apply Ext.postcomp_mk₀_injective_of_mono B (L.map S.f)
  change (bc L A B u j' S.X₁ 0 α₁).comp (Ext.mk₀ (L.map S.f)) (add_zero 0) = β.comp (Ext.mk₀ (L.map S.f)) (add_zero 0)
  rw [← bc_comp_mk₀, hα₁, bc_res hu, hα₂]

/-- **Epi four-lemma, degree `q + 1`.** -/
theorem surjAt_succ_of_ses [IsCofiltered J] (hu : ∀ {j j' : J} (a : j' ⟶ j), u j' ≫ L.map (A.map a) = u j)
    {S : ShortComplex C} (hSE : S.ShortExact) (q : ℕ)
    (hS : SurjAt L A B u (q + 1) S.X₂) (hI : InjAt L A B u (q + 1) S.X₃) (hS₃ : SurjAt L A B u q S.X₃) :
    SurjAt L A B u (q + 1) S.X₁ := by
  intro β
  obtain ⟨j, α₂, hα₂⟩ := hS (β.comp (Ext.mk₀ (L.map S.f)) (add_zero (q + 1)))
  obtain ⟨j', a, ha⟩ := hI j _ (bc_comp_f_g j (q + 1) β α₂ hα₂)
  rw [res_comp_right] at ha
  obtain ⟨α₁, hα₁⟩ := Ext.covariant_sequence_exact₂ (X := A.obj j') hSE _ ha
  have h1 : (bc L A B u j' S.X₁ (q + 1) α₁ - β).comp (Ext.mk₀ ((S.map L).f)) (add_zero (q + 1)) = 0 := by
    change (bc L A B u j' S.X₁ (q + 1) α₁ - β).comp (Ext.mk₀ (L.map S.f)) (add_zero (q + 1)) = 0
    rw [sub_eq_add_neg, Ext.add_comp, Ext.neg_comp, ← bc_comp_mk₀, hα₁, bc_res hu, hα₂, add_neg_cancel]
  obtain ⟨γ, hγ⟩ := Ext.covariant_sequence_exact₁ (X := B) (hSE.map_of_exact L) _ h1 rfl
  obtain ⟨j₂, η, hη⟩ := hS₃ γ
  refine ⟨IsCofiltered.min j' j₂, res A (IsCofiltered.minToLeft j' j₂) S.X₁ (q + 1) α₁ -
    (res A (IsCofiltered.minToRight j' j₂) S.X₃ q η).comp hSE.extClass rfl, ?_⟩
  rw [map_sub, bc_res hu, bc_comp_extClass, bc_res hu, hη]
  exact (congrArg (fun z => bc L A B u j' S.X₁ (q + 1) α₁ - z) hγ).trans (sub_sub_cancel _ _)

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

/-- A `U`-map from the lift `l` to `W` is an `X`-map from `x` to `W`. -/
def fibInc (l : Lifts e x) (W : U.Etale) (c : (liftPt e x l).point.fiber.obj W) :
    x.point.fiber.obj ((etComp e).obj W) :=
  (Over.homMk (fl (liftPt e x l) c) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ e) (fl_w (liftPt e x l) c)).trans l.2)) :
    Over.mk x.pt ⟶ (Scheme.Etale.forget X).obj ((etComp e).obj W))

variable {Λ : Type u} [CommRing Λ] (J : ModuleCat.{u} Λ)

/-- The projection of `res e (x_* J)` onto the skyscraper sheaf at a lift. -/
def pr (l : Lifts e x) :
    (res e Λ).obj (x.point.skyscraperSheaf J) ⟶ (liftPt e x l).point.skyscraperSheaf J :=
  ObjectProperty.homMk
    { app := fun W => sLift J (liftPt e x l).point (fun c => rπ e x J W (fibInc e x l W.unop c))
      naturality := fun W W' g => s_hom_ext J _ fun c => by
        simp only [Category.assoc, sLift_π, s_map_π, r_map_π]
        exact congrArg (rπ e x J W) (fl_ext x rfl) }

theorem pr_app_π (l : Lifts e x) (W : (U.Etale)ᵒᵖ) (c : (liftPt e x l).point.fiber.obj W.unop) :
    (pr e x J l).hom.app W ≫ sπ J (liftPt e x l).point W c = rπ e x J W (fibInc e x l W.unop c) :=
  sLift_π _ _ _ _

end RamanujanPetersson.EtSheaves.LshEt

end

end

-- ===== S4.Def_RP_EtPBC_A_T3dA =====
section

/-!
# S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension

* `sesPb`: pulling the injective presentation `0 → A → I → I/A → 0` back along `x : X ⟶ I/A`;
* **`exists_ses_extClass`**: every `β ∈ Ext¹(X, A)` is the class of a short exact `0 → A → E → X → 0`;
* **`exists_bc_of_ses_kill`**: for `f : P' ⟶ P` etale with a closed lift `ι'` of the fibre inclusion, `Φ : U ⟶ P'`
  finite and a mono `m : f^* G ⟶ Φ_* M_U`, the class of an extension `0 → ι^* G →a E → Λ → 0` on `P_s` is a germ
  as soon as `(ι^* G ⟶ ι'^* f^* G ⟶ ι'^* Φ_* M_U ≅ φs_* M_{U_s})` extends along `a`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.T3d

universe w v₁ u₁

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

section Pb

variable {A I Q X : C} (i : A ⟶ I) (p : I ⟶ Q) (x : X ⟶ Q)

variable [HasExt.{w} C]

theorem extClass_sesPb (hip : i ≫ p = 0) (h : (ShortComplex.mk i p hip).ShortExact) :
    (sesPb_shortExact i p x hip h).extClass = (Ext.mk₀ x).comp h.extClass (zero_add 1) := by
  have := (sesPb_shortExact i p x hip h).extClass_naturality h (sesPbMap i p x hip)
  exact (Ext.comp_mk₀_id _).symm.trans this

end Pb

end Abstract

section Geo

open AlgebraicGeometry RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.PushKill RamanujanPetersson.EtPBC.FBC

universe u

end Geo

end RamanujanPetersson.EtPBC.T3d

end

end

-- ===== S4.Def_RP_EtPBC_A_O2MV =====
section

/-!
# S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves

For a commutative square `p₁ ≫ w = p₂ ≫ v` of `P.Etale` (`W' ⟶ W, U ⟶ Z`):
* `freeMap_comp`; `stalk_freeMap_injective`/`_surjective` (fibre map injective/surjective ⇒ stalk map so);
* `mvC`: the short complex `Λ[W'] ⟶ Λ[W] ⊞ Λ[U] ⟶ Λ[Z]` (maps `(Λ[p₁], -Λ[p₂])`, `Λ[w] + Λ[v]`);
* **`mvC_shortExact`**: short exact when every fibre of `Z` is subsingleton and at every point either the fibre of
  `W` is a singleton and `p₂` is bijective on fibres, or the fibre of `U` is a singleton and `p₁` is so;
* **`mv_exists`**: a class `β ∈ Ext^{n+1}(Λ[Z], F)` killed by `Λ[w]` and `Λ[v]` is `ε.comp κ`, `κ ∈ Ext^n(Λ[W'], F)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg
  RamanujanPetersson.EtPBC.FreeStk

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

section Stalks

end Stalks

/-- **MV exactness**: a class of `Ext^{n₁}(Λ[Z], F)` killed by `Λ[w]` and `Λ[v]` comes from
`Ext^{n₀}(Λ[W'], F)` through the MV class. -/
theorem mv_exists {W' W U Z : P.Etale} {p₁ : W' ⟶ W} {p₂ : W' ⟶ U} {w : W ⟶ Z} {v : U ⟶ Z}
    {hsq : p₁ ≫ w = p₂ ≫ v} (hS : (mvC Λ p₁ p₂ w v hsq).ShortExact) (F : EtSh Λ P) {n₀ n₁ : ℕ}
    (h : 1 + n₀ = n₁) (β : Ext (freeSh Λ Z) F n₁)
    (hw : (Ext.mk₀ (freeMap Λ w)).comp β (zero_add n₁) = 0)
    (hv : (Ext.mk₀ (freeMap Λ v)).comp β (zero_add n₁) = 0) :
    ∃ κ : Ext (freeSh Λ W') F n₀, hS.extClass.comp κ h = β := by
  refine Ext.contravariant_sequence_exact₃ hS F β ?_ h
  change (Ext.mk₀ (biprod.desc (freeMap Λ w) (freeMap Λ v))).comp β (zero_add n₁) = 0
  rw [biprod.desc_eq, Ext.mk₀_add, Ext.add_comp, ← Ext.mk₀_comp_mk₀_assoc, ← Ext.mk₀_comp_mk₀_assoc, hw, hv,
    Ext.comp_zero, Ext.comp_zero, add_zero]

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L1 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes

* `mvMapHom`, **`mv_naturality`**: a morphism of MV data gives a morphism of MV complexes, so
  `ε₁ ∘ Λ[a'] = Λ[c] ∘ ε₂` in `Ext¹`.
* `mvPullHom`: `mvC(f⁻¹ data) ⟶ f^* mvC(data)` (an isomorphism), `mvPull_shortExact`;
  **`mapExact_mv`**: `f^*` of `ε.comp κ` is `ε(f⁻¹ data).comp (f^* κ)`.
* `freeToUnit_bcUnit`, **`bc_mv`**: the base change of `ε.comp κ` at a neighbourhood `j` of `s` is
  `σ_j^*(ε(ι⁻¹ data).comp (ι^* κ))`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe u

section Nat

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}
  {W'₁ W₁ U₁ Z₁ W'₂ W₂ U₂ Z₂ : P.Etale} {p₁ : W'₁ ⟶ W₁} {p₂ : W'₁ ⟶ U₁} {w : W₁ ⟶ Z₁} {v : U₁ ⟶ Z₁}
  {hsq : p₁ ≫ w = p₂ ≫ v} {q₁ : W'₂ ⟶ W₂} {q₂ : W'₂ ⟶ U₂} {x : W₂ ⟶ Z₂} {y : U₂ ⟶ Z₂} {hsq₂ : q₁ ≫ x = q₂ ≫ y}
  (a' : W'₁ ⟶ W'₂) (a : W₁ ⟶ W₂) (b : U₁ ⟶ U₂) (c : Z₁ ⟶ Z₂)
  (h₁ : a' ≫ q₁ = p₁ ≫ a) (h₂ : a' ≫ q₂ = p₂ ≫ b) (h₃ : a ≫ x = w ≫ c) (h₄ : b ≫ y = v ≫ c)

variable (Λ) in
/-- A morphism of MV data gives a morphism of MV complexes. -/
def mvMapHom : mvC Λ p₁ p₂ w v hsq ⟶ mvC Λ q₁ q₂ x y hsq₂ where
  τ₁ := freeMap Λ a'
  τ₂ := biprod.map (freeMap Λ a) (freeMap Λ b)
  τ₃ := freeMap Λ c
  comm₁₂ := by
    dsimp only [mvC]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc, ← freeMap_comp, h₁]
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc, Preadditive.comp_neg,
        Preadditive.neg_comp, ← freeMap_comp, h₂]
  comm₂₃ := by
    dsimp only [mvC]
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc, ← freeMap_comp, h₃]
    · simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc, ← freeMap_comp, h₄]

include a b h₁ h₂ h₃ h₄ in
/-- **Naturality of MV classes**: `ε₁ ∘ Λ[a'] = Λ[c] ∘ ε₂`. -/
theorem mv_naturality (hS₁ : (mvC Λ p₁ p₂ w v hsq).ShortExact) (hS₂ : (mvC Λ q₁ q₂ x y hsq₂).ShortExact) :
    hS₁.extClass.comp (Ext.mk₀ (freeMap Λ a')) (add_zero 1) = (Ext.mk₀ (freeMap Λ c)).comp hS₂.extClass (zero_add 1) :=
  hS₁.extClass_naturality hS₂ (mvMapHom Λ a' a b c h₁ h₂ h₃ h₄)

end Nat

section Pull

end Pull

section BC

end BC

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2M2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M2: local vanishing of cohomology classes

* `exists_local_lift`: a section of the target of an epimorphism lifts on an etale neighbourhood of any point of
  the geometric fibre;
* `vanish_one`, `vanish_succ`, **`local_vanish`**: every `β ∈ Ext^{q+1}(Λ[Z], F)` dies on an etale neighbourhood
  `a : N ⟶ Z` of any point `z` of the geometric fibre of `Z` over `x` (dimension shifting along the injective
  presentation `0 → F → I → I/F → 0`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

/-- **Local lifts along an epimorphism.** -/
theorem exists_local_lift {A B : EtSh Λ P} (π : A ⟶ B) [Epi π] (x : P) {Z : P.Etale}
    (z : (geomPtAt x).point.fiber.obj Z) (b : B.obj.obj (op Z)) :
    ∃ (N : P.Etale) (a : N ⟶ Z) (n : (geomPtAt x).point.fiber.obj N), (geomPtAt x).point.fiber.map a n = z ∧
      ∃ i : A.obj.obj (op N), (π.hom.app (op N)).hom i = (B.obj.map a.op).hom b := by
  have hep : Epi (((geomPtAt x).stalkF Λ).map π) := (epi_iff_stalk Λ π).1 inferInstance x
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).1 hep (germ B x z b)
  obtain ⟨V, c, p, rfl⟩ := (geomPtAt x).point.toPresheafFiber_jointly_surjective (P := A.obj) y
  have h2 : ((geomPtAt x).point.toPresheafFiber V c B.obj).hom ((π.hom.app (op V)).hom p) =
      ((geomPtAt x).point.toPresheafFiber Z z B.obj).hom b :=
    (germ_natural π x c p).symm.trans hy
  obtain ⟨U, f₁, f₀, u, hu, hf⟩ :=
    exists_common_rep' (geomPtAt x).point B.obj (j₁ := ⟨V, c⟩) (j₀ := ⟨Z, z⟩) _ _ h2
  refine ⟨U, f₀, u, hu, (A.obj.map f₁.op).hom p, ?_⟩
  exact (NatTrans.naturality_apply (φ := π.hom) f₁.op p).trans hf

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

end Opn

section Res

variable {W' W U Z : P.Etale} {p₁ : W' ⟶ W} {p₂ : W' ⟶ U} {w : W ⟶ Z} {v : U ⟶ Z} {hsq : p₁ ≫ w = p₂ ≫ v}

/-- **Classes restricted from `W` die** under the MV class. -/
theorem mv_res_W (hS : (mvC Λ p₁ p₂ w v hsq).ShortExact) {Y : EtSh Λ P} {n n' : ℕ}
    (γ : Ext.{u} (freeSh Λ W) Y n) (h : 1 + n = n') :
    hS.extClass.comp ((Ext.mk₀ (freeMap Λ p₁)).comp γ (zero_add n)) h = 0 := by
  have e : freeMap Λ p₁ = (mvC Λ p₁ p₂ w v hsq).f ≫ biprod.fst := (biprod.lift_fst _ _).symm
  calc hS.extClass.comp ((Ext.mk₀ (freeMap Λ p₁)).comp γ (zero_add n)) h
      = hS.extClass.comp ((Ext.mk₀ (mvC Λ p₁ p₂ w v hsq).f).comp ((Ext.mk₀ biprod.fst).comp γ (zero_add n))
          (zero_add n)) h := by rw [Ext.mk₀_comp_mk₀_assoc, ← e]
    _ = 0 := hS.extClass_comp_assoc _

/-- **Classes restricted from `U` die** under the MV class. -/
theorem mv_res_U (hS : (mvC Λ p₁ p₂ w v hsq).ShortExact) {Y : EtSh Λ P} {n n' : ℕ}
    (γ : Ext.{u} (freeSh Λ U) Y n) (h : 1 + n = n') :
    hS.extClass.comp ((Ext.mk₀ (freeMap Λ p₂)).comp γ (zero_add n)) h = 0 := by
  have e : freeMap Λ p₂ = (mvC Λ p₁ p₂ w v hsq).f ≫ (-biprod.snd) := by
    rw [Preadditive.comp_neg, biprod.lift_snd, neg_neg]
  calc hS.extClass.comp ((Ext.mk₀ (freeMap Λ p₂)).comp γ (zero_add n)) h
      = hS.extClass.comp ((Ext.mk₀ (mvC Λ p₁ p₂ w v hsq).f).comp ((Ext.mk₀ (-biprod.snd)).comp γ (zero_add n))
          (zero_add n)) h := by rw [Ext.mk₀_comp_mk₀_assoc, ← e]
    _ = 0 := hS.extClass_comp_assoc _

end Res

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E1 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4a: rings of finite type and unramified over a Dedekind domain

`A` Dedekind, `B` of finite type and formally unramified over `A` (e.g. etale).
* **`maximalIdeal_eq_map`**: at a prime `q` over a maximal `p`, `𝔪(B_q) = p B_q` (Mathlib's proof for finite `B`,
  with the Artinian fibre from `FormallyUnramified.finite_of_free`);
* **`isDedekindDomain_of_unramified`**: a domain `B` (with `A ↪ B`) is a Dedekind domain (incomparability from
  `Algebra.QuasiFinite.eq_of_le_of_under_eq` instead of integrality);
* **`isDomain_atPrime`**: if `B` is flat and `q` lies over `(π) ≠ 0`, then `B_q` is a domain (`𝔪 = (π)`, `π` regular,
  Krull intersection);
* **`exists_away_isDomain`**: if `B` is noetherian and `B_q` is a domain, some `B_g` (`g ∉ q`) is a domain;
* **`span_eq_of_unique`**: if `q` is the only maximal ideal containing `π`, then `π B = q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.EtPBC.EtDed

open IsLocalRing

section Max

end Max

section Ded

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [IsDedekindDomain A] [IsDomain B]
  [Algebra.FiniteType A B] [Algebra.FormallyUnramified A B]

/-- **A domain of finite type and unramified over a Dedekind domain (containing it) is Dedekind.** -/
theorem isDedekindDomain_of_unramified (hinj : Function.Injective (algebraMap A B)) : IsDedekindDomain B :=
  have : IsDedekindDomainDvr B :=
    { __ := Algebra.FiniteType.isNoetherianRing A B
      is_dvr_at_nonzero_prime := fun q hq _ => isDVR_of_ne_bot A B hinj q hq }
  inferInstance

end Ded

section Dom

end Dom

section Loc

end Loc

section Away

end Away

section Span

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.EssFiniteType A B]
  [Algebra.FormallyUnramified A B]

/-- **`π B = q`** when `q` (over the maximal ideal `(π)`) is the only maximal ideal containing `π`. -/
theorem span_eq_of_unique (q : Ideal B) [q.IsMaximal] (π : A) (hπ : q.under A = Ideal.span {π})
    (hp : (q.under A).IsMaximal) (huniq : ∀ n : Ideal B, n.IsMaximal → algebraMap A B π ∈ n → n = q) :
    Ideal.span {algebraMap A B π} = q := by
  have hπq : algebraMap A B π ∈ q := by
    have : π ∈ q.under A := by rw [hπ]; exact Ideal.mem_span_singleton_self π
    exact this
  refine le_antisymm ((Ideal.span_singleton_le_iff_mem q).2 hπq) (fun x hx => ?_)
  let I := Ideal.span {algebraMap A B π}
  let J : Ideal B := I.colon (Ideal.span {x})
  by_contra hxI
  have hJ : J ≠ ⊤ := by
    intro hJ
    apply hxI
    have h1 : (1 : B) ∈ J := hJ ▸ Submodule.mem_top
    have := Submodule.mem_colon.1 h1 x (Ideal.mem_span_singleton_self x)
    rwa [one_smul] at this
  obtain ⟨n, hn, hJn⟩ := Ideal.exists_le_maximal J hJ
  have hπJ : algebraMap A B π ∈ J := by
    refine Submodule.mem_colon.2 (fun y hy => ?_)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    rw [smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hnq : n = q := huniq n hn (hJn hπJ)
  have hm := maximalIdeal_eq_span A B q π hπ hp
  have hxm : algebraMap B (Localization.AtPrime q) x ∈ maximalIdeal (Localization.AtPrime q) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hx
  rw [hm, Ideal.mem_span_singleton'] at hxm
  obtain ⟨y, hy⟩ := hxm
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
  have hy' : IsLocalization.mk' (Localization.AtPrime q) (algebraMap A B π * c) s =
      algebraMap B (Localization.AtPrime q) x := by
    rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm]
    exact hy
  rw [IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, IsLocalization.eq_iff_exists q.primeCompl] at hy'
  obtain ⟨s', hs'⟩ := hy'
  have hJ' : (s' : B) * s ∈ J := by
    refine Submodule.mem_colon.2 (fun z hz => ?_)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [smul_eq_mul, show (s' : B) * s * (b * x) = b * ((s' : B) * (x * s)) by ring, ← hs']
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
  have h1 := hJn hJ'
  rw [hnq] at h1
  exact (q.primeCompl.mul_mem s'.2 s.2) h1

end Span

end RamanujanPetersson.EtPBC.EtDed


end

-- ===== S4.Def_RP_EtPBC_A_O2KapP =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map

For `f : X₁ ⟶ X` etale between affine schemes whose rings are finite products of Dedekind domains, and a Kummer
class `kapS p (kumD α)` on the piece `p` of `X` (`α^d = u`):
* `kerMap f p₁ : Γ(X) → Γ(X₁) ⧸ p₁`, `exists_minimalPrime_le_ker`, `kerLift`, **`piHom_comp_eq`**
  (the piece `p₁` of `X₁` maps into the piece `q` of `X` through `Spec (Γ(X₁) ⧸ p₁) ⟶ Spec (Γ(X) ⧸ q)`),
  `injective_of_etale` (an etale map of domains is injective), `resLE_congr`, `resLE_kapS_self`, `resLE_kapS_ne`;
* **`resLE_kapS_kumD_eq_zero`**: if `u` becomes a `d`-th power in the fraction field of every piece of `X₁` lying
  over `p`, then `resLE f 1 (kapS p (kumD α)) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

universe u

section Fac

variable {X X₁ : Scheme.{0}} [IsAffine X] [IsAffine X₁] [IsNoetherianRing Γ(X, ⊤)] [IsNoetherianRing Γ(X₁, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (h₁ : ∀ (m : Ideal Γ(X₁, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (f : X₁ ⟶ X)

variable {f} in
/-- `Γ(X) ⧸ q → Γ(X₁) ⧸ p₁` for `q ≤ ker`. -/
def kerLift {p₁ : minimalPrimes Γ(X₁, ⊤)} {q : minimalPrimes Γ(X, ⊤)}
    (hq : (q : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁)) :
    Γ(X, ⊤) ⧸ (q : Ideal Γ(X, ⊤)) →+* Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)) :=
  Ideal.Quotient.lift (q : Ideal Γ(X, ⊤)) (kerMap f p₁) fun a ha => RingHom.mem_ker.1 (hq ha)

end Fac

section KappaRes

end KappaRes

section Red

end Red

section KapP

end KapP

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PPTc =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTc): transfer of a piece Kummer class along a shrink `D₁ ⟶ D`

GLOB/REL PLAN v1 (5). For a shrink `dm : D₁ ⟶ D` of local-class neighbourhoods of `z` (both with one geometric
point over `z`), with Shapiro isomorphisms `θ` over `opEt Uo`:
* **`locCls_kapS_shrink`**: `ε(D) ∘ θ⁻¹(kapS p (kumD α)) = ε(D₁) ∘ θ₁⁻¹(Σ_{p₁} kapS p₁ (χ₁ p₁))`, where
  `χ₁ p₁ = kumD (γ p₁)` on the pieces of `W₁` over `p` and `0` on the others (`γ p₁ ^ d = u` there).
Proof: `locCls_shrink`, `theta_natural` along `prdMap dm`, `resLE_kapS_kumD_sum` (O2PPTb) along `wm (prdMap dm)`.
* **`piece_eq_of_away`**: under a localization `A → A[1/s]` two minimal primes over the same prime agree (Zariski
  shrinks never split pieces); **`ker_kerMap`**: `ker (kerMap f p₁) = comap f p₁`;
* **`sum_kapS_eq_single`** / **`sum_kapS_eq_zero`**: collapsing `Σ kapS Q (χ Q)` when at most one `χ Q ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Away

end Away

section KerMap

variable {X X₁ : Scheme.{0}} (f : X₁ ⟶ X)

theorem ker_kerMap (p₁ : minimalPrimes Γ(X₁, ⊤)) :
    RingHom.ker (kerMap f p₁) = Ideal.comap f.appTop.hom (p₁ : Ideal Γ(X₁, ⊤)) := by
  unfold kerMap
  rw [← RingHom.comap_ker, Ideal.mk_ker]

end KerMap

section Single

end Single

section PPTc

end PPTc

end RamanujanPetersson.EtPBC.EtKum

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

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {J : Type u₃} [Category.{v₃} J]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (A : J ⥤ C) (B : D) (u : ∀ j, B ⟶ L.obj (A.obj j))

/-- The germ image of `bc` in degree `q`, an additive subgroup for cofiltered `J`. -/
def bcImg [IsCofiltered J] (hu : ∀ {j j' : J} (a : j' ⟶ j), u j' ≫ L.map (A.map a) = u j) (F : C) (q : ℕ) :
    AddSubgroup (Ext B (L.obj F) q) where
  carrier := {β | ∃ (j : J) (α : Ext (A.obj j) F q), bc L A B u j F q α = β}
  zero_mem' := by
    obtain ⟨j⟩ : Nonempty J := IsCofiltered.nonempty
    exact ⟨j, 0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨j₁, α₁, rfl⟩ ⟨j₂, α₂, rfl⟩
    refine ⟨IsCofiltered.min j₁ j₂, res A (IsCofiltered.minToLeft j₁ j₂) F q α₁ +
      res A (IsCofiltered.minToRight j₁ j₂) F q α₂, ?_⟩
    rw [map_add, bc_res hu, bc_res hu]
  neg_mem' := by
    rintro _ ⟨j, α, rfl⟩
    exact ⟨j, -α, map_neg _ _⟩

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact

universe u

section L7a

end L7a

end RamanujanPetersson.EtPBC.EtMV

end

end


