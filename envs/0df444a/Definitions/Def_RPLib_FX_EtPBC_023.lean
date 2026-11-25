-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_023
-- name    : RPLib_FX_EtPBC_023
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:13:54.605181+00:00
-- url     : https://prove2.me/theorems/89341c3f-893c-5364-891d-d07ab3ea1a26
-- title:
--   Proper base change for the projective line, library file 023
-- statement:
--   File 023 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovPr11`: S4-EtPBC-A, R4-T2 (A3k): the residue map of an approximated presentation
--   * `S4.Def_RP_EtPBC_A_LocFlat`: S4-EtPBC-A, R4-T2 (A2c-5, E3b1): the local criterion for flatness (finite modules over a local ring)
--   * `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
--   * `S4.Def_RP_EtPBC_A_Z3Y`: S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_Z4Glue`: S4-EtPBC-A, (Z) geometric layer 9 (G-e, part 1): gluing the two charts of `Y`
--   * `S4.Def_RP_EtPBC_A_Z4Base`: S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_Z4FibA`: S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`
--   * `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
--   * `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_CovFbB`: S4-EtPBC-A, R4-T2 (G1d, part 2): the lifts agree on the overlap
--   * `S4.Def_RP_EtPBC_A_CovFbC`: S4-EtPBC-A, R4-T2 (G1d, part 3): the chart identity and the pullback square of the fibre cover
--   * `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
--   * `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
--   * `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
--   * `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
--   * `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
--   * `S4.Def_RP_EtPBC_A_CovNbA`: S4-EtPBC-A, R4-T2 (G2a): `kapV` is an isomorphism; the fibre inclusion of a neighbourhood is closed
--   * `S4.Def_RP_EtPBC_A_O2Km4`: S4-EtPBC-A, O2 M6 (O2Km4): `H¹` of an affine scheme whose ring is a product of Dedekind domains
--   * `S4.Def_RP_EtPBC_A_O2Gl1b`: S4-EtPBC-A, O2 GLOB (O2Gl1b): the algebra of stages S1-S2
--   * `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
--   * `S4.Def_RP_EtPBC_A_O2N4`: S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)
--   * `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
--   * `S4.Def_RP_EtPBC_A_O2E3`: S4-EtPBC-A, O2 C-plan S4c1 (scheme level): affine Dedekind presentations of one-point classes
--   * `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
--   * `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
--   * `S4.Def_RP_EtPBC_A_O2Gl1c`: S4-EtPBC-A, O2 GLOB (O2Gl1c): the geometric inputs of stages S1-S2
--   * `S4.Def_RP_EtPBC_A_O2Gl2e`: S4-EtPBC-A, O2 GLOB (O2Gl2e): stage S4, the values of `H` on the pieces of `W₂`
--   * `S4.Def_RP_EtPBC_A_O2Gl3c`: S4-EtPBC-A, O2 GLOB (O2Gl3c): a piece of `W₁` survives in `W₂ = W₁[1/φ₁ c₀']`
--   * `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
--   * `S4.Def_RP_EtPBC_A_O2Rel7`: S4-EtPBC-A, O2 REL (O2Rel7): the relation at `c(a)` lies in the localized subgroup
--   * `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
--   * `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
--   * `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
--   * `S4.Def_RP_EtPBC_A_O2L5a`: S4-EtPBC-A, L5a (Geo1): the horizontal section through a closed point of `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
--   * `S4.Def_RP_EtPBC_A_O2Gen1`: S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`
--   * `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
--   * `S4.Def_RP_EtPBC_A_CovFix`: S4-EtPBC-A, R4-T2 (G'): the geometric half of T2 from the corrected statement `CoverLiftAt₂`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_015
import Definitions.Def_RPLib_FX_EtPBC_018

/-!
# Proper base change for the projective line, library file 023

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovPr11`: S4-EtPBC-A, R4-T2 (A3k): the residue map of an approximated presentation
* `S4.Def_RP_EtPBC_A_LocFlat`: S4-EtPBC-A, R4-T2 (A2c-5, E3b1): the local criterion for flatness (finite modules over a local ring)
* `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
* `S4.Def_RP_EtPBC_A_Z3Y`: S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_Z4Glue`: S4-EtPBC-A, (Z) geometric layer 9 (G-e, part 1): gluing the two charts of `Y`
* `S4.Def_RP_EtPBC_A_Z4Base`: S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_Z4FibA`: S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`
* `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
* `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_CovFbB`: S4-EtPBC-A, R4-T2 (G1d, part 2): the lifts agree on the overlap
* `S4.Def_RP_EtPBC_A_CovFbC`: S4-EtPBC-A, R4-T2 (G1d, part 3): the chart identity and the pullback square of the fibre cover
* `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
* `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
* `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
* `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
* `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
* `S4.Def_RP_EtPBC_A_CovNbA`: S4-EtPBC-A, R4-T2 (G2a): `kapV` is an isomorphism; the fibre inclusion of a neighbourhood is closed
* `S4.Def_RP_EtPBC_A_O2Km4`: S4-EtPBC-A, O2 M6 (O2Km4): `H¹` of an affine scheme whose ring is a product of Dedekind domains
* `S4.Def_RP_EtPBC_A_O2Gl1b`: S4-EtPBC-A, O2 GLOB (O2Gl1b): the algebra of stages S1-S2
* `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
* `S4.Def_RP_EtPBC_A_O2N4`: S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)
* `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
* `S4.Def_RP_EtPBC_A_O2E3`: S4-EtPBC-A, O2 C-plan S4c1 (scheme level): affine Dedekind presentations of one-point classes
* `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
* `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
* `S4.Def_RP_EtPBC_A_O2Gl1c`: S4-EtPBC-A, O2 GLOB (O2Gl1c): the geometric inputs of stages S1-S2
* `S4.Def_RP_EtPBC_A_O2Gl2e`: S4-EtPBC-A, O2 GLOB (O2Gl2e): stage S4, the values of `H` on the pieces of `W₂`
* `S4.Def_RP_EtPBC_A_O2Gl3c`: S4-EtPBC-A, O2 GLOB (O2Gl3c): a piece of `W₁` survives in `W₂ = W₁[1/φ₁ c₀']`
* `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
* `S4.Def_RP_EtPBC_A_O2Rel7`: S4-EtPBC-A, O2 REL (O2Rel7): the relation at `c(a)` lies in the localized subgroup
* `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
* `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
* `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
* `S4.Def_RP_EtPBC_A_O2L5a`: S4-EtPBC-A, L5a (Geo1): the horizontal section through a closed point of `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
* `S4.Def_RP_EtPBC_A_O2Gen1`: S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`
* `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
* `S4.Def_RP_EtPBC_A_CovFix`: S4-EtPBC-A, R4-T2 (G'): the geometric half of T2 from the corrected statement `CoverLiftAt₂`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovPr11 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3k): the residue map of an approximated presentation

Setting: a square system `gC` over `Cc`, pushed to `S` (the completed side, `fh`) and to `S'` (the approximated
side, `f'`); `θh : Pres (gmap fh gC) → Q` a ring map (in the application surjective, kernel `p · Pres`).
* `pres_eval_self`: a ring map out of `Pres g` evaluates polynomials through its values on constants and variables.
* **`resid fh f' gC θh κ' hκ : Pres (gmap f' gC) →+* Q`**: coefficients by `κ'`, variables to `θh (Z j)`; it exists
  as soon as `κ' ∘ f' = θh ∘ algebraMap ∘ fh` (`resid_hz`). `resid_algebraMap`, `resid_X`, `resid_comp_presMap`.
* **`resid_surj`**: surjective if `θh` is and `κ'` reaches the constants of `θh`.
* **`resid_ker`** (headline): `ker (resid ..) = J · Pres (gmap f' gC)` from a map `q` out of `Pres (gmap f' gC)` with
  kernel in `J · Pres`, a coefficient map `lam : S → T` killing `I` (`ker θh = I · Pres (gmap fh gC)`) and sections.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Gen

end Gen

variable {Cc S S' : Type u} [CommRing Cc] [CommRing S] [CommRing S'] {r : ℕ} {Q : Type u} [CommRing Q]

/-- The residue map of the approximated presentation. -/
def resid (fh : Cc →+* S) (f' : Cc →+* S') (gC : Fin r → MvPolynomial (Fin r) Cc) (θh : Pres (gmap fh gC) →+* Q)
    (κ' : S' →+* Q) (hκ : κ'.comp f' = (θh.comp (algebraMap S (Pres (gmap fh gC)))).comp fh) :
    Pres (gmap f' gC) →+* Q :=
  presLift (gmap f' gC) κ' (fun i => θh (Ideal.Quotient.mk _ (MvPolynomial.X i))) (resid_hz fh f' gC θh κ' hκ)

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_LocFlat =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E3b1): the local criterion for flatness (finite modules over a local ring)

For a local ring `(A, 𝔪)` and a finite `A`-module `M`:
* `lf_li_flat`: over a local ring, a family in a flat module whose combinations with a coefficient outside `𝔪`
  never lie in `𝔪 • M` is linearly independent (Mathlib's `linearIndependent_of_flat`, residue field form removed);
* `lf_coef_mem`: if `M ⧸ I M` is flat over `A ⧸ I` (`I ≠ ⊤`), a relation `∑ gᵢ vᵢ = 0` among lifts of a residue
  basis has all `gᵢ ∈ I`;
* **`free_of_quot_flat'`**: `M ⧸ Iₖ M` flat over `A ⧸ Iₖ` for a family `Iₖ ≠ ⊤` with `⋂ Iₖ = 0` ⇒ `M` free;
* **`free_of_quot_flat`** (`A` noetherian, `J ≠ ⊤`): `M ⧸ J^(k+1) M` flat over `A ⧸ J^(k+1)` for all `k` ⇒ `M` free.
-/

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing

namespace RamanujanPetersson.EtPBC.Cov

universe u

section LocFlat

variable {A M : Type u} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]

/-- A relation among lifts of a residue basis has coefficients in `I` when `M ⧸ I M` is flat over `A ⧸ I`. -/
theorem lf_coef_mem (I : Ideal A) (hI : I ≠ ⊤) (hfl : Module.Flat (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M)))
    {ι : Type*} (v : ι → M)
    (h0 : ∀ (s : Finset ι) (c : ι → A), ∑ i ∈ s, c i • v i ∈ (maximalIdeal A) • (⊤ : Submodule A M) →
      ∀ i ∈ s, c i ∈ maximalIdeal A)
    (s : Finset ι) (g : ι → A) (hg : ∑ i ∈ s, g i • v i = 0) : ∀ i ∈ s, g i ∈ I := by
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (A ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI := hfl
  have e : ∀ (t : Finset ι) (c : ι → A), ∑ j ∈ t, Ideal.Quotient.mk I (c j) •
      (Submodule.Quotient.mk (v j) : M ⧸ (I • ⊤ : Submodule A M))
      = (I • ⊤ : Submodule A M).mkQ (∑ j ∈ t, c j • v j) := by
    intro t c
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => rfl
  have hle : (I • ⊤ : Submodule A M) ≤ (maximalIdeal A) • (⊤ : Submodule A M) :=
    Submodule.smul_mono_left (le_maximalIdeal hI)
  have key : ∀ x : M, (I • ⊤ : Submodule A M).mkQ x ∈
      (maximalIdeal (A ⧸ I)) • (⊤ : Submodule (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))) →
      x ∈ (maximalIdeal A) • (⊤ : Submodule A M) := by
    intro x hx
    have h1 : (I • ⊤ : Submodule A M).mkQ x ∈
        ((maximalIdeal A) • (⊤ : Submodule A M)).map (I • ⊤ : Submodule A M).mkQ := by
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr n _
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ n
        have ha : a ∈ maximalIdeal A := by
          rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
          exact fun hu => hr (hu.map _)
        exact ⟨a • m, Submodule.smul_mem_smul ha Submodule.mem_top, rfl⟩
      · intro y z hy hz
        exact add_mem hy hz
    obtain ⟨y, hy, hyx⟩ := h1
    have hd : x - y ∈ (I • ⊤ : Submodule A M) := by
      rw [← Submodule.Quotient.eq]
      exact hyx.symm
    simpa using add_mem (hle hd) hy
  have hli : LinearIndependent (A ⧸ I)
      (fun j => (Submodule.Quotient.mk (v j) : M ⧸ (I • ⊤ : Submodule A M))) := by
    refine lf_li_flat _ fun t c hc j hj => ?_
    choose c' hc' using fun j => Ideal.Quotient.mk_surjective (c j)
    have hc3 : (I • ⊤ : Submodule A M).mkQ (∑ j ∈ t, c' j • v j) ∈
        (maximalIdeal (A ⧸ I)) • (⊤ : Submodule (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))) := by
      rw [← e t c']
      simp only [hc']
      exact hc
    have hm := h0 t c' (key _ hc3) j hj
    rw [← hc' j, mem_maximalIdeal, mem_nonunits_iff]
    rw [mem_maximalIdeal, mem_nonunits_iff] at hm
    exact fun hu => hm ((isUnit_map_iff (Ideal.Quotient.mk I) _).mp hu)
  intro i hi
  have hz := linearIndependent_iff'.mp hli s (fun j => Ideal.Quotient.mk I (g j)) (by
    show ∑ j ∈ s, Ideal.Quotient.mk I (g j) • (Submodule.Quotient.mk (v j) : M ⧸ (I • ⊤ : Submodule A M)) = 0
    rw [e s g, hg, map_zero]) i hi
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end LocFlat

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs4b =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap

* `exists_presN`: if `E` is presented as `Pres g` over `P`, `f : P → P'` is a localization away from `t` with `f t` a
  unit, and `q : E → E'` is a localization away from `t` compatible with `bN : P' → E'`, then `E' ≅ Pres (gmap f g)`
  (via `presN`, bijective by `away_bij`).
* `exists_subst`: a `P`-isomorphism `Pres g ≅ Pres g'` is `presIso` of substitution data `u v` (with all four
  membership witnesses).
* `chart_pres`: a finite etale `b : P → E` is presented by a square system with etale and finite witnesses.
* **`two_chart_pres`**: the two charts `E₀, E₁` of a cover glued along `E`, their base changes to the overlap and
  substitution data between the two overlap presentations, all in one package.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section PresN

variable {P P' E' : Type u} [CommRing P] [CommRing P'] [CommRing E'] {r : ℕ}
  (f : P →+* P') (g : Fin r → MvPolynomial (Fin r) P) (bN : P' →+* E') (θ : Pres g →+* E')

theorem presN_presMap (hθ : θ.comp (algebraMap P (Pres g)) = bN.comp f) (x : Pres g) :
    presN f g bN θ hθ (presMap f g x) = θ x := by
  have h : (presN f g bN θ hθ).comp (presMap f g) = θ := by
    apply pres_ringHom_ext
    · intro a
      rw [RingHom.comp_apply, presMap_algebraMap, presN_algebraMap]
      exact (DFunLike.congr_fun hθ a).symm
    · intro j
      rw [RingHom.comp_apply, presMap_X]
      exact presLift_X _ _ _ _ j
  exact DFunLike.congr_fun h x

end PresN

section Subst

end Subst

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

theorem isAffineOpen_Yc [IsAffine V] [IsAffineHom π] (i : Fin 2) : IsAffineOpen (Yc K gV π i) :=
  (isAffineOpen_Qc K gV i).preimage π

end RamanujanPetersson.EtPBC.Z3

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

/-- Restriction `Γ(Y₁) → Γ(Y₀₁)`. -/
abbrev resY1 : Γ(Y, Yc K gV π 1) ⟶ Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) :=
  Y.presheaf.map (homOfLE inf_le_right : Yc K gV π 0 ⊓ Yc K gV π 1 ⟶ Yc K gV π 1).op

/-- The structure map `Γ(V) → Γ(Y₀₁)`. -/
abbrev strN : Γ(V, ⊤) ⟶ Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) :=
  (π ≫ qV K gV).appLE ⊤ (Yc K gV π 0 ⊓ Yc K gV π 1) (le_top.trans (Scheme.Hom.preimage_top _).ge)

/-- `Γ(V)[X]`-structure on `Γ(Y₀)` (via `t`). -/
@[instance_reducible]
def algX0 : Algebra (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) := (σY K gV π 0 1).toAlgebra

/-- `Γ(V)[X]`-structure on `Γ(Y₁)` (via `s`). -/
@[instance_reducible]
def algX1 : Algebra (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) := (σY K gV π 1 0).toAlgebra

/-- `Γ(V)[X]`-structure on `Γ(Y₀₁)` (via `t`). -/
@[instance_reducible]
def algXN : Algebra (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) :=
  ((resY0 K gV π).hom.comp (σY K gV π 0 1)).toAlgebra

/-- `Γ(V)`-structure on `Γ(Y₀)`. -/
@[instance_reducible]
def algA0 : Algebra Γ(V, ⊤) Γ(Y, Yc K gV π 0) := (ac K gV 0 ≫ π.app (Qc K gV 0)).hom.toAlgebra

/-- `Γ(V)`-structure on `Γ(Y₁)`. -/
@[instance_reducible]
def algA1 : Algebra Γ(V, ⊤) Γ(Y, Yc K gV π 1) := (ac K gV 1 ≫ π.app (Qc K gV 1)).hom.toAlgebra

attribute [local instance] algX0 algX1 algXN algA0 algA1

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4Glue =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 9 (G-e, part 1): gluing the two charts of `Y`

* `chU_sup`: `D₊(X₀) ⊔ D₊(X₁) = ⊤`; `Yc_sup`: `Y₀ ⊔ Y₁ = ⊤`.
* `struct_res`: the structure map `Γ(V) → Γ(Y, ⊤)` restricts to the chart structures; `map_map`.
* **`glueRing : secAlg φY0 φY1 →+* Γ(Y, ⊤)`** (sheaf gluing), `glueRing_res0`, `glueRing_res1`, `eq_of_res`,
  `glueRing_struct`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace HomogeneousLocalization
open RamanujanPetersson.EtCompact
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K]

variable {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}} (π : Y ⟶ PV K gV)

attribute [local instance] algX0 algX1 algXN algA0 algA1

/-- Two global sections of `Y` agreeing on both charts are equal. -/
theorem eq_of_res (s t : Γ(Y, ⊤))
    (h₀ : Y.presheaf.map (homOfLE le_top : Yc K gV π 0 ⟶ ⊤).op s =
      Y.presheaf.map (homOfLE le_top : Yc K gV π 0 ⟶ ⊤).op t)
    (h₁ : Y.presheaf.map (homOfLE le_top : Yc K gV π 1 ⟶ ⊤).op s =
      Y.presheaf.map (homOfLE le_top : Yc K gV π 1 ⟶ ⊤).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq₂ Y.sheaf (homOfLE le_top) (homOfLE le_top) (Yc_sup K gV π).ge s t h₀ h₁

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4Base =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`

* `isoSpec_inv_appTop'`, `eq_Spec_map` (a morphism `Spec R ⟶ V`, `V` affine, is `Spec` of its ring map).
* `pushout_inl_surj`, `pushout_inl_ker`: in a pushout of commutative rings along a surjection `g : A ↠ C`, the map
  `inl : B → P` is surjective with kernel `(ker g) B`.
* `hV V R' : Spec R' ⟶ V`, `hV_appTop`; `YV K gV π R' = Y ×_V Spec R'` with its `Γ(V)`-algebra structure `algYV`;
  `fR : R' →ₐ Γ(Y_{V'}, ⊤)`, `gS : secAlg →ₐ Γ(Y_{V'}, ⊤)`, **`PhiY = lift fR gS`**; `isClopen_PhiY`: for an
  idempotent `e'` of `R' ⊗ secAlg`, `D(PhiY e')` is clopen.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

section Base

attribute [local instance] algX0 algX1 algXN algA0 algA1

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

/-- The `Γ(V)`-algebra structure of `Γ(Y_{V'}, ⊤)`. -/
@[instance_reducible]
def algYV : Algebra Γ(V, ⊤) Γ(YV K gV π R', ⊤) := (strV K gV π R').hom.toAlgebra

attribute [local instance] algYV

/-- `R' → Γ(Y_{V'}, ⊤)` (second projection). -/
def fR : R' →ₐ[Γ(V, ⊤)] Γ(YV K gV π R', ⊤) where
  toRingHom := (pullback.snd (π ≫ qV K gV) (hV V R')).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
  commutes' a := by
    change _ = (strV K gV π R').hom a
    rw [strV, pullback.condition, Scheme.Hom.comp_appTop, hV_appTop]
    rfl

end Base

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4FibA =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`

For `x : Spec K ⟶ V` with `x ≫ gV = 𝟙` (so `Γ(V) → Γ(Spec K)` is surjective):
* `Yx = Y ×_V Spec K`, `fx`, `sx`; for an open `U ⊆ Y`: `TU = Y_x ×_Y U`, `jT` (open immersion onto `fx⁻¹ U`), `kT`,
  `isPullback_T`, `isPushout_T` (`U` affine).
* **`fx_app_surj`**: `Γ(Y, U) → Γ(Y_x, fx⁻¹ U)` is surjective, **`ker_fx_app`**: its kernel is `(ker x^*) Γ(Y, U)`
  (`U` affine).
* `strU`, `strU_ρ`, `appTop_surj`, `isAffineOpen_Y01`, `Yx_sup`, `eq_of_res_x` (separation on the two charts of `Y_x`),
  `fx_res`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

section Fib

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

variable (x : Spec (CommRingCat.of K) ⟶ V)

theorem Yx_sup : fx K gV π x ⁻¹ᵁ Yc K gV π 0 ⊔ fx K gV π x ⁻¹ᵁ Yc K gV π 1 = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, Yc_sup]
  rfl

/-- Two global sections of `Y_x` agreeing on both charts are equal. -/
theorem eq_of_res_x (s t : Γ(Yx K gV π x, ⊤))
    (h₀ : (Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ Yc K gV π 0 ⟶ ⊤).op s =
      (Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ Yc K gV π 0 ⟶ ⊤).op t)
    (h₁ : (Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ Yc K gV π 1 ⟶ ⊤).op s =
      (Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ Yc K gV π 1 ⟶ ⊤).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq₂ (Yx K gV π x).sheaf (homOfLE le_top) (homOfLE le_top) (Yx_sup K gV π x).ge s t h₀ h₁

variable (U : Y.Opens)

theorem top_le_jT : (⊤ : (TU K gV π x U).Opens) ≤ jT K gV π x U ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ U) := by
  have h := (Scheme.Hom.preimage_image_eq (jT K gV π x U) ⊤).ge
  rwa [image_jT] at h

theorem isPushout_T [IsAffine V] (hU : IsAffineOpen U) :
    IsPushout (U.ι ≫ π ≫ qV K gV).appTop x.appTop (kT K gV π x U).appTop
      (jT K gV π x U ≫ sx K gV π x).appTop :=
  haveI : IsAffine U.toScheme := hU
  isPushout_appTop_of_isPullback (isPullback_T K gV π x U)

theorem jT_fx : (fx K gV π x).app U ≫ (jT K gV π x U).appLE (fx K gV π x ⁻¹ᵁ U) ⊤ (top_le_jT K gV π x U) =
    U.ι.appLE U ⊤ U.ι_preimage_self.ge ≫ (kT K gV π x U).appTop := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_eq (pullback.condition (f := fx K gV π x) (g := U.ι)),
    ← appLE_top_top (kT K gV π x U) (Scheme.Hom.preimage_top _).ge, Scheme.Hom.appLE_comp_appLE]

end Fib

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4FibB =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`

* `ψx K x : Γ(V) → K`, `px K x = ker ψx` (prime), `ker_appTop_eq`, `κx : κ(p) → K`, `κx_algebraMap`.
* For `P` over `p` with `κ(p) ≅ κ(P)` (`hbij`): `χx : R' → K`, `χx_algebraMap`, **`hxχ`**:
  `Spec χx ≫ hV V R' = x`, `xχ_appTop`.
* **`yxMap K gV π R' x x' hx' : Y_x ⟶ Y ×_V Spec R'`**, `yxMap_fR`, `yxMap_gS`, `yxMap_PhiY_tmul`.
* `exists_fibreRing`: a ring map `κ(p) ⊗ Γ(Y, U) → Γ(Y_x, fx⁻¹ U)`, `c ⊗ b ↦ c · fx^* b`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

section Res

variable (K : Type u) [Field K] {V : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ V)

/-- `κ(p) → K`. -/
def κx : (px K x).ResidueField →+* K :=
  Ideal.ResidueField.lift (px K x) (ψx K x) le_rfl (κx_unit K x)

theorem κx_algebraMap (a : Γ(V, ⊤)) : κx K x (algebraMap Γ(V, ⊤) (px K x).ResidueField a) = ψx K x a := by
  rw [κx, Ideal.ResidueField.lift_algebraMap]

variable {R' : Type u} [CommRing R'] [Algebra Γ(V, ⊤) R'] (P : Ideal R') [P.IsPrime] [P.LiesOver (px K x)]
  (hbij : Function.Bijective (Ideal.ResidueField.mapₐ (px K x) P (Algebra.ofId _ _) (P.over_def (px K x))))

/-- `χ : R' → κ(P) ≅ κ(p) → K`. -/
def χx : R' →+* K :=
  (κx K x).comp ((AlgEquiv.ofBijective _ hbij).symm.toAlgHom.toRingHom.comp (algebraMap R' P.ResidueField))

theorem χx_apply (r : R') :
    χx K x P hbij r = κx K x ((AlgEquiv.ofBijective _ hbij).symm (algebraMap R' P.ResidueField r)) := rfl

theorem χx_algebraMap (a : Γ(V, ⊤)) : χx K x P hbij (algebraMap Γ(V, ⊤) R' a) = ψx K x a := by
  rw [χx_apply, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, κx_algebraMap]

/-- **`Spec χ` lifts `x`** along `Spec R' ⟶ V`. -/
theorem hxχ [IsAffine V] : Spec.map (CommRingCat.ofHom (χx K x P hbij)) ≫ hV V R' = x := by
  have hc : CommRingCat.ofHom (algebraMap Γ(V, ⊤) R') ≫ CommRingCat.ofHom (χx K x P hbij) =
      x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    ext a
    exact χx_algebraMap K x P hbij a
  rw [hV, ← Category.assoc, ← Spec.map_comp, hc, ← eq_Spec_map]

theorem xχ_appTop (r : R') :
    (Spec.map (CommRingCat.ofHom (χx K x P hbij))).appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv (χx K x P hbij r) :=
  (congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (χx K x P hbij)))).symm

end Res

section Map

attribute [local instance] algX0 algX1 algXN algA0 algA1 algYV

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']
  (x : Spec (CommRingCat.of K) ⟶ V) (x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))
  (hx' : x' ≫ hV V R' = x)

omit [IsAffine V] in
/-- A ring map `κ(p) ⊗_{Γ(V)} Γ(Y, U) → Γ(Y_x, fx⁻¹ U)`, `c ⊗ b ↦ c · fx^* b`. -/
theorem exists_fibreRing (U : Y.Opens) [Algebra Γ(V, ⊤) Γ(Y, U)]
    (halg : algebraMap Γ(V, ⊤) Γ(Y, U) = (strU K gV π U).hom) :
    ∃ j : (px K x).ResidueField ⊗[Γ(V, ⊤)] Γ(Y, U) →+* Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ U),
      ∀ c b, j (c ⊗ₜ b) = (Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ U ⟶ ⊤).op
        ((sx K gV π x).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (κx K x c))) *
          (fx K gV π x).app U b := by
  let _ : Algebra Γ(V, ⊤) Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ U) :=
    (((fx K gV π x).app U).hom.comp (algebraMap Γ(V, ⊤) Γ(Y, U))).toAlgebra
  let jB : Γ(Y, U) →ₐ[Γ(V, ⊤)] Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ U) :=
    { toRingHom := ((fx K gV π x).app U).hom
      commutes' := fun _ => rfl }
  let jK : (px K x).ResidueField →ₐ[Γ(V, ⊤)] Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ U) :=
    { toRingHom := ((Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ U ⟶ ⊤).op).hom.comp
        ((sx K gV π x).appTop.hom.comp ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp (κx K x)))
      commutes' := fun a => by
        change ((Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ U ⟶ ⊤).op).hom
          ((sx K gV π x).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
            (κx K x (algebraMap Γ(V, ⊤) (px K x).ResidueField a)))) =
            ((fx K gV π x).app U).hom (algebraMap Γ(V, ⊤) Γ(Y, U) a)
        rw [κx_algebraMap, halg]
        have h1 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (ψx K x a) = x.appTop.hom a := by
          change (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫
            (Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom a = _
          rw [Iso.hom_inv_id, Category.comp_id]
        have h2 := congrArg (fun φ => φ.appTop.hom a) (pullback.condition (f := π ≫ qV K gV) (g := x))
        simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h2
        rw [h1, ← h2]
        exact (fx_res K gV π x U _).symm }
  exact ⟨(Algebra.TensorProduct.lift jK jB (fun _ _ => Commute.all _ _)).toRingHom,
    fun c b => Algebra.TensorProduct.lift_tmul _ _ _ c b⟩

end Map

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_CovCh =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`

For `V` affine, `π : Y ⟶ P¹_V` finite, a `K`-point `x` of `V` and a finite etale `q : T ⟶ Y_x`, the charts
`Γ(Y_x, fx⁻¹ Yᵢ)` and `Γ(T, q⁻¹ fx⁻¹ Yᵢ)` satisfy every hypothesis of `CoverLiftAt`. **`nonempty_liftD`**: under
`CoverLiftAt K Γ(V) χ` (`χ` the point `x`), the lift data `LiftD` (= `CoverLift` at these charts) exist.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) (x : Spec (CommRingCat.of K) ⟶ V)

attribute [local instance] algKY

theorem beta_alg (U : Y.Opens) (a : Γ(V, ⊤)) :
    ((fx K gV π x).app U).hom ((strU K gV π U).hom a) =
      algebraMap K Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ U) (ψx K x a) := by
  have h1 := fx_res K gV π x U ((π ≫ qV K gV).appTop.hom a)
  have h2 := congrArg (fun f => f.appTop.hom a) (pullback.condition (f := π ≫ qV K gV) (g := x))
  simp only [Scheme.Hom.comp_appTop] at h2
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (x.appTop.hom a)) = x.appTop.hom a :=
    congrArg (fun φ => CommRingCat.Hom.hom φ (x.appTop.hom a)) (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of K)))
  change ((fx K gV π x).app U).hom ((Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom
    ((π ≫ qV K gV).appTop.hom a)) = ((Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ U ⟶ ⊤).op).hom
      ((sx K gV π x).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (x.appTop.hom a))))
  rw [h1, h3]
  exact congrArg _ h2

theorem isAffineOpen_Wx [IsAffine V] (U : Y.Opens) (hU : IsAffineOpen U) : IsAffineOpen (fx K gV π x ⁻¹ᵁ U) := by
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine (TU K gV π x U) := IsAffine.of_isIso (isPullback_T K gV π x U).isoPullback.hom
  rw [← image_jT]
  exact (isAffineOpen_top _).image_of_isOpenImmersion _

section Cover

variable {T : Scheme.{u}} (q : T ⟶ Yx K gV π x)

attribute [local instance] algT

theorem hψT0 : (ψT0 K gV π x q).comp (algebraMap _ _) =
    (algebraMap Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1)) _).comp (ρx0 K gV π x) := by
  ext b
  exact (congrArg (fun φ => CommRingCat.Hom.hom φ b) (Scheme.Hom.naturality q
    (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left) :
      fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1) ⟶ fx K gV π x ⁻¹ᵁ Yc K gV π 0).op)).symm

theorem hψT1 : (ψT1 K gV π x q).comp (algebraMap _ _) =
    (algebraMap Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1)) _).comp (ρx1 K gV π x) := by
  ext b
  exact (congrArg (fun φ => CommRingCat.Hom.hom φ b) (Scheme.Hom.naturality q
    (homOfLE (Scheme.Hom.preimage_mono _ inf_le_right) :
      fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1) ⟶ fx K gV π x ⁻¹ᵁ Yc K gV π 1).op)).symm

end Cover

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovY =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`

For an affine open `U ⊆ Y` (with `Γ(V) → Γ(Y, U)` the structure map), **`chY hU hA`** `: Spec (R' ⊗ Γ(Y, U)) ⟶ Y_{V'}`
is the base change of `hU.fromSpec` along `Y_{V'} ⟶ Y` (**`isPullback_chY`**), an open immersion with range
`fst⁻¹ U` (**`opensRange_chY`**), compatible with restrictions (**`chY_res`**).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

section Chart

end Chart

section Res

end Res

theorem oV_sup : oV K gV π R' (Yc K gV π 0) ⊔ oV K gV π R' (Yc K gV π 1) = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, Yc_sup, Scheme.Hom.preimage_top]

theorem oV_inf : oV K gV π R' (Yc K gV π 0) ⊓ oV K gV π R' (Yc K gV π 1) =
    oV K gV π R' (Yc K gV π 0 ⊓ Yc K gV π 1) := by
  rw [← Scheme.Hom.preimage_inf]

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFbB =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d, part 2): the lifts agree on the overlap

`eq_of_away`: ring maps out of a localization agreeing on the image are equal. **`gW_glue`**: for chart surjections
`θ₀ : E₀ ↠ G₀`, `θ₁ : E₁ ↠ G₁` compatible with localizations `ψᵢ : Eᵢ → E₀₁`, `pᵢ : Gᵢ → G₀₁` through some
`θ₀₁ : E₀₁ → G₀₁` (not assumed surjective), the two lifts of `w ≫ Spec ψᵢ` factor through one `c : W ⟶ Spec G₀₁`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

/-- **The lifts on the overlap factor through `Spec G₀₁`.** -/
theorem gW_glue {E₀ E₁ E₀₁ G₀ G₁ G₀₁ : Type u} [CommRing E₀] [CommRing E₁] [CommRing E₀₁] [CommRing G₀]
    [CommRing G₁] [CommRing G₀₁] (θ₀ : E₀ →+* G₀) (sθ₀ : Function.Surjective θ₀) (θ₁ : E₁ →+* G₁)
    (sθ₁ : Function.Surjective θ₁) (θ₀₁ : E₀₁ →+* G₀₁) (ψ₀ : E₀ →+* E₀₁) (ψ₁ : E₁ →+* E₀₁) (p₀ : G₀ →+* G₀₁)
    (p₁ : G₁ →+* G₀₁) (cθ₀ : p₀.comp θ₀ = θ₀₁.comp ψ₀) (cθ₁ : p₁.comp θ₁ = θ₀₁.comp ψ₁) (t : E₀)
    (aw : IsAwayMap ψ₀ t) (hu : IsUnit (ψ₀ t)) (awp : IsAwayMap p₀ (θ₀ t)) {W : Scheme.{u}}
    (w : W ⟶ Spec (CommRingCat.of E₀₁))
    (hk₀ : RingHom.ker θ₀ ≤ RingHom.ker (εW (w ≫ Spec.map (CommRingCat.ofHom ψ₀))))
    (hk₁ : RingHom.ker θ₁ ≤ RingHom.ker (εW (w ≫ Spec.map (CommRingCat.ofHom ψ₁)))) :
    ∃ c : W ⟶ Spec (CommRingCat.of G₀₁), gW θ₀ sθ₀ _ hk₀ = c ≫ Spec.map (CommRingCat.ofHom p₀) ∧
      gW θ₁ sθ₁ _ hk₁ = c ≫ Spec.map (CommRingCat.ofHom p₁) := by
  have hpu : IsUnit (p₀ (θ₀ t)) := by
    rw [← RingHom.comp_apply p₀ θ₀, cθ₀, RingHom.comp_apply]
    exact hu.map θ₀₁
  letI := p₀.toAlgebra
  haveI := isLoc_of_away p₀ (θ₀ t) awp hpu
  have hlu : IsUnit (liftW θ₀ sθ₀ _ hk₀ (θ₀ t)) := by
    rw [liftW_θ, εW_SpecMap, RingHom.comp_apply]
    exact hu.map _
  let c' : G₀₁ →+* Γ(W, ⊤) := IsLocalization.Away.lift (θ₀ t) hlu
  have hc0 : c'.comp p₀ = liftW θ₀ sθ₀ _ hk₀ := IsLocalization.Away.lift_comp (θ₀ t) hlu
  have hcθ : c'.comp θ₀₁ = εW w := by
    refine eq_of_away ψ₀ t aw _ _ ((hu.map θ₀₁).map c') ?_
    ext e
    show c' (θ₀₁ (ψ₀ e)) = εW w (ψ₀ e)
    rw [← RingHom.comp_apply θ₀₁ ψ₀, ← cθ₀, RingHom.comp_apply, ← RingHom.comp_apply c' p₀, hc0, liftW_θ,
      εW_SpecMap, RingHom.comp_apply]
  refine ⟨W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c'), ?_, ?_⟩
  · rw [Category.assoc, ← Spec.map_comp, gW]
    refine congrArg (W.toSpecΓ ≫ ·) (congrArg Spec.map ?_)
    ext g
    exact (RingHom.congr_fun hc0 g).symm
  · rw [Category.assoc, ← Spec.map_comp, gW]
    refine congrArg (W.toSpecΓ ≫ ·) (congrArg Spec.map ?_)
    ext g
    obtain ⟨e, rfl⟩ := sθ₁ g
    show liftW θ₁ sθ₁ _ hk₁ (θ₁ e) = c' (p₁ (θ₁ e))
    rw [liftW_θ, εW_SpecMap, RingHom.comp_apply, ← RingHom.comp_apply p₁ θ₁, cθ₁, RingHom.comp_apply,
      ← RingHom.comp_apply c' θ₀₁, hcθ]

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFbC =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d, part 3): the chart identity and the pullback square of the fibre cover

* `hxL_of`: a ring map `χ' : R' → K` over `x` gives a lift `Spec χ'` of `x`.
* **`fromSpec_yx`**: for a chart `U` of `Y` and `θ : E → Γ(T, q⁻¹ fx⁻¹ U)` as in `CoverLift`,
  `T_U ⟶ T ⟶ Y_x ⟶ Y_{V'}` equals `Spec θ ≫ Spec (alg) ≫ chY`.
* `mono_yxMap`: `Y_x ⟶ Y_{V'}` is a monomorphism.
* `pb_key`: the square of a chart of the pulled back gluing cover.
* `gW_congr`: `gW` only depends on `w`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) (x : Spec (CommRingCat.of K) ⟶ V) [IsAffine V]

variable {R' : Type u} [CommRing R'] [Algebra Γ(V, ⊤) R'] (χ' : R' →+* K)
  (hxL : Spec.map (CommRingCat.ofHom χ') ≫ hV V R' = x)

/-- **`Y_x ⟶ Y_{V'}` is a monomorphism.** -/
theorem mono_yxMap (hx : x ≫ gV = 𝟙 _) : Mono (yxMap K gV π R' x _ hxL) := by
  have : IsSplitMono x := IsSplitMono.mk' ⟨gV, hx⟩
  have h : yxMap K gV π R' x _ hxL ≫ pullback.fst _ _ = fx K gV π x := pullback.lift_fst _ _ _
  exact mono_of_mono_fac h

section Chart

attribute [local instance] algKY algT

end Chart

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFib =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover

For lift data `L : LiftD K gV π x q hx` of a fibre cover `q : T ⟶ Y_x`: the glued cover `dL L` of `Y_{V'}`
(`V' = Spec L.R'`), the lift `xL L` of `x`, and **`ψL L : U_x ⟶ T`** on `U_x = (dL L).glued ×_{Y_{V'}} Y_x`, glued
from the chart lifts `gW` (`g0`, `g1`; `overlap` on `Y₀₁`), with **`ψL_q`**: `ψL L ≫ q = pullback.snd`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algKY algT CoverLift.cR CoverLift.aR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁

universe u

variable {K : Type u} [Field K] {V : Scheme.{u}} {gV : V ⟶ Spec (CommRingCat.of K)} {Y : Scheme.{u}} {π : Y ⟶ PV K gV} {x : Spec (CommRingCat.of K) ⟶ V} [IsAffine V] [IsFinite π] {hx : x ≫ gV = 𝟙 _} {T : Scheme.{u}} {q : T ⟶ Yx K gV π x} [IsAffineHom q]

theorem hW0 : IsAffineOpen (fx K gV π x ⁻¹ᵁ Yc K gV π 0) :=
  isAffineOpen_Wx K gV π x _ (isAffineOpen_Yc K gV π 0)

theorem hW1 : IsAffineOpen (fx K gV π x ⁻¹ᵁ Yc K gV π 1) :=
  isAffineOpen_Wx K gV π x _ (isAffineOpen_Yc K gV π 1)

theorem hT0 : IsAffineOpen (q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 0)) := (hW0 (K := K) (gV := gV) (π := π) (x := x)).preimage q

theorem hT1 : IsAffineOpen (q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 1)) := (hW1 (K := K) (gV := gV) (π := π) (x := x)).preimage q

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_NbExt1 =====
section

/-!
# S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods

Plain-morphism version: a neighbourhood is given by `hj : V ⟶ S` and `v : Spec Ω ⟶ V` with `v ≫ hj = s.pt`.
* `pMapV : V ×_S P ≅ P¹_V`, `piVV : Y_V ⟶ P¹_V` (finite), `xV = (s ≫ g_K)⁻¹ ≫ v : Spec K ⟶ V`;
* `fibV : P_s ⟶ V ×_S P`, `ysV : Y_s ⟶ Y_V` (definitionally `ysj` for a `Nbhd`);
* `eYV : Y_s ⟶ Y_x` and `eY'V : Y_x ⟶ Y_s` with **`eYV_eY'V`** (`eYV ≫ eY'V = 𝟙`);
* for an etale `Γ(V)`-algebra `R'` and a lift `x'` of `xV`: `kapV : Y_{V'} ⟶ Y ×_V Spec R'` with
  **`ysV_kapV`**: `ysV' ≫ kapV = eYV ≫ yxMap`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S)
  {Y : Scheme.{u}} (π : Y ⟶ PV K gK) {V : Scheme.{u}} (hj : V ⟶ S)

@[reassoc]
theorem piVV_q : piVV K gK π hj ≫ qV K (hj ≫ gK) =
    pullback.fst (pullback.snd hj (qV K gK)) π ≫ pullback.fst hj (qV K gK) := by
  unfold piVV
  rw [Category.assoc, pMapV_q]

variable [IsIso (s.pt ≫ gK)] (v : Spec (CommRingCat.of s.Ω) ⟶ V)

theorem fibW_cond (hv : v ≫ hj = s.pt) :
    (fx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ≫ pullback.fst (pullback.snd hj (qV K gK)) π ≫
      pullback.snd hj (qV K gK)) ≫ qV K gK =
    (sx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ≫ inv (s.pt ≫ gK)) ≫ s.pt := by
  have h1 : fx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ≫ pullback.fst (pullback.snd hj (qV K gK)) π ≫
      pullback.fst hj (qV K gK) = sx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ≫ inv (s.pt ≫ gK) ≫ v := by
    exact (congrArg (fun t => fx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ≫ t)
      (piVV_q K gK π hj)).symm.trans pullback.condition
  simp only [Category.assoc]
  rw [← pullback.condition (f := hj) (g := qV K gK), reassoc_of% h1, hv]

/-- `Y_x ⟶ P_s`. -/
def fibW (hv : v ≫ hj = s.pt) : Yx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ⟶ fib (qV K gK) s :=
  pullback.lift (fx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ≫ pullback.fst _ π ≫ pullback.snd hj (qV K gK))
    (sx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ≫ inv (s.pt ≫ gK)) (fibW_cond K gK s π hj v hv)

section Ext

variable [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

/-- `Y_{V'} ⟶ Y_V ×_V Spec R'`. -/
def kapV : pullback (pullback.snd (hV V R' ≫ hj) (qV K gK)) π ⟶ YV K (hj ≫ gK) (piVV K gK π hj) R' :=
  pullback.lift (ymapR K gK π hj R') (pullback.fst _ π ≫ pullback.fst _ (qV K gK))
    (by simp only [piVV_q, ymapR, pmapR, pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc])

end Ext

end RamanujanPetersson.EtPBC

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

theorem surj_comap [Surjective V.hom] (U : X.AffineZariskiSite) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(X, U.1) (CU V U))) := by
  intro p
  have hx : U.2.fromSpec p ∈ U.1 := by
    have h : U.2.fromSpec p ∈ Set.range U.2.fromSpec := ⟨p, rfl⟩
    rwa [IsAffineOpen.range_fromSpec] at h
  obtain ⟨v, hv⟩ := V.hom.surjective (U.2.fromSpec p)
  have hvU : v ∈ Set.range (U.2.preimage V.hom).fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    show V.hom v ∈ U.1
    rw [hv]
    exact hx
  obtain ⟨q, rfl⟩ := hvU
  refine ⟨q, U.2.fromSpec.isOpenEmbedding.injective ?_⟩
  have h := congrArg (fun g : Spec (CommRingCat.of (CU V U)) ⟶ X => g q) (htauU V U)
  simp only at h
  exact h.symm.trans hv

end Cover

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

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] (U : X.AffineZariskiSite)

@[reassoc]
theorem kL_j1 {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ V.left) (h : g₁ ≫ vh V = g₂ ≫ vh V)
    (hg₁ : ∀ z, vh V (g₁ z) ∈ U.1) (hg₂ : ∀ z, vh V (g₂ z) ∈ U.1) :
    kL V U g₁ g₂ h hg₁ hg₂ ≫ Spec.map (CommRingCat.ofHom (j1 Γ(X, U.1) (CU V U)).toRingHom) =
      liftU V U g₁ hg₁ := by
  have : CommRingCat.ofHom (j1 Γ(X, U.1) (CU V U)).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        CU V U →+* CU V U ⊗[Γ(X, U.1)] CU V U) := rfl
  rw [this, kL, Category.assoc, pullbackSpecIso_hom_fst, pullback.lift_fst]

end Pt

section Cover

end Cover

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_DescK2 =====
section

/-!
# S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`

For `q : Y_s ⟶ P_s` and a short exact `0 → q_* N → E' → Λ → 0` on `P_s`:
* `Epp` (`E'' = q^* E' ⊔_{q^* q_* N} N`), `aPP`, `bPP`, **`shortExact_Epp`**: `0 → N → E'' → Λ → 0`;
* `kap0`, **`a_kap0`**: a map `τ : E'' ⟶ ψ'_* N_Z` extending `uC` gives `κ₀ : E' ⟶ (ψ' ≫ q)_* N_Z` extending `q_*(uC)`;
* `kapU_eq`, `push_uC_comp`, `rU_congr`: `q_*(uC) = rU`;
* **`T1`**: there is a finite etale surjective `T ⟶ Y_s` such that every `ψ : U_s ⟶ T` over `Y_s` yields `κ₀` with
  `a' ≫ κ₀ = rUs` (the input of `T3d.HypT`, up to the lifting `T2`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescK

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.SgUnit RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.FBC

universe u

section RU

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} {U₁ U₂ P : Scheme.{u}} (h : U₁ ⟶ U₂) (Φ : U₂ ⟶ P)

theorem kapU_eq (V : P.Etale) : kapU h Φ V = (etPullCompIso h Φ).hom.app V :=
  (cancel_mono ((etPullCompIso h Φ).inv.app V)).1 ((kapU_inv h Φ V).trans (Iso.hom_inv_id_app _ _).symm)

end RU

section Gen

end Gen

section Push

end Push

section T1

end T1

end RamanujanPetersson.EtPBC.DescK

end

end

-- ===== S4.Def_RP_EtPBC_A_CovNbA =====
section

/-!
# S4-EtPBC-A, R4-T2 (G2a): `kapV` is an isomorphism; the fibre inclusion of a neighbourhood is closed

* `kapInv`, **`IsIso (kapV ..)`**: `Y_{V'} = (Spec R' ×_S P) ×_P Y ≅ Y_V ×_V Spec R'`;
* **`isPullback_fibV`**: `P_s ⟶ W ×_S P` is the base change of `w : Spec Ω ⟶ W`; so it is a closed immersion
  when `w` is (`isClosedImmersion_fibV`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S)

section Kap

variable {Y : Scheme.{u}} (π : Y ⟶ PV K gK) {V : Scheme.{u}} (hj : V ⟶ S) [IsAffine V] (R' : Type u) [CommRing R']
  [Algebra Γ(V, ⊤) R']

theorem kapP_cond : pullback.snd (piVV K gK π hj ≫ qV K (hj ≫ gK)) (hV V R') ≫ hV V R' ≫ hj =
    (pullback.fst (piVV K gK π hj ≫ qV K (hj ≫ gK)) (hV V R') ≫ pullback.fst (pullback.snd hj (qV K gK)) π ≫
      pullback.snd hj (qV K gK)) ≫ qV K gK := by
  rw [← pullback.condition_assoc, Category.assoc, piVV_q_assoc, pullback.condition (f := hj) (g := qV K gK)]
  simp only [Category.assoc]

/-- `Y_V ×_V Spec R' ⟶ Spec R' ×_S P`. -/
def kapP : YV K (hj ≫ gK) (piVV K gK π hj) R' ⟶ pullback (hV V R' ≫ hj) (qV K gK) :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.fst _ π ≫ pullback.snd hj (qV K gK))
    (kapP_cond K gK π hj R')

theorem kapInv_cond : kapP K gK π hj R' ≫ pullback.snd (hV V R' ≫ hj) (qV K gK) =
    (pullback.fst (piVV K gK π hj ≫ qV K (hj ≫ gK)) (hV V R') ≫ pullback.snd (pullback.snd hj (qV K gK)) π) ≫ π := by
  rw [kapP, pullback.lift_snd, Category.assoc, pullback.condition (f := pullback.snd hj (qV K gK)) (g := π)]

end Kap

section Fib

end Fib

end RamanujanPetersson.EtPBC

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

instance isIso_cop_piS [Finite ι] : IsIso (cop (piS e)).hom := by
  have h3 : IsIso (sigmaSpec (fun k => CommRingCat.of (R k)) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      X.isoSpec.inv) := inferInstance
  rw [cop_piS_hom]
  exact h3

end PiS

section GenKap
universe w v₁ u₁ u₂ u₃

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

end Gen

section Frac

end Frac

section PiQ

variable {G : Type*} [CommRing G]

variable (h : ∀ (m : Ideal G) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing G]

include h in
theorem exists_toPiQ_update [DecidableEq (minimalPrimes G)] (p₀ : minimalPrimes G) (τ : G)
    (a : G ⧸ (p₀ : Ideal G)) :
    ∃ x : G, toPiQ x = Function.update (toPiQ τ) p₀ (algebraMap _ _ a) := by
  obtain ⟨x, hx⟩ := (piEquiv h).surjective (Function.update (fun p => Ideal.Quotient.mk (p : Ideal G) τ) p₀ a)
  refine ⟨x, funext fun p => ?_⟩
  have e := congrFun hx p
  rw [piEquiv_apply] at e
  rw [toPiQ_apply, e]
  by_cases hp : p = p₀
  · subst hp; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hp, Function.update_of_ne hp, toPiQ_apply]

end PiQ

section Glob

variable {O O' S G : Type*} [CommRing O] [CommRing O'] [CommRing S] [CommRing G]
  [Algebra O O'] [Algebra O S] [Algebra O' (PiQ G)] [Algebra O (PiQ G)] [IsScalarTower O O' (PiQ G)]
  (f : S →ₐ[O] PiQ G) (t : O)

include f in
theorem exists_mem_hatS_update [DecidableEq (minimalPrimes G)]
    (hG : ∀ (m : Ideal G) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing G]
    (hgen : ∀ x : G, ∃ N : ℕ, algebraMap O (PiQ G) t ^ N * toPiQ x ∈ hatS (O' := O') f)
    (τG : G) (hτ : toPiQ τG = algebraMap O (PiQ G) t) (p₀ : minimalPrimes G) {j : ℕ}
    (w : FractionRing (G ⧸ (p₀ : Ideal G)))
    (hw : ∃ a, algebraMap (G ⧸ (p₀ : Ideal G)) _ a = toPiQ τG p₀ ^ j * w) :
    ∃ N : ℕ, algebraMap O (PiQ G) t ^ N * Function.update (1 : PiQ G) p₀ w ∈ hatS (O' := O') f := by
  obtain ⟨a, ha⟩ := hw
  obtain ⟨x, hx⟩ := exists_toPiQ_update hG p₀ (τG ^ j) a
  obtain ⟨N, hN⟩ := hgen x
  refine ⟨N + j, ?_⟩
  have e : toPiQ x = algebraMap O (PiQ G) t ^ j * Function.update (1 : PiQ G) p₀ w := by
    rw [hx, ha, ← hτ]
    funext p
    by_cases hp : p = p₀
    · subst hp; simp [map_pow]
    · simp [Function.update_of_ne hp, map_pow]
  rw [pow_add, mul_assoc, ← e]
  exact hN

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

theorem isIdempotentElem_liveIdem (x : Y) : IsIdempotentElem (liveIdem h x) := by
  classical
  unfold IsIdempotentElem liveIdem
  rw [← map_mul]
  congr 1
  funext Q
  rw [Pi.mul_apply]
  split_ifs <;> simp

/-- `x' := v + (x - v) e_live`: `x` on the pieces where it lives, `v` elsewhere. -/
def liveMod (x v : Y) : Y := v + (x - v) * liveIdem h x

end Live

section Glob'

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

theorem resMapX_toGen (a : A) : resMapX (Spec.map φ) h (Plumb.toGen A a) = Plumb.toGen A' (φ.hom a) :=
  resMapX_spec φ h a

end Gen

end RamanujanPetersson.EtCompact.GalTrE

end

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

theorem exists_minimalPrime_le_ker (p₁ : minimalPrimes Γ(X₁, ⊤)) :
    ∃ q : minimalPrimes Γ(X, ⊤), (q : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁) := by
  haveI : (RingHom.ker (kerMap f p₁)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal Γ(X, ⊤)))
    (J := RingHom.ker (kerMap f p₁)) bot_le
  exact ⟨⟨q, hq⟩, hle⟩

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

-- ===== S4.Def_RP_EtPBC_A_O2E3 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4c1 (scheme level): affine Dedekind presentations of one-point classes

* `fib_injective_of_mono`: a mono of étale objects is injective on geometric fibres;
* `chartLift`, `chartRing`: an affine open `V` of `D` lying over an affine chart `c : Spec R ⟶ P` gives
  `φ_V : R ⟶ Γ(V)` with `Spec φ_V ≫ c = fromSpec ≫ D.hom`, and `φ_V` is étale;
* `A1pt k a`: the point `X = a` of `A¹`; `exists_A1pt_of_closed`: closed points of a chart are of this form;
* `phiG`, `D1`, `d1`: the basic open `Spec Γ(V)_g` as an étale object over `P` through the chart;
* **`isLoc_aff`**: a one-point class at `z ∈ range c` has a presentation `IsLocAff` through `Spec B`,
  `B` a Dedekind domain étale over `k[X]` in which `X - a` generates a prime (the `purity_xi` setting).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtDed

section Mono

end Mono

section Chart

end Chart

section A1

end A1

section D1

variable {k : Type u} [Field k] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {D : P.Etale} {V : D.left.Opens} (hV : IsAffineOpen V) (hVc : ∀ v ∈ V, D.hom v ∈ Set.range c)
  (g : Γ(D.left, V))

include c hV hVc

instance isOpenImmersion_d1 : IsOpenImmersion (d1 c hV hVc g).left :=
  show IsOpenImmersion (Spec.map (locG g) ≫ hV.fromSpec) from inferInstance

theorem d1_apply (v : Spec (CommRingCat.of (Localization.Away g))) :
    (D1 c hV hVc g).hom v = D.hom ((d1 c hV hVc g).left v) := by
  show (Spec.map (phiG c hV hVc g) ≫ c) v = D.hom ((Spec.map (locG g) ≫ hV.fromSpec) v)
  rw [phiG_fac, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]

end D1

section Aff

end Aff

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E4 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`

For a presentation `IsLocAff` through `D = Spec B ⟶ A¹ ⟶ P` (`c` the chart, `t = φ (X - a)`):
* `locT φ a : B ⟶ B_t`, `W1 c φ a := Spec B_t` over `P`, `toD1 : W1 ⟶ chEt c φ`;
* `mem_Uo_iff`: a point `u` of `Spec B` lands in `Uo` iff `t ∉ u`;
* **`isoT`**: `W1 ≅ D ×_P Uo` in `P.Etale`, with `isoT_hom_prW`, `isoT_inv_toD1`;
* `locT_cls`: the class `ε_loc ∘ κ` is `εT ∘ κ₁` with `εT := ε_loc ∘ Λ[isoT.inv]`, `κ₁ := Λ[isoT.hom]^* κ`;
* `locT_res_D`, `locT_res_U`: classes restricted from `D` or from `Uz` die under `εT`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

section T

variable {k : Type u} [Field k] {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{u}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)

variable {a}

variable {Uo : P.Opens} (hUo : ∀ u : Spec B, (chEt c φ).hom u ∈ Uo ↔ φ.hom (X - C a) ∉ u.asIdeal)

include hUo

theorem range_eqT : Set.range (Spec.map (locT φ a)) = Set.range (pullback.fst (chEt c φ).hom (opEt Uo).hom) :=
  Set.ext fun u => (range_locT φ a u).trans ((hUo u).symm.trans (range_fstUo c φ Uo u).symm)

/-- The underlying iso `Spec B_t ≅ Spec B ×_P Uo`. -/
def isoTl : Spec (CommRingCat.of (Localization.Away (φ.hom (X - C a)))) ≅
    pullback (chEt c φ).hom (opEt Uo).hom :=
  @IsOpenImmersion.isoOfRangeEq _ _ _ (Spec.map (locT φ a)) (pullback.fst (chEt c φ).hom (opEt Uo).hom)
    inferInstance (isOpenImmersion_fstUo c φ Uo) (range_eqT c φ hUo)

section Cls

end Cls

end T

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPi1_FunA =====
section

/-!
# S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change

`A → A'`, `K → K'` compatible (`A → K → K'`, `A → A' → K'`), `ι : K̄ →ₐ[K] K̄'` any `K`-embedding.

* `bcField f = K'(roots of f)` in `K̄'` (splitting field, finite, Galois when `f` is separable);
* `rootSet_bc`: the roots of `f` in `K̄'` are the `ι`-images of its roots in `K̄`;
* `icMap`: `integralClosure A L → integralClosure A' L'` induced by `ι`;
* `bcField_unram`: for `L ∈ unramSet A K` the splitting field of `L` over `K'` has trivial inertia over `A'`
  (an inertia element restricts, via `ι`, to an inertia element of `Gal(L/K)`, which is trivial);
* `map_mem_maxUnram`: `ι (K_U(A)) ⊆ K_U(A')`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace EtPi1

open GalCover Lefschetz Polynomial

noncomputable section

section FunA

variable {A K A' K' : Type} [CommRing A] [Field K] [Algebra A K]
  [CommRing A'] [Field K'] [Algebra A' K'] [Algebra K K'] [Algebra A A'] [Algebra A K']
  [IsScalarTower A K K'] [IsScalarTower A A' K']
  (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure K')

theorem icMap_coe (L : IntermediateField K (AlgebraicClosure K)) (L' : IntermediateField K' (AlgebraicClosure K'))
    (h : ∀ y : L, ι y ∈ L') (b : integralClosure A L) :
    (((icMap (A' := A') ι L L' h b : integralClosure A' L') : L') : AlgebraicClosure K') =
      ι ((b : L) : AlgebraicClosure K) := rfl

/-- **Base change preserves unramifiedness.** -/
theorem bcField_unram {L : IntermediateField K (AlgebraicClosure K)} (hL : L ∈ unramSet A K) (f : K[X])
    [f.IsSplittingField K L] (Q' : Ideal (integralClosure A' (bcField (K' := K') f))) (hQ' : Q'.IsPrime) :
    Q'.inertia (bcField (K' := K') f ≃ₐ[K'] bcField (K' := K') f) = ⊥ := by
  have := hL.2.1
  let ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure K' := IsAlgClosed.lift
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  let τ' : AlgebraicClosure K' ≃ₐ[K'] AlgebraicClosure K' := τ.liftNormal (AlgebraicClosure K')
  have hτ' : ∀ y : bcField (K' := K') f, τ' (y : AlgebraicClosure K') = ((τ y : bcField (K' := K') f) :
      AlgebraicClosure K') := fun y => τ.liftNormal_commutes (AlgebraicClosure K') y
  letI : Algebra L (AlgebraicClosure K') := (ι.comp L.val).toRingHom.toAlgebra
  haveI : IsScalarTower K L (AlgebraicClosure K') := IsScalarTower.of_algHom (ι.comp L.val)
  let ρ : L ≃ₐ[K] L := (τ'.restrictScalars K).restrictNormal L
  have hρ : ∀ y : L, ι ((ρ y : L) : AlgebraicClosure K) = τ' (ι (y : AlgebraicClosure K)) := fun y =>
    AlgEquiv.restrictNormal_commutes (τ'.restrictScalars K) L y
  have hmap : ∀ y : L, ι y ∈ bcField (K' := K') f := map_mem_bcField ι f
  have e : ∀ b : integralClosure A L, icMap (A' := A') ι L _ hmap (ρ • b) = τ • icMap ι L _ hmap b := fun b => by
    refine Subtype.ext (Subtype.ext ?_)
    show ι ((ρ (b : L) : L) : AlgebraicClosure K) = ((τ ⟨ι b, hmap b⟩ : bcField (K' := K') f) : AlgebraicClosure K')
    rw [hρ, ← hτ']
  have hin : ρ ∈ (Q'.comap (icMap (A := A) (A' := A') ι L _ hmap)).inertia (L ≃ₐ[K] L) := fun b =>
    Ideal.mem_comap.2 (by rw [RingHom.map_sub, e b]; exact hτ _)
  rw [hL.2.2 _ (Ideal.comap_isPrime _ _), Subgroup.mem_bot] at hin
  have hfixL : ∀ y : L, τ' (ι y) = ι y := fun y => by rw [← hρ, hin, AlgEquiv.one_apply]
  have hfix : ∀ w ∈ bcField (K' := K') f, τ' w = w := fun w hw => by
    have hw' : w ∈ IntermediateField.adjoin K' ((f.map (algebraMap K K')).rootSet (AlgebraicClosure K')) := hw
    clear hw
    induction hw' using IntermediateField.adjoin_induction with
    | mem x hx =>
      rw [rootSet_bc ι f] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      have hrL : r ∈ L := by
        have h3 := Algebra.subset_adjoin (R := K) hr
        rwa [adjoin_rootSet_eq L f] at h3
      exact hfixL ⟨r, hrL⟩
    | algebraMap x => exact τ'.commutes x
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  ext y
  rw [AlgEquiv.one_apply]
  exact (hτ' y).symm.trans (hfix y y.2)

end FunA

end

end EtPi1
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtPBC_A_O2Gl1c =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl1c): the geometric inputs of stages S1-S2

GLOB/REL PLAN v1, stage S1. For an affine `X` with `g : X ⟶ Spec A` etale (`A` a domain, e.g. `A = k[X]`):
* `gamMap g : A →+* Γ(X)`;
* `exists_frac_dvd` (3a): `u ≠ 0` in `Frac(Γ(X) ⧸ p)` is `x / y` with `x ∣ c_x`, `y ∣ c_y`, `c_x, c_y ∈ A ∖ 0`;
* `toPiQ_gamMap_ne_zero`: a nonzero `r ∈ A` is nonzero on every piece (flatness);
* `exists_L` (3b): one `L ≠ 0` with `L^N y` integral over `A` for every `y`;
* `mem_adjoin_wm` (Gen): `Γ(W₁) = B'[Γ(W)]` along a chart map `d` with `d.left = Spec.map ι`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap

open scoped nonZeroDivisors

universe u

section Gam

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (CommRingCat.of A)) [Etale g]

variable [IsDomain A]

/-- **A nonzero `r ∈ A` is nonzero on every piece** of `X` (flatness: pieces dominate `Spec A`). -/
theorem toPiQ_gamMap_ne_zero {r : A} (hr : r ≠ 0) (p : minimalPrimes Γ(X, ⊤)) : toPiQ (gamMap g r) p ≠ 0 := by
  let _ : Algebra A Γ(X, ⊤) := gamAlg g
  have : Algebra.Etale A Γ(X, ⊤) := etale_gamAlg g
  have hreg : IsSMulRegular Γ(X, ⊤) r :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
  have hnzd : gamMap g r ∈ Γ(X, ⊤)⁰ := by
    refine mem_nonZeroDivisors_iff_right.2 fun z hz => hreg ?_
    show r • z = r • (0 : Γ(X, ⊤))
    rw [smul_zero, Algebra.smul_def, gamAlg_algebraMap, mul_comm, hz]
  have hmem : gamMap g r ∉ (p : Ideal Γ(X, ⊤)) := fun h =>
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes h p.2 hnzd
  rw [toPiQ_apply, Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  exact hmem

end Gam

section Gen

end Gen

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2e =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2e): stage S4, the values of `H` on the pieces of `W₂`

GLOB/REL PLAN v1, stage S4 (piece level). `d = d₂₁ ≫ d₀ : D₂ ⟶ D₁ ⟶ D_{g₀}`, `q` a piece of `W₂`, `q₁` a piece of
`W₁`, `Ψ : Frac(Γ(W₁) ⧸ q₁) → Frac(Γ(W₂) ⧸ q)` compatible with `(wm (prdMap d₂₁)).appTop`:
* `piece_value`: `m^* H · bK_q(φ₂ r)^N = Ψ (toPiQ ((prdMap d₀)^* y) q₁)` when `H · ρ(r)^N = ρ y`;
* `piece_t`: `Ψ (toPiQ (gamMap shG₁ r) q₁) = bK_q (φ₂ r)`;
* `frac_value`: `X T₂^N = Ψ(T₁^N w (1 - T₁ z))`, `Ψ T₁ = T₂ ≠ 0` ⇒ `X = Ψ w (1 + T₂ (-Ψ z))` (the shape of `hHp`/`hHq`
  of `uk_diff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section Frac

end Frac

section Gen

def bK_eq {P : Scheme.{0}} {B : CommRingCat.{0}} (hB : Spec B ⟶ P) [Etale hB] (X R : P.Etale)
    (p : minimalPrimes Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤)) (b : B) :
    bK hB X R p b = algebraMap _ _ (Ideal.Quotient.mk p.1 ((bW hB X R).hom b)) := rfl

end Gen

section Piece

end Piece

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl3c =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl3c): a piece of `W₁` survives in `W₂ = W₁[1/φ₁ c₀']`

* **`exists_piece_overB`** (generic): in a localization `G₂ = G₁[1/s]`, a minimal prime `p₁ ∌ s` lies under a minimal
  prime `p₂` (`p₁ ≤ ker (κ p₂)` for any `κ` with `ker (κ q) = σ⁻¹ q`);
* **`not_mem_of_toPiQ_ne_zero`**; **`exists_piece_toDF`**: the chart form (`c₀' ≠ 0`, flatness of `W₁ → Spec k[X]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section PieceOver

variable {G₁ G₂ : Type} [CommRing G₁] [CommRing G₂]

theorem not_mem_of_toPiQ_ne_zero {G : Type} [CommRing G] {x y : G} (hxy : x = y) {p : minimalPrimes G}
    (h : toPiQ x p ≠ 0) : y ∉ p.1 := by
  subst hxy
  intro hm
  apply h
  rw [toPiQ_apply, Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero]

end PieceOver

section PieceChart

end PieceChart

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

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section GraphGeo

variable {P : Scheme.{u}} {W' W T : P.Etale}

set_option backward.isDefEq.respectTransparency false in
theorem graph_left_eq_sec (m : W ⟶ T) : (graph m).left = (sec m).left :=
  pullback.hom_ext ((graph_fst m).trans (sec_fst m).symm) ((graph_snd m).trans (sec_snd m).symm)

set_option backward.isDefEq.respectTransparency false in
/-- **Points over `fpt d` lie on graphs** of sections through all fibre points. -/
theorem graph_cover (z : P) (d : (geomPtAt z).point.fiber.obj W)
    (τ : (geomPtAt z).point.fiber.obj T → (W ⟶ T)) (hτ : ∀ b, (geomPtAt z).point.fiber.map (τ b) d = b)
    (e : ((etPull W.hom).obj T).left) (he : ((etPull W.hom).obj T).hom e = fpt z d) :
    ∃ b, e ∈ Set.range (graph (τ b)).left := by
  obtain ⟨b, hb⟩ := cover_gen z d τ hτ e he
  exact ⟨b, by rw [graph_left_eq_sec]; exact hb⟩

set_option backward.isDefEq.respectTransparency false in
theorem graph_natural (d : W' ⟶ W) (m : W ⟶ T) :
    (graph (d ≫ m)).left ≫ pullMap d = d.left ≫ (graph m).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullMap, pullback.lift_fst, graph_fst]
    try rfl
  · simp only [Category.assoc, pullMap, pullback.lift_snd, graph_snd, Category.comp_id]
    rw [← Category.assoc, graph_snd]
    first
    | exact Category.id_comp _
    | erw [Category.id_comp]
    | simp

end GraphGeo

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel7 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel7): the relation at `c(a)` lies in the localized subgroup

REL PLAN v2 (s126) + s128 fix, last REL file. `term_mem_cofinite` (O2Rel5) with `U₀ := U₁ = c(D(G))` and the bad-point
input `bad_term_at` (O2Rel6):
* **`bad_pt_root`**: a point of `c(A¹)` outside `c(D(G))` is `c(b)` for a root `b` of `G` (given `hpt`);
* **`rel_glob`** (DEF): `ε(S₀, U₁) ∘ Λ[prT S₀ U₁]^* κ_rel ∈ Gr` when points of `U₀` and outside `c(A¹)` are good.
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

section BadPt

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {G : k[X]}

/-- A point of `c(A¹)` outside `c(D(G))` is `c(b)` with `G(b) = 0`. -/
theorem bad_pt_root {x : P} (hx : x ∉ opnDg c G) (hxc : x ∈ Set.range c)
    (hpt : ∀ y : A1 k, G ∈ y.asIdeal → ∃ b, y = A1pt k b) : ∃ b : k, x = c (A1pt k b) ∧ G.IsRoot b := by
  obtain ⟨y, rfl⟩ := hxc
  have hGy : G ∈ y.asIdeal := by
    by_contra hGy
    exact hx (mem_opnDg c rfl hGy)
  obtain ⟨b, rfl⟩ := hpt y hGy
  exact ⟨b, rfl, Polynomial.dvd_iff_isRoot.1 (Ideal.mem_span_singleton.1 hGy)⟩

end BadPt

section RelGlob

end RelGlob

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2a =====
section

/-!
# S4-EtPBC-A, L3b (TB2a): section calculus for base change

* `etPull_hom_ext`: maps into `X ×_Y T` agree if their first components agree;
* `etIdPull g : etId X ≅ X ×_Y Y`, `pullUnit g : Λ_X ≅ g^*Λ_Y`, `pullUnit_one`;
* `unit_hom_ext`: maps out of `Λ_X` are determined by the image of `1`;
* transport of pulled-back sections along `pullIsoRes`, `pullCompIso`, `pullCongr`, `(pull g).map`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section TB2

variable {Λ : Type u} [CommRing Λ]

theorem pullIsoRes_hom_graph {X : Scheme.{u}} {F : EtSh Λ X} {V T : X.Etale} (m : V ⟶ T) (x : F.obj.obj (op T)) :
    (((pullIsoRes V.hom Λ).hom.app F).hom.app (op (etId V.left))).hom
        ((((pull V.hom Λ).obj F).obj.map (graph m).op).hom (pbSec V.hom x)) =
      (F.obj.map ((etCompTop V).hom ≫ m).op).hom x := by
  have hn : (((pullIsoRes V.hom Λ).hom.app F).hom.app (op (etId V.left))).hom
      ((((pull V.hom Λ).obj F).obj.map (graph m).op).hom (pbSec V.hom x)) =
      ((((res V.hom Λ).obj F).obj.map (graph m).op).hom
        ((((pullIsoRes V.hom Λ).hom.app F).hom.app (op ((etPull V.hom).obj T))).hom (pbSec V.hom x))) :=
    congrArg (fun ψ => ψ.hom (pbSec V.hom x)) (((pullIsoRes V.hom Λ).hom.app F).hom.naturality (graph m).op)
  rw [hn, pbSec_res, res_obj_map, ← map_comp_apply_sh, graph_counit]

theorem pullIsoRes_inv_graph {X : Scheme.{u}} {F : EtSh Λ X} {V T : X.Etale} (m : V ⟶ T) (x : F.obj.obj (op T)) :
    (((pullIsoRes V.hom Λ).inv.app F).hom.app (op (etId V.left))).hom ((F.obj.map ((etCompTop V).hom ≫ m).op).hom x) =
      ((((pull V.hom Λ).obj F).obj.map (graph m).op).hom (pbSec V.hom x)) := by
  rw [← pullIsoRes_hom_graph m x]
  exact sh_hom_inv_apply ((pullIsoRes V.hom Λ).app F) _ _

end TB2

section TB2o

/-! Op-form section calculus: restriction maps are op-morphisms `a : op T ⟶ op Z` that are passed through
unchanged, so consecutive steps meet in syntactically equal terms (this keeps kernel checks cheap). -/

variable {Λ : Type u} [CommRing Λ]

theorem pullMap_pbSecO {X Y : Scheme.{u}} (g : X ⟶ Y) {F G : EtSh Λ Y} (φ : F ⟶ G) {V : Y.Etale}
    {Z : X.Etale} (a : op ((etPull g).obj V) ⟶ op Z) (z : F.obj.obj (op V)) :
    ((((pull g Λ).map φ).hom.app (op Z)).hom ((((pull g Λ).obj F).obj.map a).hom (pbSec g z))) =
      ((((pull g Λ).obj G).obj.map a).hom (pbSec g ((φ.hom.app (op V)).hom z))) := by
  rw [pbSec_natural]
  exact congrArg (fun ψ => ψ.hom (pbSec g z)) ((((pull g Λ).map φ).hom.naturality a))

theorem pullMap_pullIsoRes_pbSecO {P A : Scheme.{u}} (W T : P.Etale) (q : A ⟶ W.left) (G : EtSh Λ P)
    {Z : A.Etale} (a : op ((etPull q).obj ((etPull W.hom).obj T)) ⟶ op Z) (y : G.obj.obj (op T)) :
    ((((pull q Λ).map ((pullIsoRes W.hom Λ).hom.app G)).hom.app (op Z)).hom
      ((((pull q Λ).obj ((pull W.hom Λ).obj G)).obj.map a).hom (pbSec q (pbSec W.hom y)))) =
    ((((pull q Λ).obj ((res W.hom Λ).obj G)).obj.map a).hom
      (pbSec q ((G.obj.map ((etCompAdj W.hom).counit.app T).op).hom y))) := by
  rw [pullMap_pbSecO, pbSec_res]

end TB2o

end RamanujanPetersson.EtPBC.EtMV

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

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Etale)

set_option backward.isDefEq.respectTransparency false in
theorem rhoT_eqG (V : X.Etale) (fV : V.left ⟶ W.left) (sq : V.hom ≫ f = fV ≫ W.hom) {T : Y.Etale} (m : W ⟶ T)
    (m' : V ⟶ (etPull f).obj T) (hm : m'.left ≫ pullback.fst T.hom f = fV ≫ m.left) :
    ((graph m' ≫ (etPullCompIso V.hom f).inv.app T) ≫ etPullCongr sq T) ≫ (etPullCompIso fV W.hom).hom.app T =
    (etIdPull fV).hom ≫ (etPull fV).map (graph m) := by
  apply etPull_hom_ext
  apply pullback.hom_ext
  · have h1 := etPullCompIso_hom_fst_fst fV W.hom T
    have h2 := etPullCongr_left_fst sq T
    have h3 := etPullCompIso_inv_fst V.hom f T
    have h4 := graph_left_fst m'
    have h5 : ((etPull fV).map (graph m)).left ≫ pullback.fst ((etPull W.hom).obj T).hom fV =
        pullback.fst (etId W.left).hom fV ≫ (graph m).left := pullback.lift_fst _ _ _
    have h6 := etIdPull_hom_left_fst fV
    have h7 := graph_left_fst m
    exact ((Category.assoc _ _ _).trans ((chainL (graph m').left
      ((etPullCompIso V.hom f).inv.app T).left (etPullCongr sq T).left
      ((etPullCompIso fV W.hom).hom.app T).left _ _ _ _ _ _ h1 h2 h3 h4).trans hm)).trans
      ((Category.assoc _ _ _).trans (chainR (etIdPull fV).hom.left ((etPull fV).map (graph m)).left
        _ _ _ _ _ _ h5 h6 h7)).symm
  · have key : ∀ a : etId V.left ⟶ (etPull fV).obj ((etPull W.hom).obj T),
        (a.left ≫ pullback.fst ((etPull W.hom).obj T).hom fV) ≫ pullback.snd T.hom W.hom = fV :=
      fun a => (Category.assoc _ _ _).trans ((congrArg (fun k => a.left ≫ k) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ fV) (MorphismProperty.Over.w a)).trans
          (Category.id_comp _))))
    exact (key _).trans (key _).symm

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

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section GenPL

universe w' v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {C1 : Type u₁} [Category.{v₁} C1] [Abelian C1] {h1 : HasExt.{w'} C1}
  {C2 : Type u₂} [Category.{v₂} C2] [Abelian C2] {h2 : HasExt.{w'} C2}
  {C3 : Type u₃} [Category.{v₃} C3] [Abelian C3] {h3 : HasExt.{w'} C3}
  {C4 : Type u₄} [Category.{v₄} C4] [Abelian C4] {h4 : HasExt.{w'} C4}

theorem pullL_gen [EnoughInjectives C1] (Φ : C1 ⥤ C2) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (Ψ : C2 ⥤ C4) [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ]
    (R1 : C1 ⥤ C3) [R1.Additive] [PreservesFiniteLimits R1] [PreservesFiniteColimits R1]
    (Pf : C3 ⥤ C4) [Pf.Additive] [PreservesFiniteLimits Pf] [PreservesFiniteColimits Pf]
    [(R1 ⋙ Pf).Additive] [PreservesFiniteLimits (R1 ⋙ Pf)] [PreservesFiniteColimits (R1 ⋙ Pf)]
    (τ : Φ ⋙ Ψ ≅ R1 ⋙ Pf) {A B : C1} (θ : Ext.{w'} A B 1) {A2 : C2} (p : A2 ⟶ Φ.obj A) {U4 : C4}
    (d4 : U4 ⟶ Ψ.obj A2) (eF : Ext.{w'} A2 (Φ.obj B) 1 → Ext.{w'} U4 (Ψ.obj (Φ.obj B)) 1)
    (hE : ∀ x, eF x = (Ext.mk₀ d4).comp (x.mapExactFunctor Ψ) (zero_add 1))
    {U3 Z : C3} (d3 : U3 ⟶ R1.obj A) (u : U4 ⟶ Pf.obj U3)
    (hk : (d4 ≫ Ψ.map p) ≫ τ.hom.app A = u ≫ Pf.map d3) (κ : Ext.{w'} U3 Z 1) (s : Z ⟶ R1.obj B)
    (he : (Ext.mk₀ d3).comp (θ.mapExactFunctor R1) (zero_add 1) = κ.comp (Ext.mk₀ s) (add_zero 1)) :
    (eF ((Ext.mk₀ p).comp (θ.mapExactFunctor Φ) (zero_add 1))).comp (Ext.mk₀ (τ.hom.app B)) (add_zero 1) =
      (Ext.mk₀ u).comp ((κ.mapExactFunctor Pf).comp (Ext.mk₀ (Pf.map s)) (add_zero 1)) (zero_add 1) := by
  rw [hE, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc,
    Ext.comp_assoc_of_third_deg_zero, mapExact_comp_iso Φ Ψ τ, Ext.mk₀_comp_mk₀_assoc, mapExact_compF R1 Pf, hk,
    ← Ext.mk₀_comp_mk₀_assoc]
  have e := congrArg (fun z => (Ext.mk₀ u).comp (z.mapExactFunctor Pf) (zero_add 1)) he
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at e
  exact e

end GenPL

end TB3

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L5a =====
section

/-!
# S4-EtPBC-A, L5a (Geo1): the horizontal section through a closed point of `P¹_K`

`K` algebraically closed, `z` a closed point of `P¹_K`:
* `pt_factor`: a morphism `Spec Ω ⟶ X` hitting `z` factors through the `K`-point of `z` (`pointOfClosedPoint`);
* `σz : S ⟶ P¹_S`, `t ↦ (z, t)`, a section of `qV` (`σz_qV`, `σz_pr`);
* **`geom_factor`**: a morphism `x : Spec Ω ⟶ P¹_S` with `pr (x pt) = z` is `(x ≫ qV) ≫ σz`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.Z3

universe u

section PtFactor

end PtFactor

section Sec

variable (K : Type u) [Field K] [IsAlgClosed K] {S : Scheme.{u}} (gS : S ⟶ Spec (CommRingCat.of K))
  (z : P1 K) (hz : IsClosed ({z} : Set (P1 K)))

theorem ptz_toSpecK : ptz K z hz ≫ P1.toSpecK K = 𝟙 _ := pointOfClosedPoint_comp _ _ _

/-- The horizontal section `t ↦ (z, t)` of `P¹_S ⟶ S`. -/
def σz : S ⟶ PV K gS :=
  pullback.lift (gS ≫ ptz K z hz) (𝟙 S) (by rw [Category.assoc, ptz_toSpecK, Category.comp_id, Category.id_comp])

@[reassoc]
theorem σz_qV : σz K gS z hz ≫ qV K gS = 𝟙 S := pullback.lift_snd _ _ _

@[reassoc]
theorem σz_pr : σz K gS z hz ≫ pr K gS = gS ≫ ptz K z hz := pullback.lift_fst _ _ _

/-- **Geometric points over `z` factor through the horizontal section.** -/
theorem geom_factor {Ω : Type u} [Field Ω] (x : Spec (CommRingCat.of Ω) ⟶ PV K gS)
    (hx : pr K gS (x (IsLocalRing.closedPoint Ω)) = z) : x = (x ≫ qV K gS) ≫ σz K gS z hz := by
  apply pullback.hom_ext
  · have h1 := pt_factor (P1.toSpecK K) z hz (x ≫ pr K gS) hx
    refine h1.trans ?_
    simp only [Category.assoc, σz_pr, pullback.condition_assoc]
  · rw [Category.assoc, σz_qV, Category.comp_id]

end Sec

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

/-- `etPull (𝟙 X) ≅ 𝟭`. -/
def etPullId (X : Scheme.{u}) : etPull (𝟙 X) ≅ 𝟭 X.Etale :=
  NatIso.ofComponents etPullIdC (fun m => MorphismProperty.Over.Hom.ext (etPull_map_left_fst (𝟙 X) m))

end L7a

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gen1 =====
section

/-!
# S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`

* `ptCls_comp`: `PtCls c R x → PtCls c T (x ∘ Λ[r])`; `compSub r G` (`x ↦ x ∘ Λ[r]` pulled back subgroup).
* `isClosed_of_isLoc`: an `IsLoc` point is closed.
* chart facts for any open immersion `c : A¹ ⟶ P¹`: `chart_ne_genPt`, `chart_hclA`, `chart_hGal`, `chart_hclc`,
  `A1_hpt`, `exists_A1pt_of_mem_range`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtCompact.PushStk RamanujanPetersson.EtCompact.PushBC

section PtCompSub

end PtCompSub

section CompSub

end CompSub

section Chart

variable {k : Type} [Field k]

theorem A1_hpt [IsAlgClosed k] : ∀ y : A1 k, y.asIdeal ≠ ⊥ → ∃ b, y = A1pt k b :=
  fun y hy => eq_A1pt k y (Ideal.IsPrime.isMaximal y.isPrime hy)

theorem exists_A1pt_of_mem_range [IsAlgClosed k] (c : A1 k ⟶ P1 k) [IsOpenImmersion c] (z : P1 k)
    (hz : IsClosed ({z} : Set (P1 k))) (hzr : z ∈ Set.range c) : ∃ a : k, c (A1pt k a) = z := by
  obtain ⟨y, rfl⟩ := hzr
  have hy : IsClosed ({y} : Set (A1 k)) := by
    have h := hz.preimage c.isOpenEmbedding.continuous
    rwa [← Set.image_singleton, c.isOpenEmbedding.injective.preimage_image] at h
  obtain ⟨a, ha⟩ := eq_A1pt k y ((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).1 hy)
  exact ⟨a, by rw [ha]⟩

end Chart

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b2 =====
section

/-!
# S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`

For a chart `D = chEt c φ` (`B` Dedekind, `(X - a)` a nonzero prime) and `s' : D ⟶ ιP^* W`:
* the point `d₀ = (X - a)` of `D` over `z = c a` and its `K`-point `δ₀` (`δ₀_hom : δ₀ ≫ D.hom = ptz`);
* `wK = s'(d₀)`, the `K`-point `v'` of `Vs` over `sK` (`v'_hom`), `gE₀ : D ⟶ Es` (`v ↦ (s' v, σ₀ v)`);
* `Vb = gE₀⁻¹(Og)`, `Db = opn D Vb` (`d₀ ∈ Vb`), its fibre at `z` (subsingleton, nonempty) and `hSb`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum

section Sq

end Sq

section Pt

variable {K : Type} [Field K] [IsAlgClosed K] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)]

/-- The `K`-point of `D` at `d₀`. -/
def δ₀ [IsDedekindDomain B] (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime) :
    Spec (CommRingCat.of K) ⟶ (chEt c φ).left :=
  pointOfClosedPoint ((chEt c φ).hom ≫ P1.toSpecK K) (d₀ c a φ hP) (d₀_closed c a φ ht hP)

theorem δ₀_apply [IsDedekindDomain B] (ht : φ.hom (X - C a) ≠ 0)
    (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime) (x : Spec (CommRingCat.of K)) :
    δ₀ c a φ ht hP x = d₀ c a φ hP :=
  pointOfClosedPoint_apply _ _ _ x

end Pt

section Fib

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7b1 =====
section

/-!
# S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
For a `K`-rational geometric point `s` (`[IsIso (s.pt ≫ gS)]`), `e := fibToP1 : P_s ⟶ P¹_K` is an isomorphism with
`e ≫ ιP = ι` (`fibToP1_ιP`). Base change identifications `isoE X : e^*ιP^*X ⟶ ι^*X` (natural, invertible),
the section `σG` of `ιP^*(qV^*V)` through a `K`-point `v'` of `V`, the neighbourhood `jG = (V, v')` of `s`, and
**`nbhdSec_eq`**: `nbhdSec jG = c₀ ≫ e^*σG ≫ isoE`. **`TrE`**: `Ext²(Λ[P¹], Λ[ιP^*R]) → Ext²(Λ_{P_s}, ι^*Λ[R])`,
`x ↦ u ∘ e^*x ∘ v`; **`TrE_surjective`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

universe u

section Gen

variable {X Y : Scheme.{u}}

theorem etPullCongr_natural {g g' : X ⟶ Y} (h : g = g') {T T' : Y.Etale} (m : T ⟶ T') :
    (etPull g).map m ≫ etPullCongr h T' = etPullCongr h T ≫ (etPull g').map m := by
  subst h
  exact (whisker_eq _ (etPullCongr_rfl g T')).trans ((Category.comp_id _).trans ((Category.id_comp _).symm.trans
    (eq_whisker (etPullCongr_rfl g T).symm _)))

instance etPullCongr_isIso {g g' : X ⟶ Y} (h : g = g') (T : Y.Etale) : IsIso (etPullCongr h T) := by
  subst h
  rw [etPullCongr_rfl]
  infer_instance

end Gen

section GenSurj

universe w v₁ u₁ v₂ u₂

end GenSurj

section Fib

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFix =====
section

/-!
# S4-EtPBC-A, R4-T2 (G'): the geometric half of T2 from the corrected statement `CoverLiftAt₂`

* `ker_χV`, `ker_beta`: the fibre charts `Γ(Y, U) ↠ Γ(Y_x, fx⁻¹ U)` have kernel `(ker χ) Γ(Y, U)` (`Z3.ker_fx_app`);
* **`nonempty_liftD₂`**: `CoverLiftAt₂` at `x` gives the lift data `LiftD` (as `nonempty_liftD` from `CoverLiftAt`);
* **`liftT_core₂`**, **`liftT_of_coverLiftAt₂`**: `CoverLiftAt₂` at `xV` gives `T2.LiftT (qV K gK) s π`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1

universe u

section Ker

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) (x : Spec (CommRingCat.of K) ⟶ V)

theorem ker_χV (hx : x ≫ gV = 𝟙 _) :
    letI := algKV K gV; RingHom.ker (χV K gV x hx) = RingHom.ker x.appTop.hom := by
  letI := algKV K gV
  rw [ker_appTop_eq K x]
  ext a
  exact Iff.rfl

end Ker

section Cover

attribute [local instance] algKY

attribute [local instance] algT

end Cover

end RamanujanPetersson.EtPBC.Cov

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.Cov

universe u

section Main

attribute [local instance] algX0 algX1 algXN algA0 algA1 algKY algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

end Main

end RamanujanPetersson.EtPBC

end

end


