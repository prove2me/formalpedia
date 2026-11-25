-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_077
-- name    : RPLib_FX_EtPBC_077
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:42:00.146974+00:00
-- url     : https://prove2.me/theorems/3ca0272d-69ff-5337-91c6-2987cb1f4f3e
-- title:
--   Proper base change for the projective line, library file 077
-- statement:
--   File 077 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_Z4FibC`: S4-EtPBC-A, (Z) geometric layer 13 (G-f, part 3): the `π₀` extension theorem
--   * `S4.Def_RP_EtPBC_A_O2L5c1`: S4-EtPBC-A, L5c1 (Geo3): the Mayer-Vietoris square of the graph-open `D̃` on `P¹_S`
--   * `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
--   * `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
--   * `S4.Def_RP_EtPBC_A_O2L8a`: S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_071

/-!
# Proper base change for the projective line, library file 077

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
* `S4.Def_RP_EtPBC_A_Z4FibC`: S4-EtPBC-A, (Z) geometric layer 13 (G-f, part 3): the `π₀` extension theorem
* `S4.Def_RP_EtPBC_A_O2L5c1`: S4-EtPBC-A, L5c1 (Geo3): the Mayer-Vietoris square of the graph-open `D̃` on `P¹_S`
* `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
* `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
* `S4.Def_RP_EtPBC_A_O2L8a`: S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
-/

set_option autoImplicit false

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

variable {U : Y.Opens} (hU : IsAffineOpen U) [Algebra Γ(V, ⊤) Γ(Y, U)]
  (hA : CommRingCat.ofHom (algebraMap Γ(V, ⊤) Γ(Y, U)) = strU K gV π U)

instance isOpenImmersion_chY : IsOpenImmersion (chY K gV π R' hU hA) :=
  MorphismProperty.of_isPullback (isPullback_chY K gV π R' hU hA).flip
    (inferInstance : IsOpenImmersion hU.fromSpec)

end Chart

section Res

end Res

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovCv =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`

`directed_of_range`: directedness of an open cover from its ranges. **`covV`**: the open cover of `Y_{V'} = Y ×_V Spec R'`
by the charts `Spec (R' ⊗ Γ(Y₀₁))`, `Spec (R' ⊗ Γ(Y₀))`, `Spec (R' ⊗ Γ(Y₁))`, indexed by `WalkingSpan`
(`zero ↦ Y₀₁`), with transition maps the `span` of the chart restrictions `a0`, `a1`; instance `LocallyDirected`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] [IsAffineHom π] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

instance : IsOpenImmersion (ch0 K gV π R') := isOpenImmersion_chY K gV π R' _ (struct_res K gV π 0)

instance : IsOpenImmersion (ch1 K gV π R') := isOpenImmersion_chY K gV π R' _ (struct_res K gV π 1)

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4FibC =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 13 (G-f, part 3): the `π₀` extension theorem

* `fibLift` (the fibre map of `exists_etale_idem_Y`), `fibLift_fst`, `fibLift_snd`; `chart_eq` (on a chart, the
  pulled-back idempotent is computed in `κ(p) ⊗ Γ(Y, U)`).
* **`exists_clopen_ext`**: `V` affine noetherian over `K`, `π : Y ⟶ P¹_V` finite, `x : Spec K ⟶ V` a `K`-point
  (`x ≫ gV = 𝟙`), `C₀ ⊆ Y_x` clopen. Then there are an etale `Γ(V)`-algebra `R'`, a lift `x' : Spec K ⟶ Spec R'` of
  `x` and a clopen `C ⊆ Y ×_V Spec R'` whose preimage in `Y_x` (under `yxMap`) is `C₀`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algYV

section Chart

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (x : Spec (CommRingCat.of K) ⟶ V)
  {R' : Type u} [CommRing R'] [Algebra Γ(V, ⊤) R'] (P : Ideal R') [P.IsPrime] [P.LiesOver (px K x)]
  (hbij : Function.Bijective (Ideal.ResidueField.mapₐ (px K x) P (Algebra.ofId _ _) (P.over_def (px K x))))

omit [IsAffine V] in
theorem fibLift_fst (r : R') (y : Z2.secAlg (φY0 K gV π) (φY1 K gV π)) :
    (fibLift K gV π x P hbij (r ⊗ₜ y)).1 = (AlgEquiv.ofBijective _ hbij).symm (algebraMap R' P.ResidueField r) ⊗ₜ
      Y.presheaf.map (homOfLE le_top : Yc K gV π 0 ⟶ ⊤).op (glueRing K gV π y) := by
  rw [glueRing_res0, Algebra.TensorProduct.lift_tmul, Prod.fst_mul]
  change (Algebra.TensorProduct.includeLeft (S := Γ(V, ⊤))
    ((AlgEquiv.ofBijective _ hbij).symm (algebraMap R' P.ResidueField r))) *
      (Algebra.TensorProduct.includeRight y.1.1 : (px K x).ResidueField ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) = _
  rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

omit [IsAffine V] in
theorem fibLift_snd (r : R') (y : Z2.secAlg (φY0 K gV π) (φY1 K gV π)) :
    (fibLift K gV π x P hbij (r ⊗ₜ y)).2 = (AlgEquiv.ofBijective _ hbij).symm (algebraMap R' P.ResidueField r) ⊗ₜ
      Y.presheaf.map (homOfLE le_top : Yc K gV π 1 ⟶ ⊤).op (glueRing K gV π y) := by
  rw [glueRing_res1, Algebra.TensorProduct.lift_tmul, Prod.snd_mul]
  change (Algebra.TensorProduct.includeLeft (S := Γ(V, ⊤))
    ((AlgEquiv.ofBijective _ hbij).symm (algebraMap R' P.ResidueField r))) *
      (Algebra.TensorProduct.includeRight y.1.2 : (px K x).ResidueField ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) = _
  rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- On a chart `U`, the pulled-back idempotent is computed by a map `L` to `κ(p) ⊗ Γ(Y, U)`. -/
theorem chart_eq (U : Y.Opens) [Algebra Γ(V, ⊤) Γ(Y, U)]
    (halg : algebraMap Γ(V, ⊤) Γ(Y, U) = (strU K gV π U).hom)
    (L : R' ⊗[Γ(V, ⊤)] Z2.secAlg (φY0 K gV π) (φY1 K gV π) →+* (px K x).ResidueField ⊗[Γ(V, ⊤)] Γ(Y, U))
    (hL : ∀ r y, L (r ⊗ₜ y) = (AlgEquiv.ofBijective _ hbij).symm (algebraMap R' P.ResidueField r) ⊗ₜ
      Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (glueRing K gV π y))
    (e' : R' ⊗[Γ(V, ⊤)] Z2.secAlg (φY0 K gV π) (φY1 K gV π)) (b : Γ(Y, U)) (hLe : L e' = 1 ⊗ₜ b) :
    (Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ U ⟶ ⊤).op
      ((yxMap K gV π R' x _ (hxχ K x P hbij)).appTop (PhiY K gV π R' e')) = (fx K gV π x).app U b := by
  obtain ⟨j, hj⟩ := exists_fibreRing K gV π x U halg
  have key : ∀ t, (Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ U ⟶ ⊤).op
      ((yxMap K gV π R' x _ (hxχ K x P hbij)).appTop (PhiY K gV π R' t)) = j (L t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r y =>
      rw [yxMap_PhiY_tmul, map_mul, xχ_appTop, hL, hj, fx_res, χx_apply]
    | add a c ha hc => rw [map_add, map_add, map_add, map_add, ha, hc, map_add]
  rw [key, hLe, hj]
  simp only [map_one, one_mul]

end Chart

section Main

end Main

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L5c1 =====
section

/-!
# S4-EtPBC-A, L5c1 (Geo3): the Mayer-Vietoris square of the graph-open `D̃` on `P¹_S`

`K` algebraically closed, `z` a closed point of `P¹_K`, `σz : S ⟶ P¹_S` the horizontal section (L5a), `W` etale over
`P¹_S`, `Q ⊇ pr⁻¹ z` open:
* `σz` is a closed immersion (`isClosedImmersion_σz`); `Uz := pr⁻¹ (P¹ ∖ z)`;
* `D̃ := Dg W _ Q` (L5b) over `Zz := Zs σz qV W`, `D̃ₒ := D̃ ×_P Uz`, `Ũ := Zz ×_P Uz`;
* **`mvZ_shortExact`**: `0 → Λ[D̃ₒ] → Λ[D̃] ⊞ Λ[Ũ] → Λ[Zz] → 0` is short exact (MVG2 over `Uz`, MVG1 over `z` by the
  fibre lemma `graph_good` and `geom_factor`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3

universe u

section MVZ

variable (K : Type u) [Field K] [IsAlgClosed K] {S : Scheme.{u}} (gS : S ⟶ Spec (CommRingCat.of K))
  (z : P1 K) (hz : IsClosed ({z} : Set (P1 K)))

variable (W : (PV K gS).Etale) (Q : (PV K gS).Opens)

/-- **The MV square of `D̃` is short exact.** -/
theorem mvZ_shortExact (Λ : Type u) [CommRing Λ] (hQ : ∀ x : PV K gS, pr K gS x = z → x ∈ Q) :
    (mvC Λ (prW (Dz K gS z hz W Q) (opEt (Uz K gS z hz))) (p₂z K gS z hz W Q) (wz K gS z hz W Q)
      (prW (Zz K gS z hz W) (opEt (Uz K gS z hz))) (sqz K gS z hz W Q)).ShortExact :=
  mvC_shortExactR _ _ _ _ (sqz K gS z hz W Q) (mvZ_good K gS z hz W Q hQ)

end MVZ

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

end Gen

section GenSurj

universe w v₁ u₁ v₂ u₂

end GenSurj

section Fib

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)]

theorem nbhdSec_hR (V : S.Etale) (v' : Spec (CommRingCat.of K) ⟶ V.left) (hv' : v' ≫ V.hom = sK gS s) :
    (etIdPull (fibToP1 K gS s)).hom.left ≫ ((etPull (fibToP1 K gS s)).map (σG gS s V v' hv')).left ≫
      (isoE gS s ((etPull (qV K gS)).obj V)).left ≫
        pullback.fst ((etPull (qV K gS)).obj V).hom (fibι (qV K gS) s) = fibToP1 K gS s ≫ σ₀G gS s V v' hv' := by
  have e1 := isoE_left_fst gS s ((etPull (qV K gS)).obj V)
  have e2 := etPull_map_left_fst_assoc (fibToP1 K gS s) (σG gS s V v' hv')
    (pullback.fst ((etPull (qV K gS)).obj V).hom (ιP gS s))
  have e3 := etIdPull_hom_fst_assoc (fibToP1 K gS s)
    ((σG gS s V v' hv').left ≫ pullback.fst ((etPull (qV K gS)).obj V).hom (ιP gS s))
  have e4 : (σG gS s V v' hv').left ≫ pullback.fst ((etPull (qV K gS)).obj V).hom (ιP gS s) = σ₀G gS s V v' hv' :=
    toPull_fst (T' := etId (P1 K)) (Y' := (etPull (qV K gS)).obj V) (ιP gS s) (σ₀G gS s V v' hv')
      ((pullback.lift_snd _ _ _).trans (Category.id_comp _).symm)
  exact (whisker_eq _ (whisker_eq _ e1)).trans ((whisker_eq _ e2).trans (e3.trans (whisker_eq _ e4)))

/-- **`nbhdSec jG = c₀ ≫ e^*σG ≫ isoE`.** -/
theorem nbhdSec_eq (V : S.Etale) (v' : Spec (CommRingCat.of K) ⟶ V.left) (hv' : v' ≫ V.hom = sK gS s) :
    nbhdSec (qV K gS) s (jG gS s V v' hv') = (etIdPull (fibToP1 K gS s)).hom ≫
      (etPull (fibToP1 K gS s)).map (σG gS s V v' hv') ≫ isoE gS s ((etPull (qV K gS)).obj V) := by
  apply etPull_hom_ext
  refine ((secL_fst (qV K gS) s (jG gS s V v' hv')).trans (fibToNbhd_jG gS s V v' hv')).trans ?_
  refine (nbhdSec_hR gS s V v' hv').symm.trans ?_
  exact ((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).symm

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7b2 =====
section

/-!
# S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
**`TrE_mvTheta`**: for an MV square over `qV^*V` on `P = P¹_K ×_K S` and a `K`-point `v'` of `V` over `s`, the
transport `TrE` of the `P¹_K`-class `Λ[σG] ∘ ιP^*(ε ∘ θ(p₁, κ) ∘ Λ[r])` is the base change at `jG = (V, v')` of the
family class `ε ∘ θ(p₁, κ) ∘ Λ[r]`. Proof: `mvThetaR_pull` along `e`, `bc_mvThetaR` at `jG`, and `mvTheta_map` along
the base change identifications `isoE` (`nbhdSec_eq`, `isoE_natural`, `isoE_left_fW`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

universe w v₀ u₀

section GenTr

universe w' v₁ u₁ v₂ u₂

end GenTr

section TrMV

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]
  (V : S.Etale) (v' : Spec (CommRingCat.of K) ⟶ V.left) (hv' : v' ≫ V.hom = sK gS s)

/-- `jG` with reducible projections. -/
abbrev jR : Nbhd s :=
  s.point.fiber.elementsMk V (CategoryTheory.Over.homMk ((s.pt ≫ gS) ≫ v') (jG_w gS s V v' hv') :
    CategoryTheory.Over.mk s.pt ⟶ (Scheme.Etale.forget S).obj V)

theorem jR_eq : jR gS s V v' hv' = jG gS s V v' hv' := rfl

end TrMV

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L8a =====
section

/-!
# S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
* **`Delta.surjAt_coprod`**: surjectivity on germs passes to finite coproducts (`ι : Type`, finite);
* `wGIso`, `wG`, `wG_natural`: `e^* ιP^* G ≅ ι^* G` (`e = fibToP1`, `e ≫ ιP = ι`), natural in `G`;
* **`TrG`** `G x = u ∘ e^*x ∘ wG`: `Ext²(Λ[P¹_K], ιP^*G) → Ext²(Λ_{P_s}, ι^*G)`; `TrGh` (additive, `rfl`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtCompact.PushBC

universe u

section TrG

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

/-- **The transport for any sheaf** `Ext²(Λ[P¹_K], ιP^*G) → Ext²(Λ_{P_s}, ι^*G)`. -/
def TrG (G : EtSh Λ (PV K gS)) (x : Ext.{0} (freeSh Λ (etId (P1 K))) ((pull (ιP gS s) Λ).obj G) 2) :
    Ext.{0} (unitSh Λ (fib (qV K gS) s)) ((pull (fibι (qV K gS) s) Λ).obj G) 2 :=
  (Ext.mk₀ (uE gS s Λ)).comp ((x.mapExactFunctor (pull (fibToP1 K gS s) Λ)).comp (Ext.mk₀ (wG gS s Λ G))
    (add_zero 2)) (zero_add 2)

end TrG

end RamanujanPetersson.EtPBC.EtMV

end

end


