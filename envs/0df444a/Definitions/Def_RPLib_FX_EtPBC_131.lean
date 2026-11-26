-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_131
-- name    : RPLib_FX_EtPBC_131
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:47:37.696633+00:00
-- url     : https://prove2.me/theorems/416f6181-1a98-536b-97cc-4280c97f18a8
-- title:
--   Proper base change for the projective line, library file 131
-- statement:
--   File 131 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2D2`: S4-EtPBC-A, O2 (MV route), M3 steps (2) and (4): every class of `H²(Spec A, F)` dies on a basic open
--   * `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
--   * `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_047
import Definitions.Def_RPLib_FX_EtPBC_122

/-!
# Proper base change for the projective line, library file 131

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2D2`: S4-EtPBC-A, O2 (MV route), M3 steps (2) and (4): every class of `H²(Spec A, F)` dies on a basic open
* `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
* `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2D2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M3 steps (2) and (4): every class of `H²(Spec A, F)` dies on a basic open

* `ext_eq_zero_of_comp`: dévissage along `φ : F ⟶ G` (`Ext^(n+2)(A, ker φ) = Ext^(n+1)(A, coker φ) = 0`): a class
  `e ∈ Ext^(n+2)(A, F)` with `e ∘ φ = 0` is zero;
* `isAffineOpen_bOpen`; **`acyc_bOpen`** (step (2)): `Ext^(n+1)(Λ[D(f)], Q) = 0` when `Q` has zero generic stalk,
  closed points of `Spec A` have algebraically closed residue fields and `D(f)` has a non-generic point;
* **`two_dies`** (step (4)): every `β ∈ H²(Spec A, F)` dies on some `D(f)`, `f ≠ 0` (unit `F ⟶ g_* g^* F`, its kernel
  and cokernel are acyclic on `D(f)`, and `push_two_dies`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.CurveHn

section Devissage

universe w v u

end Devissage

variable {A : Type} [CommRing A] [IsDomain A] {Λ : Type} [CommRing Λ]

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

variable [IsIntegrallyClosed A]

/-- **Step (4) (Claim D on `Spec A`)**: every class of `H²(Spec A, F)` dies on some `D(f)`, `f ≠ 0`. -/
theorem two_dies
    (hη : ∀ (M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) (e : H Λ M 2), e = 0)
    (hR : ∀ M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))),
      IsZero (R1 (gen A) Λ (Qt Λ M)))
    (hcl : ∀ y : Spec (CommRingCat.of A), IsClosed ({y} : Set (Spec (CommRingCat.of A))) →
      IsAlgClosed ((Spec (CommRingCat.of A)).residueField y))
    (hJ : ∀ f : A, f ≠ 0 → ∃ m : Spec (CommRingCat.of A), m ∈ bOpen f ∧ m ≠ GenBr.genPt A)
    (F : EtSh Λ (Spec (CommRingCat.of A))) (β : H Λ F 2) :
    ∃ f : A, f ≠ 0 ∧ (Ext.mk₀ (rD Λ f)).comp β (zero_add 2) = 0 := by
  obtain ⟨f, hf0, hf⟩ := push_two_dies hη hR ((pull (gen A) Λ).obj F)
    (β.comp (Ext.mk₀ ((pullAdj (gen A) Λ).unit.app F)) (add_zero 2))
  refine ⟨f, hf0, ?_⟩
  refine ext_eq_zero_of_comp ((pullAdj (gen A) Λ).unit.app F) _ 0
    (acyc_bOpen hcl f (hJ f hf0) _ (GenUnit.isZero_stalk_kernel_unit F) 1)
    (acyc_bOpen hcl f (hJ f hf0) _ (GenUnit.isZero_stalk_cokernel_unit F) 0) _ ?_
  rw [Ext.comp_assoc_of_third_deg_zero]
  exact hf

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

section GenDies

universe w₁ v₁ u₁

end GenDies

variable (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)

include hl hΛ

/-- **Claim D on `A¹`.** -/
theorem two_dies_A1 (F : EtSh Λ (Spec (CommRingCat.of k[X]))) (β : H Λ F 2) :
    ∃ f : k[X], f ≠ 0 ∧ (Ext.mk₀ (rD Λ f)).comp β (zero_add 2) = 0 :=
  two_dies (fun M e => H_genPt_eq_zero k l hl m hΛ 0 M e) (A1.isZero_R1_qt k l hl m hΛ)
    (fun y hy => isAlgClosed_residue k k[X] y hy) (A1.exists_closed_mem k) F β

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Bd4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`

s128 fix of REL PLAN v2: a bad point `c(b)` has `g₀(b) = 0` (`c(D(g₀)) ⊆ U₀ ∪ {z}`), so no chart `D' ∋ b` maps to
`D_{g₀}`. The map `W(D') → Y₀` is `m^* ∘ ρ` instead (`m := mG : D' ×_P U₀ ⟶ D_G ×_P U₀`, `ρ := (prdMap (toDG c hG₀))^*`):
* **`wD_hom`**, **`shG_wm_any`**: `wm m ≫ shG φ₁ = shG φ₂` for ANY `m : D₂ ×_P U₀ ⟶ D₁ ×_P U₀` between chart products;
* **`mG_rho_gamMap`**, **`mG_H_any`**: `m^* (ρ r) = bW'(φ' r)`; the `H`-relation pulled back along `m`;
* **`exists_bad_e'`**: `exists_bad_e` (O2Bd2) without `d : D' ⟶ D_{g₀}`;
* **`exists_S4H'`**: `exists_S4H` (O2Gl2k) for a generic `G` (`hG₀ : g₀ ∣ G`), also returning `H ρ(t)^N = ρ(y)`.
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

section WDHom

end WDHom

section AnyM

end AnyM

section BadChart'

end BadChart'

section S4H'

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ c₀' G : k[X]} {a : k} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  [IsAffine (prd (chEt c φ₁) (opEt Uo)).left]
  [IsAffine (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).left]
  (hD₂ : ∀ v : (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).left,
    (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom v ∈ opnDg c G)
  (d₀ : chEt c φ₁ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀))

set_option maxHeartbeats 400000 in
/-- **Stage S4 with `H` and `D₂` fixed, generic `G`**: `exists_S4H` also returning `H ρ(t)^N = ρ(y)`. -/
def exists_S4H' [Nontrivial (Localization.Away (φ₁.hom c₀'))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))]
    (p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) (u₁ : FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)) {N e₀ : ℕ} {y : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)}
    (hdvd : y ∣ gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) ((X - C a) ^ e₀ * c₀'))
    (hGc : IsUnit ((locF (B := CommRingCat.of k[X]) G).hom ((X - C a) ^ e₀ * c₀')))
    (hGt : IsUnit ((locF (B := CommRingCat.of k[X]) G).hom (X - C a)))
    {z : PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)}
    (hy : toPiQ ((wm (R := R) (prdMap d₀ (opEt Uo))).appTop y) =
      toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) (X - C a)) ^ N * Function.update (1 : PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) p₁ u₁ *
        (1 - toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) (X - C a)) * z))
    (hz : letI : Algebra B₁ (PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) := (toPiQ.comp (bW (Spec.map φ₁ ≫ c) (opEt Uo) R).hom).toAlgebra; IsIntegral B₁ z) :
    ∃ H : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), IsUnit H ∧
    H * (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
        (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a)) ^ N =
      (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop y ∧
    ∃ e : ∀ q : minimalPrimes Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤), FractionRing (Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1),
      ∃ g : (Localization.Away (φ₁.hom c₀'))[X], g.Monic ∧ 0 < g.natDegree ∧
      (∀ q, g.eval₂ (bK (Spec.map (φ₁ ≫ locF (φ₁.hom c₀')) ≫ c) (opEt Uo) R q) (e q) = 0) ∧
      ∀ p₂ : minimalPrimes Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤),
        (p₁ : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap (toDF c φ₁ (φ₁.hom c₀')) (opEt Uo))) p₂) →
        (∀ Ψ : FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) →+* FractionRing (Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₂.1),
          (∀ x, Ψ (algebraMap _ _ (Ideal.Quotient.mk p₁.1 x)) =
            algebraMap _ _ (Ideal.Quotient.mk p₂.1 ((wm (R := R) (prdMap (toDF c φ₁ (φ₁.hom c₀')) (opEt Uo))).appTop x))) →
          algebraMap _ (FractionRing (Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₂.1))
              (Ideal.Quotient.mk p₂.1 ((wm (R := R) (mG c hle (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) hD₂)).appTop H)) =
            Ψ u₁ * (1 + bK (Spec.map (φ₁ ≫ locF (φ₁.hom c₀')) ≫ c) (opEt Uo) R p₂ ((φ₁ ≫ locF (φ₁.hom c₀')).hom (X - C a)) * e p₂)) ∧
        ∀ q, q ≠ p₂ →
          algebraMap _ (FractionRing (Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1))
              (Ideal.Quotient.mk q.1 ((wm (R := R) (mG c hle (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) hD₂)).appTop H)) =
            1 + bK (Spec.map (φ₁ ≫ locF (φ₁.hom c₀')) ≫ c) (opEt Uo) R q ((φ₁ ≫ locF (φ₁.hom c₀')).hom (X - C a)) * e q :=
  letI : Algebra B₁ (PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) := (toPiQ.comp (bW (Spec.map φ₁ ≫ c) (opEt Uo) R).hom).toAlgebra
  (exists_Hg (isUnit_rho c R hG₀ hdvd hGc) (isUnit_rho c R hG₀ (dvd_refl _) hGt) N).elim fun H hH =>
  ⟨H, hH.1, hH.2, exists_S4 c R hG₀ hle φ₁ (φ₁ ≫ locF (φ₁.hom c₀')) hD₂
    (toDF c φ₁ (φ₁.hom c₀')) d₀ (bW (Spec.map φ₁ ≫ c) (opEt Uo) R (φ₁.hom c₀'))
    (isLocalization_away_toDF c φ₁ (φ₁.hom c₀') (opEt Uo) R) (locF (φ₁.hom c₀')) (toDF_left c φ₁ (φ₁.hom c₀')) (fun _ => rfl) p₁ u₁
    (X_sub_C_ne_zero a) hH.2 hy hz⟩

end S4H'

end RamanujanPetersson.EtPBC.EtKum

end

end


