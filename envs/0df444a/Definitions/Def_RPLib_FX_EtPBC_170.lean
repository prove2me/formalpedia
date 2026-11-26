-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_170
-- name    : RPLib_FX_EtPBC_170
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:07:37.24878+00:00
-- url     : https://prove2.me/theorems/7c5725f6-da78-534e-893f-a840cdfe2d69
-- title:
--   Proper base change for the projective line, library file 170
-- statement:
--   File 170 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
--   * `S4.Def_RP_EtPBC_A_O2P3b`: S4-EtPBC-A, O2 M5 P3b: purity for `H¹(Spec B[1/t], Λ)`
--   * `S4.Def_RP_EtPBC_A_O2K1`: S4-EtPBC-A, O2 M5 N2: the Kummer class `ξ` on `Spec A0[1/s]` restricts to `κ_t` on `Spec B[1/t]`
--   * `S4.Def_RP_EtPBC_A_O2T4f`: S4-EtPBC-A, O2 S5d (O2T4f): `clsD_secSplit`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_140
import Definitions.Def_RPLib_FX_EtPBC_141
import Definitions.Def_RPLib_FX_EtPBC_162

/-!
# Proper base change for the projective line, library file 170

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
* `S4.Def_RP_EtPBC_A_O2P3b`: S4-EtPBC-A, O2 M5 P3b: purity for `H¹(Spec B[1/t], Λ)`
* `S4.Def_RP_EtPBC_A_O2K1`: S4-EtPBC-A, O2 M5 N2: the Kummer class `ξ` on `Spec A0[1/s]` restricts to `κ_t` on `Spec B[1/t]`
* `S4.Def_RP_EtPBC_A_O2T4f`: S4-EtPBC-A, O2 S5d (O2T4f): `clsD_secSplit`
-/

set_option autoImplicit false

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

/-- **Claim D on `P¹`**: every `β ∈ Ext²(Λ[P¹], F)` dies on the open `chart(D(f))` for some `f ≠ 0`. -/
theorem claimD (F : EtSh Λ (P1 k)) (β : Ext (freeSh Λ (etId (P1 k))) F 2) :
    ∃ f : k[X], f ≠ 0 ∧ (Ext.mk₀ (freeMap Λ (toTop (opEt (U' k f))))).comp β (zero_add 2) = 0 := by
  obtain ⟨f, hf0, hf⟩ := chart_dies k l hl m hΛ F β
  refine ⟨f, hf0, ?_⟩
  have e1 : freeMap Λ (toTop (opEt (U' k f))) =
      freeMap Λ (toU' k f) ≫ freeMap Λ (toTop ((etComp (chartEt k).hom).obj (opEt (bOpen f)))) := by
    rw [← freeMap_comp, toTop_ext (toU' k f ≫ toTop _) (toTop (opEt (U' k f)))]
  rw [e1, ← Ext.mk₀_comp_mk₀_assoc]
  exact (congrArg (fun x => (Ext.mk₀ (freeMap Λ (toU' k f))).comp x (zero_add 2)) hf).trans
    (Ext.comp_zero _ _ _ _ _)

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2P3b =====
section

/-!
# S4-EtPBC-A, O2 M5 P3b: purity for `H¹(Spec B[1/t], Λ)`

`B` Dedekind, `Bt = B[1/t]` with `(t)` prime, `K = Frac B`, `N` invertible in `B`, `N • Λ = 0`, `ζ₀ ∈ K` a primitive
`N`-th root of unity, `τ ∈ maxUnram Bt K` with `τ ^ N = t`.

* `etale_away`, `map_genPt_away`: `Spec Bt → Spec B` is etale and maps generic point to generic point;
* `cyc_mem`: the class of a cyclic character `σ ↦ (c σ).val • g` lies in `res H¹(Spec B) + κ(kumChi τ Λ)`;
* **`purity`**, **`purity_exists`**: every `κ ∈ H¹(Spec Bt, Λ)` is `res κ₀ + κ(kumChi τ c)` with `κ₀ ∈ H¹(Spec B, Λ)`,
  `c ∈ Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer RamanujanPetersson.EtPi1
  RamanujanPetersson.EtCompact.GalTrE

section Away

end Away

section Pur

variable {B Bt K : Type} [CommRing B] [IsDedekindDomain B] [CommRing Bt] [IsDedekindDomain Bt] [Algebra B Bt]
  {t : B} [IsLocalization.Away t Bt] (ht : t ≠ 0) (hP : (Ideal.span {t}).IsPrime)
  [Field K] [Algebra B K] [Algebra Bt K] [IsScalarTower B Bt K] [IsFractionRing B K] [IsFractionRing Bt K]
  [Etale (Spec.map (CommRingCat.ofHom (algebraMap B Bt)))]
  {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] (hN : IsUnit (N : B)) (hΛ : ∀ x : Λ, N • x = 0)
  {ζ0 : K} (hζ0 : IsPrimitiveRoot ζ0 N) {τ : (maxUnram Bt K)ˣ}
  (hτ : (τ : maxUnram Bt K) ^ N = algebraMap K (maxUnram Bt K) (algebraMap B K t))

include ht hP hN in
/-- **Purity, explicit form.** -/
theorem purity_exists (κ : H Λ (unitSh Λ (Spec (CommRingCat.of Bt))) 1) :
    ∃ (κ0 : H Λ (unitSh Λ (Spec (CommRingCat.of B))) 1) (c : Λ),
      κ = resLE (Spec.map (CommRingCat.ofHom (algebraMap B Bt))) 1 κ0 +
        kappaL Bt K Λ (kumChi_mul (zetaE_prim Bt hζ0) (zetaE_fix Bt ζ0) (mem_rad_of_pow_eq hτ) (hΛ c))
          (kumChi_isLocallyConstant (zetaE_prim Bt hζ0) τ c) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.1 (purity ht hP hN hΛ hζ0 hτ κ)
  obtain ⟨κ0, rfl⟩ := AddMonoidHom.mem_range.1 hy
  obtain ⟨c, rfl⟩ := AddMonoidHom.mem_range.1 hz
  exact ⟨κ0, c, hyz.symm⟩

end Pur

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2K1 =====
section

/-!
# S4-EtPBC-A, O2 M5 N2: the Kummer class `ξ` on `Spec A0[1/s]` restricts to `κ_t` on `Spec B[1/t]`

`A0 → B` etale, `s ∈ A0`, `As = A0[1/s]`, `t = s|_B`, `Bt = B[1/t]` (so `Spec Bt → Spec As` is etale).

* `etale_as`: `Spec Bt → Spec As` is etale; `map_genPt_of_injective`: an injective map of domains sends generic point
  to generic point;
* `resLE_kum_as` (N2): `res (κ(kumChi ζ γ c)) = κ(kumChi ψζ τ c)` for `γ ^ N = s` over `As`, `τ ^ N = s` over `Bt`;
* **`purity_xi`**: every `κ ∈ H¹(Spec Bt, Λ)` is `res_B κ₀ + res_As ξ(c)`, `ξ(c) = κ(kumChi ζ γ c)` the global Kummer
  class of `s^{1/N}` on `Spec As` (`B` Dedekind, `(t)` prime, `N` invertible in `B`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer RamanujanPetersson.EtPi1
  RamanujanPetersson.EtCompact.GalTrE

section Kas

end Kas

section PurXi

variable {A0 As F B Bt K : Type} [CommRing A0] {s : A0}
  [CommRing As] [IsDomain As] [IsIntegrallyClosed As] [IsNoetherianRing As] [Algebra A0 As]
  [Field F] [Algebra As F] [IsFractionRing As F]
  [CommRing B] [IsDedekindDomain B] [Algebra A0 B]
  [CommRing Bt] [IsDedekindDomain Bt] [Algebra B Bt] [IsLocalization.Away (algebraMap A0 B s) Bt]
  [Algebra As Bt] [Algebra A0 Bt] [IsScalarTower A0 As Bt] [IsScalarTower A0 B Bt]
  [Field K] [Algebra B K] [Algebra Bt K] [IsScalarTower B Bt K] [IsFractionRing B K] [IsFractionRing Bt K]
  [Etale (Spec.map (CommRingCat.ofHom (algebraMap As Bt)))] [Etale (Spec.map (CommRingCat.ofHom (algebraMap B Bt)))]
  (ψ : F →+* K) (hψ : ∀ a : As, ψ (algebraMap As F a) = algebraMap Bt K (algebraMap As Bt a))
  (ht : algebraMap A0 B s ≠ 0) (hP : (Ideal.span {algebraMap A0 B s}).IsPrime)
  {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] (hN : IsUnit (N : B)) (hΛ : ∀ x : Λ, N • x = 0)
  {z : F} (hz : IsPrimitiveRoot z N) {γ : (maxUnram As F)ˣ}
  (hγ : (γ : maxUnram As F) ^ N = algebraMap F (maxUnram As F) (algebraMap As F (algebraMap A0 As s)))

include hψ ht hP hN in
/-- **Purity with the global Kummer class**: `H¹(Spec Bt, Λ) = res H¹(Spec B, Λ) + res ξ(Λ)`. -/
theorem purity_xi (κ : H Λ (unitSh Λ (Spec (CommRingCat.of Bt))) 1) :
    ∃ (κ0 : H Λ (unitSh Λ (Spec (CommRingCat.of B))) 1) (c : Λ),
      κ = resLE (Spec.map (CommRingCat.ofHom (algebraMap B Bt))) 1 κ0 +
        resLE (Spec.map (CommRingCat.ofHom (algebraMap As Bt))) 1
          (kappaL As F Λ (kumChi_mul (zetaE_prim As hz) (zetaE_fix As z) (mem_rad_of_pow_eq hγ) (hΛ c))
            (kumChi_isLocallyConstant (zetaE_prim As hz) γ c)) := by
  have hψs : ψ (algebraMap As F (algebraMap A0 As s)) = algebraMap B K (algebraMap A0 B s) := by
    rw [hψ, ← IsScalarTower.algebraMap_apply A0 As Bt, IsScalarTower.algebraMap_apply A0 B Bt,
      ← IsScalarTower.algebraMap_apply B Bt K]
  obtain ⟨τ, hτ⟩ := exists_tau (t := algebraMap A0 B s) Bt K hN
  have hτ' : (τ : maxUnram Bt K) ^ N = algebraMap K (maxUnram Bt K) (ψ (algebraMap As F (algebraMap A0 As s))) := by
    rw [hψs, hτ]
  obtain ⟨κ0, c, hκ⟩ := purity_exists ht hP hN hΛ (hz.map_of_injective ψ.injective) hτ κ
  refine ⟨κ0, c, hκ.trans ?_⟩
  rw [resLE_kum_as ψ hψ hz hγ hτ' (hΛ c)]

end PurXi

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4f =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4f): `clsD_secSplit`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Split

variable {k : Type} [Field k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

set_option backward.isDefEq.respectTransparency false in
/-- **Splitting off a section**: `Λ[N] ≅ Λ_D ⊞ Λ[N|secV σ]` splits every class with coefficients `Λ[N]`. -/
theorem clsD_secSplit {F : EtSh Λ P} {Nn : (chEt c φ).left.Etale} [IsSeparated Nn.hom]
    (σ : etId (chEt c φ).left ⟶ Nn) (f : freeSh Λ Nn ⟶ (res (chEt c φ).hom Λ).obj F)
    (Y : H Λ ((res (toD1 c φ a).left Λ).obj (freeSh Λ Nn)) 1) :
    clsD c φ a hUz hS f Y =
      clsD c φ a hUz hS (freeMap Λ σ ≫ f) (Y.comp (Ext.mk₀ ((res (toD1 c φ a).left Λ).map
        ((secSplitIso Λ σ).inv ≫ biprod.fst))) (add_zero 1)) +
      clsD c φ a hUz hS (freeMap Λ (opnι Nn (secV σ)) ≫ f) (Y.comp (Ext.mk₀ ((res (toD1 c φ a).left Λ).map
        ((secSplitIso Λ σ).inv ≫ biprod.snd))) (add_zero 1)) := by
  have hf : f = ((secSplitIso Λ σ).inv ≫ biprod.fst) ≫ (freeMap Λ σ ≫ f) +
      ((secSplitIso Λ σ).inv ≫ biprod.snd) ≫ (freeMap Λ (opnι Nn (secV σ)) ≫ f) := by
    conv_lhs => rw [← Iso.inv_hom_id_assoc (secSplitIso Λ σ) f, secSplitIso_hom, biprod.desc_eq]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
  conv_lhs => rw [hf]
  rw [clsD_addF, clsD_comp c φ a hUz hS ((secSplitIso Λ σ).inv ≫ biprod.fst) (freeMap Λ σ ≫ f),
    clsD_comp c φ a hUz hS ((secSplitIso Λ σ).inv ≫ biprod.snd) (freeMap Λ (opnι Nn (secV σ)) ≫ f)]

end Split

end RamanujanPetersson.EtPBC.EtMV

end

end


