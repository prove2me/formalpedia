-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_211
-- name    : RPLib_FX_EtPBC_211
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:10:49.852416+00:00
-- url     : https://prove2.me/theorems/8c1f96f3-6a2b-585a-b7d5-c4ced1a664b6
-- title:
--   Proper base change for the projective line, library file 211
-- statement:
--   File 211 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2PP4e`: S4-EtPBC-A, O2 PP' (O2PP4e): PP' at `D` from the S1 data, shrinking to `D₁ := D_F`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_206

/-!
# Proper base change for the projective line, library file 211

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2PP4e`: S4-EtPBC-A, O2 PP' (O2PP4e): PP' at `D` from the S1 data, shrinking to `D₁ := D_F`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2PP4e =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4e): PP' at `D` from the S1 data, shrinking to `D₁ := D_F`

`pp_DD1` (O2PP4d) at `D₁ := D_F` (`toDF`, `d₀ := toDg`, `ι₀ := liftDg`) for `F` divisible by `g₀`, `L'`, `c_x'`, `c_y'`
with `F(a) ≠ 0`; the field maps `Ψ` by `exists_psi_away` (`isLocalization_away_toDF`).
* **`pp_D1`** (DEF): the target class `ε(D)∘θ⁻¹(kapS p (kumD α))` lies in `Gr`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section PPD1

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {Uo Uz : P.Opens} (h : Uo ≤ Uz) {a : k} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ (c (A1pt k a)))
  (R : P.Etale) [IsAffine R.left] {g₀ : k[X]}
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  (hg₀ : ∀ v : (chEt c (locF (B := CommRingCat.of k[X]) g₀)).left,
    (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v ∈ Uo ∨ (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v = c (A1pt k a))
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
  (hD : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
  (hDn : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
  (hDr : ∀ v : (chEt c φ).left, (chEt c φ).hom v ∈ Uo ∨ (chEt c φ).hom v = (c (A1pt k a)))
  [QuasiCompact ((etPull (opEt Uo).hom).obj R).hom] [IsSeparated ((etPull (opEt Uo).hom).obj R).hom]
  (Λ : Type) [CommRing Λ] (n : ℕ)
  (hn : ∀ y : (opEt Uo).left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt Uo).hom).obj R)) = n)
  [IsAffine ((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))]
  (hW : ∀ (m : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  {N : ℕ} [NeZero N] {ζ0 : k} (hζ0 : IsPrimitiveRoot ζ0 N)

set_option maxHeartbeats 4000000 in
include hg₀ in
/-- **PP' at `D` from the S1 data**: `pp_DD1` at the shrink `D₁ := D_F`. -/
def pp_D1 (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {α : (maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))))ˣ}
    (hα : α ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0) {u : FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))}
    (hu : (α : maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))))) ^ d = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))))) u)
    [IsAlgClosed k] [IsDomain B] {x y : Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)}
    (hx0 : Ideal.Quotient.mk p.1 x ≠ 0) (hy0 : Ideal.Quotient.mk p.1 y ≠ 0) (hu0 : u ≠ 0)
    (hu_eq : u = algebraMap (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) _ (Ideal.Quotient.mk p.1 x) /
      algebraMap (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) _ (Ideal.Quotient.mk p.1 y))
    {cx cy cx' cy' : k[X]} {ex ey : ℕ}
    (hxd : Ideal.Quotient.mk p.1 x ∣ Ideal.Quotient.mk p.1 (gamMap (shG c φ (Uo := Uo) R) cx))
    (hyd : Ideal.Quotient.mk p.1 y ∣ Ideal.Quotient.mk p.1 (gamMap (shG c φ (Uo := Uo) R) cy))
    (hcx : cx = (X - C a) ^ ex * cx') (hcy : cy = (X - C a) ^ ey * cy')
    [Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hAY : algebraMap k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) = gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))
    (hY₀ : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hGal : ∀ b : k, Subsingleton (Gal (c (A1pt k b))))
    {L L' : k[X]} {e : ℕ} (hL : L = (X - C a) ^ e * L')
    (hLY : ∀ y : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤), ∃ N : ℕ, IsIntegral k[X] (L ^ N • y))
    [Finite {b : k // c (A1pt k b) ∉ Uo ∧ b ≠ a}] (hg0 : g₀ ≠ 0)
    {F : k[X]} (hFg : g₀ ∣ F) (hFL : L' ∣ F) (hFx : cx' ∣ F) (hFy : cy' ∣ F) (hFa : F.eval a ≠ 0)
    (Gr : AddSubgroup (Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2)) (good : P → Prop)
    (hGd : ∀ x, good x → ∀ γ, IsLoc Λ (freeSh Λ R) x γ → γ ∈ Gr)
    (hgood : ∀ x ∈ Uo, good x) (hgoodc : ∀ x ∉ Set.range c, good x)
    (hfin : (Set.range c)ᶜ.Finite) (hclc : ∀ x ∉ Set.range c, IsClosed ({x} : Set P))
    (hclA : ∀ b : k, IsClosed ({c (A1pt k b)} : Set P))
    (hpt : ∀ y : A1 k, y.asIdeal ≠ ⊥ → ∃ b, y = A1pt k b) :
    (locC_shortExact (Λ := Λ) (chEt c φ) h (c (A1pt k a)) hz hD hDn hDr).extClass.comp
      ((theta Λ R n hn (prT (chEt c φ) (opEt Uo))).symm
        (kapS hW Λ p (kumD (hζW c φ R hζ0 p) (hζWΓ c φ R (ζ0 := ζ0) p) hdN hα hgΛ)))
      (show 1 + 1 = 2 from rfl) ∈ Gr :=
  haveI : IsAffine (prd (chEt c φ) (opEt Uo)).left :=
    isAffine_prdUo c φ (hUo_of_range c φ hDr (hzU_of c h hz))
  haveI : IsAffine (prd (chEt c (φ ≫ locF (φ.hom F))) (opEt Uo)).left :=
    isAffine_prdUo c _ (hUo_of_range c _ (range_toDF c φ (φ.hom F) hDr) (hzU_of c h hz))
  haveI : Fintype (minimalPrimes Γ(((etPull (prd (chEt c (φ ≫ locF (φ.hom F))) (opEt Uo)).hom).obj R).left, ⊤)) := Fintype.ofFinite _
  haveI : DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c (φ ≫ locF (φ.hom F))) (opEt Uo)).hom).obj R).left, ⊤)) := Classical.decEq _
  haveI := hD
  hDn.elim fun n₀ =>
  haveI hN₁ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c (φ ≫ locF (φ.hom F)))) :=
    nonempty_fib_toDF c φ (φ.hom F) (c (A1pt k a)) n₀ (not_mem_fpt_of_eval_ne_zero c φ n₀ hFa)
  haveI : IsDomain (CommRingCat.of (Localization.Away (φ.hom F))) :=
    isDomain_locF (ne_zero_of_eval_ne_zero c φ n₀ hFa)
  pp_DD1 c h hz R hg₀ (φ ≫ locF (φ.hom F)) (toDg c φ (φ.hom F) g₀ (isUnit_locF_comp_of_dvd φ hFg))
    (subsingleton_fib_toDF c φ (φ.hom F) (c (A1pt k a))) hN₁ (range_toDF c φ (φ.hom F) hDr) Λ n hn
    (isDomain_loc_W c _ R) hζ0 φ (toDF c φ (φ.hom F)) hD hDn hDr hW p hdN hα hgΛ hu hx0 hy0 hu0 hu_eq hxd hyd hcx hcy
    (isUnit_locF_comp_of_dvd φ hFx) (isUnit_locF_comp_of_dvd φ hFy)
    (fun p₁ hp => exists_psi_away (wm (R := R) (prdMap (toDF c φ (φ.hom F)) (opEt Uo))).appTop.hom _ (isLocalization_away_toDF c φ (φ.hom F) (opEt Uo) R) p p₁
      (kerMap (wm (R := R) (prdMap (toDF c φ (φ.hom F)) (opEt Uo))) p₁) (ker_kerMap (wm (R := R) (prdMap (toDF c φ (φ.hom F)) (opEt Uo))) p₁) hp)
    hAY hY₀ hGal (liftDg φ (φ.hom F) g₀ (isUnit_locF_comp_of_dvd φ hFg)) rfl hL (isUnit_locF_comp_of_dvd φ hFL) hLY
    hg0 (isUnit_locF_comp_of_dvd φ hFg) Gr good hGd hgood hgoodc hfin hclc hclA hpt

end PPD1

end RamanujanPetersson.EtPBC.EtKum

end

end


