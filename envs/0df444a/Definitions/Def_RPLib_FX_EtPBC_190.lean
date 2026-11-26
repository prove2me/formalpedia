-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_190
-- name    : RPLib_FX_EtPBC_190
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T02:01:55.163931+00:00
-- url     : https://prove2.me/theorems/8b77b7f0-ad19-5094-b890-9f76c4545e23
-- title:
--   Proper base change for the projective line, library file 190
-- statement:
--   File 190 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_184

/-!
# Proper base change for the projective line, library file 190

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2PP2 =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)

GLOB/REL PLAN v1 stage S4 data: for `G = g₀ c₀' t` (an opaque variable with `hGdef`), the `D_G` and
`D₂ := D₁_{c₀'}` instances (`isAffine_prdG`, `isAffine_prdUo`, Km6 instances), the `D₂` fibre data (ZarCh) and `hD₂`,
`hR₂₁`, then `pp_core` (O2PP1).
* helpers: `dvd_of_Gdef`, `tdvd_of_Gdef`, `ne_zero_of_Gdef`, `hpt_of_ne_zero`, `isUnit_locF_self`, `hzU_of`,
  `hUo_of_range`, `mem_opnDg_or`, `mem_opnDg_prd'`, `nontrivial_of_fpt`;
* **`pp_G`** (DEF): the target class at `D₁` lies in `Gr`, from the S2-S3 output and `c₀'`.
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

section Helpers

end Helpers

section PPG

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {Uo Uz : P.Opens} (h : Uo ≤ Uz) {a : k} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ (c (A1pt k a)))
  (R : P.Etale) [IsAffine R.left] {g₀ : k[X]}
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  (hg₀ : ∀ v : (chEt c (locF (B := CommRingCat.of k[X]) g₀)).left,
    (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v ∈ Uo ∨ (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v = c (A1pt k a))
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  [IsAffine (prd (chEt c φ₁) (opEt Uo)).left]
  (d₀ : chEt c φ₁ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀))
  (hD₁ : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ₁)))
  (hDn₁ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ₁)))
  (hDr₁ : ∀ v : (chEt c φ₁).left, (chEt c φ₁).hom v ∈ Uo ∨ (chEt c φ₁).hom v = (c (A1pt k a)))
  [QuasiCompact ((etPull (opEt Uo).hom).obj R).hom] [IsSeparated ((etPull (opEt Uo).hom).obj R).hom]
  (Λ : Type) [CommRing Λ] (n : ℕ)
  (hn : ∀ y : (opEt Uo).left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt Uo).hom).obj R)) = n)
  [IsAffine ((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))]
  (hW₁ : ∀ (m : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  {N : ℕ} [NeZero N] {ζ0 : k} (hζ0 : IsPrimitiveRoot ζ0 N)

set_option maxHeartbeats 1000000 in
include hg₀ d₀ in
/-- **PP' at `D₁`, `G` generic**: the target class at `D₁` lies in `Gr`. -/
def pp_G (p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))ˣ}
    (hγ₁ : γ₁ ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0) {u₁ : (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))}
    (hu₁ : (γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) ^ d = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))) u₁)
    [Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hAY : algebraMap k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) = gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))
    (hY₀ : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hGal : ∀ b : k, Subsingleton (Gal (c (A1pt k b))))
    {M : ℕ}
    (uS : integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
    (hu : ∀ b : k, c (A1pt k b) ∉ Uo → a ≠ b → uS - algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C a) ^ M ∈
      Ideal.span {algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C b)})
    {c₀' : k[X]} (hc : c₀' ≠ 0) (hca : c₀'.eval a ≠ 0) (hg0 : g₀ ≠ 0) (hg₁ : IsUnit (φ₁.hom g₀)) {e₀ : ℕ}
    (hdvd : liveMod hY₀ (uS : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a) ^ M) ∣ gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) ((X - C a) ^ e₀ * c₀'))
    {zI : PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)}
    (hy : toPiQ ((wm (R := R) (prdMap d₀ (opEt Uo))).appTop (liveMod hY₀ (uS : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a) ^ M))) =
      toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) (X - C a)) ^ M * Function.update (1 : PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) p₁ u₁ *
        (1 - toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) (X - C a)) * zI))
    (hzI : letI : Algebra B₁ (PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) := (toPiQ.comp (bW (Spec.map φ₁ ≫ c) (opEt Uo) R).hom).toAlgebra; IsIntegral B₁ zI)
    (Gr : AddSubgroup (Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2)) (good : P → Prop)
    (hGd : ∀ x, good x → ∀ γ, IsLoc Λ (freeSh Λ R) x γ → γ ∈ Gr)
    (hgood : ∀ x ∈ Uo, good x) (hgoodc : ∀ x ∉ Set.range c, good x)
    (hfin : (Set.range c)ᶜ.Finite) (hclc : ∀ x ∉ Set.range c, IsClosed ({x} : Set P))
    (hclA : ∀ b : k, IsClosed ({c (A1pt k b)} : Set P))
    (hpt : ∀ y : A1 k, y.asIdeal ≠ ⊥ → ∃ b, y = A1pt k b)
    {G : k[X]} (hGdef : G = g₀ * c₀' * (X - C a)) :
    (locC_shortExact (Λ := Λ) (chEt c φ₁) h (c (A1pt k a)) hz hD₁ hDn₁ hDr₁).extClass.comp
      ((theta Λ R n hn (prT (chEt c φ₁) (opEt Uo))).symm
        (kapS hW₁ Λ p₁ (kumD (hζW c φ₁ R hζ0 p₁) (hζWΓ c φ₁ R (ζ0 := ζ0) p₁) hdN hγ₁ hgΛ)))
      (show 1 + 1 = 2 from rfl) ∈ Gr :=
  haveI : IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left :=
    isAffine_prdG c (dvd_of_Gdef hGdef) hg₀ (tdvd_of_Gdef hGdef)
  haveI : Fintype (minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)) := Fintype.ofFinite _
  haveI : DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)) := Classical.decEq _
  haveI : IsAffine (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).left :=
    isAffine_prdUo c _ (hUo_of_range c _ (range_toDF c φ₁ (φ₁.hom c₀') hDr₁) (hzU_of c h hz))
  haveI : Fintype (minimalPrimes Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤)) := Fintype.ofFinite _
  haveI : DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤)) := Classical.decEq _
  haveI := hD₁
  hDn₁.elim fun n₁ =>
  haveI hN₂ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c (φ₁ ≫ locF (φ₁.hom c₀')))) :=
    nonempty_fib_toDF c φ₁ (φ₁.hom c₀') (c (A1pt k a)) n₁ (not_mem_fpt_of_eval_ne_zero c φ₁ n₁ hca)
  hN₂.elim fun n₂ =>
  haveI : Nontrivial (Localization.Away (φ₁.hom c₀')) := nontrivial_of_fpt c φ₁ (φ₁.hom c₀') n₂
  pp_core c h hz R (dvd_of_Gdef hGdef) (opnDg_le c (dvd_of_Gdef hGdef) hg₀ (tdvd_of_Gdef hGdef)) φ₁
    (fun v => mem_opnDg_prd' c h hz (φ₁ ≫ locF (φ₁.hom c₀')) (hg₁.map (locF (φ₁.hom c₀')).hom)
      (isUnit_locF_self (φ₁.hom c₀')) hGdef v) d₀ hD₁ hDn₁ hDr₁
    (subsingleton_fib_toDF c φ₁ (φ₁.hom c₀') (c (A1pt k a))) hN₂ (range_toDF c φ₁ (φ₁.hom c₀') hDr₁)
    (fun v => mem_opnDg_or c (hzU_of c h hz) (φ₁ ≫ locF (φ₁.hom c₀')) (hg₁.map (locF (φ₁.hom c₀')).hom)
      (isUnit_locF_self (φ₁.hom c₀')) hGdef (range_toDF c φ₁ (φ₁.hom c₀') hDr₁) v)
    Λ n hn hW₁ (isDomain_loc_W c _ R) hζ0 (isDomain_loc_W c _ R) p₁ hdN hγ₁ hgΛ hu₁ hc hAY hY₀
    (ne_zero_of_Gdef hg0 hc hGdef) (tdvd_of_Gdef hGdef) hGal uS hu hdvd
    (isUnit_locF_of_dvd_pow (Eq.subst (motive := fun F => (X - C a) ^ e₀ * c₀' ∣ F ^ (e₀ + 1)) hGdef.symm
      (dvd_G_pow g₀ c₀' a e₀)))
    (isUnit_locF_of_dvd (tdvd_of_Gdef hGdef)) hy hzI Gr good hGd hgood hgoodc hfin hclc hclA
    (hpt_of_ne_zero (ne_zero_of_Gdef hg0 hc hGdef) hpt)

end PPG

end RamanujanPetersson.EtPBC.EtKum

end

end


