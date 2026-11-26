-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_206
-- name    : RPLib_FX_EtPBC_206
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T02:43:59.769788+00:00
-- url     : https://prove2.me/theorems/d835daf8-adba-59ef-9df9-e460fe4994cd
-- title:
--   Proper base change for the projective line, library file 206
-- statement:
--   File 206 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2PP4d`: S4-EtPBC-A, O2 PP' (O2PP4d): PP' at `D` through a chart `dm : D₁ ⟶ D` (generic `D₁`)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_200

/-!
# Proper base change for the projective line, library file 206

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2PP4d`: S4-EtPBC-A, O2 PP' (O2PP4d): PP' at `D` through a chart `dm : D₁ ⟶ D` (generic `D₁`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2PP4d =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4d): PP' at `D` through a chart `dm : D₁ ⟶ D` (generic `D₁`)

GLOB/REL PLAN v1 stage S1 with `D₁` generic (`φ₁`, `dm`, `d₀` opaque): transfer the class to the pieces `p₁` of `W₁`
(`locCls_kapS_chart`, O2PPTd; one radical per piece by `exists_gam`), and on each piece over `p` apply `pp_term` (O2PP4c)
with the field map `Ψ` from `hpsi`; the other pieces carry `0`.
* generic: `comp_symm_cases_mem`, `exists_cases_fun`, `isDomain_locF`; chart: `ne_zero_of_eval_ne_zero`;
* **`pp_DD1`** (DEF): the target class `ε(D)∘θ⁻¹(kapS p (kumD α))` lies in `Gr`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

open scoped nonZeroDivisors

universe w v u

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Cases

end Cases

section ChartNZ

end ChartNZ

section PPDD1

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

variable {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
  [IsAffine (prd (chEt c φ) (opEt Uo)).left] (dm : chEt c φ₁ ⟶ chEt c φ)
  (hD : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
  (hDn : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
  (hDr : ∀ v : (chEt c φ).left, (chEt c φ).hom v ∈ Uo ∨ (chEt c φ).hom v = (c (A1pt k a)))
  [IsAffine ((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))]
  (hW : ∀ (m : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))

set_option maxHeartbeats 4000000 in
include hg₀ hD₁ hDn₁ hDr₁ hW₁ in
/-- **PP' at `D` through `dm : D₁ ⟶ D`**: PPT transfer, then `pp_term` on the pieces over `p`. -/
def pp_DD1 (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {α : (maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))))ˣ}
    (hα : α ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0) {u : FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))}
    (hu : (α : maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))))) ^ d = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))))) u)
    [IsAlgClosed k] {x y : Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)}
    (hx0 : Ideal.Quotient.mk p.1 x ≠ 0) (hy0 : Ideal.Quotient.mk p.1 y ≠ 0) (hu0 : u ≠ 0)
    (hu_eq : u = algebraMap (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) _ (Ideal.Quotient.mk p.1 x) /
      algebraMap (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) _ (Ideal.Quotient.mk p.1 y))
    {cx cy cx' cy' : k[X]} {ex ey : ℕ}
    (hxd : Ideal.Quotient.mk p.1 x ∣ Ideal.Quotient.mk p.1 (gamMap (shG c φ (Uo := Uo) R) cx))
    (hyd : Ideal.Quotient.mk p.1 y ∣ Ideal.Quotient.mk p.1 (gamMap (shG c φ (Uo := Uo) R) cy))
    (hcx : cx = (X - C a) ^ ex * cx') (hcy : cy = (X - C a) ^ ey * cy')
    (hcx₁ : IsUnit (φ₁.hom cx')) (hcy₁ : IsUnit (φ₁.hom cy'))
    (hpsi : ∀ p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤), (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap dm (opEt Uo))) p₁) →
      ∃ Ψ : FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) →+* FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1), ∀ a' : Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤),
        Ψ (algebraMap _ _ (Ideal.Quotient.mk p.1 a')) =
          algebraMap _ _ (Ideal.Quotient.mk p₁.1 ((wm (R := R) (prdMap dm (opEt Uo))).appTop a')))
    [Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hAY : algebraMap k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) = gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))
    (hY₀ : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hGal : ∀ b : k, Subsingleton (Gal (c (A1pt k b))))
    [IsDomain B₁] (ι₀ : CommRingCat.of (Localization.Away g₀) ⟶ B₁) (hd₀ : d₀.left = Spec.map ι₀)
    {L L' : k[X]} {e : ℕ} (hL : L = (X - C a) ^ e * L') (hL' : IsUnit (φ₁.hom L'))
    (hLY : ∀ y : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤), ∃ N : ℕ, IsIntegral k[X] (L ^ N • y))
    [Finite {b : k // c (A1pt k b) ∉ Uo ∧ b ≠ a}] (hg0 : g₀ ≠ 0) (hg₁ : IsUnit (φ₁.hom g₀))
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
  (exists_gam hW hW₁ (wm (R := R) (prdMap dm (opEt Uo))) p hu).elim fun _ hγ =>
  (exists_cases_fun (fun p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) => (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap dm (opEt Uo))) p₁))
    (fun p₁ => kumD (hζW c φ₁ R hζ0 p₁) (hζWΓ c φ₁ R (ζ0 := ζ0) p₁) hdN (hγ.1 p₁) hgΛ)).elim fun χ₁ hχ =>
  mem_of_eq_mem (locCls_kapS_chart c φ φ₁ h hz R dm hD hDn hDr hD₁ hDn₁ hDr₁ Λ n hn hW hW₁ p hζ0 hdN hα hγ.1 hgΛ hu
      hγ.2 χ₁ hχ.1 hχ.2)
    (comp_symm_sum_mem _ _ _ Gr _ fun p₁ =>
      comp_symm_cases_mem _ _ _ Gr ((p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap dm (opEt Uo))) p₁))
        (kapS hW₁ Λ p₁) (χ₁ p₁)
        (kumD (hζW c φ₁ R hζ0 p₁) (hζWΓ c φ₁ R (ζ0 := ζ0) p₁) hdN (hγ.1 p₁) hgΛ) (hχ.1 p₁) (hχ.2 p₁) fun hp =>
      (hpsi p₁ hp).elim fun Ψ hΨ =>
      pp_term c h hz R hg₀ φ₁ d₀ hD₁ hDn₁ hDr₁ Λ n hn hW₁ hζ0 p₁ hdN φ dm p hx0 hy0 hu0 hu_eq hxd hyd hcx hcy
        hcx₁ hcy₁ Ψ hΨ (hγ.1 p₁) hgΛ (hγ.2 p₁ hp Ψ hΨ) hAY hY₀ hGal ι₀ hd₀ hL hL' hLY hg0 hg₁
        Gr good hGd hgood hgoodc hfin hclc hclA hpt)

end PPDD1

end RamanujanPetersson.EtPBC.EtKum

end

end


