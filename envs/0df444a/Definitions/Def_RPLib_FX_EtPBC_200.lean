-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_200
-- name    : RPLib_FX_EtPBC_200
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T02:39:28.463523+00:00
-- url     : https://prove2.me/theorems/7ec37dfc-04b1-5440-8036-3789250e23b0
-- title:
--   Proper base change for the projective line, library file 200
-- statement:
--   File 200 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2T4e`: S4-EtPBC-A, O2 S5d (O2T4e): `clsD_addF`, `clsD_graph`
--   * `S4.Def_RP_EtPBC_A_O2PP4c`: S4-EtPBC-A, O2 PP' (O2PP4c): PP' at a chart `D₁ ⟶ D` for one piece `p₁` over `p`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_194
import Definitions.Def_RPLib_FX_EtPBC_197

/-!
# Proper base change for the projective line, library file 200

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2T4e`: S4-EtPBC-A, O2 S5d (O2T4e): `clsD_addF`, `clsD_graph`
* `S4.Def_RP_EtPBC_A_O2PP4c`: S4-EtPBC-A, O2 PP' (O2PP4c): PP' at a chart `D₁ ⟶ D` for one piece `p₁` over `p`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2T4e =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4e): `clsD_addF`, `clsD_graph`
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

section GenAddF
universe w v₁ u₁ v₂ u₂ v₃ u₃

end GenAddF

section Split

end Split

section Graph

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

set_option backward.isDefEq.respectTransparency false in
/-- **The graph summand is a point class**: `clsD (Λ[Γ_s] ≫ resFreeIso) Y = pcD c' ∘ Λ[s]`. -/
theorem clsD_graph (hφ : φ.hom.Etale) [IsDedekindDomain B] (ht : φ.hom (X - C a) ≠ 0)
    (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime) {T : P.Etale} (s : chEt c φ ⟶ T)
    (Y : H Λ ((res (toD1 c φ a).left Λ).obj (freeSh Λ (etId (chEt c φ).left))) 1) :
    ∃ c' : Λ, clsD c φ a hUz hS (freeMap Λ (graph s) ≫ (resFreeIso Λ (chEt c φ).hom T).hom) Y =
      (pcD c φ a hN hΛ hUz hS c').comp (Ext.mk₀ (freeMap Λ s)) (add_zero 2) := by
  rw [← secMap_graph, clsD_comp]
  exact clsD_sec c φ a hN hΛ hUz hS hφ ht hP s _

end Graph

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP4c =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4c): PP' at a chart `D₁ ⟶ D` for one piece `p₁` over `p`

GLOB/REL PLAN v1 stage S1 data on `D₁` (`u = x / y`, `x ∣ c_x`, `y ∣ c_y` on the piece `p` of `W`, `c_• = t^e c_•'` with
`c_•'` units on `D₁`, `Ψ` the field map `p ↦ p₁`) give `hj₁`, `hj₂` (`exists_hj_pair'`), `u₁ = Ψ u ≠ 0` and `h1`
(`chart_h1`); then `pp_chart` (O2PP3).
* **`pp_term`** (DEF): the class `ε(D₁)∘θ₁⁻¹(kapS p₁ (kumD γ₁))` lies in `Gr` when `γ₁^d = Ψ u`.
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

section PPTerm

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

set_option maxHeartbeats 4000000 in
include hg₀ in
/-- **PP' for one piece `p₁` of `D₁` over `p`** (S1 data, then `pp_chart`). -/
def pp_term (p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) {d : ℕ} [NeZero d] (hdN : d ∣ N)
    [IsAlgClosed k] {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
    [IsAffine (prd (chEt c φ) (opEt Uo)).left] (dm : chEt c φ₁ ⟶ chEt c φ)
    (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) {x y : Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)}
    (hx0 : Ideal.Quotient.mk p.1 x ≠ 0) (hy0 : Ideal.Quotient.mk p.1 y ≠ 0)
    {u : FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)} (hu0 : u ≠ 0)
    (hu_eq : u = algebraMap (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) _ (Ideal.Quotient.mk p.1 x) /
      algebraMap (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) _ (Ideal.Quotient.mk p.1 y))
    {cx cy cx' cy' : k[X]} {ex ey : ℕ}
    (hxd : Ideal.Quotient.mk p.1 x ∣ Ideal.Quotient.mk p.1 (gamMap (shG c φ (Uo := Uo) R) cx))
    (hyd : Ideal.Quotient.mk p.1 y ∣ Ideal.Quotient.mk p.1 (gamMap (shG c φ (Uo := Uo) R) cy))
    (hcx : cx = (X - C a) ^ ex * cx') (hcy : cy = (X - C a) ^ ey * cy')
    (hcx₁ : IsUnit (φ₁.hom cx')) (hcy₁ : IsUnit (φ₁.hom cy'))
    (Ψ : FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) →+* FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))
    (hΨ : ∀ a' : Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), Ψ (algebraMap _ _ (Ideal.Quotient.mk p.1 a')) =
      algebraMap _ _ (Ideal.Quotient.mk p₁.1 ((wm (R := R) (prdMap dm (opEt Uo))).appTop a')))
    {γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))ˣ}
    (hγ₁ : γ₁ ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0)
    (hu₁ : (γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) ^ d = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))) (Ψ u))
    [Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hAY : algebraMap k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) = gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))
    (hY₀ : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hGal : ∀ b : k, Subsingleton (Gal (c (A1pt k b))))
    [IsDomain B₁] (ι₀ : CommRingCat.of (Localization.Away g₀) ⟶ B₁) (hd₀ : d₀.left = Spec.map ι₀)
    {L L' : k[X]} {e : ℕ} (hL : L = (X - C a) ^ e * L') (hL' : IsUnit (φ₁.hom L'))
    (hLY : ∀ y : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤), ∃ N : ℕ, IsIntegral k[X] (L ^ N • y))
    [Finite {b : k // c (A1pt k b) ∉ Uo ∧ b ≠ a}]
    (hg0 : g₀ ≠ 0) (hg₁ : IsUnit (φ₁.hom g₀))
    (Gr : AddSubgroup (Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2)) (good : P → Prop)
    (hGd : ∀ x, good x → ∀ γ, IsLoc Λ (freeSh Λ R) x γ → γ ∈ Gr)
    (hgood : ∀ x ∈ Uo, good x) (hgoodc : ∀ x ∉ Set.range c, good x)
    (hfin : (Set.range c)ᶜ.Finite) (hclc : ∀ x ∉ Set.range c, IsClosed ({x} : Set P))
    (hclA : ∀ b : k, IsClosed ({c (A1pt k b)} : Set P))
    (hpt : ∀ y : A1 k, y.asIdeal ≠ ⊥ → ∃ b, y = A1pt k b) :
    (locC_shortExact (Λ := Λ) (chEt c φ₁) h (c (A1pt k a)) hz hD₁ hDn₁ hDr₁).extClass.comp
      ((theta Λ R n hn (prT (chEt c φ₁) (opEt Uo))).symm
        (kapS hW₁ Λ p₁ (kumD (hζW c φ₁ R hζ0 p₁) (hζWΓ c φ₁ R (ζ0 := ζ0) p₁) hdN hγ₁ hgΛ)))
      (show 1 + 1 = 2 from rfl) ∈ Gr :=
  haveI : p.1.IsPrime := p.2.1.1
  (exists_hj_pair' p p₁ (wm (R := R) (prdMap dm (opEt Uo))).appTop.hom Ψ hΨ hu_eq hxd hyd hx0 hy0
    (wm_gamMap_pow_mul c R φ φ₁ dm hcx) (wm_gamMap_pow_mul c R φ φ₁ dm hcy)
    (isUnit_gamMap_shG c R φ₁ hcx₁) (isUnit_gamMap_shG c R φ₁ hcy₁)).elim fun hj₁ hj₂ =>
  pp_chart c h hz R hg₀ φ₁ d₀ hD₁ hDn₁ hDr₁ Λ n hn hW₁ hζ0 p₁ hdN hγ₁ hgΛ hu₁ hAY hY₀ hGal ι₀ hd₀ hL hL' hLY
    (fun x' => chart_h1 c φ₁ a hD₁ hDn₁.some x') (fracMap_ne_zero p.1 p₁ Ψ hu0) hj₁ hj₂ hg0 hg₁
    Gr good hGd hgood hgoodc hfin hclc hclA hpt

end PPTerm

end RamanujanPetersson.EtPBC.EtKum

end

end


