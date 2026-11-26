-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_197
-- name    : RPLib_FX_EtPBC_197
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T02:08:32.202327+00:00
-- url     : https://prove2.me/theorems/e32e0bf1-1305-5156-832f-0729f363e00d
-- title:
--   Proper base change for the projective line, library file 197
-- statement:
--   File 197 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2PP3`: S4-EtPBC-A, O2 PP' (O2PP3): PP' at a chart `D₁` from the S2-S3 data
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_190

/-!
# Proper base change for the projective line, library file 197

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2PP3`: S4-EtPBC-A, O2 PP' (O2PP3): PP' at a chart `D₁` from the S2-S3 data
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2PP3 =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP3): PP' at a chart `D₁` from the S2-S3 data

GLOB/REL PLAN v1: `exists_S23_chart_bad` (O2PP3a) on `D₁` with the bad points `b ≠ a` (`c(b) ∉ U₀`), then the
factorisation `c₀ = (X - a)^e₀ c₀'` (`exists_eq_pow_mul_eval_ne_zero`), `G := g₀ c₀' (X - a)`, and `pp_G` (O2PP2).
* **`pp_chart`** (DEF): the target class at `D₁` lies in `Gr`, from the chart data (`hL`, `hLY`, `h1`, `hj₁`, `hj₂`).
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

section PPChart

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
/-- **PP' at a chart `D₁`**: the target class at `D₁` lies in `Gr`, from the S2-S3 chart data. -/
def pp_chart (p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))ˣ}
    (hγ₁ : γ₁ ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0) {u₁ : (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))}
    (hu₁ : (γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) ^ d = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))) u₁)
    [Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hAY : algebraMap k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) = gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))
    (hY₀ : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hGal : ∀ b : k, Subsingleton (Gal (c (A1pt k b))))
    [IsDomain B₁] (ι₀ : CommRingCat.of (Localization.Away g₀) ⟶ B₁) (hd₀ : d₀.left = Spec.map ι₀)
    {L L' : k[X]} {e : ℕ} (hL : L = (X - C a) ^ e * L') (hL' : IsUnit (φ₁.hom L'))
    (hLY : ∀ y : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤), ∃ N : ℕ, IsIntegral k[X] (L ^ N • y))
    (h1 : ∀ x : B₁, ∃ c₀ : k[X], ∃ y : B₁, x = φ₁.hom c₀ + φ₁.hom (X - C a) * y)
    [Finite {b : k // c (A1pt k b) ∉ Uo ∧ b ≠ a}] (hu0 : u₁ ≠ 0) {j : ℕ}
    (hj₁ : ∃ b, algebraMap (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) _ b = toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) (X - C a)) p₁ ^ j * u₁)
    (hj₂ : ∃ b, algebraMap (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) _ b = toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) (X - C a)) p₁ ^ j * u₁⁻¹)
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
  (exists_S23_chart_bad c R φ₁ d₀ ι₀ hd₀ hAY hY₀ hW₁ a hL hL' hLY h1
    (fun b : k => c (A1pt k b) ∉ Uo ∧ b ≠ a) (fun _ hb => hb.2)
    (not_isUnit_t c φ₁ hDn₁) p₁ hu0 hj₁ hj₂).elim fun M hM =>
  hM.elim fun uS hM => hM.elim fun _zI hM => hM.2.2.2.1.elim fun _c₀ hc₀ =>
  (exists_eq_pow_mul_eval_ne_zero hc₀.1 a).elim fun e₀ he₀ => he₀.elim fun c₀' hc₀' =>
  (⟨_, rfl⟩ : ∃ G : k[X], G = g₀ * c₀' * (X - C a)).elim fun _G hGdef =>
  pp_G c h hz R hg₀ φ₁ d₀ hD₁ hDn₁ hDr₁ Λ n hn hW₁ hζ0 p₁ hdN hγ₁ hgΛ hu₁ hAY hY₀ hGal (M := M) uS
    (fun b hbU hab => by exact hM.1 b ⟨hbU, hab.symm⟩) (ne_zero_right_of_eq hc₀'.1 hc₀.1) hc₀'.2 hg0 hg₁ (e₀ := e₀)
    (dvd_map_of_eq (⇑(gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))) hc₀'.1 hc₀.2)
    hM.2.2.2.2 hM.2.1 Gr good hGd hgood hgoodc hfin hclc hclA hpt hGdef

end PPChart

end RamanujanPetersson.EtPBC.EtKum

end

end


