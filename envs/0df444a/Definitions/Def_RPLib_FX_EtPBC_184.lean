-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_184
-- name    : RPLib_FX_EtPBC_184
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:58:58.040648+00:00
-- url     : https://prove2.me/theorems/da3cf3fa-1dcd-5b95-b483-88e10c83a005
-- title:
--   Proper base change for the projective line, library file 184
-- statement:
--   File 184 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2PP1`: S4-EtPBC-A, O2 PP' (O2PP1): the core of PP' at the chart `D₁` (after stages S2-S3)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_131
import Definitions.Def_RPLib_FX_EtPBC_172
import Definitions.Def_RPLib_FX_EtPBC_180

/-!
# Proper base change for the projective line, library file 184

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2PP1`: S4-EtPBC-A, O2 PP' (O2PP1): the core of PP' at the chart `D₁` (after stages S2-S3)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2PP1 =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP1): the core of PP' at the chart `D₁` (after stages S2-S3)

GLOB/REL PLAN v1 + REL PLAN v2. With the S2-S3 output (`hdvd`, `hy`, `hzI` of `exists_S23_chart`, `c₀ = t^e₀ c₀'`) and
`G := g₀ c₀' t` kept generic: `exists_S4H'` (O2Bd4) gives `H`, `e`, `g`; `exists_root_of_isUnit` (O2KapN) gives the
roots `β_Q`; `core_locU` (O2Gl3f) moves the target to the relation term at `D₂`, which `rel_glob` (O2Rel7) puts in `Gr`.
* **`isUnit_natCast_of_prim_map`**: `d ∣ N` is a unit in any ring receiving `k` (`k` has a primitive `N`-th root);
* **`pp_core`** (DEF): the target class at `D₁` lies in `Gr`.
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

section PPCore

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {Uo Uz : P.Opens} (h : Uo ≤ Uz) {a : k} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ (c (A1pt k a)))
  (hG : Subsingleton (Gal (c (A1pt k a))))
  (R : P.Etale) [IsAffine R.left] {g₀ c₀' G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  [IsAffine (prd (chEt c φ₁) (opEt Uo)).left]
  [IsAffine (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).left]
  (hD₂ : ∀ v : (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).left, (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom v ∈ opnDg c G)
  (d₀ : chEt c φ₁ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀))
  (hD₁ : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ₁)))
  (hDn₁ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ₁)))
  (hDr₁ : ∀ v : (chEt c φ₁).left, (chEt c φ₁).hom v ∈ Uo ∨ (chEt c φ₁).hom v = (c (A1pt k a)))
  (hS₂ : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c (φ₁ ≫ locF (φ₁.hom c₀')))))
  (hN₂ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c (φ₁ ≫ locF (φ₁.hom c₀')))))
  (hR₂ : ∀ v : (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))).left, (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))).hom v ∈ Uo ∨ (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))).hom v = (c (A1pt k a)))
  (hR₂₁ : ∀ v : (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))).left, (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))).hom v ∈ opnDg c G ∨
    (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))).hom v = (c (A1pt k a)))
  [QuasiCompact ((etPull (opEt Uo).hom).obj R).hom] [IsSeparated ((etPull (opEt Uo).hom).obj R).hom]
  (Λ : Type) [CommRing Λ] (n : ℕ)
  (hn : ∀ y : (opEt Uo).left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt Uo).hom).obj R)) = n)
  [IsAffine ((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))]
  (hW₁ : ∀ (m : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [IsAffine ((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤))]
  (hW₂ : ∀ (m : Ideal Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  {N : ℕ} [NeZero N] {ζ0 : k} (hζ0 : IsPrimitiveRoot ζ0 N)
  [IsAffine ((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤))]
  (hY : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))

set_option maxHeartbeats 1000000 in
include h hz hG₀ hle hD₂ d₀ hD₁ hDn₁ hDr₁ hS₂ hN₂ hR₂ hR₂₁ hn hW₁ hW₂ hζ0 hY in
/-- **PP' core at `D₁`**: the target class `ε(D₁) ∘ θ₁⁻¹ (kapS p₁ (kumD γ₁))` lies in `Gr`. -/
def pp_core (p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))ˣ}
    (hγ₁ : γ₁ ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0) {u₁ : (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))}
    (hu₁ : (γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) ^ d = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))) u₁)
    (hc : c₀' ≠ 0)
    [Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hAY : algebraMap k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) = gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))
    (hY₀ : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hG0 : G ≠ 0) (hGt : X - C a ∣ G) (hGal : ∀ b : k, Subsingleton (Gal (c (A1pt k b))))
    {M : ℕ}
    (uS : integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
    (hu : ∀ b : k, c (A1pt k b) ∉ Uo → a ≠ b → uS - algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C a) ^ M ∈
      Ideal.span {algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C b)})
    [Nontrivial (Localization.Away (φ₁.hom c₀'))] {e₀ : ℕ}
    (hdvd : liveMod hY₀ (uS : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a) ^ M) ∣ gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) ((X - C a) ^ e₀ * c₀'))
    (hGc : IsUnit ((locF (B := CommRingCat.of k[X]) G).hom ((X - C a) ^ e₀ * c₀')))
    (hGtU : IsUnit ((locF (B := CommRingCat.of k[X]) G).hom (X - C a)))
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
    (hpt : ∀ y : A1 k, G ∈ y.asIdeal → ∃ b, y = A1pt k b) :
    (locC_shortExact (Λ := Λ) (chEt c φ₁) h (c (A1pt k a)) hz hD₁ hDn₁ hDr₁).extClass.comp
      ((theta Λ R n hn (prT (chEt c φ₁) (opEt Uo))).symm
        (kapS hW₁ Λ p₁ (kumD (hζW c φ₁ R hζ0 p₁) (hζWΓ c φ₁ R (ζ0 := ζ0) p₁) hdN hγ₁ hgΛ)))
      (show 1 + 1 = 2 from rfl) ∈ Gr :=
  (exists_S4H' c R hG₀ hle φ₁ hD₂ d₀ p₁ u₁ hdvd hGc hGtU hy hzI).elim fun _H hHx =>
  hHx.2.2.elim fun _e hex => hex.elim fun _g hgx =>
  (Classical.skolem.1 fun Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) =>
    exists_root_of_isUnit (K := FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1))
      (isUnit_natCast_of_prim_map ((Ideal.Quotient.mk Q.1).comp
        ((gamMap (shG c (locF (B := CommRingCat.of k[X]) G) (Uo := Uo) R)).comp Polynomial.C)) hζ0 hdN)
      (hHx.1.map (Ideal.Quotient.mk Q.1))).elim fun _β hβH =>
  Eq.mpr (congrArg (fun x => x ∈ Gr)
    (core_locU c h hz (hGal a) R hG₀ hle φ₁ hD₂ d₀ hD₁ hDn₁ hDr₁ hS₂ hN₂ hR₂ hR₂₁ Λ n hn hW₁ hW₂ hζ0 hY p₁ hdN hγ₁
      hgΛ hu₁ hc hHx.1 (fun Q => mem_rad_of_pow_eq (hβH Q)) hβH hgx.1 hgx.2.1 hgx.2.2.1 hgx.2.2.2))
    (rel_glob c R hG₀ hle Λ n hn hζ0 hY hAY hY₀ hG0 hGt hGal uS hu hHx.2.1 hdN (fun Q => mem_rad_of_pow_eq (hβH Q))
      hgΛ hβH Gr good hGd hgood hgoodc hfin hclc hclA hpt (hle.trans h) hz hS₂ hN₂ hR₂₁)

end PPCore

end RamanujanPetersson.EtPBC.EtKum

end

end


