-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_172
-- name    : RPLib_FX_EtPBC_172
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:01:27.495723+00:00
-- url     : https://prove2.me/theorems/127e1a87-8ef9-5b72-b8d0-d29ac22c3b09
-- title:
--   Proper base change for the projective line, library file 172
-- statement:
--   File 172 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Rel7`: S4-EtPBC-A, O2 REL (O2Rel7): the relation at `c(a)` lies in the localized subgroup
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_152
import Definitions.Def_RPLib_FX_EtPBC_165

/-!
# Proper base change for the projective line, library file 172

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Rel7`: S4-EtPBC-A, O2 REL (O2Rel7): the relation at `c(a)` lies in the localized subgroup
-/

set_option autoImplicit false

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

end BadPt

section RelGlob

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  (Λ : Type) [CommRing Λ] (n : ℕ)
  (hn : ∀ y : (opEt Uo).left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt Uo).hom).obj R)) = n)
  {N : ℕ} [NeZero N] {ζ0 : k} (hζ0 : IsPrimitiveRoot ζ0 N)
  [IsAffine ((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤))]
  (hY : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))

set_option maxHeartbeats 1000000 in
/-- **The relation at `c(a)` lies in `Gr`** (`term_mem_cofinite` at `U₀ := c(D(G))`, bad points by `bad_term_at`). -/
def rel_glob
    [Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hAY : algebraMap k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) = gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))
    (hY₀ : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    {a : k} {M : ℕ} (hG0 : G ≠ 0) (hGt : X - C a ∣ G)
    (hGal : ∀ b : k, Subsingleton (Gal (c (A1pt k b))))
    (uS : integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
    (hu : ∀ b : k, c (A1pt k b) ∉ Uo → a ≠ b → uS - algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C a) ^ M ∈
      Ideal.span {algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C b)})
    {Hg : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)}
    (hH : Hg * (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
        (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a)) ^ M =
      (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
        (liveMod hY₀ (uS : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a) ^ M)))
    {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {β : ∀ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), (maxUnram (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)))ˣ}
    (hβ : ∀ Q, β Q ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0)
    (hβH : ∀ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), (β Q : (maxUnram (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)))) ^ d =
      algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1))) (algebraMap (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 Hg)))
    (Gr : AddSubgroup (Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2)) (good : P → Prop)
    (hGd : ∀ x, good x → ∀ γ, IsLoc Λ (freeSh Λ R) x γ → γ ∈ Gr)
    (hgood : ∀ x ∈ Uo, good x) (hgoodc : ∀ x ∉ Set.range c, good x)
    (hfin : (Set.range c)ᶜ.Finite) (hclc : ∀ x ∉ Set.range c, IsClosed ({x} : Set P))
    (hclA : ∀ b : k, IsClosed ({c (A1pt k b)} : Set P))
    (hpt : ∀ y : A1 k, G ∈ y.asIdeal → ∃ b, y = A1pt k b)
    {S₀ : P.Etale} {Uz₀ : P.Opens} (h₀ : opnDg c G ≤ Uz₀) (hz₀ : ∀ x : P, x ∈ Uz₀ ↔ x ≠ c (A1pt k a))
    (hS₀ : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj S₀))
    (hN₀ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj S₀))
    (hR₀ : ∀ v : S₀.left, S₀.hom v ∈ opnDg c G ∨ S₀.hom v = c (A1pt k a)) :
    (locC_shortExact (Λ := Λ) S₀ h₀ (c (A1pt k a)) hz₀ hS₀ hN₀ hR₀).extClass.comp
      ((Ext.mk₀ (freeMap Λ (prT S₀ (opEt (opnDg c G))))).comp ((Ext.mk₀ (freeMap Λ (sigG c hle))).comp ((theta Λ R n hn (prT (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo))).symm (∑ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), kapS hY Λ Q (kumD (hζW c (locF (B := CommRingCat.of k[X]) G) R hζ0 Q) (hζWΓ c (locF (B := CommRingCat.of k[X]) G) R (ζ0 := ζ0) Q) hdN (hβ Q) hgΛ))) (zero_add 1)) (zero_add 1))
      (show 1 + 1 = 2 from rfl) ∈ Gr :=
  rel_glob_gen c Gr good hGd _ hG0 hgood hgoodc hfin hclc hclA hpt
    (fun b hab hbU => bad_term_at c R hG₀ hle Λ n hn hζ0 hY hAY hY₀ hG0 hGt hab hbU (hGal b) uS (hu b hbU hab) hH hdN
      hβ hgΛ hβH) h₀ hz₀ hS₀ hN₀ hR₀

end RelGlob

end RamanujanPetersson.EtPBC.EtKum

end

end


