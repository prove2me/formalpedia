-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_165
-- name    : RPLib_FX_EtPBC_165
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:59:23.1238+00:00
-- url     : https://prove2.me/theorems/9bf188fd-63b0-55e8-b318-a3a9c6e85966
-- title:
--   Proper base change for the projective line, library file 165
-- statement:
--   File 165 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Rel6`: S4-EtPBC-A, O2 REL (O2Rel6): the relation term at a bad point `c(b)` vanishes, for any nbhd `V = U₁ ∪ {c(b)}`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_158

/-!
# Proper base change for the projective line, library file 165

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Rel6`: S4-EtPBC-A, O2 REL (O2Rel6): the relation term at a bad point `c(b)` vanishes, for any nbhd `V = U₁ ∪ {c(b)}`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Rel6 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel6): the relation term at a bad point `c(b)` vanishes, for any nbhd `V = U₁ ∪ {c(b)}`

REL PLAN v2 (s126) + s128 fix. `bad_term_zero'` (O2Bd5) on the chart `D' := D_{G_b}` (`G = (X - C b)^m G_b`,
`G_b(b) ≠ 0`, `exists_eq_pow_mul_eval_ne_zero`), with the chart data of O2Rel4 and `d' := toOpEt D' V`:
* **`bad_term_at`** (DEF): the bad-point input `hk` of `term_mem_cofinite` (O2Rel5) for `x = c(b)`, `U₀ := U₁ = c(D(G))`.
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

section BadAt

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
/-- **The relation term at a bad point `c(b)` vanishes** (any nbhd `V = U₁ ∪ {c(b)}`, any `Uz = {c(b)}ᶜ`). -/
def bad_term_at
    [Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hAY : algebraMap k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) = gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))
    (hY₀ : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    {a b : k} {M : ℕ} (hG0 : G ≠ 0) (hGt : X - C a ∣ G) (hab : a ≠ b) (hbU : c (A1pt k b) ∉ Uo)
    (hGal : Subsingleton (Gal (c (A1pt k b))))
    (uS : integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
    (hu : uS - algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C a) ^ M ∈
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
      algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1))) (algebraMap (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 Hg))) :
    ∀ (V : P.Opens) (_hV : ∀ y : P, y ∈ V ↔ y ∈ opnDg c G ∨ y = c (A1pt k b))
      (Uz : P.Opens) (h : opnDg c G ≤ Uz) (hz : ∀ y : P, y ∈ Uz ↔ y ≠ c (A1pt k b))
      (hS : Subsingleton ((geomPtAt (c (A1pt k b))).point.fiber.obj (opEt V)))
      (hN : Nonempty ((geomPtAt (c (A1pt k b))).point.fiber.obj (opEt V)))
      (hR : ∀ v : (opEt V).left, (opEt V).hom v ∈ opnDg c G ∨ (opEt V).hom v = c (A1pt k b)),
      (locC_shortExact (Λ := Λ) (opEt V) h (c (A1pt k b)) hz hS hN hR).extClass.comp
        ((Ext.mk₀ (freeMap Λ (prT (opEt V) (opEt (opnDg c G))))).comp ((Ext.mk₀ (freeMap Λ (sigG c hle))).comp ((theta Λ R n hn (prT (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo))).symm (∑ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), kapS hY Λ Q (kumD (hζW c (locF (B := CommRingCat.of k[X]) G) R hζ0 Q) (hζWΓ c (locF (B := CommRingCat.of k[X]) G) R (ζ0 := ζ0) Q) hdN (hβ Q) hgΛ))) (zero_add 1)) (zero_add 1))
        (show 1 + 1 = 2 from rfl) = 0 :=
  fun V hV _Uz h hz hS hN hR =>
  (exists_eq_pow_mul_eval_ne_zero hG0 b).elim fun _m hm => hm.elim fun Gb hGb =>
  haveI : IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) Gb)) (opEt Uo)).left := isAffine_badCh c hGb.1 hle hbU
  haveI : Fintype (minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) Gb)) (opEt Uo)).hom).obj R).left, ⊤)) := Fintype.ofFinite _
  haveI : DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) Gb)) (opEt Uo)).hom).obj R).left, ⊤)) := Classical.decEq _
  bad_term_zero' c (fun y hy => (hz y).2 fun e => hbU (e ▸ hy)) hz hGal R hG₀ hle h hS hN hR
    (locF (B := CommRingCat.of k[X]) Gb)
    (toOpEt (chEt c (locF (B := CommRingCat.of k[X]) Gb)) V fun v => (hV _).2 (badCh_r₁ c hGb.1 v))
    (badCh_s c _) (badCh_n c hGb.2) (badCh_r₁ c hGb.1) (badCh_r c hGb.1 hle) (badCh_D' c hGb.1 hbU) Λ n hn hζ0 hY
    hAY hY₀ (badCh_hta hGb.1 hab hGt) uS hu hH hdN hβ hgΛ hβH

end BadAt

end RamanujanPetersson.EtPBC.EtKum

end

end


