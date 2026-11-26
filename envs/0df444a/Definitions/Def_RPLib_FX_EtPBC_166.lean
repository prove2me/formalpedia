-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_166
-- name    : RPLib_FX_EtPBC_166
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:41:39.978262+00:00
-- url     : https://prove2.me/theorems/681af250-7051-5950-b1f4-21717b5162f2
-- title:
--   Proper base change for the projective line, library file 166
-- statement:
--   File 166 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Gl3d`: S4-EtPBC-A, O2 GLOB (O2Gl3d): the core step `D₁ → D₂ → D_G` (generic form)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_158
import Definitions.Def_RPLib_FX_EtPBC_159

/-!
# Proper base change for the projective line, library file 166

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Gl3d`: S4-EtPBC-A, O2 GLOB (O2Gl3d): the core step `D₁ → D₂ → D_G` (generic form)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Gl3d =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl3d): the core step `D₁ → D₂ → D_G` (generic form)

* **`core₁₂`**: for chart nbhds `D₁ = chEt c φ₁`, `D₂ = chEt c φ₂`, any `dm : D₂ ⟶ D₁`, a piece `p₁` of `W₁` with a
  UNIQUE piece `p₂` of `W₂` over it, and the inputs of `uk_diff` at `(D₂, p₂)` (with `u := Ψ u₁`):
  `ε(D₁) ∘ θ₁⁻¹ (kapS p₁ (kumD γ₁)) = ε(D₂) ∘ Λ[m]^* (θ'⁻¹ c_Y)`.
  Proof: `locCls_kapS_chart` (O2PPTd) with `χ₂ q := if q = p₂ then kumD (γ₂ q) else 0`, `sum_kapS_eq_single` (O2PPTc),
  then `uk_diff` (O2UKd2).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Core

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  {B₂ : CommRingCat.{0}} (φ₂ : CommRingCat.of k[X] ⟶ B₂) [Etale (Spec.map φ₂ ≫ c)]
  {Uo Uz : P.Opens} (h : Uo ≤ Uz) {a : k} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a))
  (hG : Subsingleton (Gal (c (A1pt k a))))
  (R : P.Etale) [IsAffine R.left] (dm : chEt c φ₂ ⟶ chEt c φ₁)
  (hD₁ : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ₁)))
  (hDn₁ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ₁)))
  (hDr₁ : ∀ v : (chEt c φ₁).left, (chEt c φ₁).hom v ∈ Uo ∨ (chEt c φ₁).hom v = c (A1pt k a))
  (hD₂ : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ₂)))
  (hDn₂ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ₂)))
  (hDr₂ : ∀ v : (chEt c φ₂).left, (chEt c φ₂).hom v ∈ Uo ∨ (chEt c φ₂).hom v = c (A1pt k a))
  [QuasiCompact ((etPull (opEt Uo).hom).obj R).hom] [IsSeparated ((etPull (opEt Uo).hom).obj R).hom]
  (Λ : Type) [CommRing Λ] (n : ℕ)
  (hn : ∀ y : (opEt Uo).left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt Uo).hom).obj R)) = n)
  [IsAffine ((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))]
  (hW₁ : ∀ (m : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [IsAffine ((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤))]
  (hW₂ : ∀ (m : Ideal Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  {N : ℕ} [NeZero N] {ζ0 : k} (hζ0 : IsPrimitiveRoot ζ0 N)
  {T' : P.Etale} (τ' : T' ⟶ opEt Uo) (m : prd (chEt c φ₂) (opEt Uo) ⟶ T')
  (hm : m ≫ τ' = prT (chEt c φ₂) (opEt Uo))
  [IsAffine ((etPull T'.hom).obj R).left] [IsNoetherianRing Γ(((etPull T'.hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull T'.hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤))]
  (hY : ∀ (m : Ideal Γ(((etPull T'.hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  {ζY : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), (maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))}
  (hζY : ∀ Q, IsPrimitiveRoot (ζY Q) N)
  (hζΓY : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))), σ (ζY Q) = ζY Q)

set_option maxHeartbeats 1000000 in
include hG hz hDr₁ hDr₂ hm hζ0 in
/-- **The core step** `D₁ → D₂ → D_G` (generic in `φ₁ φ₂ dm T' τ' m`). (A `def`, see O2Gl2k.) -/
def core₁₂ (p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))ˣ}
    (hγ₁ : γ₁ ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) d)
    {γ₂ : ∀ q : minimalPrimes Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤), (maxUnram (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1) (FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1)))ˣ}
    (hγ₂ : ∀ q, γ₂ q ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1) (FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1)))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0) {u₁ : (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))}
    (hu₁ : (γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) ^ d = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))) u₁)
    (hγ₂u : ∀ q : minimalPrimes Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤), (p₁ : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap dm (opEt Uo))) q) →
      ∀ Ψ : (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)) →+* (FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1)),
      (∀ a : Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤), Ψ (algebraMap _ _ (Ideal.Quotient.mk p₁.1 a)) =
        algebraMap _ _ (Ideal.Quotient.mk q.1 ((wm (R := R) (prdMap dm (opEt Uo))).appTop a))) →
      (γ₂ q : (maxUnram (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1) (FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1)))) ^ d = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1) (FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1))) (Ψ u₁))
    (p₂ : minimalPrimes Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤)) (hp₂ : (p₁ : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap dm (opEt Uo))) p₂))
    (huq : ∀ q : minimalPrimes Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤), (p₁ : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap dm (opEt Uo))) q) → q = p₂)
    (Ψ : (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)) →+* (FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₂.1)))
    (hΨ : ∀ a : Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤), Ψ (algebraMap _ _ (Ideal.Quotient.mk p₁.1 a)) =
      algebraMap _ _ (Ideal.Quotient.mk p₂.1 ((wm (R := R) (prdMap dm (opEt Uo))).appTop a)))
    {β : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), (maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))ˣ}
    (hβ : ∀ Q, β Q ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))) d)
    {K : Type} [Field K] (χ : B₂ →+* K)
    (hχ : (chEt c φ₂).hom (⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩ : Spec B₂) = c (A1pt k a))
    {g : B₂[X]} (hg : g.Monic) (hgn : 0 < g.natDegree) {t : B₂} (ht : χ t = 0) (hd : IsUnit (d : B₂))
    {e : ∀ q : minimalPrimes Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤), (FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1))}
    (he : ∀ q, g.eval₂ (bK (Spec.map φ₂ ≫ c) (opEt Uo) R q) (e q) = 0)
    (sY : Γ(((etPull T'.hom).obj R).left, ⊤)) (hs : (wm (R := R) m).appTop sY = sXW c φ₂ R ζ0)
    (hzY : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), ζY Q = algebraMap _ (maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))
      (algebraMap (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 sY)))
    {Hg : Γ(((etPull T'.hom).obj R).left, ⊤)} (hH : IsUnit Hg)
    (hβH : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), (β Q : (maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))) ^ d =
      algebraMap _ (maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1))) (algebraMap (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 Hg)))
    (cY : H Λ (unitSh Λ ((etPull T'.hom).obj R).left) 1)
    (hcY : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), resLE (piHom (piEquiv hY) Q) 1 cY =
      kappaLH (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)) Λ (kumD (hζY Q) (hζΓY Q) hdN (hβ Q) hgΛ))
    (hHp : algebraMap (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₂.1) (FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₂.1)) (Ideal.Quotient.mk p₂.1 ((wm (R := R) m).appTop Hg)) =
      Ψ u₁ * (1 + bK (Spec.map φ₂ ≫ c) (opEt Uo) R p₂ t * e p₂))
    (hHq : ∀ q, q ≠ p₂ → algebraMap (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1) (FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1))
      (Ideal.Quotient.mk q.1 ((wm (R := R) m).appTop Hg)) = 1 + bK (Spec.map φ₂ ≫ c) (opEt Uo) R q t * e q) :
    (locC_shortExact (Λ := Λ) (chEt c φ₁) h (c (A1pt k a)) hz hD₁ hDn₁ hDr₁).extClass.comp
      ((theta Λ R n hn (prT (chEt c φ₁) (opEt Uo))).symm
        (kapS hW₁ Λ p₁ (kumD (hζW c φ₁ R hζ0 p₁) (hζWΓ c φ₁ R (ζ0 := ζ0) p₁) hdN hγ₁ hgΛ)))
      (show 1 + 1 = 2 from rfl) =
    (locC_shortExact (Λ := Λ) (chEt c φ₂) h (c (A1pt k a)) hz hD₂ hDn₂ hDr₂).extClass.comp
      ((Ext.mk₀ (freeMap Λ m)).comp ((theta Λ R n hn τ').symm cY) (zero_add 1))
      (show 1 + 1 = 2 from rfl) :=
  (locCls_kapS_chart c φ₁ φ₂ h hz R dm hD₁ hDn₁ hDr₁ hD₂ hDn₂ hDr₂ Λ n hn hW₁ hW₂ p₁ hζ0 hdN hγ₁ hγ₂ hgΛ hu₁ hγ₂u
    (fun q => if q = p₂ then kumD (hζW c φ₂ R hζ0 q) (hζWΓ c φ₂ R (ζ0 := ζ0) q) hdN (hγ₂ q) hgΛ else 0)
    (fun q hq => if_pos (huq q hq))
    (fun q hq => if_neg fun (e : q = p₂) => hq (e ▸ hp₂))).trans <|
  (congrArg (fun x => (locC_shortExact (Λ := Λ) (chEt c φ₂) h (c (A1pt k a)) hz hD₂ hDn₂ hDr₂).extClass.comp
      ((theta Λ R n hn (prT (chEt c φ₂) (opEt Uo))).symm x) (show 1 + 1 = 2 from rfl))
    ((sum_kapS_eq_single hW₂ Λ
      (fun q => if q = p₂ then kumD (hζW c φ₂ R hζ0 q) (hζWΓ c φ₂ R (ζ0 := ζ0) q) hdN (hγ₂ q) hgΛ else 0) p₂
      fun _q hq => if_neg hq).trans (congrArg (fun x => kapS hW₂ Λ p₂ x) (if_pos rfl)))).trans <|
  uk_diff c φ₂ h hz hG hD₂ hDn₂ hDr₂ R hW₂ Λ (hζW c φ₂ R hζ0) (hζWΓ c φ₂ R (ζ0 := ζ0)) n hn τ' m hm hY hζY hζΓY
    p₂ hdN (hγ₂ p₂) hβ hgΛ χ hχ hg hgn ht hd he (sXW c φ₂ R ζ0) sY hs (ζW_eq c φ₂ R hζ0 p₂) hzY
    (hγ₂u p₂ hp₂ Ψ hΨ) hH hβH cY hcY hHp hHq

end Core

end RamanujanPetersson.EtPBC.EtKum

end

end


