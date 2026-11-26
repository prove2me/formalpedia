-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_173
-- name    : RPLib_FX_EtPBC_173
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:59:35.542452+00:00
-- url     : https://prove2.me/theorems/a273dbed-ddf8-57d5-87c7-14e2f2f76b6c
-- title:
--   Proper base change for the projective line, library file 173
-- statement:
--   File 173 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Gl3e`: S4-EtPBC-A, O2 GLOB (O2Gl3e): the core step on the charts
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_052
import Definitions.Def_RPLib_FX_EtPBC_166

/-!
# Proper base change for the projective line, library file 173

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Gl3e`: S4-EtPBC-A, O2 GLOB (O2Gl3e): the core step on the charts
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Gl3e =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl3e): the core step on the charts

* **`exists_psi_away`** (generic): in a localization `G₂ = G₁[1/s]`, a minimal prime `p₁ ≤ σ⁻¹ p₂` gives the field map
  `Ψ : Frac(G₁ ⧸ p₁) → Frac(G₂ ⧸ p₂)` compatible with `σ`;
* **`core_chart`**: `core₁₂` (O2Gl3d) at `D₂ := chEt c (φ₁ ≫ locF (φ₁.hom c₀'))`, `dm := toDF`, `T' := D_G ×_P U₀`
  (`G` generic with `g₀ ∣ G`), `m := mG`, `c_Y := Σ_Q kapS Q (kumD β_Q)`, taking the output of `exists_S4H` (O2Gl2k)
  and roots `β_Q` of `H` as hypotheses; `p₂` (exists_piece_toDF), its uniqueness (piece_unique_away), `Ψ`, the
  radicals `γ₂` (exists_gam) and `χ` (exists_chi) are produced inside.
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

section PsiAway

end PsiAway

section CoreChart

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
include hG hz hDr₁ hR₂ hζ0 d₀ hG₀ in
/-- **The core step on the charts**: `ε(D₁) ∘ θ₁⁻¹ (kapS p₁ (kumD γ₁)) = ε(D₂) ∘ Λ[mG]^* θ_G⁻¹ (Σ_Q kapS Q (kumD β_Q))`.
(A `def`, see O2Gl2k.) -/
def core_chart (p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))ˣ}
    (hγ₁ : γ₁ ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0) {u₁ : (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))}
    (hu₁ : (γ₁ : (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) ^ d = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))) u₁)
    (hc : c₀' ≠ 0) {Hg : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)} (hH : IsUnit Hg)
    {β : ∀ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), (maxUnram (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)))ˣ}
    (hβ : ∀ Q, β Q ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)))) d)
    (hβH : ∀ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), (β Q : (maxUnram (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)))) ^ d =
      algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1))) (algebraMap (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 Hg)))
    {e : ∀ q : minimalPrimes Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤), (FractionRing (Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1))} {g : (Localization.Away (φ₁.hom c₀'))[X]}
    (hg : g.Monic) (hgn : 0 < g.natDegree)
    (he : ∀ q, g.eval₂ (bK (Spec.map (φ₁ ≫ locF (φ₁.hom c₀')) ≫ c) (opEt Uo) R q) (e q) = 0)
    (hHpq : ∀ p₂ : minimalPrimes Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤), (p₁ : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap (toDF c φ₁ (φ₁.hom c₀')) (opEt Uo))) p₂) →
      (∀ Ψ : (FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)) →+* (FractionRing (Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₂.1)),
        (∀ x, Ψ (algebraMap _ _ (Ideal.Quotient.mk p₁.1 x)) =
          algebraMap _ _ (Ideal.Quotient.mk p₂.1 ((wm (R := R) (prdMap (toDF c φ₁ (φ₁.hom c₀')) (opEt Uo))).appTop x))) →
        algebraMap _ (FractionRing (Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₂.1)) (Ideal.Quotient.mk p₂.1 ((wm (R := R) (mG c hle (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) hD₂)).appTop Hg)) =
          Ψ u₁ * (1 + bK (Spec.map (φ₁ ≫ locF (φ₁.hom c₀')) ≫ c) (opEt Uo) R p₂ ((φ₁ ≫ locF (φ₁.hom c₀')).hom (X - C a)) * e p₂)) ∧
      ∀ q, q ≠ p₂ → algebraMap _ (FractionRing (Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1)) (Ideal.Quotient.mk q.1 ((wm (R := R) (mG c hle (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) hD₂)).appTop Hg)) =
        1 + bK (Spec.map (φ₁ ≫ locF (φ₁.hom c₀')) ≫ c) (opEt Uo) R q ((φ₁ ≫ locF (φ₁.hom c₀')).hom (X - C a)) * e q) :
    (locC_shortExact (Λ := Λ) (chEt c φ₁) h (c (A1pt k a)) hz hD₁ hDn₁ hDr₁).extClass.comp
      ((theta Λ R n hn (prT (chEt c φ₁) (opEt Uo))).symm
        (kapS hW₁ Λ p₁ (kumD (hζW c φ₁ R hζ0 p₁) (hζWΓ c φ₁ R (ζ0 := ζ0) p₁) hdN hγ₁ hgΛ)))
      (show 1 + 1 = 2 from rfl) =
    (locC_shortExact (Λ := Λ) (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) h (c (A1pt k a)) hz hS₂ hN₂ hR₂).extClass.comp
      ((Ext.mk₀ (freeMap Λ (mG c hle (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) hD₂))).comp
        ((theta Λ R n hn (prT (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo))).symm
          (∑ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), kapS hY Λ Q (kumD (hζW c (locF (B := CommRingCat.of k[X]) G) R hζ0 Q) (hζWΓ c (locF (B := CommRingCat.of k[X]) G) R (ζ0 := ζ0) Q) hdN (hβ Q) hgΛ))) (zero_add 1))
      (show 1 + 1 = 2 from rfl) :=
  hN₂.elim fun n₂ =>
  (exists_chi c (φ₁ ≫ locF (φ₁.hom c₀')) n₂).elim fun _K hK => hK.elim fun _ hK => hK.elim fun χ hχ =>
  (exists_piece_toDF c R φ₁ hc p₁).elim fun p₂ hp₂ =>
  (exists_psi_away (wm (R := R) (prdMap (toDF c φ₁ (φ₁.hom c₀')) (opEt Uo))).appTop.hom (bW (Spec.map φ₁ ≫ c) (opEt Uo) R (φ₁.hom c₀'))
    (isLocalization_away_toDF c φ₁ (φ₁.hom c₀') (opEt Uo) R) p₁ p₂ (kerMap (wm (R := R) (prdMap (toDF c φ₁ (φ₁.hom c₀')) (opEt Uo))) p₂) (ker_kerMap _ p₂) hp₂).elim
    fun Ψ hΨ =>
  (RamanujanPetersson.EtPBC.EtKum.exists_gam hW₁ hW₂ (wm (R := R) (prdMap (toDF c φ₁ (φ₁.hom c₀')) (opEt Uo))) p₁ hu₁).elim fun _γ₂ hγ₂ =>
  core₁₂ c φ₁ (φ₁ ≫ locF (φ₁.hom c₀')) h hz hG R (toDF c φ₁ (φ₁.hom c₀')) hD₁ hDn₁ hDr₁ hS₂ hN₂ hR₂ Λ n hn hW₁ hW₂ hζ0
    (prT (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)) (mG c hle (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) hD₂) (mG_prT c hle (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) hD₂) hY
    (hζW c (locF (B := CommRingCat.of k[X]) G) R hζ0) (hζWΓ c (locF (B := CommRingCat.of k[X]) G) R (ζ0 := ζ0))
    p₁ hdN hγ₁ hγ₂.1 hgΛ hu₁ hγ₂.2 p₂ hp₂
    (fun _q hq => piece_unique_away (wm (R := R) (prdMap (toDF c φ₁ (φ₁.hom c₀')) (opEt Uo))) _ (isLocalization_away_toDF c φ₁ (φ₁.hom c₀') (opEt Uo) R) p₁ hq hp₂)
    Ψ hΨ hβ χ hχ.1 hg hgn hχ.2 (isUnit_natCast_of_prim (φ₁ ≫ locF (φ₁.hom c₀')) hζ0 hdN) he
    (sXW c (locF (B := CommRingCat.of k[X]) G) R ζ0)
    (wm_mG_sXW c R hG₀ hle (φ₁ ≫ locF (φ₁.hom c₀')) hD₂ (toDF c φ₁ (φ₁.hom c₀') ≫ d₀) ζ0)
    (ζW_eq c (locF (B := CommRingCat.of k[X]) G) R hζ0) hH hβH
    (∑ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), kapS hY Λ Q (kumD (hζW c (locF (B := CommRingCat.of k[X]) G) R hζ0 Q) (hζWΓ c (locF (B := CommRingCat.of k[X]) G) R (ζ0 := ζ0) Q) hdN (hβ Q) hgΛ))
    (resLE_kapS_sum hY Λ (fun Q => (kumD (hζW c (locF (B := CommRingCat.of k[X]) G) R hζ0 Q) (hζWΓ c (locF (B := CommRingCat.of k[X]) G) R (ζ0 := ζ0) Q) hdN (hβ Q) hgΛ)))
    ((hHpq p₂ hp₂).1 Ψ hΨ) (hHpq p₂ hp₂).2

end CoreChart

end RamanujanPetersson.EtPBC.EtKum

end

end


