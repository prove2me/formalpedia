-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_150
-- name    : RPLib_FX_EtPBC_150
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:39:33.720472+00:00
-- url     : https://prove2.me/theorems/72c25e96-719d-540b-9602-333e6db4ce65
-- title:
--   Proper base change for the projective line, library file 150
-- statement:
--   File 150 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2PPTc`: S4-EtPBC-A, O2 GLOB (O2PPTc): transfer of a piece Kummer class along a shrink `D₁ ⟶ D`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_136
import Definitions.Def_RPLib_FX_EtPBC_143

/-!
# Proper base change for the projective line, library file 150

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2PPTc`: S4-EtPBC-A, O2 GLOB (O2PPTc): transfer of a piece Kummer class along a shrink `D₁ ⟶ D`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2PPTc =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTc): transfer of a piece Kummer class along a shrink `D₁ ⟶ D`

GLOB/REL PLAN v1 (5). For a shrink `dm : D₁ ⟶ D` of local-class neighbourhoods of `z` (both with one geometric
point over `z`), with Shapiro isomorphisms `θ` over `opEt Uo`:
* **`locCls_kapS_shrink`**: `ε(D) ∘ θ⁻¹(kapS p (kumD α)) = ε(D₁) ∘ θ₁⁻¹(Σ_{p₁} kapS p₁ (χ₁ p₁))`, where
  `χ₁ p₁ = kumD (γ p₁)` on the pieces of `W₁` over `p` and `0` on the others (`γ p₁ ^ d = u` there).
Proof: `locCls_shrink`, `theta_natural` along `prdMap dm`, `resLE_kapS_kumD_sum` (O2PPTb) along `wm (prdMap dm)`.
* **`piece_eq_of_away`**: under a localization `A → A[1/s]` two minimal primes over the same prime agree (Zariski
  shrinks never split pieces); **`ker_kerMap`**: `ker (kerMap f p₁) = comap f p₁`;
* **`sum_kapS_eq_single`** / **`sum_kapS_eq_zero`**: collapsing `Σ kapS Q (χ Q)` when at most one `χ Q ≠ 0`.
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

section Away

end Away

section KerMap

end KerMap

section Single

end Single

section PPTc

variable {P : Scheme.{0}} {Uo Uz : P.Opens} (h : Uo ≤ Uz) {z : P} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ z)
  {D D₁ : P.Etale} (dm : D₁ ⟶ D)
  (hD : Subsingleton ((geomPtAt z).point.fiber.obj D)) (hDn : Nonempty ((geomPtAt z).point.fiber.obj D))
  (hDr : ∀ v : D.left, D.hom v ∈ Uo ∨ D.hom v = z)
  (hD₁ : Subsingleton ((geomPtAt z).point.fiber.obj D₁)) (hDn₁ : Nonempty ((geomPtAt z).point.fiber.obj D₁))
  (hDr₁ : ∀ v : D₁.left, D₁.hom v ∈ Uo ∨ D₁.hom v = z)
  (R : P.Etale) [QuasiCompact ((etPull (opEt Uo).hom).obj R).hom] [IsSeparated ((etPull (opEt Uo).hom).obj R).hom]
  (Λ : Type) [CommRing Λ] (n : ℕ)
  (hn : ∀ y : (opEt Uo).left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt Uo).hom).obj R)) = n)
  [IsAffine ((etPull (prd D (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))]
  (hW : ∀ (m : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [IsAffine ((etPull (prd D₁ (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤))]
  (hW₁ : ∀ (m : Ideal Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))

set_option maxHeartbeats 1000000 in
/-- **Transfer of a piece Kummer class along a shrink `dm : D₁ ⟶ D`.** (A `def`: `.olean` export folds theorem
  types, too slow on this statement.) -/
def locCls_kapS_shrink (p : minimalPrimes Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)) {N : ℕ} [NeZero N]
    {ζ : maxUnram (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))))}
    (hζ : IsPrimitiveRoot ζ N)
    (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)))))),
      σ ζ = ζ)
    {ζ₁ : ∀ p₁ : minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤), maxUnram (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))}
    (hζ₁ : ∀ p₁, IsPrimitiveRoot (ζ₁ p₁) N)
    (hζΓ₁ : ∀ p₁ : minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤),
      ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))), σ (ζ₁ p₁) = ζ₁ p₁)
    {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {α : (maxUnram (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)))))ˣ}
    (hα : α ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)))
      (FractionRing (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)))))) d)
    {γ : ∀ p₁ : minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤), (maxUnram (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))ˣ}
    (hγ : ∀ p₁, γ p₁ ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0)
    {u : FractionRing (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)))} (sX : Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)) (sX₁ : Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤))
    (hzX : ζ = algebraMap _ (maxUnram (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)))))
      (algebraMap (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))))
        (Ideal.Quotient.mk (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)) sX)))
    (hz₁ : ∀ p₁ : minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤), ζ₁ p₁ =
      algebraMap _ (maxUnram (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)))
        (algebraMap (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)) (Ideal.Quotient.mk p₁.1 sX₁)))
    (hs : (wm (R := R) (prdMap dm (opEt Uo))).appTop sX = sX₁)
    (hu : (α : maxUnram (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))))) ^ d =
      algebraMap _ (maxUnram (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))))) u)
    (hγu : ∀ p₁ : minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤), (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap dm (opEt Uo))) p₁) →
      ∀ Ψ : FractionRing (Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤))) →+* FractionRing (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1),
      (∀ a : Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤), Ψ (algebraMap _ _ (Ideal.Quotient.mk (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)) a)) =
        algebraMap _ _ (Ideal.Quotient.mk p₁.1 ((wm (R := R) (prdMap dm (opEt Uo))).appTop a))) →
      (γ p₁ : maxUnram (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))) ^ d =
        algebraMap _ (maxUnram (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) (FractionRing (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))) (Ψ u))
    (χ₁ : ∀ p₁ : minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤), ChL (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p₁ : Ideal Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤)))
      (FractionRing (Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p₁ : Ideal Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤)))) Λ)
    (hχ₁ : ∀ p₁ : minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤), (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap dm (opEt Uo))) p₁) →
      χ₁ p₁ = kumD (hζ₁ p₁) (hζΓ₁ p₁) hdN (hγ p₁) hgΛ)
    (hχ₀ : ∀ p₁ : minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤), ¬ (p : Ideal Γ(((etPull (prd D (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap dm (opEt Uo))) p₁) → χ₁ p₁ = 0) :
    (locC_shortExact (Λ := Λ) D h z hz hD hDn hDr).extClass.comp
      ((theta Λ R n hn (prT D (opEt Uo))).symm (kapS hW Λ p (kumD hζ hζΓ hdN hα hgΛ)))
      (show 1 + 1 = 2 from rfl) =
    (locC_shortExact (Λ := Λ) D₁ h z hz hD₁ hDn₁ hDr₁).extClass.comp
      ((theta Λ R n hn (prT D₁ (opEt Uo))).symm (∑ p₁ : minimalPrimes Γ(((etPull (prd D₁ (opEt Uo)).hom).obj R).left, ⊤), kapS hW₁ Λ p₁ (χ₁ p₁)))
      (show 1 + 1 = 2 from rfl) := by
  refine (locCls_shrink h dm (locC_shortExact (Λ := Λ) D₁ h z hz hD₁ hDn₁ hDr₁) _ _).trans ?_
  refine congrArg (fun x => (locC_shortExact (Λ := Λ) D₁ h z hz hD₁ hDn₁ hDr₁).extClass.comp x
    (show 1 + 1 = 2 from rfl)) ?_
  apply (theta Λ R n hn (prT D₁ (opEt Uo))).injective
  refine (theta_natural Λ R n hn (prdMap dm (opEt Uo)) (prdMap_prT dm (opEt Uo)) _).trans ?_
  refine (congrArg (resLE (wm (R := R) (prdMap dm (opEt Uo))) 1) (AddEquiv.apply_symm_apply _ _)).trans ?_
  refine Eq.trans ?_ (AddEquiv.apply_symm_apply _ _).symm
  exact resLE_kapS_kumD_sum hW hW₁ Λ (wm (R := R) (prdMap dm (opEt Uo))) p hζ hζΓ hζ₁ hζΓ₁ hdN hα hγ hgΛ sX sX₁ hzX hz₁ hs hu hγu χ₁ hχ₁ hχ₀

end PPTc

end RamanujanPetersson.EtPBC.EtKum

end

end


