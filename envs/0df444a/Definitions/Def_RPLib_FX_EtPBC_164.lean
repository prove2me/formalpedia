-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_164
-- name    : RPLib_FX_EtPBC_164
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:52:39.891066+00:00
-- url     : https://prove2.me/theorems/dfb74c42-a3ef-4d2b-b3ef-30a9f56194e2
-- title:
--   Proper base change for the projective line, library file 164
-- statement:
--   File 164 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Km9c`: S4-EtPBC-A, O2 M6 (O2Km9c): `ext_mem_of_kum` for ANY bijection `Ψ : Ext¹(Λ[D_o], Λ[R]) ≃+ H¹(W)`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_157

/-!
# Proper base change for the projective line, library file 164

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Km9c`: S4-EtPBC-A, O2 M6 (O2Km9c): `ext_mem_of_kum` for ANY bijection `Ψ : Ext¹(Λ[D_o], Λ[R]) ≃+ H¹(W)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Km9c =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km9c): `ext_mem_of_kum` for ANY bijection `Ψ : Ext¹(Λ[D_o], Λ[R]) ≃+ H¹(W)`

Setting of O2Km6 (`D = Spec B` over `𝔸¹ ⊆ P`, `D_o = D ×_P Uo` affine, `R` affine with constant degree `n` over
`D_o`, `W = D_o ×_P R`), plus primitive `N`-th roots of unity `ζ p` on the pieces and `N • Λ = 0`.
(Roots of unity `ζW`, `hζW`, `hζWΓ`: O2Km9a; `hW := isDomain_loc_W ..`: O2Km6. All W-specific terms are hypotheses
here: concrete instance/proof terms inside `kapS` made `lean -o` cost 500+ user-s.)
* **`ext_mem_of_kumΨ`** (O2Km9b with `shapFree` replaced by an arbitrary `Ψ`, e.g. `theta` of O2Th1): an additive subgroup `G ≤ Ext²(Λ_P, Λ[R])` containing
  `ε_loc ∘ Ψ⁻¹ (kapS p (kumD α g))` for every piece `p` and every Kummer character (`α ^ d = u`) contains
  `ε_loc ∘ κ` for every `κ ∈ Ext¹(Λ[D_o], Λ[R])` (O2Km6 + O2Km8).
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

section Red

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {Uo Uz : P.Opens}
  (h : Uo ≤ Uz) {z : P} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ z)
  (hD : Subsingleton ((geomPtAt z).point.fiber.obj (chEt c φ)))
  (hDn : Nonempty ((geomPtAt z).point.fiber.obj (chEt c φ)))
  (hDr : ∀ v : (chEt c φ).left, (chEt c φ).hom v ∈ Uo ∨ (chEt c φ).hom v = z)
  (R : P.Etale) [IsAffine R.left] [IsAffine ((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))]
  (hW : ∀ (m : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (Λ : Type) [CommRing Λ] {N : ℕ} [NeZero N] (hΛ : ∀ x : Λ, N • x = 0)
  {ζ : ∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1))}
  (hζ : ∀ p, IsPrimitiveRoot (ζ p) N)
  (hζΓ : ∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)
    (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)))), σ (ζ p) = ζ p)
  (Ψ : Ext.{0} (freeSh Λ (prd (chEt c φ) (opEt Uo))) (freeSh Λ R) 1 ≃+
    H Λ (unitSh Λ ((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left) 1)

include hΛ in
/-- **Reduction to Kummer pieces.** (A `def`, not a `theorem`: at `.olean` export Lean folds every theorem type
for library-suggestion symbol frequencies, which costs 500+ s on this statement.) -/
def ext_mem_of_kumΨ (G : AddSubgroup (Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2))
    (hG : ∀ (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) (d : ℕ) [NeZero d]
      (hdN : d ∣ N)
      (α : (maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)
        (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)))ˣ)
      (hα : α ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)
        (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)))) d)
      (u : FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1))
      (_ : (α : maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)
        (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1))) ^ d =
          algebraMap _ _ u) (g : Λ) (hg : d • g = 0),
      (locC_shortExact (Λ := Λ) (chEt c φ) h z hz hD hDn hDr).extClass.comp
        (Ψ.symm
          (kapS hW Λ p (kumD (hζ p) (hζΓ p) hdN hα hg)))
        (show 1 + 1 = 2 from rfl) ∈ G)
    (κ : Ext.{0} (freeSh Λ (prd (chEt c φ) (opEt Uo))) (freeSh Λ R) 1) :
    (locC_shortExact (Λ := Λ) (chEt c φ) h z hz hD hDn hDr).extClass.comp κ (show 1 + 1 = 2 from rfl) ∈ G := by
  let L := ((locC_shortExact (Λ := Λ) (chEt c φ) h z hz hD hDn hDr).extClass.precomp (freeSh Λ R)
    (show 1 + 1 = 2 from rfl)).comp
      Ψ.symm.toAddMonoidHom
  have hm := h1_mem_of_kum hW Λ hΛ hζ hζΓ (G.comap L)
    (fun p d _ hdN α hα u hu g hg => hG p d hdN α hα u hu g hg)
    (Ψ κ)
  have e : L (Ψ κ) =
      (locC_shortExact (Λ := Λ) (chEt c φ) h z hz hD hDn hDr).extClass.comp κ (show 1 + 1 = 2 from rfl) := by
    change (locC_shortExact (Λ := Λ) (chEt c φ) h z hz hD hDn hDr).extClass.comp
      (Ψ.symm
        (Ψ κ))
        (show 1 + 1 = 2 from rfl) = _
    rw [AddEquiv.symm_apply_apply]
  rw [← e]
  exact hm

end Red

end RamanujanPetersson.EtPBC.EtKum

end

end


