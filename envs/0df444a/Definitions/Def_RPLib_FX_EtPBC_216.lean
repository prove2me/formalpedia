-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_216
-- name    : RPLib_FX_EtPBC_216
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:42:56.844492+00:00
-- url     : https://prove2.me/theorems/2416e74a-f17a-5421-9643-3d608eaadf64
-- title:
--   Proper base change for the projective line, library file 216
-- statement:
--   File 216 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2PP4g`: S4-EtPBC-A, O2 PP' (O2PP4g): PP' at a chart `D` for every class `κ`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_164
import Definitions.Def_RPLib_FX_EtPBC_214

/-!
# Proper base change for the projective line, library file 216

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2PP4g`: S4-EtPBC-A, O2 PP' (O2PP4g): PP' at a chart `D` for every class `κ`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2PP4g =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4g): PP' at a chart `D` for every class `κ`

`ext_mem_of_kumΨ` (O2Km9c, reduction to Kummer pieces, `Ψ := θ(prT D Uo)`, roots of unity `ζW`) with `pp_D` (O2PP4f)
on every piece and radical.
* **`pp_all`** (DEF): `ε(D)∘κ ∈ Gr` for every `κ : Ext¹(Λ[prd D (opEt Uo)], Λ[R])`.
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

section PPAll

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {Uo Uz : P.Opens} (h : Uo ≤ Uz) {a : k} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ (c (A1pt k a)))
  (R : P.Etale) [IsAffine R.left] {g₀ : k[X]}
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  (hg₀ : ∀ v : (chEt c (locF (B := CommRingCat.of k[X]) g₀)).left,
    (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v ∈ Uo ∨ (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v = c (A1pt k a))
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
  (hD : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
  (hDn : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
  (hDr : ∀ v : (chEt c φ).left, (chEt c φ).hom v ∈ Uo ∨ (chEt c φ).hom v = (c (A1pt k a)))
  [QuasiCompact ((etPull (opEt Uo).hom).obj R).hom] [IsSeparated ((etPull (opEt Uo).hom).obj R).hom]
  (Λ : Type) [CommRing Λ] (n : ℕ)
  (hn : ∀ y : (opEt Uo).left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt Uo).hom).obj R)) = n)
  [IsAffine ((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))]
  (hW : ∀ (m : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  {N : ℕ} [NeZero N] {ζ0 : k} (hζ0 : IsPrimitiveRoot ζ0 N)

set_option maxHeartbeats 1000000 in
include hg₀ in
/-- **PP' at `D` for every `κ`**: Kummer pieces (`ext_mem_of_kumΨ`), then `pp_D` on each. -/
def pp_all (hΛ : ∀ x : Λ, N • x = 0) [IsAlgClosed k] [IsDomain B]
    (hGal : ∀ b : k, Subsingleton (Gal (c (A1pt k b))))
    [Finite {b : k // c (A1pt k b) ∉ Uo ∧ b ≠ a}] (hg0 : g₀ ≠ 0) (hga : g₀.eval a ≠ 0)
    (Gr : AddSubgroup (Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2)) (good : P → Prop)
    (hGd : ∀ x, good x → ∀ γ, IsLoc Λ (freeSh Λ R) x γ → γ ∈ Gr)
    (hgood : ∀ x ∈ Uo, good x) (hgoodc : ∀ x ∉ Set.range c, good x)
    (hfin : (Set.range c)ᶜ.Finite) (hclc : ∀ x ∉ Set.range c, IsClosed ({x} : Set P))
    (hclA : ∀ b : k, IsClosed ({c (A1pt k b)} : Set P))
    (hpt : ∀ y : A1 k, y.asIdeal ≠ ⊥ → ∃ b, y = A1pt k b) :
    ∀ κ : Ext.{0} (freeSh Λ (prd (chEt c φ) (opEt Uo))) (freeSh Λ R) 1,
    (locC_shortExact (Λ := Λ) (chEt c φ) h (c (A1pt k a)) hz hD hDn hDr).extClass.comp κ
      (show 1 + 1 = 2 from rfl) ∈ Gr :=
  ext_mem_of_kumΨ c φ h hz hD hDn hDr R hW Λ hΛ (hζW c φ R hζ0) (hζWΓ c φ R (ζ0 := ζ0))
    (theta Λ R n hn (prT (chEt c φ) (opEt Uo))) Gr
    (fun p _ _ hdN _ hα _ hu _ hg => pp_D c h hz R hg₀ φ hD hDn hDr Λ n hn hW hζ0 p hdN hα hg hu hGal hg0 hga
      Gr good hGd hgood hgoodc hfin hclc hclA hpt)

end PPAll

end RamanujanPetersson.EtPBC.EtKum

end

end


