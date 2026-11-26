-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_214
-- name    : RPLib_FX_EtPBC_214
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:38:58.604928+00:00
-- url     : https://prove2.me/theorems/b3feed3b-f644-51f7-b9d9-f07dbe380dcc
-- title:
--   Proper base change for the projective line, library file 214
-- statement:
--   File 214 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_EGenP`: S4-EtPBC-A, R3 (degree `q`): the generic step for any predicate, and `BCSurj (q+1)` for `FGT` sheaves on `P¹_S`
--   * `S4.Def_RP_EtPBC_A_O2PP4f`: S4-EtPBC-A, O2 PP' (O2PP4f): PP' at a chart `D` for a piece `p` and a Kummer radical `α`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_208
import Definitions.Def_RPLib_FX_EtPBC_211

/-!
# Proper base change for the projective line, library file 214

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_EGenP`: S4-EtPBC-A, R3 (degree `q`): the generic step for any predicate, and `BCSurj (q+1)` for `FGT` sheaves on `P¹_S`
* `S4.Def_RP_EtPBC_A_O2PP4f`: S4-EtPBC-A, O2 PP' (O2PP4f): PP' at a chart `D` for a piece `p` and a Kummer radical `α`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_EGenP =====
section

/-!
# S4-EtPBC-A, R3 (degree `q`): the generic step for any predicate, and `BCSurj (q+1)` for `FGT` sheaves on `P¹_S`

* **`genStepP_of`**: the generic step `GenStepP Λ C` for any predicate `C` that holds for every `π_* M_Y` with `π`
  finite and `M` finite, `Λ` finite (same proof as `genStep_of`, which is the case `C = BCSurj 0`);
* **`bcInj_one_qV`**: base change is injective on germs in degree `1` for every sheaf on `P¹_S` (δ-lemma from degree
  `0`: `bcInj_zero`, `bcSurj_zero_qV`);
* **`bcSurj_succ_fgt_qV`**: if `BCSurj (q+1)` holds for every `π_* M_Y` (`π` finite, `M` finite; `Λ` finite),
  `BCInj (q+1)` and `BCSurj q`
  for every sheaf, then `BCSurj (q+1)` holds for every `FGT` sheaf on `P¹_S`; **`bcSurj_one_fgt_qV`** (`q = 0`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech GenAlg RamanujanPetersson.EtPBC.Z3

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Base change is injective on germs in degree `1` for every sheaf on `P¹_S`.** -/
theorem bcInj_one_qV (K : Type u) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]
    (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) [IsIso (s.pt ≫ gK)] [IsNoetherian S]
    [LocallyOfFiniteType gK] [IsNoetherianRing Λ] (G : EtSh Λ (PV K gK)) : BCInj Λ (qV K gK) s 1 G :=
  Delta.injAt_succ (bcUnit_comp Λ (qV K gK) s) 0 (fun H => bcInj_zero Λ (qV K gK) s H)
    (fun H => bcSurj_zero_qV K p gK s H) G

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP4f =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4f): PP' at a chart `D` for a piece `p` and a Kummer radical `α`

GLOB/REL PLAN v1 stage S1: `u = x / y` with `x ∣ c_x`, `y ∣ c_y` (`exists_frac_dvd`, (3a)), the density element `L`
(`exists_L`, (3b), algebra `gamAlg`), the splits `c_• = t^e c_•'`, `L = t^e L'` (`exists_eq_pow_mul_eval_ne_zero`, (3c)) and
`F := g₀ L' c_x' c_y'` (opaque via `∃`-elim), then `pp_D1` (O2PP4e).
* helpers: `ne_zero_of_pow_eq`, `F_facts`;
* **`pp_D`** (DEF): the target class `ε(D)∘θ⁻¹(kapS p (kumD α))` lies in `Gr`.
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

section PPD

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

set_option maxHeartbeats 4000000 in
include hg₀ in
/-- **PP' at `D`** for the piece `p` and the radical `α` (`α^d = u`): S1 data, then `pp_D1`. -/
def pp_D (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {α : (maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))))ˣ}
    (hα : α ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0) {u : FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))}
    (hu : (α : maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))))) ^ d = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))))) u)
    [IsAlgClosed k] [IsDomain B]
    (hGal : ∀ b : k, Subsingleton (Gal (c (A1pt k b))))
    [Finite {b : k // c (A1pt k b) ∉ Uo ∧ b ≠ a}] (hg0 : g₀ ≠ 0) (hga : g₀.eval a ≠ 0)
    (Gr : AddSubgroup (Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2)) (good : P → Prop)
    (hGd : ∀ x, good x → ∀ γ, IsLoc Λ (freeSh Λ R) x γ → γ ∈ Gr)
    (hgood : ∀ x ∈ Uo, good x) (hgoodc : ∀ x ∉ Set.range c, good x)
    (hfin : (Set.range c)ᶜ.Finite) (hclc : ∀ x ∉ Set.range c, IsClosed ({x} : Set P))
    (hclA : ∀ b : k, IsClosed ({c (A1pt k b)} : Set P))
    (hpt : ∀ y : A1 k, y.asIdeal ≠ ⊥ → ∃ b, y = A1pt k b) :
    (locC_shortExact (Λ := Λ) (chEt c φ) h (c (A1pt k a)) hz hD hDn hDr).extClass.comp
      ((theta Λ R n hn (prT (chEt c φ) (opEt Uo))).symm
        (kapS hW Λ p (kumD (hζW c φ R hζ0 p) (hζWΓ c φ R (ζ0 := ζ0) p) hdN hα hgΛ)))
      (show 1 + 1 = 2 from rfl) ∈ Gr :=
  letI : Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) := gamAlg (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R)
  Exists.elim (exists_frac_dvd (shG c φ (Uo := Uo) R) p (ne_zero_of_pow_eq hu)) fun _ hx =>
  Exists.elim hx fun _ hxy =>
  Exists.elim hxy.2.2.2 fun _ hcx => Exists.elim hcx fun _ hc =>
  Exists.elim (exists_L (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R)) fun _ hL =>
  Exists.elim (exists_eq_pow_mul_eval_ne_zero hc.1 a) fun _ hex => Exists.elim hex fun cx' hcx' =>
  Exists.elim (exists_eq_pow_mul_eval_ne_zero hc.2.1 a) fun _ hey => Exists.elim hey fun cy' hcy' =>
  Exists.elim (exists_eq_pow_mul_eval_ne_zero hL.1 a) fun _ he => Exists.elim he fun L' hL' =>
  Exists.elim (⟨_, rfl⟩ : ∃ F : k[X], F = g₀ * L' * cx' * cy') fun _ hF =>
  have hFf := F_facts hF hga hL'.2 hcx'.2 hcy'.2
  pp_D1 c h hz R hg₀ φ hD hDn hDr Λ n hn hW hζ0 p hdN hα hgΛ hu hxy.1 hxy.2.1 (ne_zero_of_pow_eq hu) hxy.2.2.1
    hc.2.2.1 hc.2.2.2 hcx'.1 hcy'.1 (gamAlg_algebraMap _) (isDomain_loc_W c _ R) hGal hL'.1 hL.2 hg0
    hFf.1 hFf.2.1 hFf.2.2.1 hFf.2.2.2.1 hFf.2.2.2.2 Gr good hGd hgood hgoodc hfin hclc hclA hpt

end PPD

end RamanujanPetersson.EtPBC.EtKum

end

end


