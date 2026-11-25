-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_103
-- name    : RPLib_FX_EtPBC_103
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:59:50.753868+00:00
-- url     : https://prove2.me/theorems/9188725c-d501-54fc-b99d-fb01d76eec97
-- title:
--   Proper base change for the projective line, library file 103
-- statement:
--   File 103 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2PP3a`: S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points
--   * `S4.Def_RP_EtPBC_A_FibP1`: S4-EtPBC-A, G0: the fibre of a `P¹`-bundle at a rational point, and base change in degrees `≥ 4`
--   * `S4.Def_RP_EtPBC_A_O2a`: S4-EtPBC-A, O2a: base change surjectivity passes to quotients in the top degree
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_082
import Definitions.Def_RPLib_FX_EtPBC_089

/-!
# Proper base change for the projective line, library file 103

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2PP3a`: S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points
* `S4.Def_RP_EtPBC_A_FibP1`: S4-EtPBC-A, G0: the fibre of a `P¹`-bundle at a rational point, and base change in degrees `≥ 4`
* `S4.Def_RP_EtPBC_A_O2a`: S4-EtPBC-A, O2a: base change surjectivity passes to quotients in the top degree
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2PP3a =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points

GLOB/REL PLAN v1: `exists_S23B` / `exists_S23_chart` (O2Gl2j) with `t = X - a` and `J_b = (X - b)` for the points
`b` with `p b` (`p b → b ≠ a`), so that no `J`-family has to be built at the chart level (instance paths on
`integralClosure k[X] Γ(Y₀)` built outside the generic lemma made the chart-level unification time out).
* helpers: `ne_zero_right_of_eq`, `dvd_map_of_eq`, `badJ`, `badJ_pairwise`, `badJ_coprime`, `badJ_mem`;
* **`exists_S23B_bad`** (generic rings) and **`exists_S23_chart_bad`** (the chart instance).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section PP3Helpers

section BadJ

end BadJ

end PP3Helpers

section S23BBad

end S23BBad

section S23Bad

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ : k[X]}
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  [IsAffine (prd (chEt c φ₁) (opEt Uo)).left]
  (d₀ : chEt c φ₁ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀))

/-- **Stages S2-S3 on the charts, `J` = the bad points `(X - b)`, `p b → b ≠ a`** (`t = X - C a`, `y := liveMod uS t^N` on `Y₀`, `κ₀ = (prdMap d₀)^*`). -/
def exists_S23_chart_bad [IsDomain B₁] (ι₀ : CommRingCat.of (Localization.Away g₀) ⟶ B₁) (hd₀ : d₀.left = Spec.map ι₀)
    [Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hAY : algebraMap k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) =
      gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))
    (hY : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
      [m.IsMaximal], IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hG : ∀ (m : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal],
      IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)]
    [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))] (a : k)
    {L L' : k[X]} {e : ℕ} (hL : L = (X - C a) ^ e * L') (hL' : IsUnit (φ₁.hom L'))
    (hLY : ∀ y : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤),
      ∃ N : ℕ, IsIntegral k[X] (L ^ N • y))
    (h1 : ∀ x : B₁, ∃ c₀ : k[X], ∃ y : B₁, x = φ₁.hom c₀ + φ₁.hom (X - C a) * y)
    (p : k → Prop) [Finite (Subtype p)] (hpa : ∀ b, p b → b ≠ a)
    (ht : ¬ IsUnit (φ₁.hom (X - C a)))
    (p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))
    {u₁ : FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1)} (hu₁ : u₁ ≠ 0) {j : ℕ}
    (hj₁ : ∃ b, algebraMap (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) _ b =
      toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) (X - C a)) p₁ ^ j * u₁)
    (hj₂ : ∃ b, algebraMap (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) _ b =
      toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) (X - C a)) p₁ ^ j * u₁⁻¹) :
    ∃ (N : ℕ) (uS : integralClosure k[X]
        Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
      (z : PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)),
      (∀ b, p b → uS - algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C a) ^ N ∈
        Ideal.span {algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C b)}) ∧
      (letI : Algebra B₁ (PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) :=
        (toPiQ.comp (bW (Spec.map φ₁ ≫ c) (opEt Uo) R).hom).toAlgebra; IsIntegral B₁ z) ∧
      liveMod hY (uS : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
        (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a) ^ N) ∈
        Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)⁰ ∧
      (∃ c₀ : k[X], c₀ ≠ 0 ∧
        liveMod hY (uS : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
          (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a) ^ N) ∣
          gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) c₀) ∧
      toPiQ ((wm (R := R) (prdMap d₀ (opEt Uo))).appTop
        (liveMod hY (uS : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
          (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a) ^ N))) =
        toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) (X - C a)) ^ N *
          Function.update (1 : PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) p₁ u₁ *
          (1 - toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) (X - C a)) * z) :=
  exists_S23B_bad hY hG φ₁.hom (bW (Spec.map φ₁ ≫ c) (opEt Uo) R).hom (gamMap (shG c φ₁ (Uo := Uo) R))
    (fun r => (gamMap_shG c R φ₁ r).symm) (wm (R := R) (prdMap d₀ (opEt Uo))).appTop.hom
    (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R)) hAY
    (fun r => appTop_gamMap (wm (R := R) (prdMap d₀ (opEt Uo)))
      (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (shG c φ₁ (Uo := Uo) R)
      (shG_wm c (locF (B := CommRingCat.of k[X]) g₀) φ₁ R d₀) r)
    a (mem_adjoin_wm R (Spec.map (locF (B := CommRingCat.of k[X]) g₀) ≫ c) (Spec.map φ₁ ≫ c) ι₀ d₀ hd₀ (opEt Uo))
    hL hL' hLY h1 p hpa
    (toPiQ_gamMap_ne_zero (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X_sub_C_ne_zero a))
    (injective_bW_piece (Spec.map φ₁ ≫ c) (opEt Uo) R) ht
    (toPiQ_gamMap_ne_zero (shG c φ₁ (Uo := Uo) R) (X_sub_C_ne_zero a)) p₁ hu₁ hj₁ hj₂

end S23Bad

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_FibP1 =====
section

/-!
# S4-EtPBC-A, G0: the fibre of a `P¹`-bundle at a rational point, and base change in degrees `≥ 4`

* `nbhdTop s`: the trivial etale neighbourhood `(S, s)`;
* `bcSurj_of_subsingleton`: base change is surjective on germs when the target `H^q(P_s, ι^* G)` is trivial;
* for `g = pullback.snd : P¹_K ×_K S ⟶ S` and a geometric point `s` with `s.pt ≫ gS` an isomorphism (a `K`-rational
  point, `K = K̄`): **`fibToP1`** `: P_s ⟶ P¹_K` is an isomorphism, `fibH` transports `H^q`, and
  **`p1Bundle_bcSurj_add_four`**: base change is surjective on germs in degrees `q + 4` for every sheaf.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- Base change is surjective on germs when the target is trivial. -/
theorem bcSurj_of_subsingleton (q : ℕ) (G : EtSh Λ P)
    (h : Subsingleton (H Λ ((pull (fibι g s) Λ).obj G) q)) : BCSurj Λ g s q G :=
  fun _ => ⟨nbhdTop s, 0, (map_zero _).trans (Subsingleton.elim _ _)⟩

end Gen

section P1Bundle

end P1Bundle

section P1Vanish

end P1Vanish

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2a =====
section

/-!
# S4-EtPBC-A, O2a: base change surjectivity passes to quotients in the top degree

* `Delta.surjAt_of_epi`: for `0 → X₁ → X₂ → X₃ → 0`, surjectivity in degree `q` for `X₂` gives surjectivity in
  degree `q` for `X₃` when `Ext^(q+1)(B, L X₁) = 0` (covariant exact sequence, no germ argument for `X₁`);
* `bcSurj_of_epi`: the same for base change germs along an epimorphism `G ⟶ H` of sheaves;
* **`bcSurj_two_of_epi`**: on `P¹_S` at a `K`-rational geometric point (`K = K̄`, `ℓ ≠ char K`, `ℓ^m Λ = 0`),
  `BCSurj 2` passes to quotients (`H³` of the fibre vanishes for every sheaf).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

section Epi

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}}

/-- **`BCSurj q` passes along an epimorphism** when `H^(q+1)` of the fibre restriction of the kernel vanishes. -/
theorem bcSurj_of_epi (g : P ⟶ S) (s : GeomPt S) {G H : EtSh Λ P} (e : G ⟶ H) [Epi e] (q : ℕ)
    (hG : BCSurj Λ g s q G)
    (h0 : ∀ x : Ext (unitSh Λ (fib g s)) ((pull (fibι g s) Λ).obj (kernel e)) (q + 1), x = 0) :
    BCSurj Λ g s q H := by
  let SK := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  have hSK : SK.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
  exact Delta.surjAt_of_epi hSK q hG h0

end Epi

section P1Two

end P1Two

end RamanujanPetersson.EtPBC

end

end


