-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_061
-- name    : RPLib_FX_EtPBC_061
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:58:31.474797+00:00
-- url     : https://prove2.me/theorems/ddc97585-10dc-5304-a9c4-601a36de10bd
-- title:
--   Proper base change for the projective line, library file 061
-- statement:
--   File 061 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Th1b`: S4-EtPBC-A, O2 M6 (O2Th1b): Shapiro over a FIXED base `D₀` (definitions `thetaV`, `theta`, `thX`)
--   * `S4.Def_RP_EtPBC_A_O2PPTc`: S4-EtPBC-A, O2 GLOB (O2PPTc): transfer of a piece Kummer class along a shrink `D₁ ⟶ D`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_224

/-!
# Proper base change for the projective line, library file 061

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Th1b`: S4-EtPBC-A, O2 M6 (O2Th1b): Shapiro over a FIXED base `D₀` (definitions `thetaV`, `theta`, `thX`)
* `S4.Def_RP_EtPBC_A_O2PPTc`: S4-EtPBC-A, O2 GLOB (O2PPTc): transfer of a piece Kummer class along a shrink `D₁ ⟶ D`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2Th1b =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1b): Shapiro over a FIXED base `D₀` (definitions `thetaV`, `theta`, `thX`)

For `τ : T ⟶ D₀` (`W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`):
* **`theta Λ R n hn τ : Ext¹_P(Λ[T], Λ[R]) ≃+ H¹(T ×_P R, Λ)`**;
* `thX`: the `W₀`-level class (`theta_apply`, naturality: O2Th1c).
* (surgery) `theta := thetaGen ..` with generic `thXEGen`/`thetaGen` and `extFreeUT`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.GalTrE

universe u

section GenTheta

universe w₁ v₁ u₁ v₂ u₂ u₃

end GenTheta

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} {D₀ : P.Etale} (R : P.Etale)

variable [QuasiCompact ((etPull D₀.hom).obj R).hom] [IsSeparated ((etPull D₀.hom).obj R).hom]
  (n : ℕ) (hn : ∀ y : D₀.left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull D₀.hom).obj R)) = n)

/-- `extFreeU` at `ovrW R τ`, stated at the target form of `θ_τ` (the identification of the two `H¹` forms is
paid here once, so `theta` instantiates `thetaGen` syntactically). -/
def extFreeUT {T : P.Etale} (τ : T ⟶ D₀) :
    Ext.{u} (freeSh Λ (ovrW R τ)) (unitSh Λ ((etPull D₀.hom).obj R).left) 1 ≃+
      H Λ (unitSh Λ ((etPull T.hom).obj R).left) 1 :=
  extFreeU Λ (ovrW R τ) 1

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end

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

variable {Y : Scheme.{0}} [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)]
  (hY : ∀ (m : Ideal Γ(Y, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [∀ Q : minimalPrimes Γ(Y, ⊤), IsDedekindDomain (Γ(Y, ⊤) ⧸ (Q : Ideal Γ(Y, ⊤)))]
  [Fintype (minimalPrimes Γ(Y, ⊤))] [DecidableEq (minimalPrimes Γ(Y, ⊤))] (Λ : Type) [CommRing Λ]

/-- A sum of piece classes with only one nonzero character. -/
def sum_kapS_eq_single
    (χ : ∀ Q : minimalPrimes Γ(Y, ⊤), ChL (Γ(Y, ⊤) ⧸ (Q : Ideal Γ(Y, ⊤)))
      (FractionRing (Γ(Y, ⊤) ⧸ (Q : Ideal Γ(Y, ⊤)))) Λ) (Q : minimalPrimes Γ(Y, ⊤))
    (hχ : ∀ Q', Q' ≠ Q → χ Q' = 0) :
    ∑ Q' : minimalPrimes Γ(Y, ⊤), kapS hY Λ Q' (χ Q') = kapS hY Λ Q (χ Q) := by
  refine Finset.sum_eq_single Q (fun Q' _ hQ' => ?_) (fun hQ => absurd (Finset.mem_univ Q) hQ)
  have e0 : χ Q' = 0 := hχ Q' hQ'
  simp only [e0, map_zero]

end Single

section PPTc

end PPTc

end RamanujanPetersson.EtPBC.EtKum

end

end


