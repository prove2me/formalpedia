-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_006
-- name    : RPLib_FX_EtPBC_006
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:06:38.462799+00:00
-- url     : https://prove2.me/theorems/9ffb576c-c9b6-5749-81b2-9e273dba5c2f
-- title:
--   Proper base change for the projective line, library file 006
-- statement:
--   File 006 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
--   * `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
--   * `S4.Def_RP_EtPBC_A_O2KapN`: S4-EtPBC-A, O2 M6 (O2KapN): naturality of Kummer classes along etale maps of Dedekind domains
--   * `S4.Def_RP_EtPBC_A_O2UKd1`: S4-EtPBC-A, O2 M6 (O2UKd1): a global Kummer class along a composite `X₁ ⟶ X ⟶ Y`
--   * `S4.Def_RP_EtPBC_A_O2Th1b`: S4-EtPBC-A, O2 M6 (O2Th1b): Shapiro over a FIXED base `D₀` (definitions `thetaV`, `theta`, `thX`)
--   * `S4.Def_RP_EtPBC_A_O2Th1c`: S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`
--   * `S4.Def_RP_EtPBC_A_O2Km1`: S4-EtPBC-A, O2 M6 (O2Km1): the Shapiro scheme `W = D_o ×_P R` is affine
--   * `S4.Def_RP_EtPBC_A_O2T3`: S4-EtPBC-A, O2 S5c: sections after shrinking, and the graph splitting
--   * `S4.Def_RP_Lefschetz_UnrIn`: S4-Lefschetz L4c (part 2): unramified subextensions in any algebraically closed field
--   * `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
--   * `S4.Def_RP_EtPBC_A_O2T5`: S4-EtPBC-A, O2 S5e: splitting off finitely many disjoint sections
--   * `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
--   * `S4.Def_RP_EtPBC_A_O2PP4a`: S4-EtPBC-A, O2 PP' (O2PP4a): generic glue for the S1 layer
--   * `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
--   * `S4.Def_RP_EtPBC_A_O2Mob`: S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity
--   * `S4.Def_RP_EtPBC_A_O2TB1`: S4-EtPBC-A, L3a (TB1): pulled-back sections
--   * `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
--   * `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
--   * `S4.Def_RP_EtPBC_A_O2Dg2`: S4-EtPBC-A, O2 M6 (O2Dg2): the generic-degree locus of an etale `W ⟶ P¹` is open and cofinite
--   * `S4.Def_RP_EtPBC_A_O2L1b`: S4-EtPBC-A, L1b (MVr): Mayer-Vietoris for free sheaves with arbitrary fibres of `Z`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_003

/-!
# Proper base change for the projective line, library file 006

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
* `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
* `S4.Def_RP_EtPBC_A_O2KapN`: S4-EtPBC-A, O2 M6 (O2KapN): naturality of Kummer classes along etale maps of Dedekind domains
* `S4.Def_RP_EtPBC_A_O2UKd1`: S4-EtPBC-A, O2 M6 (O2UKd1): a global Kummer class along a composite `X₁ ⟶ X ⟶ Y`
* `S4.Def_RP_EtPBC_A_O2Th1b`: S4-EtPBC-A, O2 M6 (O2Th1b): Shapiro over a FIXED base `D₀` (definitions `thetaV`, `theta`, `thX`)
* `S4.Def_RP_EtPBC_A_O2Th1c`: S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`
* `S4.Def_RP_EtPBC_A_O2Km1`: S4-EtPBC-A, O2 M6 (O2Km1): the Shapiro scheme `W = D_o ×_P R` is affine
* `S4.Def_RP_EtPBC_A_O2T3`: S4-EtPBC-A, O2 S5c: sections after shrinking, and the graph splitting
* `S4.Def_RP_Lefschetz_UnrIn`: S4-Lefschetz L4c (part 2): unramified subextensions in any algebraically closed field
* `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
* `S4.Def_RP_EtPBC_A_O2T5`: S4-EtPBC-A, O2 S5e: splitting off finitely many disjoint sections
* `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
* `S4.Def_RP_EtPBC_A_O2PP4a`: S4-EtPBC-A, O2 PP' (O2PP4a): generic glue for the S1 layer
* `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
* `S4.Def_RP_EtPBC_A_O2Mob`: S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity
* `S4.Def_RP_EtPBC_A_O2TB1`: S4-EtPBC-A, L3a (TB1): pulled-back sections
* `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
* `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
* `S4.Def_RP_EtPBC_A_O2Dg2`: S4-EtPBC-A, O2 M6 (O2Dg2): the generic-degree locus of an etale `W ⟶ P¹` is open and cofinite
* `S4.Def_RP_EtPBC_A_O2L1b`: S4-EtPBC-A, L1b (MVr): Mayer-Vietoris for free sheaves with arbitrary fibres of `Z`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2P3a =====
section

/-!
# S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps

* `ChL A K Λ`: the additive group of additive locally constant characters `π₁(A) → Λ`; `mem_ChL`, `chl_cyc`;
* `zetaE_prim`, `zetaE_fix`: a primitive root `ζ₀ ∈ K` in `maxUnram A K`;
* `kumTau hζ hζΓ hτ hΛ : Λ →+ ChL`, `c ↦ kumChi ζ τ c`;
* **`kappaLH A K Λ : ChL A K Λ →+ H¹(Spec A, Λ)`** (`kappaL`, additive by `kappa_add`), **`kappaLH_surj`**;
* `resLEHom g n : H^n(X, Λ) →+ H^n(U, Λ)` (`resLE` is additive).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer RamanujanPetersson.EtPi1
  RamanujanPetersson.EtCompact.GalTrE

section ChL

end ChL

section KappaLH

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A] (Λ : Type) [CommRing Λ]

/-- **The class map `κ : ChL →+ H¹(Spec A, Λ)`.** -/
def kappaLH : ChL A K Λ →+ H Λ (unitSh Λ (Spec (CommRingCat.of A))) 1 :=
  AddMonoidHom.mk' (fun χ => kappaL A K Λ (mem_ChL.1 χ.2).1 (mem_ChL.1 χ.2).2) (fun χ₁ χ₂ =>
    kappa_add A K isLisse_unitSh (unitCoc_isCocycle A K Λ (mem_ChL.1 χ₁.2).1)
      (unitCoc_isLocallyConstant A K Λ (mem_ChL.1 χ₁.2).2) (unitCoc_isCocycle A K Λ (mem_ChL.1 χ₂.2).1)
      (unitCoc_isLocallyConstant A K Λ (mem_ChL.1 χ₂.2).2) _ _ (fun _ => add_smul _ _ _))

end KappaLH

section ResH

universe u

end ResH

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapP =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map

For `f : X₁ ⟶ X` etale between affine schemes whose rings are finite products of Dedekind domains, and a Kummer
class `kapS p (kumD α)` on the piece `p` of `X` (`α^d = u`):
* `kerMap f p₁ : Γ(X) → Γ(X₁) ⧸ p₁`, `exists_minimalPrime_le_ker`, `kerLift`, **`piHom_comp_eq`**
  (the piece `p₁` of `X₁` maps into the piece `q` of `X` through `Spec (Γ(X₁) ⧸ p₁) ⟶ Spec (Γ(X) ⧸ q)`),
  `injective_of_etale` (an etale map of domains is injective), `resLE_congr`, `resLE_kapS_self`, `resLE_kapS_ne`;
* **`resLE_kapS_kumD_eq_zero`**: if `u` becomes a `d`-th power in the fraction field of every piece of `X₁` lying
  over `p`, then `resLE f 1 (kapS p (kumD α)) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

universe u

section Fac

variable {X X₁ : Scheme.{0}} [IsAffine X] [IsAffine X₁] [IsNoetherianRing Γ(X, ⊤)] [IsNoetherianRing Γ(X₁, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (h₁ : ∀ (m : Ideal Γ(X₁, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (f : X₁ ⟶ X)

/-- `Γ(X) → Γ(X₁) ⧸ p₁`. -/
def kerMap (p₁ : minimalPrimes Γ(X₁, ⊤)) : Γ(X, ⊤) →+* Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)) :=
  (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤))).comp f.appTop.hom

end Fac

section KappaRes

end KappaRes

section Red

end Red

section KapP

end KapP

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapN =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapN): naturality of Kummer classes along etale maps of Dedekind domains

* **`resLE_kumD`**: along an etale `Spec.map φ` (`η' ↦ η`) with `ψ : K → K'` extending `φ`, the class `κ(kumD α)`
  (`α^d = u`) restricts to `κ(kumD γ)` for any radical `γ` with `γ^d = ψ u` (roots of unity matched by `ψ`);
* **`exists_root_of_isUnit`**: a unit of a Dedekind domain has a `d`-th root in `K_U` (`d` invertible);
* **`resLE_kumD_eq`**: two Kummer classes from `A` and `A''` agree on `A'` once their radicands differ by a `d`-th
  power there and one of them is a unit of `A'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

section Root

variable {A K : Type} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- **A unit has a `d`-th root in `K_U`** (`d` invertible in `A`). -/
theorem exists_root_of_isUnit {d : ℕ} [NeZero d] (hd : IsUnit (d : A)) {a : A} (ha : IsUnit a) :
    ∃ γ : (maxUnram A K)ˣ, (γ : maxUnram A K) ^ d = algebraMap K (maxUnram A K) (algebraMap A K a) := by
  have : IsDedekindDomain (integralClosure A (⊥ : IntermediateField K (AlgebraicClosure K))) :=
    integralClosure.isDedekindDomain (A := A) (K := K) (L := (⊥ : IntermediateField K (AlgebraicClosure K)))
  have : IsFractionRing (integralClosure A (⊥ : IntermediateField K (AlgebraicClosure K)))
      (⊥ : IntermediateField K (AlgebraicClosure K)) :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K _
  obtain ⟨b, hb⟩ : ∃ b : integralClosure A (⊥ : IntermediateField K (AlgebraicClosure K)),
      b = algebraMap A _ a := ⟨_, rfl⟩
  have hbu : IsUnit b := hb ▸ ha.map _
  obtain ⟨a', ha'⟩ : ∃ a' : (⊥ : IntermediateField K (AlgebraicClosure K)),
      a' = algebraMap (integralClosure A _) _ b := ⟨_, rfl⟩
  have ha'K : (a' : AlgebraicClosure K) = algebraMap K _ (algebraMap A K a) := by
    rw [ha', hb]
    show algebraMap A (AlgebraicClosure K) a = _
    rw [IsScalarTower.algebraMap_apply A K (AlgebraicClosure K)]
  have ha0 : a' ≠ 0 := by
    intro h0
    have h2 : (a' : AlgebraicClosure K) = 0 := by rw [h0]; rfl
    rw [ha'K, map_eq_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective,
      map_eq_zero_iff _ (IsFractionRing.injective A K)] at h2
    exact ha.ne_zero h2
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (a' : AlgebraicClosure K) (NeZero.pos d)
  have hU : γ ∈ maxUnram A K := by
    refine root_mem_maxUnram_of_dvd A (bot_mem_unramSet _ _) hd ha0 (fun v => ?_) hγ
    have hv : b ∉ v.asIdeal := fun hm => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hbu)
    rw [ha', IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hv, WithZero.log_one]
    exact dvd_zero _
  have hγ0 : (⟨γ, hU⟩ : maxUnram A K) ≠ 0 := by
    intro h0
    have h1 : γ = 0 := congrArg Subtype.val h0
    rw [h1, zero_pow (NeZero.ne d), eq_comm] at hγ
    exact ha0 (Subtype.ext hγ)
  refine ⟨Units.mk0 _ hγ0, Subtype.ext ?_⟩
  rw [Units.val_mk0, IntermediateField.coe_pow]
  exact hγ.trans ha'K

end Root

section KapN

end KapN

section KapE

end KapE

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2UKd1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UKd1): a global Kummer class along a composite `X₁ ⟶ X ⟶ Y`

Generic (abstract affine schemes) forms of the two facts used by `uk_diff` / `uk_kill_glob` (O2UKd2):
* `resLE_kumG_eq_zero`: a global Kummer class dies along `g` once its radicand is a `d`-th power on every piece;
* **`resLE_kapS_kumD_eq_comp`**: along `f : X₁ ⟶ X`, the piece class `kapS p (kumD α)` (`α ^ d = u`) equals the
  restriction of a global Kummer class `c_Y` of a unit `H` along `g₀ : X ⟶ Y`, when `g₀^* H = u · r_p` on `p`,
  `g₀^* H = r_q` on the other pieces, and every `r_q` becomes a `d`-th power along every `Ψ` compatible with `f`;
* **`resLE_kumG_eq_zero_comp`**: the same class dies along `f` when `g₀^* H = r_q` on every piece.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

section Aux

/-- Field algebra: `H = a · w ^ d`, `H ≠ 0` ⇒ `a = H · (w⁻¹) ^ d`. -/
theorem eq_mul_inv_pow {F : Type} [Field F] {a w H : F} {d : ℕ} (hH : H ≠ 0) (h : H = a * w ^ d) :
    a = H * w⁻¹ ^ d := by
  have hw : w ^ d ≠ 0 := fun h0 => hH (by rw [h, h0, mul_zero])
  rw [h, inv_pow, mul_assoc, mul_inv_cancel₀ hw, mul_one]

end Aux

section KillG

end KillG

section KapDC

end KapDC

end RamanujanPetersson.EtPBC.EtKum

end

end

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

/-- Generic `thXE`: `Ext(A₀, B) ≃+ Ext(A₁, B) ≃+ Ext(X, Y) ≃+ Ext(X', Y)` (`HasExt` instances are implicit
binders, unified from the use site). -/
def thXEGen {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] {h₁ : HasExt.{w₁} C₁}
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] {h₂ : HasExt.{w₁} C₂}
    {A₀ A₁ B : C₁} {X X' Y : C₂} (e₁ : A₁ ≅ A₀) (Θ : Ext.{w₁} A₁ B 1 ≃+ Ext.{w₁} X Y 1) (e₂ : X' ≅ X) :
    Ext.{w₁} A₀ B 1 ≃+ Ext.{w₁} X' Y 1 :=
  ((extIsoLeft e₁ B 1).trans Θ).trans (extIsoLeft e₂ Y 1)

end GenTheta

section Theta

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Th1c =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`

For `τ : T ⟶ D₀` (`W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`):
* `theta_apply`: `θ_τ x = extFreeU (thX x)` (via `thXE`, `theta_eq_thXE`, `thXE_eq`);
* **`theta_natural`**: for `m : T₁ ⟶ T₂` with `m ≫ τ₂ = τ₁`,
  `θ_{τ₁}(Λ[m]^* x) = resLE (wm m) (θ_{τ₂} x)`.
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

section Gen

/-- Generic form: the `thXE` chain applied to `x` (definitional over abstract abelian categories). -/
theorem thXE_gen {C₁ C₂ C₃ : Type*} [Category C₁] [Abelian C₁] [HasExt.{u} C₁] [Category C₂] [Abelian C₂]
    [HasExt.{u} C₂] [Category C₃] [Abelian C₃] [HasExt.{u} C₃]
    {T₁ A₁ G₁ : C₁} {V₂ G₂ G₂' : C₂} {X₃ Y₃ Z₃ O₃ : C₃}
    (e₁ : A₁ ≅ T₁) (F : Ext A₁ G₁ 1 ≃+ Ext V₂ G₂ 1) (e₂ : G₂ ≅ G₂') (S : Ext X₃ Y₃ 1 ≃+ Ext V₂ G₂' 1)
    (e₃ : Z₃ ≅ X₃) (e₄ : O₃ ≅ Z₃) (x : Ext T₁ G₁ 1) :
    (((extIsoLeft e₁ G₁ 1).trans ((((F.trans (extIsoRight V₂ e₂ 1)).trans S.symm).trans
        (extIsoLeft e₃ Y₃ 1)))).trans (extIsoLeft e₄ Y₃ 1)) x =
      (Ext.mk₀ e₄.hom).comp ((Ext.mk₀ e₃.hom).comp (S.symm ((F ((Ext.mk₀ e₁.hom).comp x (zero_add 1))).comp
        (Ext.mk₀ e₂.hom) (add_zero 1))) (zero_add 1)) (zero_add 1) := by
  simp only [AddEquiv.trans_apply, extIsoLeft_apply, extIsoRight_apply]

end Gen

section GenNat

universe w₁ v₁ u₁

/-- Generic `thX_natural`: two commuting squares and one `Ext` identity in one abelian category give
`a ∘ (i₂ ∘ (p₂ ∘ y₂)) = i₁ ∘ (p₁ ∘ y₁)` (`HasExt` an implicit binder). -/
theorem thX_natural_gen {C : Type u₁} [Category.{v₁} C] [Abelian C] {hC : HasExt.{w₁} C}
    {o₁ o₂ q₁ q₂ s₁ s₂ O : C} (a : o₁ ⟶ o₂) (i₁ : o₁ ⟶ q₁) (i₂ : o₂ ⟶ q₂) (b : q₁ ⟶ q₂)
    (p₁ : q₁ ⟶ s₁) (p₂ : q₂ ⟶ s₂) (c : s₁ ⟶ s₂) (y₁ : Ext.{w₁} s₁ O 1) (y₂ : Ext.{w₁} s₂ O 1)
    (h1 : a ≫ i₂ = i₁ ≫ b) (h2 : b ≫ p₂ = p₁ ≫ c) (h3 : (Ext.mk₀ c).comp y₂ (zero_add 1) = y₁) :
    (Ext.mk₀ a).comp ((Ext.mk₀ i₂).comp ((Ext.mk₀ p₂).comp y₂ (zero_add 1)) (zero_add 1)) (zero_add 1) =
      (Ext.mk₀ i₁).comp ((Ext.mk₀ p₁).comp y₁ (zero_add 1)) (zero_add 1) := by
  subst h3
  rw [Ext.mk₀_comp_mk₀_assoc, h1, ← Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc b, h2,
    ← Ext.mk₀_comp_mk₀_assoc]

end GenNat

section Theta

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km1): the Shapiro scheme `W = D_o ×_P R` is affine

* `isAffineHom_of_isAffine_source`: a morphism from an affine scheme to a separated scheme is affine;
* `isAffine_etPull`: `D ×_P R` is affine for affine `D`, `R` over a separated `P`; `isAffineHom_etPull`: its
  structure map to `D` is affine (hence quasi-compact and separated: `quasiCompact_etPull`, `isSeparated_etPull'`);
* `isAffine_prdUo`: `D ×_P Uo ≅ Spec B_t` is affine for an affine Dedekind presentation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV

universe u

section Affine

/-- A morphism from an affine scheme to a separated scheme is affine. -/
theorem isAffineHom_of_isAffine_source {X P : Scheme.{u}} [IsAffine X] [P.IsSeparated] (f : X ⟶ P) :
    IsAffineHom f := by
  have : IsAffineHom (f ≫ terminal.from P) := isAffineHom_of_isAffine _
  exact IsAffineHom.of_comp f (terminal.from P)

variable {P : Scheme.{u}} [P.IsSeparated] (D R : P.Etale) [IsAffine R.left]

set_option backward.isDefEq.respectTransparency false in
theorem isAffineHom_etPull : IsAffineHom ((etPull D.hom).obj R).hom := by
  let f : R.left ⟶ P := R.hom
  let g : D.left ⟶ P := D.hom
  have hR : IsAffineHom f := isAffineHom_of_isAffine_source f
  have : IsAffineHom (pullback.snd f g) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) f g hR
  exact this

end Affine

section Prd

end Prd

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T3 =====
section

/-!
# S4-EtPBC-A, O2 S5c: sections after shrinking, and the graph splitting

* `exists_opn_pt`: an open of `N` whose only geometric point over a closed Galois-trivial `z` is a given one;
* **`isLoc_sec`**: a one-point class has a presentation `D` with a map `s : D ⟶ T` through a given point `t` of `T`;
* `isClosed_range_sec`, `secV σ`: a section `σ` of a separated etale `N` has closed range, with open complement;
* **`isIso_secSplit`**, `secSplitIso`: `Λ_X ⊞ Λ[N|secV σ] ≅ Λ[N]`, first summand `Λ[σ]`;
* `isSeparated_opn`; `isSeparated_etPull` (so the graph of `m : W ⟶ T` splits).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg

universe u

section PtOpn

end PtOpn

section SecSplit

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {N : X.Etale} [IsSeparated N.hom] (σ : etId X ⟶ N)

/-- A section of a separated etale `N` has closed range. -/
theorem isClosed_range_sec : IsClosed (Set.range σ.left) := by
  have : IsClosedImmersion (σ.left ≫ N.hom) := by
    rw [MorphismProperty.Over.w σ]
    show IsClosedImmersion (𝟙 X)
    infer_instance
  have := IsClosedImmersion.of_comp (f := σ.left) (g := N.hom)
  exact σ.left.isClosedEmbedding.isClosed_range

/-- The complement of a section, an open of `N`. -/
def secV : N.left.Opens := ⟨(Set.range σ.left)ᶜ, (isClosed_range_sec σ).isOpen_compl⟩

end SecSplit

section Lift

variable {X : Scheme.{u}}

instance isSeparated_opn (N : X.Etale) [IsSeparated N.hom] (V : N.left.Opens) : IsSeparated (opn N V).hom := by
  show IsSeparated (V.ι ≫ N.hom)
  infer_instance

end Lift

section GraphSplit

variable {P : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
instance isSeparated_etPull (W T : P.Etale) [IsSeparated T.hom] : IsSeparated ((etPull W.hom).obj T).hom := by
  rw [etPull_obj_hom]
  first
    | infer_instance
    | (rw [← pullbackSymmetry_hom_comp_fst]; infer_instance)
    | exact MorphismProperty.pullback_snd (P := @IsSeparated) T.hom W.hom inferInstance

end GraphSplit

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_Lefschetz_UnrIn =====
section

/-!
# S4-Lefschetz L4c (part 2): unramified subextensions in any algebraically closed field

`UnrIn A K Ω L`: `L` is a finite Galois subextension of `Ω/K` whose inertia groups on the integral closure of `A`
vanish. For `Ω = K̄` (`AlgebraicClosure K`) this is `unramSet A K` (`unramSet_eq_unrIn`, by `rfl`). The predicate is
transported along any `K`-isomorphism `ι : Ω₁ ≃ₐ[K] Ω₂` (`unrIn_map_iff`), and membership in `K_U` is membership
in one unramified `L` (`mem_maxUnram_iff`), so `y ∈ K_U ↔ ∃ L, UnrIn A K Ω₂ L ∧ ι y ∈ L` (`mem_maxUnram_iff_of_equiv`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open GalCover

noncomputable section

/-! ### Inertia transport along an equivariant ring isomorphism and a group isomorphism -/

section InertiaTransport2

end InertiaTransport2

/-! ### `UnrIn` and its transport -/

section UnrIn

end UnrIn

/-! ### Membership in `K_U` -/

section MemMax

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

theorem mem_maxUnram_iff (y : AlgebraicClosure K) :
    y ∈ maxUnram A K ↔ ∃ L ∈ unramSet A K, y ∈ L := by
  have hdir : Directed (· ≤ ·)
      (fun L : unramSet A K => (L : IntermediateField K (AlgebraicClosure K))) :=
    directedOn_iff_directed.mp (directedOn_unramSet A K)
  have : Nonempty (unramSet A K) := ⟨⟨⊥, bot_mem_unramSet A K⟩⟩
  rw [← SetLike.mem_coe, maxUnram, IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion]
  exact ⟨fun ⟨L, h⟩ => ⟨L, L.2, h⟩, fun ⟨L, hL, h⟩ => ⟨⟨L, hL⟩, h⟩⟩

end MemMax

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtPi1_FunA =====
section

/-!
# S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change

`A → A'`, `K → K'` compatible (`A → K → K'`, `A → A' → K'`), `ι : K̄ →ₐ[K] K̄'` any `K`-embedding.

* `bcField f = K'(roots of f)` in `K̄'` (splitting field, finite, Galois when `f` is separable);
* `rootSet_bc`: the roots of `f` in `K̄'` are the `ι`-images of its roots in `K̄`;
* `icMap`: `integralClosure A L → integralClosure A' L'` induced by `ι`;
* `bcField_unram`: for `L ∈ unramSet A K` the splitting field of `L` over `K'` has trivial inertia over `A'`
  (an inertia element restricts, via `ι`, to an inertia element of `Gal(L/K)`, which is trivial);
* `map_mem_maxUnram`: `ι (K_U(A)) ⊆ K_U(A')`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace EtPi1

open GalCover Lefschetz Polynomial

noncomputable section

section FunA

variable {A K A' K' : Type} [CommRing A] [Field K] [Algebra A K]
  [CommRing A'] [Field K'] [Algebra A' K'] [Algebra K K'] [Algebra A A'] [Algebra A K']
  [IsScalarTower A K K'] [IsScalarTower A A' K']
  (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure K')

/-- The map of integral closures induced by `ι` when `ι L ⊆ L'`. -/
def icMap (L : IntermediateField K (AlgebraicClosure K)) (L' : IntermediateField K' (AlgebraicClosure K'))
    (h : ∀ y : L, ι y ∈ L') : integralClosure A L →+* integralClosure A' L' where
  toFun b := ⟨⟨ι b, h b⟩, by
    have h1 : IsIntegral A (ι ((b : L) : AlgebraicClosure K)) :=
      IsIntegral.map (ι.restrictScalars A) (IsIntegral.map (L.val.restrictScalars A) b.2)
    exact (isIntegral_algHom_iff (L'.val.restrictScalars A') Subtype.val_injective).1 h1.tower_top⟩
  map_one' := Subtype.ext (Subtype.ext (map_one ι))
  map_mul' x y := Subtype.ext (Subtype.ext
    (map_mul ι ((x : L) : AlgebraicClosure K) ((y : L) : AlgebraicClosure K)))
  map_zero' := Subtype.ext (Subtype.ext (map_zero ι))
  map_add' x y := Subtype.ext (Subtype.ext
    (map_add ι ((x : L) : AlgebraicClosure K) ((y : L) : AlgebraicClosure K)))

end FunA

end

end EtPi1
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtPBC_A_O2T5 =====
section

/-!
# S4-EtPBC-A, O2 S5e: splitting off finitely many disjoint sections

* `secLiftOI g σ h`: a section `σ` of `N` lifted through an open immersion `g : R ⟶ N` containing its range;
* **`clsD_splitAll`**: for sections `σ i` (`i ∈ S`, a finset) of a separated etale `N` over `D = Spec B` with
  pairwise disjoint ranges, `clsD f Y` is a sum of section summands `clsD (Λ[σ i] ≫ f) Y'` plus one residual
  summand `clsD (Λ[g] ≫ f) Y_R` through an open immersion `g : R ⟶ N` missing every range `σ i`, `i ∈ S`;
  `R` is affine when `N` is (`isAffine_opn_secV`: section ranges are clopen).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

section LiftOI

variable {X : Scheme.{u}} {R N : X.Etale}

set_option backward.isDefEq.respectTransparency false in
/-- A section lifted through an open immersion containing its range. -/
def secLiftOI (g : R ⟶ N) [IsOpenImmersion g.left] (σ : etId X ⟶ N) (h : Set.range σ.left ⊆ Set.range g.left) :
    etId X ⟶ R :=
  MorphismProperty.Over.homMk (IsOpenImmersion.lift g.left σ.left h) (by
    rw [← MorphismProperty.Over.w g, IsOpenImmersion.lift_fac_assoc]
    exact MorphismProperty.Over.w σ)

set_option backward.isDefEq.respectTransparency false in
theorem secLiftOI_comp (g : R ⟶ N) [IsOpenImmersion g.left] (σ : etId X ⟶ N)
    (h : Set.range σ.left ⊆ Set.range g.left) : secLiftOI g σ h ≫ g = σ :=
  MorphismProperty.Over.Hom.ext (IsOpenImmersion.lift_fac _ _ _)

end LiftOI

section Aff

end Aff

section SplitAll

end SplitAll

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T6 =====
section

/-!
# S4-EtPBC-A, O2 S5f: geometry of graphs of sections

For `m : W ⟶ T` in `P.Etale`, `graph m : etId W.left ⟶ (etPull W.hom).obj T` (lib O2T1):
* `graph_fst`, `graph_snd`, `graph_left_eq_sec` (it is EGeoB's `sec m`), **`graph_cover`** (points over `fpt d`
  lie on graphs of sections through every fibre point);
* `graphMeet m m'` (where the graphs meet), closed for separated `T`; `graph_meet_eq`, **`not_mem_graphMeet`**
  (graphs of sections through different fibre points do not meet at `fpt d`), `disjoint_graph`;
* `pullMap d`, **`graph_natural`**, **`graphMeet_natural`** (meeting loci pull back along `d : W' ⟶ W`);
* `eq_fpt_of_over`: `fpt d` is the only point over `z` when the fibre over `z` is a singleton.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

section GraphGeo

variable {P : Scheme.{u}} {W' W T : P.Etale}

set_option backward.isDefEq.respectTransparency false in
/-- The base change map `W' ×_P T ⟶ W ×_P T` along `d : W' ⟶ W`. -/
def pullMap (d : W' ⟶ W) : ((etPull W'.hom).obj T).left ⟶ ((etPull W.hom).obj T).left :=
  pullback.lift (pullback.fst T.hom W'.hom) (pullback.snd T.hom W'.hom ≫ d.left)
    (pullback.condition.trans (by rw [Category.assoc, MorphismProperty.Over.w d]))

end GraphGeo

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP4a =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4a): generic glue for the S1 layer

* `comp_symm_sum_mem`, `comp_symm_dite_mem`, `mem_of_eq_mem`: membership of `ε ∘ θ⁻¹(Σ_i v_i)` in an additive
  subgroup from the summands (the piece sum of the PPT transfer, characters `if p ≤ ker then kumD else 0`);
* `exists_hj_pair`: `hj₁`, `hj₂` of `pp_chart` in `toPiQ` form from `u = x / y`, `x ∣ c_x`, `y ∣ c_y`
  (`exists_pow_mul_psi_pair` along a ring map `σ`), `fracMap_ne_zero`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC.EtMV

universe w v u

section ExtMem

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X Y Z : C} {a b c : ℕ}
  (ε : Ext.{w} X Y a) (h : a + b = c) {M : Type*} [AddCommGroup M] (θ : Ext.{w} Y Z b ≃+ M)
  (Gr : AddSubgroup (Ext.{w} X Z c))

theorem comp_symm_sum_mem {ι : Type*} [Fintype ι] (v : ι → M) (hv : ∀ i, ε.comp (θ.symm (v i)) h ∈ Gr) :
    ε.comp (θ.symm (∑ i, v i)) h ∈ Gr := by
  rw [map_sum, ext_comp_sum]
  exact Gr.sum_mem fun i _ => hv i

end ExtMem

section HJ

end HJ

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals

REL PLAN v2 (s126) + s128 fix. At a bad point `c(b)` (`G = (X - C b)^m G_b`, `G_b(b) ≠ 0`, `c(b) ∉ U₀`), the chart
`D' := D_{G_b} = chEt c (locF G_b)` satisfies the hypotheses of `bad_term_zero'` (O2Bd5):
* fibres: **`subsingleton_fib_of_mono`**, **`nonempty_fib_of_mem`** (generic);
* **`bad_pt`**, **`badCh_r₁`** (`hDr₁`), **`badCh_r`** (`hDr`), **`badCh_D'`** (`hD'`), **`badCh_hUo`**, **`isAffine_badCh`**,
  **`badCh_hta`** (`hta`), **`badCh_n`** (`hDn`);
* CRT ideals `J b := (X - C b) S`: **`span_coprime_pow`** (`hJt`), **`pairwise_span_coprime`** (`hJ`) of `exists_S23_chart`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtCompact.Cech

section Fib

variable {P : Scheme.{0}}

/-- Fibres of a monomorphism are subsingletons. -/
theorem subsingleton_fib_of_mono (D : P.Etale) [Mono D.hom] (x : P) :
    Subsingleton ((geomPtAt x).point.fiber.obj D) := by
  have h : ∀ e : (geomPtAt x).point.fiber.obj D, ((geomPtAt x).liftOf e).left ≫ D.hom = (geomPtAt x).pt :=
    fun e => Over.w ((geomPtAt x).liftOf e)
  exact ⟨fun e e' => fiber_ext _ ((cancel_mono D.hom).1 ((h e).trans (h e').symm))⟩

end Fib

section BadCh

end BadCh

section BadCh2

end BadCh2

section JAlg

end JAlg

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Mob =====
section

/-!
# S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity

* `mobA c`: the shear `X₀ ↦ X₀ + c X₁`, `X₁ ↦ X₁`; `mobG c` the graded ring hom; `mobP c := Proj.map (mobG c)`,
  an isomorphism of `P¹` with inverse `mobP (-c)`.
* **`chartM c := chartA1 ≫ mobP c`**: an open immersion `A¹ ⟶ P¹` whose range is `P¹ ∖ {mobP c ∞}`
  (`mem_range_chartM`); `c ↦ mobP c ∞` is injective (`mobP_infPt_injective`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

section Mob

variable {K : Type} [Field K]

theorem X1_not_mem_infPt : (X 1 : MvPolynomial (Fin 2) K) ∉ (P1.infPt K).asHomogeneousIdeal := by
  rcases P1.cover K (P1.infPt K) with h | h
  · exact absurd h (P1.infPt_not_mem_range K)
  · exact (P1.mem_range_chartA1'_iff K _).1 h

end Mob

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB1 =====
section

/-!
# S4-EtPBC-A, L3a (TB1): pulled-back sections

* `pbSec f x`: the section `f^* x` of `f^* F` over `f⁻¹ V` (unit of `f^* ⊣ f_*`);
* `pbSec_natural`, `pbSec_restrict`: naturality in `F` and in `V`;
* `pbSec_comp`: `pullCompIso` sends `(g ≫ f)^* x` to `g^* f^* x` (restricted along `etPullCompIso`);
* `pbSec_res`: for etale `g`, `pullIsoRes` sends `g^* x` to `x` restricted along the counit of `etComp ⊣ etPull`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC

universe u

section Pb

variable {Λ : Type u} [CommRing Λ]

/-- The pulled-back section `f^* x ∈ (f^* F)(f⁻¹ V)` of `x ∈ F(V)`. -/
def pbSec {X Y : Scheme.{u}} (f : X ⟶ Y) {F : EtSh Λ Y} {V : Y.Etale} (x : F.obj.obj (op V)) :
    ((pull f Λ).obj F).obj.obj (op ((etPull f).obj V)) :=
  (((pullAdj f Λ).unit.app F).hom.app (op V)).hom x

end Pb

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2a =====
section

/-!
# S4-EtPBC-A, L3b (TB2a): section calculus for base change

* `etPull_hom_ext`: maps into `X ×_Y T` agree if their first components agree;
* `etIdPull g : etId X ≅ X ×_Y Y`, `pullUnit g : Λ_X ≅ g^*Λ_Y`, `pullUnit_one`;
* `unit_hom_ext`: maps out of `Λ_X` are determined by the image of `1`;
* transport of pulled-back sections along `pullIsoRes`, `pullCompIso`, `pullCongr`, `(pull g).map`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section TB2

variable {Λ : Type u} [CommRing Λ]

theorem etPull_hom_ext {X Y : Scheme.{u}} (g : X ⟶ Y) {Z : X.Etale} {T : Y.Etale}
    {a b : Z ⟶ (etPull g).obj T}
    (h : a.left ≫ pullback.fst T.hom g = b.left ≫ pullback.fst T.hom g) : a = b :=
  MorphismProperty.Over.Hom.ext (pullback.hom_ext h
    ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm))

theorem etId_hom' (X : Scheme.{u}) : (etId X).hom = 𝟙 X := rfl

/-- `X ≅ Y ×_Y X` as etale `X`-schemes. -/
def etIdPull {X Y : Scheme.{u}} (g : X ⟶ Y) : etId X ≅ (etPull g).obj (etId Y) where
  hom := MorphismProperty.Over.homMk (pullback.lift g (𝟙 X) (by exact (Category.comp_id g).trans (Category.id_comp g).symm))
    (by exact pullback.lift_snd _ _ _) trivial
  inv := MorphismProperty.Over.homMk (pullback.snd (etId Y).hom g) (by exact Category.comp_id _) trivial
  hom_inv_id := MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)
  inv_hom_id := etPull_hom_ext g (by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => pullback.snd (etId Y).hom g ≫ k) (pullback.lift_fst _ _ _)).trans ?_
    refine ((pullback.condition (f := (etId Y).hom) (g := g)).symm.trans (Category.comp_id _)).trans ?_
    exact (Category.id_comp _).symm)

theorem sh_comp_apply {X : Scheme.{u}} {F G H : EtSh Λ X} (φ : F ⟶ G) (ψ : G ⟶ H) (V : X.Etaleᵒᵖ)
    (s : F.obj.obj V) : ((φ ≫ ψ).hom.app V).hom s = (ψ.hom.app V).hom ((φ.hom.app V).hom s) := rfl

theorem sh_hom_inv_apply {X : Scheme.{u}} {F G : EtSh Λ X} (e : F ≅ G) (V : X.Etaleᵒᵖ) (s : F.obj.obj V) :
    (e.inv.hom.app V).hom ((e.hom.hom.app V).hom s) = s :=
  congrArg (fun ψ : F ⟶ F => (ψ.hom.app V).hom s) e.hom_inv_id

theorem map_comp_apply_sh {X : Scheme.{u}} (F : EtSh Λ X) {V'' V' V : X.Etale} (a : V'' ⟶ V') (b : V' ⟶ V)
    (s : F.obj.obj (op V)) : (F.obj.map (a ≫ b).op).hom s = (F.obj.map a.op).hom ((F.obj.map b.op).hom s) := by
  rw [op_comp, Functor.map_comp]
  rfl

theorem res_obj_map {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] (F : EtSh Λ X) {V' V : U.Etale} (a : V' ⟶ V)
    (s : F.obj.obj (op ((etComp g).obj V))) :
    ((((res g Λ).obj F).obj.map a.op).hom s) = (F.obj.map ((etComp g).map a).op).hom s := rfl

theorem res_map_app {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {F G : EtSh Λ X} (φ : F ⟶ G) (V : U.Etale)
    (s : F.obj.obj (op ((etComp g).obj V))) :
    ((((res g Λ).map φ).hom.app (op V)).hom s) = (φ.hom.app (op ((etComp g).obj V))).hom s := rfl

/-- `X ×_g T ⟶ X ×_{g'} T` for `g = g'`. -/
def etPullCongr {X Y : Scheme.{u}} {g g' : X ⟶ Y} (h : g = g') (T : Y.Etale) :
    (etPull g).obj T ⟶ (etPull g').obj T :=
  MorphismProperty.Over.homMk (pullback.lift (pullback.fst T.hom g) (pullback.snd T.hom g)
    (by rw [← h]; exact pullback.condition)) (by exact pullback.lift_snd _ _ _) trivial

@[reassoc]
theorem etPullCongr_left_fst {X Y : Scheme.{u}} {g g' : X ⟶ Y} (h : g = g') (T : Y.Etale) :
    (etPullCongr h T).left ≫ pullback.fst T.hom g' = pullback.fst T.hom g :=
  pullback.lift_fst _ _ _

theorem etPullCongr_rfl {X Y : Scheme.{u}} (g : X ⟶ Y) (T : Y.Etale) :
    etPullCongr (rfl : g = g) T = 𝟙 _ :=
  etPull_hom_ext g ((etPullCongr_left_fst rfl T).trans (Category.id_comp _).symm)

end TB2

section TB2o

/-! Op-form section calculus: restriction maps are op-morphisms `a : op T ⟶ op Z` that are passed through
unchanged, so consecutive steps meet in syntactically equal terms (this keeps kernel checks cheap). -/

variable {Λ : Type u} [CommRing Λ]

variable (Λ) in
/-- `(pullCompIso g h).hom.app F`, typed with nested pullbacks. -/
def pullCompHom {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C) (F : EtSh Λ C) :
    (pull (g ≫ h) Λ).obj F ⟶ (pull g Λ).obj ((pull h Λ).obj F) := (pullCompIso Λ g h).hom.app F

variable (Λ) in
/-- `(pullCompIso g h).inv.app F`, typed with nested pullbacks. -/
def pullCompInv {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C) (F : EtSh Λ C) :
    (pull g Λ).obj ((pull h Λ).obj F) ⟶ (pull (g ≫ h) Λ).obj F := (pullCompIso Λ g h).inv.app F

theorem mapO_comp_apply {X : Scheme.{u}} (F : EtSh Λ X) {U U' U'' : X.Etaleᵒᵖ} (a : U ⟶ U') (b : U' ⟶ U'')
    (s : F.obj.obj U) : (F.obj.map (a ≫ b)).hom s = (F.obj.map b).hom ((F.obj.map a).hom s) := by
  rw [Functor.map_comp]
  rfl

theorem map_congr_apply {X : Scheme.{u}} (F : EtSh Λ X) {U U' : X.Etaleᵒᵖ} {r r' : U ⟶ U'} (h : r = r')
    (s : F.obj.obj U) : (F.obj.map r).hom s = (F.obj.map r').hom s := by
  rw [h]

theorem pullCongr_pbSecO {X Y : Scheme.{u}} {g g' : X ⟶ Y} (h : g = g') {F : EtSh Λ Y} {T : Y.Etale}
    {Z : X.Etale} (a : op ((etPull g).obj T) ⟶ op Z) (x : F.obj.obj (op T)) :
    (((pullCongr Λ h).hom.app F).hom.app (op Z)).hom ((((pull g Λ).obj F).obj.map a).hom (pbSec g x)) =
      ((((pull g' Λ).obj F).obj.map ((etPullCongr h T).op ≫ a)).hom (pbSec g' x)) := by
  subst h
  rw [etPullCongr_rfl, op_id, Category.id_comp]
  rfl

theorem app2 {X : Scheme.{u}} {F0 F1 F2 : EtSh Λ X} (a1 : F0 ⟶ F1) (a2 : F1 ⟶ F2) {V : X.Etaleᵒᵖ}
    {s0 : F0.obj.obj V} {s1 : F1.obj.obj V} {s2 : F2.obj.obj V}
    (h1 : (a1.hom.app V).hom s0 = s1) (h2 : (a2.hom.app V).hom s1 = s2) :
    ((a1 ≫ a2).hom.app V).hom s0 = s2 := by
  subst h1 h2
  rfl

end TB2o

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2b =====
section

/-!
# S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section TB2b

variable {Λ : Type u} [CommRing Λ]

@[reassoc]
theorem etIdPull_hom_left_fst {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (etIdPull g).hom.left ≫ pullback.fst (etId Y).hom g = g :=
  pullback.lift_fst _ _ _

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Etale)

/-- `f_W : W ×_Y X ⟶ W`. -/
def fW : ((etPull f).obj W).left ⟶ W.left := pullback.fst W.hom f

theorem etPullCompIso_hom_fst_fst {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (V : C.Etale) :
    ((etPullCompIso g f).hom.app V).left ≫ pullback.fst ((etPull f).obj V).hom g ≫ pullback.fst V.hom f =
      pullback.fst V.hom (g ≫ f) :=
  MorphismProperty.Over.pullbackComp_left_fst_fst g f V

theorem appN3 {X : Scheme.{u}} {F0 F1 F2 F3 : EtSh Λ X} (a1 : F0 ⟶ F1) (a2 : F1 ⟶ F2) (a3 : F2 ⟶ F3)
    {V : X.Etaleᵒᵖ} {s0 : F0.obj.obj V} {s1 : F1.obj.obj V} {s2 : F2.obj.obj V} {s3 : F3.obj.obj V}
    (h1 : (a1.hom.app V).hom s0 = s1) (h2 : (a2.hom.app V).hom s1 = s2) (h3 : (a3.hom.app V).hom s2 = s3) :
    ((a1 ≫ a2 ≫ a3).hom.app V).hom s0 = s3 := by
  subst h1 h2 h3
  rfl

theorem map4_congr {P : Scheme.{u}} (F : EtSh Λ P) {A B C D E Z : P.Etaleᵒᵖ} (x1 : A ⟶ B) (x2 : B ⟶ C)
    (x3 : C ⟶ D) (x4 : D ⟶ Z) (y1 : A ⟶ E) (y2 : E ⟶ Z) (h : x1 ≫ x2 ≫ x3 ≫ x4 = y1 ≫ y2) (s : F.obj.obj A) :
    (F.obj.map (x1 ≫ x2 ≫ x3 ≫ x4)).hom s = (F.obj.map (y1 ≫ y2)).hom s := by
  rw [h]

end TB2b

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Dg2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Dg2): the generic-degree locus of an etale `W ⟶ P¹` is open and cofinite

* `card_le_genPt`: every geometric fibre of `W` has at most the generic number of points (lower semicontinuity,
  `exists_nbhd_card_le`, and the generic point lies in every non-empty open);
* `isOpen_genDeg`: the locus where the fibre has the generic number of points is open;
* **`exists_genDeg_open`**: that locus is an open `U` of `P¹` with finite complement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtDeg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.CurveHn

section GenDeg

variable (k : Type) [Field k] (W : (P1 k).Etale) [QuasiCompact W.hom] [IsSeparated W.hom]

/-- The generic point lies in every open neighbourhood of every point. -/
theorem genPt_mem_of_isOpen {O : Set (P1 k)} (hO : IsOpen O) {x : P1 k} (hx : x ∈ O) : P1.genPt k ∈ O := by
  have hcl : x ∈ closure ({P1.genPt k} : Set (P1 k)) := by
    rw [P1.closure_genPt k]
    exact Set.mem_univ x
  obtain ⟨y, hyO, hy⟩ := mem_closure_iff.1 hcl O hO hx
  rw [Set.mem_singleton_iff.1 hy] at hyO
  exact hyO

end GenDeg

end RamanujanPetersson.EtPBC.EtDeg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L1b =====
section

/-!
# S4-EtPBC-A, L1b (MVr): Mayer-Vietoris for free sheaves with arbitrary fibres of `Z`

**`mvC_shortExactR`**: the MV complex `Λ[W'] ⟶ Λ[W] ⊞ Λ[U] ⟶ Λ[Z]` of a commutative square `p₁ ≫ w = p₂ ≫ v` of
`P.Etale` is short exact when, at every geometric point `x` and every point `c` of the fibre of `Z` at `x`, the fibre
square satisfies `MVG1` (one point of `W` over `c`, `p₂` bijective over `c`) or `MVG2` (one point of `U` over `c`,
`p₁` bijective over `c`). Proof: stalks are free on fibres (`freeLin`), then `mv_inj`, `mv_surj`, `mv_exact` (L1a).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

/-- The fibre square of `p₁ ≫ w = p₂ ≫ v` at a geometric point commutes. -/
theorem fiber_sq {W' W U Z : P.Etale} {p₁ : W' ⟶ W} {p₂ : W' ⟶ U} {w : W ⟶ Z} {v : U ⟶ Z}
    (hsq : p₁ ≫ w = p₂ ≫ v) (x : P) (a' : (geomPtAt x).point.fiber.obj W') :
    (geomPtAt x).point.fiber.map w ((geomPtAt x).point.fiber.map p₁ a') =
      (geomPtAt x).point.fiber.map v ((geomPtAt x).point.fiber.map p₂ a') := by
  have h := congrArg (fun f => (geomPtAt x).point.fiber.map f a') hsq
  simpa only [Functor.map_comp, types_comp_apply] using h

end RamanujanPetersson.EtPBC.EtMV

end

end


