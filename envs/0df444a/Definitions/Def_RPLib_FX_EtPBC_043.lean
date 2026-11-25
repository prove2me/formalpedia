-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_043
-- name    : RPLib_FX_EtPBC_043
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:12:03.514387+00:00
-- url     : https://prove2.me/theorems/7ccfb11b-3f0d-5c7b-b7ca-58d0c405ad0d
-- title:
--   Proper base change for the projective line, library file 043
-- statement:
--   File 043 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
--   * `S4.Def_RP_EtPBC_A_O2Tr1`: S4-EtPBC-A, O2 M6b (O2Tr1): the trace section of a separated etale `W` of constant degree over an open
--   * `S4.Def_RP_EtPBC_A_O2Dg`: S4-EtPBC-A, O2 M6 (O2Dg): constant degree after shrinking a one-point presentation
--   * `S4.Def_RP_EtPBC_A_O2UK2b`: S4-EtPBC-A, O2 M6 (O2UK2b): the `d`-th root of `1 + t e` on the pieces over an etale `B → B'`
--   * `S4.Def_RP_EtPBC_A_O2ZarCh`: S4-EtPBC-A, O2 GLOB (O2ZarCh): the chart toolbox for the global step
--   * `S4.Def_RP_EtPBC_A_O2Km9a`: S4-EtPBC-A, O2 M6 (O2Km9a): roots of unity on the Shapiro pieces
--   * `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
--   * `S4.Def_RP_EtPBC_A_O2Dg2`: S4-EtPBC-A, O2 M6 (O2Dg2): the generic-degree locus of an etale `W ⟶ P¹` is open and cofinite
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_035

/-!
# Proper base change for the projective line, library file 043

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
* `S4.Def_RP_EtPBC_A_O2Tr1`: S4-EtPBC-A, O2 M6b (O2Tr1): the trace section of a separated etale `W` of constant degree over an open
* `S4.Def_RP_EtPBC_A_O2Dg`: S4-EtPBC-A, O2 M6 (O2Dg): constant degree after shrinking a one-point presentation
* `S4.Def_RP_EtPBC_A_O2UK2b`: S4-EtPBC-A, O2 M6 (O2UK2b): the `d`-th root of `1 + t e` on the pieces over an etale `B → B'`
* `S4.Def_RP_EtPBC_A_O2ZarCh`: S4-EtPBC-A, O2 GLOB (O2ZarCh): the chart toolbox for the global step
* `S4.Def_RP_EtPBC_A_O2Km9a`: S4-EtPBC-A, O2 M6 (O2Km9a): roots of unity on the Shapiro pieces
* `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
* `S4.Def_RP_EtPBC_A_O2Dg2`: S4-EtPBC-A, O2 M6 (O2Dg2): the generic-degree locus of an etale `W ⟶ P¹` is open and cofinite
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

theorem kappaLH_apply (χ : ChL A K Λ) :
    kappaLH A K Λ χ = kappaL A K Λ (mem_ChL.1 χ.2).1 (mem_ChL.1 χ.2).2 := rfl

end KappaLH

section ResH

universe u

end ResH

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Tr1 =====
section

/-!
# S4-EtPBC-A, O2 M6b (O2Tr1): the trace section of a separated etale `W` of constant degree over an open

* `agr τ₁ τ₂`: for `τ₁ τ₂ : T ⟶ W` over `P` (`W` separated etale), the range of the pull-back of the diagonal of `W`
  along `(τ₁, τ₂)`: closed (`isClosed_agr`), and a fibre point `v` of `T` has `τ₁ v = τ₂ v` iff `fpt v ∈ agr τ₁ τ₂`
  (`mem_agr_iff`).
* **`exists_split_inj`**: for `x ∈ U₀` and `W` quasi-compact separated etale, an etale `T` over `U₀` with a point `t`
  over `x̄` and maps `τ p : T ⟶ W` (`p` in the fibre of `W` over `x̄`) with `τ p (t) = p`, pairwise distinct at every
  geometric point of `T`.
* `locSec τ = Σ_p τ_p^* taut`; `stalkFree_locSec_apply` (all coefficients of its germ are `1` where the `τ_p` biject
  onto the fibre); `stalkFree_injective`.
* **`exists_tr`**: if every geometric fibre of `W` over `U₀` has `n` points, there is a section `s ∈ Λ[W](U₀)` whose
  germ at every geometric point of `U₀` is the sum of all points of the fibre (the trace `Λ[U₀] ⟶ Λ[W]`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtTr

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk
  RamanujanPetersson.EtPBC.EtMV

universe u

variable {P : Scheme.{u}}

section Agr

end Agr

/-- **A splitting neighbourhood over `U₀` with pairwise distinct sheets.** -/
theorem exists_split_inj (U₀ : P.Opens) (W : P.Etale) [QuasiCompact W.hom] [IsSeparated W.hom] (x : P)
    (hx : x ∈ U₀) :
    ∃ (T : P.Etale) (t : (geomPtAt x).point.fiber.obj T) (τ : (geomPtAt x).point.fiber.obj W → (T ⟶ W)),
      (∀ v : T.left, T.hom v ∈ U₀) ∧ (∀ p, (geomPtAt x).point.fiber.map (τ p) t = p) ∧
      ∀ (y : P) (v : (geomPtAt y).point.fiber.obj T) (p q : (geomPtAt x).point.fiber.obj W),
        (geomPtAt y).point.fiber.map (τ p) v = (geomPtAt y).point.fiber.map (τ q) v → p = q := by
  classical
  have hfin := finite_fiber W x
  obtain ⟨T₀, t₀, τ₀, -, hτ₀⟩ := exists_split x (fun _ : PUnit.{u+1} => W)
  let τ' : (geomPtAt x).point.fiber.obj W → (T₀ ⟶ W) := fun p => τ₀ ⟨PUnit.unit, p⟩
  have hτ' : ∀ p, (geomPtAt x).point.fiber.map (τ' p) t₀ = p := fun p => hτ₀ ⟨PUnit.unit, p⟩
  let O : Set T₀.left := T₀.hom ⁻¹' (U₀ : Set P) ∩
    ⋂ (p : (geomPtAt x).point.fiber.obj W) (q : (geomPtAt x).point.fiber.obj W),
      {v | p ≠ q → v ∉ agr (τ' p) (τ' q)}
  have hO : IsOpen O := by
    refine (U₀.isOpen.preimage T₀.hom.continuous).inter
      (isOpen_iInter_of_finite fun p => isOpen_iInter_of_finite fun q => ?_)
    by_cases hpq : p = q
    · have e : {v : T₀.left | p ≠ q → v ∉ agr (τ' p) (τ' q)} = Set.univ := by
        ext v; simp [hpq]
      rw [e]; exact isOpen_univ
    · have e : {v : T₀.left | p ≠ q → v ∉ agr (τ' p) (τ' q)} = (agr (τ' p) (τ' q))ᶜ := by
        ext v; simp [hpq]
      rw [e]; exact (isClosed_agr _ _).isOpen_compl
  have ht₀O : fpt x t₀ ∈ O := by
    refine ⟨?_, Set.mem_iInter.2 fun p => Set.mem_iInter.2 fun q => fun hpq hm => hpq ?_⟩
    · show T₀.hom (fpt x t₀) ∈ U₀
      rw [fib_over]; exact hx
    · have e := (mem_agr_iff (τ' p) (τ' q) x t₀).1 hm
      rwa [hτ', hτ'] at e
  let OO : T₀.left.Opens := ⟨O, hO⟩
  obtain ⟨t, ht, -⟩ := exists_lift_fib (opnι T₀ OO) x t₀ (⟨fpt x t₀, ht₀O⟩ : OO)
    (Scheme.Opens.ι_apply OO ⟨fpt x t₀, ht₀O⟩)
  refine ⟨opn T₀ OO, t, fun p => opnι T₀ OO ≫ τ' p, fun v => ?_, fun p => ?_, fun y v p q hpq => ?_⟩
  · exact (show (opnι T₀ OO).left v ∈ O from opnι_mem T₀ OO v).1
  · rw [Functor.map_comp_apply, ht, hτ']
  · rw [Functor.map_comp_apply, Functor.map_comp_apply] at hpq
    have hm := (mem_agr_iff (τ' p) (τ' q) y _).2 hpq
    rw [fib_left_map] at hm
    by_contra hne
    have hv := (show (opnι T₀ OO).left (fpt y v) ∈ O from opnι_mem T₀ OO (fpt y v)).2
    exact (Set.mem_iInter.1 (Set.mem_iInter.1 hv p) q) hne hm

section Loc

end Loc

end RamanujanPetersson.EtPBC.EtTr

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Dg =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Dg): constant degree after shrinking a one-point presentation

* `card_fib_etPull`: `#(g^* R)_ȳ = #R_{g(y)}‾` for etale `g`;
* `exists_nbhd_card_le`: the geometric fibre size of a separated quasi-compact etale `W` is lower semicontinuous;
* `exists_away_deg`: a lower semicontinuous `δ` on `Spec B` (`B` a noetherian domain) is constant on
  `D(f) ∩ D(t)` for some `f` with `t ∤ f`;
* **`isLocAff_deg`**: an affine Dedekind presentation can be shrunk so that `R` has constant geometric fibre
  size over every point of `Spec B` off the special fibre; **`card_fib_prd`**: then `(D ×_P Uo) ×_P R ⟶ D ×_P Uo`
  has constant degree (the hypothesis of `shapFree`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtDeg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV

universe u

section Card

/-- **Lower semicontinuity** of the geometric fibre size. -/
theorem exists_nbhd_card_le {P : Scheme.{u}} (W : P.Etale) [QuasiCompact W.hom] [IsSeparated W.hom] (x : P) :
    ∃ O : Set P, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O,
      Nat.card ((geomPtAt x).point.fiber.obj W) ≤ Nat.card ((geomPtAt y).point.fiber.obj W) := by
  obtain ⟨T, t, τ, -, -, hinj⟩ := EtTr.exists_split_inj ⊤ W x (by simp)
  have : Etale T.hom := T.prop
  refine ⟨Set.range T.hom, T.hom.isOpenMap.isOpen_range, ⟨fpt x t, fib_over x t⟩, ?_⟩
  rintro _ ⟨v, rfl⟩
  obtain ⟨b, -⟩ := exists_fib_over T v
  have := finite_fiber W (T.hom v)
  exact Nat.card_le_card_of_injective (fun p => (geomPtAt (T.hom v)).point.fiber.map (τ p) b)
    fun p q h => hinj _ b p q h

end Card

section Ring

end Ring

section Aff

end Aff

end RamanujanPetersson.EtPBC.EtDeg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2UK2b =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UK2b): the `d`-th root of `1 + t e` on the pieces over an etale `B → B'`

`D = Spec B` etale over `P` (through `hB`), `X R : P.Etale`, `W := (D ×_P X) ×_P R`; `wD : W ⟶ D`,
`bW : B ⟶ Γ(W)`, `bK p : B →+* Frac(Γ(W) ⧸ p)`.
* `wm_wD`: `wm (prdMap d X) ≫ wD D X = wD D₁ X ≫ d.left`;
* `uk_root'`: O2UK1 `uk_root` with an explicit ring map `ι : B ⟶ B'` (`Spec ι` etale);
* **`exists_pow_of_uk`**: for `D₁ ⟶ Spec B'` and a piece `p₁` of `W₁ := (D₁ ×_P X) ×_P R`, every `Ψ` compatible with
  `wm (prdMap d X)` sends `1 + t e` (`e` a root of `g` over `B`) to a `d`-th power.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.GenGeo

universe u

section WD

end WD

section Ring

variable {P : Scheme.{u}} {B : CommRingCat.{u}} (hB : Spec B ⟶ P) [Etale hB] (X R : P.Etale)

variable {B' : CommRingCat.{u}} (ι : B ⟶ B') [Etale (Spec.map ι)]

variable {D₁ : P.Etale} (d₁ : D₁ ⟶ Scheme.Etale.mk (Spec.map ι ≫ hB))

def bK_key (p : minimalPrimes Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤)) (p₁ : minimalPrimes Γ(((etPull (prd D₁ X).hom).obj R).left, ⊤))
    (Ψ : FractionRing (Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤) ⧸ p.1) →+* FractionRing (Γ(((etPull (prd D₁ X).hom).obj R).left, ⊤) ⧸ p₁.1))
    (hΨ : ∀ a, Ψ (algebraMap _ _ (Ideal.Quotient.mk p.1 a)) =
      algebraMap _ _ (Ideal.Quotient.mk p₁.1 ((wm (R := R) (prdMap (d₁ ≫ nD hB ι) X)).appTop a))) (b : B) :
    Ψ (bK hB X R p b) = bK₁ hB X R ι d₁ p₁ (ι b) := by
  have e0 := congrArg (fun φ => φ b) (bW_comp_appTop hB X R ι d₁)
  simp only [CategoryTheory.comp_apply] at e0
  exact (hΨ _).trans (congrArg (fun a => algebraMap _ _ (Ideal.Quotient.mk p₁.1 a)) e0)

/-- **The radicand `1 + t e` becomes a `d`-th power on every piece over `B'`.** -/
def exists_pow_of_uk (p : minimalPrimes Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤)) (p₁ : minimalPrimes Γ(((etPull (prd D₁ X).hom).obj R).left, ⊤))
    (Ψ : FractionRing (Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤) ⧸ p.1) →+* FractionRing (Γ(((etPull (prd D₁ X).hom).obj R).left, ⊤) ⧸ p₁.1))
    (hΨ : ∀ a, Ψ (algebraMap _ _ (Ideal.Quotient.mk p.1 a)) =
      algebraMap _ _ (Ideal.Quotient.mk p₁.1 ((wm (R := R) (prdMap (d₁ ≫ nD hB ι) X)).appTop a)))
    {g : B[X]} {t : B} {d : ℕ} {y : Fin g.natDegree → B'}
    (hy : ∀ (S : Type u) [CommRing S] (σ : B' →+* S) (e : S), g.eval₂ (σ.comp ι.hom) e = 0 →
      (∑ i : Fin g.natDegree, σ (y i) * e ^ (i : ℕ)) ^ d = 1 + σ (ι t) * e)
    {e : FractionRing (Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤) ⧸ p.1)} (he : g.eval₂ (bK hB X R p) e = 0) :
    ∃ v, v ^ d = Ψ (1 + bK hB X R p t * e) := by
  have hΨK : Ψ.comp (bK hB X R p) = (bK₁ hB X R ι d₁ p₁).comp ι.hom :=
    RingHom.ext (bK_key hB X R ι d₁ p p₁ Ψ hΨ)
  have hroot : g.eval₂ ((bK₁ hB X R ι d₁ p₁).comp ι.hom) (Ψ e) = 0 :=
    (congrArg (fun φ => g.eval₂ φ (Ψ e)) hΨK).symm.trans
      ((Polynomial.hom_eval₂ g (bK hB X R p) Ψ e).symm.trans ((congrArg Ψ he).trans (map_zero Ψ)))
  refine ⟨_, (hy _ (bK₁ hB X R ι d₁ p₁) (Ψ e) hroot).trans ?_⟩
  exact ((Ψ.map_add 1 (bK hB X R p t * e)).trans (congrArg₂ (· + ·) Ψ.map_one
    ((Ψ.map_mul (bK hB X R p t) e).trans (congrArg (· * Ψ e) (bK_key hB X R ι d₁ p p₁ Ψ hΨ t))))).symm

end Ring

section UK

end UK

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2ZarCh =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2ZarCh): the chart toolbox for the global step

GLOB/REL PLAN v1 (file LocU+ZarCh). `c : A1 k ⟶ P` an open immersion, `D = chEt c φ` (`φ : k[X] ⟶ B`).
* `subsingleton_fib_toDF`, `nonempty_fib_toDF`, `range_toDF`: the one-point chart conditions survive a shrink
  `D_f ⟶ D` when `f` does not vanish at the special point;
* `isLocalization_away_toDF`, `comap_injective_toDF`: O2Pb (Zar) for `toDF`;
* `etale_chEt_locF`, `isOpenImmersion_chEt_locF`: `D_g := chEt c (k[X] ⟶ k[X]_g)` is an open of `P`;
  `opnDg c g := c(D(g))` its range;
* `liftDg`, `toDg`: `D_f ⟶ D_g` over `P` when `φ g` is a unit in `B_f`;
* `secD`, `secD_prT`: the section `opEt U ⟶ D ×_P U` for an open immersion `D` whose range contains `U`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtDeg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtPBC.EtShap

universe u

section Shrink

variable {k : Type u} [Field k] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{u}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (f : B)

/-- O2Pb (Zar) for `toDF`. -/
theorem isLocalization_away_toDF (X R : P.Etale) [IsAffine ((etPull (prd (chEt c φ) X).hom).obj R).left] :
    letI := (wm (R := R) (prdMap (toDF c φ f) X)).appTop.hom.toAlgebra
    IsLocalization.Away (bW (Spec.map φ ≫ c) X R f)
      Γ(((etPull (prd (chEt c (φ ≫ locF f)) X).hom).obj R).left, ⊤) :=
  isLocalization_away_wm R (Spec.map φ ≫ c) f (Spec.map (φ ≫ locF f) ≫ c) (toDF c φ f) rfl X

end Shrink

section Dg

end Dg

section Sec

end Sec

end RamanujanPetersson.EtPBC.EtDeg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km9a =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km9a): roots of unity on the Shapiro pieces

Setting of O2Km6 (`D = Spec B` over `𝔸¹ ⊆ P`, `D_o = D ×_P Uo` affine, `R` affine with constant degree `n` over
`D_o`, `W = D_o ×_P R`), plus a primitive `N`-th root of unity `ζ0 ∈ k` and `N • Λ = 0`.
* `fW p : k →+* Frac(Γ(W) ⧸ p)`, `ζW p`, `hζW` (primitive), `hζWΓ` (fixed by `π₁`);
  (the hypotheses `hζ`, `hζΓ` of `ext_mem_of_kum`, O2Km9b).
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

section Zeta

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left]

variable {N : ℕ} {ζ0 : k} (hζ0 : IsPrimitiveRoot ζ0 N)

/-- The image of `ζ0` in `maxUnram (Γ(W) ⧸ p)`. -/
noncomputable def ζW (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) :
    maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)
      (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)) :=
  algebraMap _ _ (fW c φ R p ζ0)

end Zeta

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PPTd =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks

For chart neighbourhoods `D = chEt c φ`, `D₁ = chEt c φ₁` and any `dm : D₁ ⟶ D` in `P.Etale`:
* `left_spec_map`: `dm.left ≫ Spec.map φ = Spec.map φ₁`; **`shG_wm`**: `wm (prdMap dm) ≫ shG c φ = shG c φ₁`;
* `sXW c φ R ζ0 ∈ Γ(W)` (the image of `ζ0 ∈ k`), `ζW_eq`, **`wm_appTop_sXW`**;
* **`locCls_kapS_chart`**: `locCls_kapS_shrink` (O2PPTc) with the roots of unity `ζW` of O2Km9a on both sides;
* **`piece_unique_away`**: if `Γ(X₁) = Γ(X)[1/s]` along `f`, at most one piece of `X₁` lies over a piece of `X`
  (applies to `toDF` by `isLocalization_away_toDF`, O2ZarCh).
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

section Chart

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  {Uo : P.Opens} (R : P.Etale) [IsAffine R.left] (dm : chEt c φ₁ ⟶ chEt c φ)

def ζW_eq {N : ℕ} {ζ0 : k} (_hζ0 : IsPrimitiveRoot ζ0 N) (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) :
    ζW c φ R (ζ0 := ζ0) p = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)))
      (algebraMap (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)) (Ideal.Quotient.mk p.1 (sXW c φ R ζ0))) :=
  rfl

end Chart

section ChartPPT

end ChartPPT

end RamanujanPetersson.EtPBC.EtKum

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

/-- **Every fibre has at most the generic number of points.** -/
theorem card_le_genPt (x : P1 k) :
    Nat.card ((geomPtAt x).point.fiber.obj W) ≤ Nat.card ((geomPtAt (P1.genPt k)).point.fiber.obj W) := by
  obtain ⟨O, hO, hxO, hle⟩ := exists_nbhd_card_le W x
  exact hle _ (genPt_mem_of_isOpen k hO hxO)

/-- **The generic-degree locus is open.** -/
theorem isOpen_genDeg :
    IsOpen {x : P1 k | Nat.card ((geomPtAt (P1.genPt k)).point.fiber.obj W) ≤
      Nat.card ((geomPtAt x).point.fiber.obj W)} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨O, hO, hxO, hle⟩ := exists_nbhd_card_le W x
  exact ⟨O, fun y hy => le_trans hx (hle y hy), hO, hxO⟩

/-- **The generic-degree locus is an open with finite complement.** -/
theorem exists_genDeg_open :
    ∃ U : (P1 k).Opens, (∀ x : P1 k, x ∈ U ↔ Nat.card ((geomPtAt x).point.fiber.obj W) =
      Nat.card ((geomPtAt (P1.genPt k)).point.fiber.obj W)) ∧ ((U : Set (P1 k))ᶜ).Finite := by
  have : AlgebraicGeometry.IsNoetherian (P1 k) := ⟨⟩
  refine ⟨⟨_, isOpen_genDeg k W⟩, fun x => ⟨fun hx => le_antisymm (card_le_genPt k W x) hx, fun hx => hx.ge⟩, ?_⟩
  refine finite_of_isClosed_pts (isOpen_genDeg k W).isClosed_compl fun x hx => ?_
  refine P1.isClosed_of_ne_genPt k x fun h => hx ?_
  subst h
  show Nat.card ((geomPtAt (P1.genPt k)).point.fiber.obj W) ≤ Nat.card ((geomPtAt (P1.genPt k)).point.fiber.obj W)
  exact le_rfl

end GenDeg

end RamanujanPetersson.EtPBC.EtDeg

end

end


