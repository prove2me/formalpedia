-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_091
-- name    : RPLib_FX_EtPBC_091
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:08:29.750822+00:00
-- url     : https://prove2.me/theorems/677afdee-415f-5d00-82a6-0b4df2ba78a4
-- title:
--   Proper base change for the projective line, library file 091
-- statement:
--   File 091 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_Inj0d`: S4-EtPBC-A, G1d part 1: the open `good` (complement of the closed image of the support); `goodPt` is in `Inj0dg`
--   * `S4.Def_RP_EtPBC_A_Inj0f`: S4-EtPBC-A, G1d part 3: **`bcInj_zero`** (base change is injective on germs in degree `0` for universally closed `g`)
--   * `S4.Def_RP_EtPBC_A_O2UK2c`: S4-EtPBC-A, O2 M6 (O2UK2c): Kummer classes of `1 + t e` die under `ε_loc`
--   * `S4.Def_RP_EtPBC_A_O2T4e`: S4-EtPBC-A, O2 S5d (O2T4e): `clsD_addF`, `clsD_graph`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_048
import Definitions.Def_RPLib_FX_EtPBC_081

/-!
# Proper base change for the projective line, library file 091

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_Inj0d`: S4-EtPBC-A, G1d part 1: the open `good` (complement of the closed image of the support); `goodPt` is in `Inj0dg`
* `S4.Def_RP_EtPBC_A_Inj0f`: S4-EtPBC-A, G1d part 3: **`bcInj_zero`** (base change is injective on germs in degree `0` for universally closed `g`)
* `S4.Def_RP_EtPBC_A_O2UK2c`: S4-EtPBC-A, O2 M6 (O2UK2c): Kummer classes of `1 + t e` die under `ε_loc`
* `S4.Def_RP_EtPBC_A_O2T4e`: S4-EtPBC-A, O2 S5d (O2T4e): `clsD_addF`, `clsD_graph`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_Inj0d =====
section

/-!
# S4-EtPBC-A, G1d part 1: the open `good` (complement of the closed image of the support); `goodPt` is in `Inj0dg`
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- The open complement of `bad`. -/
def good [UniversallyClosed g] (j : Nbhd s) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0) :
    j.1.left.Opens :=
  ⟨(bad Λ g s j G α)ᶜ, ((pullback.fst j.1.hom g).isClosedMap _ (isClosed_supp G _)).isOpen_compl⟩

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0f =====
section

/-!
# S4-EtPBC-A, G1d part 3: **`bcInj_zero`** (base change is injective on germs in degree `0` for universally closed `g`)
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- Every germ of the restriction of `sec0 α` to `good` vanishes. -/
theorem good_germ_zero [UniversallyClosed g] (j : Nbhd s) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0)
    (y : P) (b : (geomPtAt y).point.fiber.obj ((etPull g).obj (opn j.1 (good Λ g s j G α)))) :
    ((geomPtAt y).point.toPresheafFiber ((etPull g).obj (opn j.1 (good Λ g s j G α))) b G.obj).hom
      ((G.obj.map ((etPull g).map (opnι j.1 (good Λ g s j G α))).op).hom (sec0 Λ g s j G α)) = 0 := by
  have hw := ConcreteCategory.congr_hom ((geomPtAt y).point.toPresheafFiber_w
    ((etPull g).map (opnι j.1 (good Λ g s j G α))) b G.obj) (sec0 Λ g s j G α)
  refine hw.trans (germ_eq_zero_of_not_mem_supp G _ y _ ?_)
  intro hmem
  have e := congrArg (fun φ => φ.base (fpt y b)) (etPull_map_left_fst g (opnι j.1 (good Λ g s j G α)))
  have hO : (pullback.fst j.1.hom g).base (fpt y ((geomPtAt y).point.fiber.map
      ((etPull g).map (opnι j.1 (good Λ g s j G α))) b)) ∈ good Λ g s j G α :=
    (congrArg (fun z => z ∈ good Λ g s j G α) e).mpr
      (opnι_mem j.1 (good Λ g s j G α) ((pullback.fst (opn j.1 (good Λ g s j G α)).hom g).base (fpt y b)))
  exact (show _ ∉ bad Λ g s j G α from hO) ⟨_, hmem, rfl⟩

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2UK2c =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UK2c): Kummer classes of `1 + t e` die under `ε_loc`

Setting of O2Km9c at `z = c(a)` with `Uo` as the Shapiro base (`θ := theta Λ R n hn (prT D (opEt Uo))`, O2Th1b).
* **`uk_kill`**: if `e ∈ Frac(Γ(W) ⧸ p)` is a root of a monic `g ∈ B[X]`, `t ∈ B` vanishes at a point `χ` of `D`
  over `z`, `d` is a unit in `B` and `α ^ d = 1 + t e`, then `ε_loc(D) ∘ θ⁻¹(kapS p (kumD α)) = 0`.
  (A `def`: theorem types are folded at `.olean` export, which is slow on concrete-`W` statements.)
  Proof: `uk_root'` (O2UK1/UK2b) gives `B → B'` etale with a `d`-th root of `1 + t e`; `exists_goodChart` (UK2a) a
  chart `D₁ ⟶ Spec B'` with one geometric point over `z`; `locCls_shrink`, `theta_natural` (O2Th1c) and
  `resLE_kapS_kumD_eq_zero` (O2KapP) with `exists_pow_of_uk` (UK2b).
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

section UK2

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {Uo Uz : P.Opens}
  (h : Uo ≤ Uz) {a : k} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a)) (hG : Subsingleton (Gal (c (A1pt k a))))
  (hD : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
  (hDn : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
  (hDr : ∀ v : (chEt c φ).left, (chEt c φ).hom v ∈ Uo ∨ (chEt c φ).hom v = c (A1pt k a))
  (R : P.Etale) [IsAffine R.left] [IsAffine ((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))]
  (hW : ∀ (m : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (Λ : Type) [CommRing Λ] {N : ℕ} [NeZero N]
  {ζ : ∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1))}
  (hζ : ∀ p, IsPrimitiveRoot (ζ p) N)
  (hζΓ : ∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)
    (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)))), σ (ζ p) = ζ p)
  (n : ℕ) (hn : ∀ y : (opEt Uo).left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt Uo).hom).obj R)) = n)

include hG hz hDr in
/-- **The charts of `uk_kill`** (no `Ext`): an etale `B → B'` with a `d`-th root of `1 + t e` (UK2b `uk_root'`) and a
good chart `D₁ ⟶ Spec B'` with exactly one geometric point over `z` (UK2a `exists_goodChart`). -/
theorem exists_ukChart {K : Type} [Field K] (χ : B →+* K)
    (hχ : (chEt c φ).hom (⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩ : Spec B) = c (A1pt k a))
    {g : B[X]} (hg : g.Monic) (hgn : 0 < g.natDegree) {t : B} (ht : χ t = 0) {d : ℕ} (hd : IsUnit (d : B)) :
    ∃ (B' : CommRingCat.{0}) (ι : B ⟶ B') (_ : Etale (Spec.map ι)) (y : Fin g.natDegree → B'),
      (∀ (S : Type) [CommRing S] (σ : B' →+* S) (e : S), g.eval₂ (σ.comp ι.hom) e = 0 →
        (∑ i : Fin g.natDegree, σ (y i) * e ^ (i : ℕ)) ^ d = 1 + σ (ι t) * e) ∧
      ∃ (B₁ : CommRingCat.{0}) (φ₁ : CommRingCat.of k[X] ⟶ B₁) (_ : Etale (Spec.map φ₁ ≫ c))
        (_ : chEt c φ₁ ⟶ Scheme.Etale.mk (Spec.map ι ≫ (Spec.map φ ≫ c))),
        Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ₁)) ∧
        Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ₁)) ∧
        ∀ v : (chEt c φ₁).left, (chEt c φ₁).hom v ∈ Uo ∨ (chEt c φ₁).hom v = c (A1pt k a) := by
  have hzc : IsClosed ({c (A1pt k a)} : Set P) := by
    have e1 : ({c (A1pt k a)} : Set P) = (Uz : Set P)ᶜ := Set.ext fun x => by
      rw [Set.mem_singleton_iff, Set.mem_compl_iff, SetLike.mem_coe, hz x, not_not]
    rw [e1]
    exact Uz.isOpen.isClosed_compl
  obtain ⟨B', ι, hι, χ', y, hχ', hy⟩ := uk_root' χ hg hgn ht hd
  refine ⟨B', ι, hι, y, hy, ?_⟩
  let v' : Spec B' := ⟨RingHom.ker χ', RingHom.ker_isPrime χ'⟩
  have hv' : Spec.map ι v' = (⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩ : Spec B) :=
    PrimeSpectrum.ext ((RingHom.comap_ker χ' ι.hom).trans (congrArg RingHom.ker hχ'))
  have hNv : (Scheme.Etale.mk (Spec.map ι ≫ (Spec.map φ ≫ c))).hom v' = c (A1pt k a) :=
    (congrArg (fun x => (chEt c φ).hom x) hv').trans hχ
  obtain ⟨n₀, -, -⟩ := exists_lift_fib (toTop (Scheme.Etale.mk (Spec.map ι ≫ (Spec.map φ ≫ c))))
    (c (A1pt k a)) (topPt (c (A1pt k a))) v' (hNv.trans (fpt_topPt _ _).symm)
  exact exists_goodChart c hzc hG (Scheme.Etale.mk (Spec.map ι ≫ (Spec.map φ ≫ c)))
    (fun v => ⟨Spec.map φ (Spec.map ι v), rfl⟩) n₀ (fun v => hDr (Spec.map ι v))

end UK2

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4e =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4e): `clsD_addF`, `clsD_graph`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section GenAddF
universe w v₁ u₁ v₂ u₂ v₃ u₃

end GenAddF

section Split

variable {k : Type} [Field k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

set_option backward.isDefEq.respectTransparency false in
theorem clsD_addF {F : EtSh Λ P} {G : EtSh Λ (chEt c φ).left} (f f' : G ⟶ (res (chEt c φ).hom Λ).obj F)
    (Y : H Λ ((res (toD1 c φ a).left Λ).obj G) 1) :
    clsD c φ a hUz hS (f + f') Y = clsD c φ a hUz hS f Y + clsD c φ a hUz hS f' Y :=
  cls_addF_gen (res (toD1 c φ a).left Λ) f f' ((resCompIso Λ (toD1 c φ a)).hom.app F) Y
    (hS.extClass.comp (Ext.mk₀ (freeMap Λ (isoT c φ hUz).inv)) (add_zero 1)) (extFree Λ (W1 c φ a) F 1)

end Split

section Graph

end Graph

end RamanujanPetersson.EtPBC.EtMV

end

end


