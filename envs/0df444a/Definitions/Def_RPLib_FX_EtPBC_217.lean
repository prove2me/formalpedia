-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_217
-- name    : RPLib_FX_EtPBC_217
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:53:44.830884+00:00
-- url     : https://prove2.me/theorems/ba8d422e-6f2c-5c0c-98d8-4287cc9b87bf
-- title:
--   Proper base change for the projective line, library file 217
-- statement:
--   File 217 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_H1Q`: S4-EtPBC-A, R2 for `P¹_S`: degree-1 base change for every sheaf, given the curve case
--   * `S4.Def_RP_EtPBC_A_PBCStkb`: S4-EtPBC-A, L1g part 2: degree `0` (`pbcEquivZero`) and **`pbc_of_germs`** (all degrees; see `PBCStk` for the
--   * `S4.Def_RP_EtPBC_A_O1G1`: S4-EtPBC-A, O1 glue: **degree-1 base change on `P¹_S`**
--   * `S4.Def_RP_EtPBC_A_O2PP5b`: S4-EtPBC-A, O2 PP' (O2PP5b): PP' for every `IsLoc` class at a bad chart point
--   * `S4.Def_RP_EtPBC_A_O2Gen2`: S4-EtPBC-A, O2 Gen2: one-point classes on `P¹` are sums of point classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_207
import Definitions.Def_RPLib_FX_EtPBC_215
import Definitions.Def_RPLib_FX_EtPBC_216

/-!
# Proper base change for the projective line, library file 217

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_H1Q`: S4-EtPBC-A, R2 for `P¹_S`: degree-1 base change for every sheaf, given the curve case
* `S4.Def_RP_EtPBC_A_PBCStkb`: S4-EtPBC-A, L1g part 2: degree `0` (`pbcEquivZero`) and **`pbc_of_germs`** (all degrees; see `PBCStk` for the
* `S4.Def_RP_EtPBC_A_O1G1`: S4-EtPBC-A, O1 glue: **degree-1 base change on `P¹_S`**
* `S4.Def_RP_EtPBC_A_O2PP5b`: S4-EtPBC-A, O2 PP' (O2PP5b): PP' for every `IsLoc` class at a bad chart point
* `S4.Def_RP_EtPBC_A_O2Gen2`: S4-EtPBC-A, O2 Gen2: one-point classes on `P¹` are sums of point classes
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_H1Q =====
section

/-!
# S4-EtPBC-A, R2 for `P¹_S`: degree-1 base change for every sheaf, given the curve case

* `isAffineHom_to_fib`: maps from affine schemes to a geometric fibre of a separated morphism are affine;
* **`bcSurj_one_qV`**: `BCSurj 1` for every sheaf on `P¹_S` at `s`, given `BCSurj 1` for every `π_* M_Y` with
  `π : Y ⟶ P¹_S` finite and `M` finite (`Λ` finite; the curve case R4).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

variable {Λ : Type u} [CommRing Λ] {S : Scheme.{u}}

/-- **Degree-1 base change for every sheaf on `P¹_S`**, given the curve case. -/
theorem bcSurj_one_qV (K : Type u) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]
    (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) [IsIso (s.pt ≫ gK)] [IsNoetherian S]
    [LocallyOfFiniteType gK] [IsNoetherianRing Λ] [Finite Λ]
    (hC : ∀ {Y : Scheme.{u}} (π : Y ⟶ PV K gK) [IsFinite π] (M : ModuleCat.{u} Λ) [Finite M],
      BCSurj Λ (qV K gK) s 1 ((push π Λ).obj (constSh Λ Y M)))
    (G : EtSh Λ (PV K gK)) : BCSurj Λ (qV K gK) s 1 G :=
  bcSurj_one_of_fgt (qV K gK) s (fun h hZ => isAffineHom_to_fib (qV K gK) s h hZ)
    (bcSurj_one_fgt_qV K p gK s hC) G

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_PBCStkb =====
section

/-!
# S4-EtPBC-A, L1g part 2: degree `0` (`pbcEquivZero`) and **`pbc_of_germs`** (all degrees; see `PBCStk` for the
statement in words)
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Degree `0`.** -/
def pbcEquivZero (F : EtSh Λ P) (hI : BCInj Λ g s 0 F) (hS : BCSurj Λ g s 0 F) :
    ToType ((s.stalkF Λ).obj (((push g Λ).rightDerived 0).obj F)) ≃+ H Λ ((pull (fibι g s) Λ).obj F) 0 :=
  ((s.stalkF Λ).mapIso ((push g Λ).rightDerivedZeroIsoSelf.app F)).toLinearEquiv.toAddEquiv.trans
    (stalkEquiv s (sec0Ext_map Λ g F) hI hS)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O1G1 =====
section

/-!
# S4-EtPBC-A, O1 glue: **degree-1 base change on `P¹_S`**

* `coverLiftAt₂_ft`: `CoverLiftAt₂` for a finite-type algebra over a perfect field (Artin approximation `artinApproxAt`
  fed into `coverLiftAt₂_of_approx`);
* `liftT_qV`: the lifting property `LiftT (qV K gK) s π` for every finite `π : Y ⟶ P¹_S`, from an affine noetherian
  etale neighbourhood of `s`;
* **`bcSurj_one_PV`**: `BCSurj 1` for every sheaf on `P¹_S` at a geometric point `s` with `s ≫ g_K` an isomorphism
  (`S` noetherian, locally of finite type over a perfect field `K`, `Λ` finite noetherian).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

end RamanujanPetersson.EtPBC.Cov

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.Cov

universe u

variable (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S)
  [IsIso (s.pt ≫ gK)]

/-- **Degree-1 base change for every sheaf on `P¹_S`** at a geometric point `s` with `s ≫ g_K` an isomorphism. -/
theorem bcSurj_one_PV {Λ : Type u} [CommRing Λ] (p : ℕ) [ExpChar K p] [PerfectRing K p] [IsNoetherian S]
    [LocallyOfFiniteType gK] [IsNoetherianRing Λ] [Finite Λ] (G : EtSh Λ (PV K gK)) :
    BCSurj Λ (qV K gK) s 1 G := by
  haveI : PerfectField K := PerfectRing.toPerfectField K p
  haveI : IsClosedImmersion s.pt := T3d.isClosedImmersion_of_isIso_comp gK s.pt
  haveI : IsClosedImmersion (fibι (qV K gK) s) := T3d.isClosedImmersion_fibι (qV K gK) s
  haveI : CompactSpace (fib (qV K gK) s) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (qV K gK) s.pt)
  exact GenGeo.bcSurj_one_qV K p gK s (fun π _ M _ => T2.bcSurj_one_push_of_liftT (qV K gK) s
    (GenGeo.bcSurj_zero_qV K p gK s) π M (liftT_qV K gK s π)) G

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP5b =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP5b): PP' for every `IsLoc` class at a bad chart point

* **`pp_isLoc`**: with `R` of constant degree `n` over a cofinite `U₀ ∌ c(a)` of good points, every `IsLoc` class at
  `c(a)` lies in `Gr` (`exists_g_chart`, `isLoc_chart` (O2PP5a), `pp_all` (O2PP4g)).
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

section PPIsLoc

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {U₀ Uz : P.Opens} (h₀ : U₀ ≤ Uz) {a : k} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ (c (A1pt k a)))
  (R : P.Etale) [IsAffine R.left] (hU₀ : ((U₀ : Set P)ᶜ).Finite)
  (Λ : Type) [CommRing Λ] (n : ℕ)
  (hn : ∀ y : (opEt U₀).left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt U₀).hom).obj R)) = n)
  {N : ℕ} [NeZero N] {ζ0 : k} (hζ0 : IsPrimitiveRoot ζ0 N)

set_option maxHeartbeats 1000000 in
include h₀ hz hU₀ hn hζ0 in
/-- **PP' for `IsLoc` classes at `c(a) ∉ U₀`**: shrink to a domain chart over `U₀` (`isLoc_chart`), then `pp_all`. -/
theorem pp_isLoc (hΛ : ∀ x : Λ, N • x = 0) [IsAlgClosed k]
    (hGal : ∀ b : k, Subsingleton (Gal (c (A1pt k b))))
    (Gr : AddSubgroup (Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2)) (good : P → Prop)
    (hGd : ∀ x, good x → ∀ γ, IsLoc Λ (freeSh Λ R) x γ → γ ∈ Gr)
    (hgood : ∀ x ∈ U₀, good x) (hgoodc : ∀ x ∉ Set.range c, good x)
    (hfin : (Set.range c)ᶜ.Finite) (hclc : ∀ x ∉ Set.range c, IsClosed ({x} : Set P))
    (hclA : ∀ b : k, IsClosed ({c (A1pt k b)} : Set P))
    (hpt : ∀ y : A1 k, y.asIdeal ≠ ⊥ → ∃ b, y = A1pt k b)
    (β : Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2) (hβ : IsLoc Λ (freeSh Λ R) (c (A1pt k a)) β) : β ∈ Gr := by
  have hzU : c (A1pt k a) ∉ U₀ := fun hm => (hz _).1 (h₀ hm) rfl
  obtain ⟨g₀, hga, hg₀⟩ := exists_g_chart c a U₀ hU₀
  have hg0 : g₀ ≠ 0 := fun h => hga (by rw [h, Polynomial.eval_zero])
  have : Finite ↥((U₀ : Set P)ᶜ) := hU₀.to_subtype
  have : Finite {b : k // c (A1pt k b) ∉ U₀ ∧ b ≠ a} :=
    Finite.of_injective (fun b => (⟨c (A1pt k b.1), b.2.1⟩ : ↥((U₀ : Set P)ᶜ)))
      (fun b b' hbb => Subtype.ext (A1pt_injective (c.isOpenEmbedding.injective (congrArg Subtype.val hbb))))
  haveI : IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt U₀)).left :=
    isAffine_prdUo c _ (hUo_of_range c _ hg₀ hzU)
  obtain ⟨B, φ, _, _, hD, hDn, hDr, κ, rfl⟩ := isLoc_chart c h₀ hz hg₀ hga β hβ
  haveI : IsAffine (prd (chEt c φ) (opEt U₀)).left := isAffine_prdUo c φ (hUo_of_range c φ hDr hzU)
  haveI : Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt U₀)).hom).obj R).left, ⊤)) := Fintype.ofFinite _
  haveI : DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt U₀)).hom).obj R).left, ⊤)) :=
    Classical.decEq _
  exact pp_all c h₀ hz R hg₀ φ hD hDn hDr Λ n hn (isDomain_loc_W c φ R) hζ0 hΛ hGal hg0 hga Gr good hGd hgood
    hgoodc hfin hclc hclA hpt κ

end PPIsLoc

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gen2 =====
section

/-!
# S4-EtPBC-A, O2 Gen2: one-point classes on `P¹` are sums of point classes

* `genT Λ hN hΛ T`: the subgroup generated by point classes `PtCls Λ c hN hΛ T` over all charts `c : A¹ ⟶ P¹`;
* `comp_mem_genT`: `genT` is stable under `x ↦ x ∘ Λ[r]`;
* `good_mem_genT`: an `IsLoc` class at a point of generic degree lies in `genT` (`isLoc_free_good`);
* `isLoc_comp_mem`: for `R` affine, every `IsLoc` class `β'` of `Λ[R]` has `β' ∘ Λ[r] ∈ genT` (`pp_isLoc` over a
  moved chart `chartM c₀` missing a generic-degree point);
* `isLoc_mem_genT`: every `IsLoc` class of `Λ[T]` lies in `genT` (`isLoc_free_res`);
* **`gen_free`**: with `N = l ^ m`, every class in `Ext² (Λ, Λ[T])` lies in `genT` (`mem_locSpan_P1`).
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
  RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtCompact.PushStk RamanujanPetersson.EtCompact.PushBC

section Gen

variable {k : Type} [Field k] [IsAlgClosed k] (Λ : Type) [CommRing Λ] {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0)
  (hΛ : ∀ x : Λ, N • x = 0)

set_option maxHeartbeats 1000000 in
theorem isLoc_comp_mem (R T : (P1 k).Etale) [IsAffine R.left] (r : R ⟶ T) (z : P1 k)
    (β' : Ext.{0} (freeSh Λ (etId (P1 k))) (freeSh Λ R) 2) (hβ' : IsLoc Λ (freeSh Λ R) z β') :
    β' ∈ compSub r (genT Λ hN hΛ T) := by
  have hzc := isClosed_of_isLoc hβ'
  obtain ⟨Ug, hUg, hUgf⟩ := exists_genDeg_open k R
  have hS : ((Ug : Set (P1 k))ᶜ ∪ {z}).Finite := hUgf.union (Set.finite_singleton z)
  obtain ⟨c₀, hc₀⟩ := (hS.preimage (fun _ _ _ _ h => mobP_infPt_injective h)).exists_notMem
  have hiU : mobP k c₀ (P1.infPt k) ∈ Ug := by
    by_contra h
    exact hc₀ (Or.inl h)
  have hiz : mobP k c₀ (P1.infPt k) ≠ z := fun h => hc₀ (Or.inr h)
  obtain ⟨a', ha'⟩ := exists_A1pt_of_mem_range (chartM k c₀) z hzc ((mem_range_chartM c₀ z).2 (Ne.symm hiz))
  let Uz : (P1 k).Opens := ⟨{z}ᶜ, hzc.isOpen_compl⟩
  have hz : ∀ x : P1 k, x ∈ Uz ↔ x ≠ chartM k c₀ (A1pt k a') := fun x => by rw [ha']; exact Iff.rfl
  have h₀ : Ug ⊓ Uz ≤ Uz := inf_le_right
  have hU₀ : (((Ug ⊓ Uz : (P1 k).Opens) : Set (P1 k))ᶜ).Finite := by
    refine hS.subset ?_
    intro x hx
    by_cases h : x ∈ Ug
    · right
      by_contra h'
      exact hx ⟨h, h'⟩
    · left
      exact h
  have hn : ∀ y : (opEt (Ug ⊓ Uz)).left,
      Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt (Ug ⊓ Uz)).hom).obj R)) =
        Nat.card ((geomPtAt (P1.genPt k)).point.fiber.obj R) := fun y => by
    rw [card_fib_etPull (opEt (Ug ⊓ Uz)).hom R y]
    exact (hUg _).1 (show _ ∈ (Ug : Set (P1 k)) ∩ (Uz : Set (P1 k)) from hom_mem_of_map (𝟙 (opEt (Ug ⊓ Uz))) y).1
  obtain ⟨ζ0, hζ0⟩ := exists_primitiveRoot_of_ne hN
  have hβ'' : IsLoc Λ (freeSh Λ R) (chartM k c₀ (A1pt k a')) β' := by rw [ha']; exact hβ'
  refine pp_isLoc (chartM k c₀) h₀ hz R hU₀ Λ _ hn hζ0 hΛ (fun b => chart_hGal (chartM k c₀) b)
    (compSub r (genT Λ hN hΛ T)) (fun x => Nat.card ((geomPtAt x).point.fiber.obj R) =
      Nat.card ((geomPtAt (P1.genPt k)).point.fiber.obj R))
    (fun x hx γ hγ => comp_mem_genT Λ hN hΛ r (good_mem_genT Λ hN hΛ R x hx γ hγ))
    (fun x hx => (hUg x).1 (show x ∈ (Ug : Set (P1 k)) ∩ (Uz : Set (P1 k)) from hx).1) ?_ ?_
    (chart_hclc (chartM k c₀)) (chart_hclA (chartM k c₀)) A1_hpt β' hβ''
  · intro x hx
    have hx' : x = mobP k c₀ (P1.infPt k) := by
      by_contra h
      exact hx ((mem_range_chartM c₀ x).2 h)
    rw [hx']
    exact (hUg _).1 hiU
  · refine (Set.finite_singleton (mobP k c₀ (P1.infPt k))).subset ?_
    intro x hx
    by_contra h
    exact hx ((mem_range_chartM c₀ x).2 h)

end Gen

section Free

end Free

end RamanujanPetersson.EtPBC.EtKum

end

end


