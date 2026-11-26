-- Prove2me | Definitions.Def_RPLib_FX_GOSC_08
-- name    : RPLib_FX_GOSC_08
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:37:28.659846+00:00
-- url     : https://prove2.me/theorems/89f01027-52f8-5ce9-9243-559819a468d4
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 08 of 14
-- statement:
--   File 08 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_PtPro`: S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)
--   * `S4.Def_RP_Lefschetz_PtCov`: S4-Lefschetz, L5c3: one finite level for all blocks, normalized Frobenius elements at points
--   * `S4.Def_RP_Lefschetz_PtData`: S4-Lefschetz, L6b: the point data of the trace formula
--   * `S4.Def_RP_GOS_B_Cnt`: S4-GOS-B, part Cnt: the twisted Frobenius traces of the perfect complex are `l`-independent point counts
--   * `S4.Def_RP_GOS_B_Sub`: S4-GOS-B, part Sub: subgroup sums of the point counts (O6b, group theory)
--   * `S4.Def_RP_GOS_B_Cov`: S4-GOS-B, part Cov: the concrete cover `M ⊆ K_U` over `K = 𝔽_q(X)` (O4u, O8b)
--   * `S4.Def_RP_GOS_B_GPt`: S4-GOS-B, part GPt: Lefschetz count on the concrete cover `M ⊇ M^H` (O6c, per point)
--   * `S4.Def_RP_GOS_B_PlKc`: S4-GOS-B, part PlKc: a function field over `𝔽_q` and over its full constant field `k_E` (O6d glue)
--   * `S4.Def_RP_GOS_B_WeilE`: S4-GOS-B, part WeilE: the affine point counts of any function field satisfy an integer recurrence (O6d)
--   * `S4.Def_RP_GOS_B_GCnt`: S4-GOS-B, part GCnt: subgroup sums of the point counts on the concrete cover (O6c)
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_F2_046
import Definitions.Def_RPLib_FX_GOSC_07

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 08 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_PtPro`: S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)
* `S4.Def_RP_Lefschetz_PtCov`: S4-Lefschetz, L5c3: one finite level for all blocks, normalized Frobenius elements at points
* `S4.Def_RP_Lefschetz_PtData`: S4-Lefschetz, L6b: the point data of the trace formula
* `S4.Def_RP_GOS_B_Cnt`: S4-GOS-B, part Cnt: the twisted Frobenius traces of the perfect complex are `l`-independent point counts
* `S4.Def_RP_GOS_B_Sub`: S4-GOS-B, part Sub: subgroup sums of the point counts (O6b, group theory)
* `S4.Def_RP_GOS_B_Cov`: S4-GOS-B, part Cov: the concrete cover `M ⊆ K_U` over `K = 𝔽_q(X)` (O4u, O8b)
* `S4.Def_RP_GOS_B_GPt`: S4-GOS-B, part GPt: Lefschetz count on the concrete cover `M ⊇ M^H` (O6c, per point)
* `S4.Def_RP_GOS_B_PlKc`: S4-GOS-B, part PlKc: a function field over `𝔽_q` and over its full constant field `k_E` (O6d glue)
* `S4.Def_RP_GOS_B_WeilE`: S4-GOS-B, part WeilE: the affine point counts of any function field satisfy an integer recurrence (O6d)
* `S4.Def_RP_GOS_B_GCnt`: S4-GOS-B, part GCnt: subgroup sums of the point counts on the concrete cover (O6c)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_PtPro =====
section

/-!
# S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)

* `finite_setOf_pow_eq`, `finite_quot_ker`: points with values in a finite set have finite residue rings.
* `resPt`, `jPt`: restriction `π₁(U) → Gal(L/K)` and the inclusion `O_L → O_{K_U}` (the pro-chart over `A`) for a
  finite unramified Galois level `L`, with `resPt_surjective`, `jPt_smul`.
* `exists_frob_pro`: for a point `w` of the pro-chart with `Fr ∘ w = w` on `A` (finite image), some `F ∈ π₁(U)` has
  `w ∘ F = Fr ∘ w` (finite levels by `hom_smul_trans`, then compactness of `π₁(U)`).
* `IsFrobPt Fr u F` and `exists_isFrobPt`: every point `u` of `A` has a Frobenius element.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open GalCover CurveCoh

section PtProGen

end PtProGen

section PtPro

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- **Frobenius elements exist** at points of the pro-chart (finite levels, then compactness of `π₁(U)`). -/
theorem exists_frob_pro {Ω : Type} [Field Ω] (Fr : Ω →+* Ω) (w : proChart A K A →+* Ω)
    (hFr : ∀ a : A, Fr (w (algebraMap A _ a)) = w (algebraMap A _ a))
    (hfin : (Set.range (w.comp (algebraMap A (proChart A K A)))).Finite) :
    ∃ F : Pi1 A K, ∀ b, w (F • b) = Fr (w b) := by
  classical
  let t : proChart A K A → Set (Pi1 A K) := fun b => {σ | w (σ • b) = Fr (w b)}
  have hcl : ∀ b, IsClosed (t b) := by
    intro b
    refine isClosed_of_mul_mem (fixElt A K (b : maxUnram A K)) (fixElt_isOpen A K _) _ fun σ hσ s hs => ?_
    have hsb : s • b = b := Subtype.ext hs
    show w ((σ * s) • b) = Fr (w b)
    rw [mul_smul, hsb]
    exact hσ
  have hst : ∀ S : Finset (proChart A K A), (Set.univ ∩ ⋂ b ∈ S, t b).Nonempty := by
    intro S
    obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K
      (S.image fun b : proChart A K A => ((b : maxUnram A K) : AlgebraicClosure K)) (fun x hx => by
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
        exact (b : maxUnram A K).2)
    have hLU : L ≤ maxUnram A K := by
      unfold maxUnram
      exact le_iSup (f := fun L : unramSet A K => (L : IntermediateField K (AlgebraicClosure K))) ⟨L, hL⟩
    haveI := hL.1
    haveI := hL.2.1
    haveI : IsFractionRing (integralClosure A L) L :=
      integralClosure.isFractionRing_of_finite_extension (A := A) K L
    haveI : IsGaloisGroup (L ≃ₐ[K] L) A (integralClosure A L) :=
      IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) A (integralClosure A L) K L
    haveI : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L (integralClosure A L)
    let w' : integralClosure A L →+* Ω := w.comp (jPt A K hLU)
    have hww : w'.comp (algebraMap A _) = (Fr.comp w').comp (algebraMap A _) := RingHom.ext fun a => by
      show w (jPt A K hLU (algebraMap A _ a)) = Fr (w (jPt A K hLU (algebraMap A _ a)))
      rw [jPt_algebraMap, hFr]
    haveI : Finite (integralClosure A L ⧸ RingHom.ker (Fr.comp w')) := finite_quot_ker _ (by
      refine hfin.subset ?_
      rintro _ ⟨a, rfl⟩
      refine ⟨a, ?_⟩
      show w (algebraMap A _ a) = Fr (w (jPt A K hLU (algebraMap A _ a)))
      rw [jPt_algebraMap, hFr])
    obtain ⟨g, hg⟩ := hom_smul_trans (A := A) (G := L ≃ₐ[K] L) w' (Fr.comp w') hww
    obtain ⟨F, rfl⟩ := resPt_surjective A K hLU g
    refine ⟨F, Set.mem_univ _, Set.mem_iInter₂.2 fun b hb => ?_⟩
    have hbL : ((b : maxUnram A K) : AlgebraicClosure K) ∈ L :=
      hle (IntermediateField.subset_adjoin K _ (Finset.mem_coe.2
        (Finset.mem_image_of_mem (fun b : proChart A K A => ((b : maxUnram A K) : AlgebraicClosure K)) hb)))
    have hint : IsIntegral A (⟨((b : maxUnram A K) : AlgebraicClosure K), hbL⟩ : L) := by
      have h1 : ((IntermediateField.inclusion hLU).restrictScalars A)
          (⟨((b : maxUnram A K) : AlgebraicClosure K), hbL⟩ : L) = (b : maxUnram A K) := Subtype.ext rfl
      have h2 : IsIntegral A (((IntermediateField.inclusion hLU).restrictScalars A)
          (⟨((b : maxUnram A K) : AlgebraicClosure K), hbL⟩ : L)) := by
        rw [h1]
        exact b.2
      exact (isIntegral_algHom_iff ((IntermediateField.inclusion hLU).restrictScalars A)
        (IntermediateField.inclusion hLU).toRingHom.injective).1 h2
    have hbb : b = jPt A K hLU ⟨⟨((b : maxUnram A K) : AlgebraicClosure K), hbL⟩, hint⟩ :=
      Subtype.ext (Subtype.ext rfl)
    show w (F • b) = Fr (w b)
    rw [hbb, ← jPt_smul]
    exact (hg _).symm
  obtain ⟨F, -, hF⟩ := isCompact_univ.inter_iInter_nonempty t hcl hst
  exact ⟨F, fun b => Set.mem_iInter.1 hF b⟩

end PtPro

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtCov =====
section

/-!
# S4-Lefschetz, L5c3: one finite level for all blocks, normalized Frobenius elements at points

* `exists_unramSet_fix`: a finite unramified Galois level `L` containing a finite set of `K_U`, whose fixer in
  `π₁(U)` lies in a given open subgroup; `fix_of_resPt_eq_one`, `pi_eq_of_resPt_eq`, `piBar` (`π` through
  `Gal(L/K)`), `piBar_resPt`.
* `isConj_of_isFrobPt`: two Frobenius elements at the same point are conjugate modulo an open normal subgroup.
* `kStar hq n`: the constants `x ∈ K_U` with `x ^ (q ^ n) = x` (a finite field with an `Fq`-algebra structure),
  `incStar` into the pro-chart.
* `exists_normFrob`: at every point `u` (with `Fr ∘ u = u`, finite image) there are a point `w` of the pro-chart over
  `u` and a Frobenius element `F` (`w ∘ F = Fr ∘ w`) with `w = ιS` on `kStar` (normalization by `φ ^ j`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open GalCover CurveCoh

section PtCovLevel

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

variable {A K}

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

end PtCovLevel

section KStar

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
variable {k0 : Type} [Field k0] [Fintype k0] [Algebra k0 K] {p e : ℕ} [Fact p.Prime] [CharP K p]

theorem finite_kStar (hq : Fintype.card k0 = p ^ e) (n : ℕ) (hQ : 1 < p ^ (e * n)) :
    Finite (kStar A K hq n) := by
  have h : ((kStar A K hq n : Set (maxUnram A K))).Finite :=
    (finite_setOf_pow_eq (F := maxUnram A K) hQ).subset fun x hx => hx
  exact h.to_subtype

theorem incStar_algebraMap [Algebra k0 A] [IsScalarTower k0 A K] (hq : Fintype.card k0 = p ^ e) (n : ℕ)
    (hQ : 1 < p ^ (e * n)) (c : k0) :
    incStar A K hq n hQ (algebraMap k0 _ c) = algebraMap A (proChart A K A) (algebraMap k0 A c) := by
  refine Subtype.ext ?_
  show algebraMap K (maxUnram A K) (algebraMap k0 K c) = algebraMap A (maxUnram A K) (algebraMap k0 A c)
  rw [IsScalarTower.algebraMap_apply A K (maxUnram A K), ← IsScalarTower.algebraMap_apply k0 A K]

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- **Normalized Frobenius elements**: at a point `u` of `A` (fixed by `Fr`, finite image) there are a point `w` of
the pro-chart over `u` with prescribed values `ιS` on the constants `kStar`, and `F ∈ π₁(U)` with `w ∘ F = Fr ∘ w`. -/
theorem exists_normFrob [Algebra k0 A] [IsScalarTower k0 A K] (hq : Fintype.card k0 = p ^ e) (n : ℕ)
    (hQ : 1 < p ^ (e * n)) {φ : Pi1 A K} (hφ : IsFrobLift A K (Fintype.card k0) φ)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (ιS : kStar A K hq n →+* Ω) (u : A →+* Ω)
    (hu : ∀ a, Fr (u a) = u a) (hfin : (Set.range u).Finite)
    (hι : ∀ c : k0, ιS (algebraMap k0 _ c) = u (algebraMap k0 A c)) :
    ∃ (w : proChart A K A →+* Ω) (F : Pi1 A K), w.comp (algebraMap A _) = u ∧ (∀ b, w (F • b) = Fr (w b)) ∧
      ∀ x, w (incStar A K hq n hQ x) = ιS x := by
  haveI := faithfulSMul_proChart A K
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by
    rw [h, mul_zero, pow_zero] at hQ
    exact lt_irrefl 1 hQ
  obtain ⟨w1, hw1⟩ := exists_hom_extend (B := proChart A K A) u
  have hwa : ∀ a, w1 (algebraMap A _ a) = u a := fun a => RingHom.congr_fun hw1 a
  obtain ⟨F1, hF1⟩ := exists_frob_pro A K Fr w1 (fun a => by rw [hwa, hu]) (by rw [hw1]; exact hfin)
  haveI := finite_kStar A K hq n hQ
  obtain ⟨j, hj⟩ := CP4a.exists_frob_pow_of_finite (k0 := k0) (w1.comp (incStar A K hq n hQ)) ιS (fun c => by
    rw [RingHom.comp_apply, incStar_algebraMap, hwa, hι])
  have hconst : ∀ x : kStar A K hq n, IsConst (Fintype.card k0) (x : maxUnram A K) := fun x =>
    ⟨n, hn, (mem_kStar A K hq n x).1 x.2⟩
  refine ⟨w1.comp (MulSemiringAction.toRingHom (Pi1 A K) (proChart A K A) (φ ^ j)), (φ ^ j)⁻¹ * F1 * φ ^ j,
    ?_, ?_, ?_⟩
  · refine RingHom.ext fun a => ?_
    show w1 ((φ ^ j) • algebraMap A (proChart A K A) a) = u a
    rw [smul_algebraMap_proChart, hwa]
  · intro b
    show w1 ((φ ^ j) • (((φ ^ j)⁻¹ * F1 * φ ^ j) • b)) = Fr (w1 ((φ ^ j) • b))
    rw [← mul_smul, mul_assoc, mul_inv_cancel_left, mul_smul, hF1]
  · intro x
    show w1 ((φ ^ j) • incStar A K hq n hQ x) = ιS x
    rw [hj x, RingHom.comp_apply, ← map_pow]
    congr 1
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow]
    exact frob_pow_apply hφ (hconst x) j

end KStar

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtData =====
section

/-!
# S4-Lefschetz, L6b: the point data of the trace formula

* `finite_homs_of_adjoin`: ring maps `R → Ω` out of a finitely generated `k`-algebra, with fixed restriction to `k`
  and values in a finite set, form a finite set.
* `finite_ptSet`: the `F_{q^m}`-points of `U` (ring maps `u : R → Ω` with prescribed restriction to `F_q` and
  `Fr ∘ u = u`, `Fr = (·)^(q^m)`) form a finite set.
* **`exists_ptData`**: a finite set `S` of these points together with normalized Frobenius elements `F_u`: exactly the
  hypotheses `hS`, `hFu` of `lefschetz_twist`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh

section PtDataGen

end PtDataGen

section PtData

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

/-- **The `F_{q^m}`-points of `U` form a finite set.** -/
theorem finite_ptSet {Ω : Type} [Field Ω] {m : ℕ} (hm : 0 < m) (Fr : Ω →+* Ω)
    (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m)) (c : Fq →+* Ω) :
    {u : Rfin Fq K →+* Ω | u.comp (algebraMap Fq (Rfin Fq K)) = c ∧ Fr.comp u = u}.Finite := by
  have := finiteType_RfinFq Fq K
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra Fq (Rfin Fq K)).FG)
  have hQ : 1 < Fintype.card Fq ^ m := Nat.one_lt_pow hm.ne' Fintype.one_lt_card
  refine (finite_homs_of_adjoin s hs c _ (finite_setOf_pow_eq (F := Ω) hQ)).subset ?_
  rintro u ⟨hc, hfix⟩
  refine ⟨hc, fun a => ?_⟩
  show u a ^ (Fintype.card Fq ^ m) = u a
  rw [← hFr]
  exact RingHom.congr_fun hfix a

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)

include hq in
/-- **L6b: point data.** The finite set `S` of `F_{q^m}`-points of `U` (with restriction `ιS` to `F_q`) and normalized
Frobenius elements `F_u` at them: exactly the hypotheses `hS`, `hFu` of `lefschetz_twist`. -/
theorem exists_ptData {r : ℕ} (hQ : 1 < p ^ (e * r)) {φ : Pi1 (Rfin Fq K) K}
    (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {m : ℕ} (hm : 0 < m)
    (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m)) (ιS : kStar (Rfin Fq K) K hq r →+* Ω) :
    ∃ (S : Finset (Rfin Fq K →+* Ω)) (Fu : (Rfin Fq K →+* Ω) → Pi1 (Rfin Fq K) K),
      (∀ u, u ∈ S ↔ (u.comp (algebraMap Fq (Rfin Fq K)) = ιS.comp (algebraMap Fq (kStar (Rfin Fq K) K hq r)) ∧
        Fr.comp u = u)) ∧
      ∀ u ∈ S, ∃ w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω,
        w.comp (algebraMap (Rfin Fq K) _) = u ∧ (∀ b, w (Fu u • b) = Fr (w b)) ∧
          ∀ x, w (incStar (Rfin Fq K) K hq r hQ x) = ιS x := by
  classical
  have hT := finite_ptSet Fq K hm Fr hFr (ιS.comp (algebraMap Fq (kStar (Rfin Fq K) K hq r)))
  have hQm : 1 < Fintype.card Fq ^ m := Nat.one_lt_pow hm.ne' Fintype.one_lt_card
  have hS : ∀ u, u ∈ hT.toFinset ↔ (u.comp (algebraMap Fq (Rfin Fq K)) =
      ιS.comp (algebraMap Fq (kStar (Rfin Fq K) K hq r)) ∧ Fr.comp u = u) := fun u => by
    rw [Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hex : ∀ u ∈ hT.toFinset, ∃ F : Pi1 (Rfin Fq K) K, ∃ w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω,
      w.comp (algebraMap (Rfin Fq K) _) = u ∧ (∀ b, w (F • b) = Fr (w b)) ∧
        ∀ x, w (incStar (Rfin Fq K) K hq r hQ x) = ιS x := by
    intro u hu
    obtain ⟨hc, hfix⟩ := (hS u).1 hu
    have hu' : ∀ a, Fr (u a) = u a := fun a => RingHom.congr_fun hfix a
    have hfin : (Set.range u).Finite := by
      refine (finite_setOf_pow_eq (F := Ω) hQm).subset ?_
      rintro _ ⟨a, rfl⟩
      show u a ^ (Fintype.card Fq ^ m) = u a
      rw [← hFr]
      exact hu' a
    obtain ⟨w, F, h1, h2, h3⟩ := exists_normFrob (Rfin Fq K) K hq r hQ hφ Fr ιS u hu' hfin
      (fun c => (RingHom.congr_fun hc c).symm)
    exact ⟨F, w, h1, h2, h3⟩
  choose! Fu hFu using hex
  exact ⟨hT.toFinset, Fu, hS, hFu⟩

end PtData

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_GOS_B_Cnt =====
section

/-!
# S4-GOS-B, part Cnt: the twisted Frobenius traces of the perfect complex are `l`-independent point counts

* `exists_ptData_alg`: the point data of `exists_ptData` for `Ω = K̄`, `Fr = z ↦ z ^ (q ^ m)`, `ιS` the inclusion.
* **`ptSeq`**: `ptSeq g m = |C(g)| · #{u ∈ U(𝔽_{q^m}) : π(F_u) ~ g}` (an integer, `0` at `m = 0`), independent of `l`.
* **`pcSeq_eq_ptSeq`**: for `l ∤ q`, `n > 0`, `m > 0`: `pcSeq (ℤ/l^n) … g m = ptSeq g m`
  (`lefschetz_trace_inv_comp` + `lefschetz_count_main`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Cnt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

/-- The inclusion `kStar ⊆ K_U ⊆ K̄`. -/
def ιK (r : ℕ) : kStar (Rfin Fq K) K hq r →+* AlgebraicClosure K :=
  (maxUnram (Rfin Fq K) K).val.toRingHom.comp (kStar (Rfin Fq K) K hq r).subtype

include he in
/-- `exists_ptData` for `Ω = K̄`. -/
theorem exists_ptData_alg {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ) {m : ℕ}
    (hm : 0 < m) {r : ℕ} (hr : 0 < r) :
    ∃ (S : Finset (Rfin Fq K →+* AlgebraicClosure K)) (Fu : (Rfin Fq K →+* AlgebraicClosure K) → Pi1 (Rfin Fq K) K),
      (∀ u, u ∈ S ↔ (u.comp (algebraMap Fq (Rfin Fq K)) =
          (ιK Fq K hq r).comp (algebraMap Fq (kStar (Rfin Fq K) K hq r)) ∧
        (iterateFrobenius (AlgebraicClosure K) p (e * m)).comp u = u)) ∧
      ∀ u ∈ S, ∃ w : proChart (Rfin Fq K) K (Rfin Fq K) →+* AlgebraicClosure K,
        w.comp (algebraMap (Rfin Fq K) _) = u ∧
          (∀ b, w (Fu u • b) = iterateFrobenius (AlgebraicClosure K) p (e * m) (w b)) ∧
          ∀ x, w (incStar (Rfin Fq K) K hq r (hQ_of hr he) x) = ιK Fq K hq r x :=
  exists_ptData Fq K hq (hQ_of hr he) hφ hm _ (frob_alg Fq K hq m) (ιK Fq K hq r)

/-- `l`-independent twisted point counts `|C(g)| · #{u ∈ U(𝔽_{q^m}) : π(F_u) ~ g}` (`0` at `m = 0`). -/
def ptSeq {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ) {Gf : Type} [Group Gf]
    [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf) (g : Gf) (m : ℕ) : ℤ :=
  if hm : 0 < m then
    (Nat.card {z : Gf // z⁻¹ * g * z = g} : ℤ) *
      (ptCount (exists_ptData_alg Fq K hq he hφ hm (Nat.mul_pos hm (Fintype.card_pos (α := Gf)))).choose
        (fun u => π ((exists_ptData_alg Fq K hq he hφ hm
          (Nat.mul_pos hm (Fintype.card_pos (α := Gf)))).choose_spec.choose u)) g : ℤ)
  else 0

end Cnt

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_Sub =====
section

/-!
# S4-GOS-B, part Sub: subgroup sums of the point counts (O6b, group theory)

* `ptSet`, `ptFu`: the point data chosen in `ptSeq` (the `𝔽_{q^m}`-points of `U` in `K̄`, normalized Frobenius elements).
* `ptSeq_eq_sum`: `ptSeq γ m = Σ_{u} #{b ∈ Gf | b⁻¹ π(F_u) b = γ}` (`sum_card_conj_eq`).
* `card_mem_eq_sum`: `Σ_{h ∈ H'} #{b | b⁻¹ X b = h} = #{b | b⁻¹ X b ∈ H'}`.
* **`sum_ptSeq_subgroup`**: `Σ_{h ∈ H'} ptSeq h m = Σ_u #{b ∈ Gf | b⁻¹ π(F_u) b ∈ H'}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Sub

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

/-- The `𝔽_{q^m}`-points of `U` chosen in `ptSeq`. -/
def ptSet {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ) (Gf : Type) [Group Gf]
    [Fintype Gf] {m : ℕ} (hm : 0 < m) : Finset (Rfin Fq K →+* AlgebraicClosure K) :=
  (exists_ptData_alg Fq K hq he hφ hm (Nat.mul_pos hm (Fintype.card_pos (α := Gf)))).choose

/-- The normalized Frobenius elements chosen in `ptSeq`. -/
def ptFu {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ) (Gf : Type) [Group Gf]
    [Fintype Gf] {m : ℕ} (hm : 0 < m) : (Rfin Fq K →+* AlgebraicClosure K) → Pi1 (Rfin Fq K) K :=
  (exists_ptData_alg Fq K hq he hφ hm (Nat.mul_pos hm (Fintype.card_pos (α := Gf)))).choose_spec.choose

theorem ptSeq_eq_sum {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ) {Gf : Type}
    [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf) {m : ℕ} (hm : 0 < m) (γ : Gf) :
    ptSeq Fq K hq he hφ π γ m = ((∑ u ∈ ptSet Fq K hq he hφ Gf hm,
      Nat.card {b : Gf // b⁻¹ * π (ptFu Fq K hq he hφ Gf hm u) * b = γ} : ℕ) : ℤ) := by
  rw [ptSeq, dif_pos hm, ptSet, ptFu, sum_card_conj_eq, Nat.cast_mul]

/-- **Subgroup sums of the counts**: `Σ_{h ∈ H'} ptSeq h m = Σ_u #{b | b⁻¹ π(F_u) b ∈ H'}`. -/
theorem sum_ptSeq_subgroup {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf) {m : ℕ} (hm : 0 < m)
    (H' : Subgroup Gf) [Fintype H'] :
    ∑ h : H', ptSeq Fq K hq he hφ π (h : Gf) m = ((∑ u ∈ ptSet Fq K hq he hφ Gf hm,
      Nat.card {b : Gf // b⁻¹ * π (ptFu Fq K hq he hφ Gf hm u) * b ∈ H'} : ℕ) : ℤ) := by
  simp only [ptSeq_eq_sum Fq K hq he hφ π hm]
  rw [← Nat.cast_sum, Finset.sum_comm]
  exact congrArg _ (Finset.sum_congr rfl fun u _ => card_mem_eq_sum H' _)

end Sub

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_Cov =====
section

/-!
# S4-GOS-B, part Cov: the concrete cover `M ⊆ K_U` over `K = 𝔽_q(X)` (O4u, O8b)

`M` finite Galois over `K = RatFunc 𝔽_q`, `G = Gal(M/K)`:
* `rfinEquiv`: `R_fin(M) ≃ O_M` (the integral closure of `R_fin(K)` in `M` used by S4-Lefschetz), `G`-equivariant
  (`rfinEquiv_smul`);
* `hun_rfin`: every prime of `R_fin(M)` has trivial inertia if `M` is unramified over `R_fin(K)`;
  **`hfin_of_unram`** (O4u): the `hfin` hypothesis of `chiPC_eq_Phi_of`;
* `iotaG`: `Gal(M/K) →* Gf` with `iotaG (resPt σ) = π σ` (O8b), injective; surjective if `π` is.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh Lefschetz

section Cov

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (M : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))) [FiniteDimensional (RatFunc Fq) M]
  [IsGalois (RatFunc Fq) M]

variable {M} (hMU : M ≤ maxUnram (Rfin Fq (RatFunc Fq)) (RatFunc Fq))

theorem resPt_eq_one_iff (σ : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)) :
    resPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup := by
  have h := resPt_mem_fix_iff (Fq := Fq) (K := RatFunc Fq) (le_refl M) hMU σ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h1 y hy
    have h2 := h.1 (by rw [h1]; exact one_mem _)
    exact h2 y ((IntermediateField.mem_restrict hMU y).1 hy)
  · intro h1
    have h2 := h.2 fun y hy => h1 y ((IntermediateField.mem_restrict hMU y).2 hy)
    rw [IntermediateField.mem_fixingSubgroup_iff] at h2
    ext y
    have h3 := h2 y ((IntermediateField.mem_restrict (le_refl M) y).2 y.2)
    rw [AlgEquiv.one_apply]
    exact congrArg Subtype.val h3

variable {Gf : Type} [Group Gf] (π : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq) →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)

include hπM in
theorem pi_eq_of_resPt_eq {a b : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)}
    (h : resPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU a = resPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU b) :
    π a = π b := by
  have h1 : resPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := (hπM _).2 ((resPt_eq_one_iff Fq hMU _).1 h1)
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2

/-- **O8b**: `Gal(M/K) → Gf` induced by `π`. -/
def iotaG : (M ≃ₐ[RatFunc Fq] M) →* Gf where
  toFun g := π (Function.surjInv (resPt_surjective (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU) g)
  map_one' := by
    rw [← map_one π]
    exact pi_eq_of_resPt_eq Fq hMU π hπM (by
      rw [Function.surjInv_eq (resPt_surjective (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU), map_one])
  map_mul' g h := by
    rw [← map_mul π]
    exact pi_eq_of_resPt_eq Fq hMU π hπM (by
      rw [map_mul, Function.surjInv_eq (resPt_surjective (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU),
        Function.surjInv_eq (resPt_surjective (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU),
        Function.surjInv_eq (resPt_surjective (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU)])

theorem iotaG_resPt (σ : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)) :
    iotaG Fq hMU π hπM (resPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU σ) = π σ :=
  pi_eq_of_resPt_eq Fq hMU π hπM
    (Function.surjInv_eq (resPt_surjective (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU) _)

theorem iotaG_injective : Function.Injective (iotaG Fq hMU π hπM) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨σ, rfl⟩ := resPt_surjective (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU g
  rw [iotaG_resPt] at hg
  exact (resPt_eq_one_iff Fq hMU σ).2 ((hπM σ).1 hg)

theorem iotaG_surjective (hπs : Function.Surjective π) : Function.Surjective (iotaG Fq hMU π hπM) := by
  intro x
  obtain ⟨σ, rfl⟩ := hπs x
  exact ⟨_, iotaG_resPt Fq hMU π hπM σ⟩

end Cov

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_GPt =====
section

/-!
# S4-GOS-B, part GPt: Lefschetz count on the concrete cover `M ⊇ M^H` (O6c, per point)

`K = RatFunc 𝔽_q`, `M ⊆ K_U` finite Galois and unramified over `R_fin(K)`, `G = Gal(M/K)`, `H ≤ G`,
`E' = M^H` (`fixF`). For a point `u : R_fin(K) → K̄` with finite image and a lift `w` of `u` to the pro-chart on
which `F ∈ π_1` acts as `Fr`:
**`card_conj_mem_eq`**: `#{x ∈ G | x⁻¹ F|_M x ∈ H} = #{v : R_fin(E') → K̄ over u | Fr ∘ v = v} · |H|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh Lefschetz CupDuality

section GPt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {M : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))} [FiniteDimensional (RatFunc Fq) M]
  [IsGalois (RatFunc Fq) M]

variable (hun : IsUnramifiedSub (Rfin Fq (RatFunc Fq)) (RatFunc Fq) M)
  (hMU : M ≤ maxUnram (Rfin Fq (RatFunc Fq)) (RatFunc Fq))

include hun in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **The Lefschetz count on `M / M^H`** at one point `u` with Frobenius `F`. -/
theorem card_conj_mem_eq (H : Subgroup (M ≃ₐ[RatFunc Fq] M))
    (Fr : AlgebraicClosure (RatFunc Fq) →+* AlgebraicClosure (RatFunc Fq))
    (u : Rfin Fq (RatFunc Fq) →+* AlgebraicClosure (RatFunc Fq)) (hfinu : (Set.range u).Finite)
    (w : proChart (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Rfin Fq (RatFunc Fq)) →+* AlgebraicClosure (RatFunc Fq))
    (hwu : w.comp (algebraMap (Rfin Fq (RatFunc Fq)) _) = u) (F : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq))
    (hwF : ∀ b, w (F • b) = Fr (w b)) :
    Nat.card {x : M ≃ₐ[RatFunc Fq] M // x⁻¹ * resPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU F * x ∈ H} =
      Nat.card {v : Rfin Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H) →+* AlgebraicClosure (RatFunc Fq) //
        v.comp (algebraMap (Rfin Fq (RatFunc Fq)) _) = u ∧ Fr.comp v = v} * Nat.card H := by
  letI := actRfin Fq (RatFunc Fq) M (M ≃ₐ[RatFunc Fq] M)
  haveI := isGaloisGroup_rfin Fq (RatFunc Fq) M (M ≃ₐ[RatFunc Fq] M)
  haveI hSC : SMulCommClass H (Rfin Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H)) (Rfin Fq M) :=
    (isGaloisGroup_rfin Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H) M H).commutes
  haveI hInv : Algebra.IsInvariant (Rfin Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H)) (Rfin Fq M) H :=
    (isGaloisGroup_rfin Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H) M H).isInvariant
  haveI := isScalarTower_rfin_fixF Fq H
  haveI := faithfulSMul_rfin_fixF Fq H
  let w0 : Rfin Fq M →+* AlgebraicClosure (RatFunc Fq) :=
    w.comp ((jPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU).comp (rfinEquiv Fq M).toRingEquiv.toRingHom)
  have hw0 : w0.comp (algebraMap (Rfin Fq (RatFunc Fq)) (Rfin Fq M)) = u := by
    rw [← hwu]
    refine RingHom.ext fun a => ?_
    have h1 := jPt_algebraMap (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU a
    show w (jPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU (rfinEquiv Fq M (algebraMap _ (Rfin Fq M) a))) =
      w (algebraMap _ _ a)
    rw [AlgEquiv.commutes]
    exact congrArg w h1
  have hF : ∀ b, Fr (w0 b) = w0 (resPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU F • b) := by
    intro b
    show Fr (w (jPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU (rfinEquiv Fq M b))) =
      w (jPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU (rfinEquiv Fq M (resPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU F • b)))
    have h3 := jPt_smul (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU F (rfinEquiv Fq M b)
    rw [rfinEquiv_smul]
    refine (hwF _).symm.trans ?_
    exact congrArg w h3.symm
  exact card_fixed_ptRes H (C := Rfin Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H)) (hun_rfin Fq M hun) Fr u
    (hfin_gen u hfinu) w0 hw0 _ hF

end GPt

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_PlKc =====
section

/-!
# S4-GOS-B, part PlKc: a function field over `𝔽_q` and over its full constant field `k_E` (O6d glue)

`d := [k_E : 𝔽_q]`.
* `plKc`: places over `k_E` ≃ places over `𝔽_q` (`R_fin`, `R_∞` do not see the constant field);
  `ffv_plKc` (same valuations), `deg_plKc` (`deg_{𝔽_q} = d · deg_{k_E}`);
* **`genusF_Kc`**: `g(E/𝔽_q) = d · g(E/k_E)`;
* **`numPoints_Kc`**: `N_m(E/𝔽_q) = [d ∣ m] d N_{m/d}(E/k_E)` (as `dil d`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places Lefschetz RR

section PlKc

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

theorem ffv_plKc (P : Place (Kc Fq E) E) : ffv Fq E (plKc Fq E P) = ffv (Kc Fq E) E P := by
  rcases P with P | P
  · refine Valuation.ext fun x => ?_
    exact valuation_comap_equiv (rfinKcEquiv Fq E).symm (RingEquiv.refl E)
      (fun b => rfinKcEquiv_symm_val Fq E b) P x
  · refine Valuation.ext fun x => ?_
    exact valuation_comap_equiv (rinfKcEquiv Fq E).symm (RingEquiv.refl E)
      (fun b => rinfKcEquiv_symm_val Fq E b) P x

/-- **Genus over the full constant field**: `g(E/𝔽_q) = [k_E : 𝔽_q] g(E/k_E)`. -/
theorem genusF_Kc : genusF Fq E = Module.finrank Fq (Kc Fq E) * genusF (Kc Fq E) E :=
  genus_scl (ffData Fq E) (ffData (Kc Fq E) E) (plKc Fq E) (fun P => ffv_plKc Fq E P)
    (Module.finrank Fq (Kc Fq E)) (fun P => deg_plKc Fq E P) (ffData_axioms (Fq := Fq) (F := E))
    (ffData_axioms (Fq := Kc Fq E) (F := E)) rfl

end PlKc

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_WeilE =====
section

/-!
# S4-GOS-B, part WeilE: the affine point counts of any function field satisfy an integer recurrence (O6d)

For a function field `E/𝔽_q` with full constant field `k_E` (`d = [k_E : 𝔽_q]`), the sequence
`ê m = [d ∣ m] d a(m/d) - Σ_{R | ∞} [deg R ∣ m] deg R`, `a j = N_j(E/k_E)` (`j > 0`), `a 0 = 2 - 2 g(E/k_E)`:
* `weilSeq_zero`: `ê 0 = χ_c(E)`;
* `weilSeq_pos`: `ê m = #Hom_{𝔽_q}(R_fin(E), L)` for `[L : 𝔽_q] = m > 0`;
* **`exists_weil_rec`**: an integer recurrence `Σ_j b_j ê(k + j) = 0` with `l ∤ b_0` for every prime `l ∤ q`
  (Weil for `E/k_E`: `CP4a.zeta_RH_FE`, then `exists_rec_weil_fin`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places Lefschetz RR

section WeilE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

theorem weilSeq_zero : weilSeq Fq E 0 = chiC Fq E := by
  rw [weilSeq, chiC, dil, if_pos (dvd_zero _), Nat.zero_div, weilA, if_pos rfl,
    ellF_zero (Fq := Fq) (F := E), genusF_Kc Fq E]
  simp only [dvd_zero, if_true]
  push_cast
  ring

end WeilE

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_GCnt =====
section

/-!
# S4-GOS-B, part GCnt: subgroup sums of the point counts on the concrete cover (O6c)

`K = RatFunc 𝔽_q`, `M ⊆ K_U` finite Galois and unramified over `R_fin(K)`, `π : π_1 → Gf` with kernel `π_1(M)` and
`π` surjective, `ι = iotaG : Gal(M/K) ≅ Gf`. For `H ≤ Gal(M/K)`, `E' = M^H`, `m > 0`:
**`sum_ptSeq_map`**: `Σ_{h ∈ ι H} ptSeq h m = |ι H| · weilSeq E' m` (`= |H| · #Hom_{𝔽_q}(R_fin(E'), 𝔽_{q^m})`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh Lefschetz CupDuality CP4a

section GCnt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {p e : ℕ} [Fact p.Prime] [CharP (RatFunc Fq) p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

theorem ιK_comp_algebraMap (r : ℕ) :
    (ιK Fq (RatFunc Fq) hq r).comp (algebraMap Fq (kStar (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hq r)) =
      algebraMap Fq (AlgebraicClosure (RatFunc Fq)) := by
  refine RingHom.ext fun c => ?_
  show (((algebraMap Fq (kStar (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hq r) c :
    kStar (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hq r) : maxUnram (Rfin Fq (RatFunc Fq)) (RatFunc Fq)) :
      AlgebraicClosure (RatFunc Fq)) = _
  rw [kStar_algebraMap_val, IsScalarTower.algebraMap_apply Fq (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))]
  rfl

variable {M : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))} [FiniteDimensional (RatFunc Fq) M]
  [IsGalois (RatFunc Fq) M] (hun : IsUnramifiedSub (Rfin Fq (RatFunc Fq)) (RatFunc Fq) M)
  (hMU : M ≤ maxUnram (Rfin Fq (RatFunc Fq)) (RatFunc Fq))
  {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq) →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup) (hπs : Function.Surjective π)

include hπs in
theorem card_conj_map_iotaG (H : Subgroup (M ≃ₐ[RatFunc Fq] M)) (σ : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)) :
    Nat.card {b : Gf // b⁻¹ * π σ * b ∈ H.map (iotaG Fq hMU π hπM)} =
      Nat.card {x : M ≃ₐ[RatFunc Fq] M // x⁻¹ * resPt (Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU σ * x ∈ H} := by
  let eι := Equiv.ofBijective (iotaG Fq hMU π hπM)
    ⟨iotaG_injective Fq hMU π hπM, iotaG_surjective Fq hMU π hπM hπs⟩
  refine Nat.card_congr (eι.subtypeEquiv fun x => ?_).symm
  show _ ↔ (iotaG Fq hMU π hπM x)⁻¹ * π σ * iotaG Fq hMU π hπM x ∈ H.map (iotaG Fq hMU π hπM)
  rw [← iotaG_resPt Fq hMU π hπM σ, ← map_inv, ← map_mul, ← map_mul,
    Subgroup.mem_map_iff_mem (iotaG_injective Fq hMU π hπM)]

variable {φ : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)}
  (hφ : IsFrobLift (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq) φ)

end GCnt

end

end RamanujanPetersson.GOS


end


