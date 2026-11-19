-- Prove2me | Definitions.Def_RPLib_S4_CDPack41c
-- name    : RPLib_S4_CDPack41c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T13:45:44.905253+00:00
-- url     : https://prove2.me/theorems/d7c262a7-4bb1-4516-840f-d0319decddd7
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 41c of 71
-- statement:
--   Part 41c of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_AJGen`: The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack41
import Definitions.Def_RPLib_S4_CDPack41t
import Definitions.Def_RPLib_S4_CDPack36c

/-!
# Curve-duality library package, part 41c of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_AJGen`: The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJGen =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`

* `exists_pool`: arbitrarily large finite sets of points off the roots of `b(x)`.
* `PtY K F c0` (points of `B' = Rfin F'` off `x = ∞`), `tpY` (their `F`-points, injective).
* `goodY_ext`: nonspecial `b`-generic sets of such points extend off any finite set.
* `symPt_convPt_eq`: the converted point depends only on the support.
* **`exists_piece_through`**: every closed point `Q0` of `B'` lies on some piece `Spec LocR c0 D c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AJGen

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **Large pools of points** off the roots of `b(x)`. -/
theorem exists_pool (b : K[X]) (hb : b ≠ 0) (m : ℕ) :
    ∃ T : Finset (Rfin K F →ₐ[K] K), m ≤ T.card ∧ ∀ φ ∈ T, b.eval (φ (xB K F)) ≠ 0 := by
  obtain ⟨a1, ha1, hfib⟩ := exists_fib_data (K := K) (F := F)
  have hab : a1 * b ≠ 0 := mul_ne_zero ha1 hb
  obtain ⟨Λ, hΛ, hΛc⟩ := (finite_setOfPred_isRoot hab).infinite_compl.exists_subset_card_eq m
  have hΛab : ∀ c ∈ Λ, (a1 * b).eval c ≠ 0 := fun c hc h => hΛ (Finset.mem_coe.2 hc) h
  obtain ⟨s, Z, -, -, -, -, hZx, hZc⟩ := hfib Λ fun c hc => by
    have h := hΛab c hc
    rw [eval_mul] at h
    exact left_ne_zero_of_mul h
  refine ⟨Z, ?_, fun φ hφ => ?_⟩
  · have hn : 0 < Module.finrank K[X] (Rfin K F) :=
      (Module.finrank_pos_iff_of_free (R := K[X]) (M := Rfin K F)).2 inferInstance
    rw [hZc, hΛc]
    exact Nat.le_mul_of_pos_right _ hn
  · have h := hΛab _ ((hZx φ).1 hφ)
    rw [eval_mul] at h
    exact right_ne_zero_of_mul h

variable (c0 : K)

variable (K F) in
/-- Points of `B' = Rfin F'` off `x = ∞`. -/
abbrev PtY : Type u := {e : Rfin K (SynF K F c0) →ₐ[K] K // e (xS K F c0) ≠ 0}

/-- Their `F`-points. -/
noncomputable def tpY (e : PtY K F c0) : Rfin K F →ₐ[K] K := tpH c0 e.1 e.2

theorem tpY_injective : Function.Injective (tpY (K := K) (F := F) c0) :=
  fun _ _ h => Subtype.ext (eq_of_tpH_eq c0 h)

theorem tpH_congr {e1 e2 : Rfin K (SynF K F c0) →ₐ[K] K} (h : e1 = e2) (h1 : e1 (xS K F c0) ≠ 0)
    (h2 : e2 (xS K F c0) ≠ 0) : tpH c0 e1 h1 = tpH c0 e2 h2 := by
  subst h; rfl

/-- Good sets: nonspecial and `b`-generic. -/
def GoodY (b : K[X]) (C : Finset (PtY K F c0)) : Prop :=
  ellFK K (SynF K F c0) (Zdiv (C.map (Function.Embedding.subtype _))) = 1 ∧
    ∀ e ∈ C, b.eval (e.1 (xB K (SynF K F c0))) ≠ 0

theorem goodY_empty (b : K[X]) : GoodY (K := K) (F := F) c0 b ∅ := by
  refine ⟨?_, fun e he => absurd he (Finset.notMem_empty e)⟩
  rw [Finset.map_empty, Zdiv_empty]
  exact ellFK_zero'

/-- **Extension step** for good sets (`exists_add_nonspecial` on a pool). -/
theorem goodY_ext {b : K[X]} (hb : b ≠ 0) (C : Finset (PtY K F c0)) (hC : GoodY c0 b C)
    (hCc : C.card < genusFK K F) (Bad : Finset (PtY K F c0)) :
    ∃ q, q ∉ C ∧ q ∉ Bad ∧ GoodY c0 b (insert q C) := by
  obtain ⟨hC1, hCb⟩ := hC
  have hg : genusFK K (SynF K F c0) = genusFK K F := genusFK_eq (synEquiv K F c0)
  obtain ⟨T0, hT0c, hT0⟩ := exists_pool (F := SynF K F c0) (X * b) (mul_ne_zero X_ne_zero hb)
    (2 * genusFK K (SynF K F c0) + (Bad ∪ C).card)
  let ι := Function.Embedding.subtype (fun e : Rfin K (SynF K F c0) →ₐ[K] K => e (xS K F c0) ≠ 0)
  have hdis : Disjoint (C.map ι) (T0 \ (Bad ∪ C).map ι) := by
    rw [Finset.disjoint_left]
    intro φ hφ hφT
    exact (Finset.mem_sdiff.1 hφT).2 (Finset.map_subset_map.2 Finset.subset_union_right hφ)
  have hcard : 2 * genusFK K (SynF K F c0) ≤ (T0 \ (Bad ∪ C).map ι).card := by
    have h1 := Finset.le_card_sdiff ((Bad ∪ C).map ι) T0
    rw [Finset.card_map] at h1
    omega
  obtain ⟨P, hP, hP1⟩ := exists_add_nonspecial hdis hC1 (by rw [Finset.card_map, hg]; exact hCc) (by omega)
  obtain ⟨hPT, hPB⟩ := Finset.mem_sdiff.1 hP
  have hPe := hT0 P hPT
  rw [eval_mul, eval_X] at hPe
  let q : PtY K F c0 := ⟨P, left_ne_zero_of_mul hPe⟩
  have hqP : ι q = P := rfl
  refine ⟨q, fun h => hPB (Finset.mem_map.2 ⟨q, Finset.mem_union_right _ h, rfl⟩),
    fun h => hPB (Finset.mem_map.2 ⟨q, Finset.mem_union_left _ h, rfl⟩), ?_, ?_⟩
  · show ellFK K (SynF K F c0) (Zdiv ((insert q C).map ι)) = 1
    rw [Finset.map_insert, hqP]; exact hP1
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact right_ne_zero_of_mul hPe
    · exact hCb e he

/-- **The converted point depends only on its support.** -/
theorem symPt_convPt_eq {R : Type*} [CommRing R] [Algebra K R] {n' : ℕ}
    (φ' : SymRing K (Rfin K (SynF K F c0)) n' →ₐ[K] R) (hu : IsUnit (φ' (normS K (xS K F c0))))
    (hn : genusFK K F = n') (y : R →ₐ[K] K) (a : Fin (genusFK K F) → PtY K F c0) (ha : Function.Injective a)
    (hE : ptSet (y.comp φ') = (Finset.univ.image a).map (Function.Embedding.subtype _)) :
    symPt (convPt c0 φ' hu hn y) = symPt (tpY c0 ∘ a) := by
  subst hn
  have himg : Finset.univ.image (convPt c0 φ' hu rfl y) = Finset.univ.image (tpY c0 ∘ a) := by
    ext φ
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩
      have hm : liftTuple (y.comp φ') i ∈ ptSet (y.comp φ') := (mem_ptSet _ _).2 ⟨_, rfl⟩
      rw [hE] at hm
      obtain ⟨e, he, hee⟩ := Finset.mem_map.1 hm
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 he
      exact ⟨l, tpH_congr c0 hee _ _⟩
    · rintro ⟨l, rfl⟩
      have hm : (a l).1 ∈ ptSet (y.comp φ') := by
        rw [hE]; exact Finset.mem_map_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      obtain ⟨i, hi⟩ := (mem_ptSet _ _).1 hm
      exact ⟨i, tpH_congr c0 hi _ _⟩
  have hinj2 : Function.Injective (tpY c0 ∘ a) := (tpY_injective c0).comp ha
  have hinj1 : Function.Injective (convPt c0 φ' hu rfl y) := by
    have h := Finset.card_image_of_injective Finset.univ hinj2
    rw [← himg] at h
    exact fun i1 i2 e => Finset.card_image_iff.1 h (Finset.mem_coe.2 (Finset.mem_univ i1))
      (Finset.mem_coe.2 (Finset.mem_univ i2)) e
  exact symPt_eq_of_image_eq hinj1 hinj2 himg

set_option maxHeartbeats 1000000 in
/-- The greedy choice of `E` (`exists_greedy` with `GoodY`, from a point of `X0`). -/
theorem exists_goodTuple {b : K[X]} (hb0 : b ≠ 0) : ∃ a : Fin (genusFK K F) → PtY K F c0,
    Function.Injective a ∧ GoodY c0 b (Finset.univ.image a) ∧ symPt (tpY c0 ∘ a) (lawPre K F).u0 ≠ 0 := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (LawRing K F)
  obtain ⟨y0R, -⟩ := exists_algHom_ker_eq (k := K) m
  have hy0 : (y0R.comp (awayι (K := K) (lawPre K F).u0)) (lawPre K F).u0 ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit (lawPre K F).u0).map y0R).ne_zero
  have ht0 : symPt (liftTuple (y0R.comp (awayι (K := K) (lawPre K F).u0))) (lawPre K F).u0 ≠ 0 := by
    rw [symPt_liftTuple]; exact hy0
  exact exists_greedy (tpY c0) (tpY_injective c0) (fun w hw => finite_zero hw) (GoodY c0 b)
    (goodY_empty c0 b) (goodY_ext c0 hb0) (lawPre K F).u0 _ ht0

theorem ptSet_convφ {r : ℕ} (D : NuData K (SynF K F c0) (1 + r)) (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))
    (y : ConvR c0 D c →ₐ[K] K) : ptSet (y.comp (convφ c0 D c)) =
      D.nuF (padPt phi1 c rfl ((y.comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c))) := by
  rw [convφ, ← AlgHom.comp_assoc, ptSet_pieceMap]

theorem convU_ne_zero {r : ℕ} (D : NuData K (SynF K F c0) (1 + r)) (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))
    (y : ConvR c0 D c →ₐ[K] K) (a : Fin (genusFK K F) → PtY K F c0) (ha : Function.Injective a)
    (hpt : ptSet (y.comp (convφ c0 D c)) = (Finset.univ.image a).map (Function.Embedding.subtype _))
    (hau : symPt (tpY c0 ∘ a) (lawPre K F).u0 ≠ 0) : y (convU c0 D c) ≠ 0 := by
  have e := AlgHom.congr_fun (comp_convS c0 D c y) (lawPre K F).u0
  rw [symPt_convPt_eq c0 _ _ _ y a ha hpt] at e
  rw [← e] at hau
  exact hau

set_option maxHeartbeats 1000000 in
/-- **AJGen: the pieces cover the chart**: every closed point `Q0` of `B'` lies on some piece. -/
theorem exists_piece_through (Q0 : Rfin K (SynF K F c0) →ₐ[K] K) :
    ∃ r : ℕ, ∃ D : NuData K (SynF K F c0) (1 + r), ∃ c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K),
      ∃ x : LocR c0 D c →ₐ[K] K, x.comp (pieceIn c0 D c) = Q0 := by
  obtain ⟨b, hb0, hsec⟩ := exists_secE Q0
  have hg : genusFK K (SynF K F c0) = genusFK K F := genusFK_eq (synEquiv K F c0)
  obtain ⟨a, ha, ⟨hNS1, hab⟩, hau⟩ := exists_goodTuple (F := F) c0 hb0
  obtain ⟨E, hE⟩ : ∃ E : Finset (Rfin K (SynF K F c0) →ₐ[K] K),
      E = (Finset.univ.image a).map (Function.Embedding.subtype _) := ⟨_, rfl⟩
  have hEc : E.card = genusFK K (SynF K F c0) := by
    rw [hE, Finset.card_map, Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin, hg]
  have hEb : ∀ e ∈ E, b.eval (e (xB K (SynF K F c0))) ≠ 0 := by
    intro e he
    rw [hE] at he
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 he
    exact hab e' he'
  have hEx : ∀ e ∈ E, e (xS K F c0) ≠ 0 := by
    intro e he
    rw [hE] at he
    obtain ⟨e', -, rfl⟩ := Finset.mem_map.1 he
    exact e'.2
  have hNS : IsNS K (SynF K F c0) E := const_of_ellFK_eq_one (Zdiv_nonneg E) (by rw [hE]; exact hNS1)
  obtain ⟨s, Z, hs0, hex, hZ, hZc, hQZ, hEZ, hQE, hmZ⟩ := hsec E hEb (2 * genusFK K (SynF K F c0))
  obtain ⟨r, D, c, -, hA, hrole⟩ := exists_nuE hs0 hex hZ hZc hQZ hEZ hQE hEc hNS hmZ
  have hpad : ptSet (padPt (phi1 (k := K) (B := Rfin K (SynF K F c0))) c rfl Q0) = Z \ E := by
    rw [ptSet_padPt1, hA]
  obtain ⟨hgood, hnu⟩ := hrole _ hpad
  refine ⟨r, D, c, exists_pieceIn c0 D c Q0 ?_ ?_ ?_⟩
  · rw [apply_pieceF]; exact hgood
  · intro z hz e he
    rw [ptSet_pieceMap, hz, hnu] at he
    exact hEx e he
  · intro y hy
    exact convU_ne_zero c0 D c y a ha (by rw [ptSet_convφ, hy, hnu, hE]) hau

end AJGen

end RamanujanPetersson.JacComplete

end


