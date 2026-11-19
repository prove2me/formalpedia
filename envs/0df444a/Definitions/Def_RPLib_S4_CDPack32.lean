-- Prove2me | Definitions.Def_RPLib_S4_CDPack32
-- name    : RPLib_S4_CDPack32
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:50:16.226769+00:00
-- url     : https://prove2.me/theorems/785fe0ad-9143-4772-8250-05c26eb4fb92
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 32 of 71
-- statement:
--   Part 32 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_GenRole`: S4-JacLaw, file O9f (G5 GenRole): one role of the configuration, and the witness steps
--   * `Def_RP_JacLaw_GenCfg`: S4-JacLaw, file O9g (G5 GenCfg): the configuration
--   * `Def_RP_JacFrob_BrC`: S4-JacFrob, part BrC (bridge 2): contraction of places of `F-bar` to the levels `F_{lev j}`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack31
import Definitions.Def_RPLib_S4_CDPack28c
import Definitions.Def_RPLib_S4_CDPack29b
import Definitions.Def_RPLib_S4_CDPack29
import Definitions.Def_RPLib_S4_CDPack24

/-!
# Curve-duality library package, part 32 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_GenRole`: S4-JacLaw, file O9f (G5 GenRole): one role of the configuration, and the witness steps
* `Def_RP_JacLaw_GenCfg`: S4-JacLaw, file O9g (G5 GenCfg): the configuration
* `Def_RP_JacFrob_BrC`: S4-JacFrob, part BrC (bridge 2): contraction of places of `F-bar` to the levels `F_{lev j}`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_GenRole =====
section

/-!
# S4-JacLaw, file O9f (G5 GenRole): one role of the configuration, and the witness steps

* `exists_enum`: an injective tuple enumerating a finset.
* **`exists_role`**: from a section `s` with exact pole divisor `Hn` and full reduced zero set `Z`, and `A ⊆ Z`
  with `#A = d` and `Z \ A` nonspecial: a `NuData` with `Hn` that is good on `A` with `ν(A) = Z \ A`.
* `ne_u3`, **`ne_numA_m`**, **`ne_numA_r`**: a point `z` of `T` where the inner and outer units of `mOut` /
  `rOut` do not vanish (so `z` lifts to `D(numA _)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

theorem exists_enum {α : Type*} (A : Finset α) {d : ℕ} (hA : A.card = d) :
    ∃ t : Fin d → α, Function.Injective t ∧ ∀ φ, φ ∈ A ↔ ∃ i, t i = φ := by
  let e : Fin d ≃ A := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hA])).symm
  refine ⟨fun i => (e i).1, fun i j h => e.injective (Subtype.ext h), fun φ => ?_⟩
  constructor
  · intro hφ; exact ⟨e.symm ⟨φ, hφ⟩, by simp⟩
  · rintro ⟨i, rfl⟩; exact (e i).2

section GenRole

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **One role**: a `NuData` good on `A` with `ν(A) = Z \ A`. -/
theorem exists_role {d : ℕ} (hdg : genusFK K F ≤ d + 1) {Hn : Places.Divisor K F} (hHn : IsInf Hn)
    (hHn0 : 0 ≤ Hn) (hdeg : Places.Divisor.deg Hn = ((d + genusFK K F : ℕ) : ℤ))
    {s : Places.Rfin K F} (hs0 : s ≠ 0) (hs : ExactPoleH s Hn)
    {Z A : Finset (Places.Rfin K F →ₐ[K] K)} (hZ : ∀ φ, φ ∈ Z ↔ φ s = 0) (hZc : Z.card = d + genusFK K F)
    (hA : A ⊆ Z) (hAc : A.card = d) (hNS : IsNS K F (Z \ A)) :
    ∃ D : NuData K F d, D.Hn = Hn ∧
      ∀ y : SymRing K (Places.Rfin K F) d →ₐ[K] K, ptSet y = A → y D.good ≠ 0 ∧ D.nuF y = Z \ A := by
  obtain ⟨t, ht, hti⟩ := exists_enum A hAc
  have hdiv := div_of_card hs0 hHn hs hZ (by rw [hZc, hdeg])
  have hrank : ∀ w ∈ Linf K F Hn, (∀ i, t i w = 0) → ∃ c : K, w = c • s := fun w hw hw0 =>
    hrank_of_const hs0 hHn hdiv hA hNS hw fun φ hφ => by
      obtain ⟨i, rfl⟩ := (hti φ).1 hφ
      exact hw0 i
  obtain ⟨D, hDH, hgood, c, hc0, hsec⟩ :=
    exists_nuData hdg hHn hHn0 hdeg hs0 hs t ht hrank Z (fun φ hφ => (hZ φ).1 hφ) hZc
  refine ⟨D, hDH, fun y hy => ?_⟩
  have hpt : ptSet (symPt t) = A := by
    rw [ptSet_symPt]
    ext φ
    rw [Finset.mem_image, hti φ]
    simp only [Finset.mem_univ, true_and]
  have hyt : y = symPt t := eq_of_ptSet_eq (hy.trans hpt.symm) (by rw [hy, hAc])
  subst hyt
  refine ⟨hgood, ?_⟩
  have hz : zeroFin (k := K) (D.sec (symPt t)) = Z := by
    refine zeroFin_eq fun φ => ?_
    rw [NuData.sec_symPt, hsec, map_smul, smul_eq_mul, mul_eq_zero, or_iff_right hc0]
    exact hZ φ
  rw [NuData.nuF, hz, hpt]

section Wit

variable {T : Type u} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]
  {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3)) (D2 : NuData K F (genusFK K F + r2))
  (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))

theorem ne_u3 (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) (z : T →ₐ[K] K)
    {A3 : Finset (Places.Rfin K F →ₐ[K] K)}
    (hA : ptSet (z.comp φa) ∪ ptSet (z.comp φb) ∪ Finset.univ.image c0 = A3)
    (h3 : ∀ y : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r3) →ₐ[K] K, ptSet y = A3 → y D3.good ≠ 0) :
    z (padMap (sumMap φa φb) c0 rfl D3.good) ≠ 0 := by
  have e : z (padMap (sumMap φa φb) c0 rfl D3.good) = (z.comp (padMap (sumMap φa φb) c0 rfl)) D3.good := rfl
  rw [e, comp_padMap]
  refine h3 _ ?_
  rw [ptSet_padPt, comp_sumMap, ptSet_sumPt, hA]

/-- **The units of `m` at a point**: `z(u3) ≠ 0` and `z(num u2) ≠ 0`. -/
theorem ne_numA_m (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) (z : T →ₐ[K] K)
    {A3 E : Finset (Places.Rfin K F →ₐ[K] K)}
    (hA : ptSet (z.comp φa) ∪ ptSet (z.comp φb) ∪ Finset.univ.image c0 = A3)
    (h3 : ∀ y : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r3) →ₐ[K] K, ptSet y = A3 →
      y D3.good ≠ 0 ∧ D3.nuF y = E)
    (h2 : ∀ y : SymRing K (Places.Rfin K F) (genusFK K F + r2) →ₐ[K] K, ptSet y = E ∪ Finset.univ.image c1 →
      y D2.good ≠ 0) :
    z (numA (padMap (mIn D3 c0 φa φb) c1 rfl D2.good)) ≠ 0 := by
  have hu := ne_u3 D3 c0 φa φb z hA fun y hy => (h3 y hy).1
  obtain ⟨x, hx⟩ := exists_baseAway _ z hu
  have key : x (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) ≠ 0 := by
    have e : x (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) =
        (x.comp (padMap (mIn D3 c0 φa φb) c1 rfl)) D2.good := rfl
    rw [e, comp_padMap]
    refine h2 _ ?_
    rw [ptSet_padPt]
    have e2 : ptSet (x.comp (mIn D3 c0 φa φb)) = E := by
      rw [mIn, NuData.ptSet_nuStep, hx]
      exact (h3 _ (by rw [comp_padMap, ptSet_padPt, comp_sumMap, ptSet_sumPt, hA])).2
    rw [e2]
  have h := (numA_pt (K := K) _ x).2 key
  have hx' : x.comp (awayι (K := K) (padMap (sumMap φa φb) c0 rfl D3.good)) = z := hx
  rwa [hx'] at h

/-- **The units of `r` at a point**: `z(v2) ≠ 0` and `z(num v3) ≠ 0`. -/
theorem ne_numA_r (φa φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) (z : T →ₐ[K] K)
    {C2 A3 E : Finset (Places.Rfin K F →ₐ[K] K)}
    (hC : ptSet (z.comp φc) ∪ Finset.univ.image c1 = C2)
    (h2 : ∀ y : SymRing K (Places.Rfin K F) (genusFK K F + r2) →ₐ[K] K, ptSet y = C2 →
      y D2.good ≠ 0 ∧ D2.nuF y = E)
    (hA : ptSet (z.comp φa) ∪ E ∪ Finset.univ.image c0 = A3)
    (h3 : ∀ y : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r3) →ₐ[K] K, ptSet y = A3 →
      y D3.good ≠ 0) :
    z (numA (padMap (rSum D2 c1 φa φc) c0 rfl D3.good)) ≠ 0 := by
  have hv : z (padMap φc c1 rfl D2.good) ≠ 0 := by
    have e : z (padMap φc c1 rfl D2.good) = (z.comp (padMap φc c1 rfl)) D2.good := rfl
    rw [e, comp_padMap]
    exact (h2 _ (by rw [ptSet_padPt, hC])).1
  obtain ⟨x, hx⟩ := exists_baseAway _ z hv
  have key : x (padMap (rSum D2 c1 φa φc) c0 rfl D3.good) ≠ 0 := by
    have e : x (padMap (rSum D2 c1 φa φc) c0 rfl D3.good) =
        (x.comp (padMap (rSum D2 c1 φa φc) c0 rfl)) D3.good := rfl
    rw [e, comp_padMap]
    refine h3 _ ?_
    rw [ptSet_padPt]
    have e1 : x.comp ((IsScalarTower.toAlgHom K T (Localization.Away (padMap φc c1 rfl D2.good))).comp φa) =
        z.comp φa := by
      rw [← AlgHom.comp_assoc]
      exact congrArg (fun w => w.comp φa) hx
    have e2 : ptSet (x.comp (rIn D2 c1 φc)) = E := by
      rw [rIn, NuData.ptSet_nuStep, hx]
      exact (h2 _ (by rw [comp_padMap, ptSet_padPt, hC])).2
    show ptSet (x.comp (sumMap ((IsScalarTower.toAlgHom K T _).comp φa) (rIn D2 c1 φc))) ∪
      Finset.univ.image c0 = A3
    rw [comp_sumMap, ptSet_sumPt, e1, e2, hA]
  have h := (numA_pt (K := K) _ x).2 key
  have hx' : x.comp (awayι (K := K) (padMap φc c1 rfl D2.good)) = z := hx
  rwa [hx'] at h

end Wit

end GenRole

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_GenCfg =====
section

/-!
# S4-JacLaw, file O9g (G5 GenCfg): the configuration

* `role_sub`, `role_card`, `role_sdiff`: finset bookkeeping for one role `X ∪ (Z \ U)` with `X ∪ W = U`.
* `RoleOn D A W`: `D` is good on every point with point set `A`, and `ν = W` there.
* `exists_role_of`: `exists_role` in the configuration shape.
* `exists_pool`: fibre sections over any finset of good points, and a pool of `≥ 5g - 1` good points.
* **`exists_cfg`**: a `LawData` with point tuples `ta`, `tb` and the six roles of the law at `(ta, tb)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Sets

variable {α : Type*} [DecidableEq α]

theorem role_sub {Z U X W : Finset α} (hU : U ⊆ Z) (hXW : X ∪ W = U) : X ∪ (Z \ U) ⊆ Z := by
  refine Finset.union_subset (fun φ hφ => hU ?_) Finset.sdiff_subset
  rw [← hXW]
  exact Finset.mem_union_left W hφ

theorem role_card {Z U X W : Finset α} (hXW : X ∪ W = U) :
    (X ∪ (Z \ U)).card = X.card + (Z \ U).card := by
  refine Finset.card_union_of_disjoint ?_
  rw [Finset.disjoint_left]
  intro φ hX hZ
  refine (Finset.mem_sdiff.1 hZ).2 ?_
  rw [← hXW]
  exact Finset.mem_union_left W hX

theorem role_sdiff {Z U X W : Finset α} (hU : U ⊆ Z) (hXW : X ∪ W = U) (hd : Disjoint X W) :
    Z \ (X ∪ (Z \ U)) = W := by
  ext φ
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or, not_and, not_not]
  constructor
  · rintro ⟨hZ, hX, hU'⟩
    have h := hU' hZ
    rw [← hXW, Finset.mem_union] at h
    exact h.resolve_left hX
  · intro hW
    have hWU : φ ∈ U := by
      rw [← hXW]
      exact Finset.mem_union_right X hW
    exact ⟨hU hWU, Finset.disjoint_right.1 hd hW, fun _ => hWU⟩

theorem image_enum {n : ℕ} (t : Fin n → α) (S : Finset α) (hS : ∀ φ, φ ∈ S ↔ ∃ i, t i = φ) :
    Finset.univ.image t = S := by
  ext φ
  rw [Finset.mem_image, hS φ]
  simp only [Finset.mem_univ, true_and]

end Sets

section GenCfg

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- `D` is good on every point with point set `A`, with `ν = W` there. -/
abbrev RoleOn {d : ℕ} (D : NuData K F d) (A W : Finset (Places.Rfin K F →ₐ[K] K)) : Prop :=
  ∀ y : SymRing K (Places.Rfin K F) d →ₐ[K] K, ptSet y = A → y D.good ≠ 0 ∧ D.nuF y = W

/-- **One role in configuration shape**: `A = X ∪ (Z \ U)`, `ν(A) = W` where `X ∪ W = U`. -/
theorem exists_role_of {d : ℕ} (hdg : genusFK K F ≤ d + 1) {Hn : Places.Divisor K F} (hHn : IsInf Hn)
    (hHn0 : 0 ≤ Hn) (hdeg : Places.Divisor.deg Hn = ((d + genusFK K F : ℕ) : ℤ))
    {s : Places.Rfin K F} (hs0 : s ≠ 0) (hs : ExactPoleH s Hn)
    {Z U X W : Finset (Places.Rfin K F →ₐ[K] K)} (hZ : ∀ φ, φ ∈ Z ↔ φ s = 0)
    (hZc : Z.card = d + genusFK K F) (hU : U ⊆ Z) (hXW : X ∪ W = U) (hd : Disjoint X W)
    (hXc : X.card + (Z \ U).card = d) (hNS : IsNS K F W) :
    ∃ D : NuData K F d, D.Hn = Hn ∧ RoleOn D (X ∪ (Z \ U)) W := by
  have hsd := role_sdiff hU hXW hd
  obtain ⟨D, hD, h⟩ := exists_role hdg hHn hHn0 hdeg hs0 hs hZ hZc (role_sub hU hXW)
    ((role_card hXW).trans hXc) (by rw [hsd]; exact hNS)
  exact ⟨D, hD, fun y hy => ⟨(h y hy).1, (h y hy).2.trans hsd⟩⟩

/-- **Fibre sections and a pool of good points.** -/
theorem exists_pool : ∃ a0 : K[X],
    (∀ U : Finset (Places.Rfin K F →ₐ[K] K), (∀ φ ∈ U, a0.eval (φ (xB K F)) ≠ 0) →
      ∃ s : Places.Rfin K F, ∃ Z : Finset (Places.Rfin K F →ₐ[K] K),
        s ≠ 0 ∧ ExactPoleH s (poleDiv (K := K) (incB K F s)) ∧
        (poleDiv (K := K) (incB K F s)).deg = (Z.card : ℤ) ∧ (∀ φ, φ ∈ Z ↔ φ s = 0) ∧ U ⊆ Z) ∧
    ∃ T : Finset (Places.Rfin K F →ₐ[K] K), 5 * genusFK K F ≤ T.card + 1 ∧
      ∀ φ ∈ T, a0.eval (φ (xB K F)) ≠ 0 := by
  obtain ⟨a0, ha0, hfib⟩ := exists_fib_data (K := K) (F := F)
  refine ⟨a0, fun U hU => ?_, ?_⟩
  · obtain ⟨s, Z, hs0, hs, hdeg, hZ, hZx, hZc⟩ := hfib (U.image fun φ => φ (xB K F)) (by
      intro c hc
      obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.1 hc
      exact hU φ hφ)
    exact ⟨s, Z, hs0, hs, by rw [hdeg, hZc], hZ, fun φ hφ => (hZx φ).2 (Finset.mem_image_of_mem _ hφ)⟩
  · obtain ⟨Λ, hΛ, hΛc⟩ :=
      (finite_setOfPred_isRoot ha0).infinite_compl.exists_subset_card_eq (5 * genusFK K F)
    have hΛa : ∀ c ∈ Λ, a0.eval c ≠ 0 := fun c hc h => hΛ (Finset.mem_coe.2 hc) h
    obtain ⟨s, Z, -, -, -, -, hZx, hZc⟩ := hfib Λ hΛa
    have hn : 0 < finrank K[X] (Places.Rfin K F) :=
      (Module.finrank_pos_iff_of_free (R := K[X]) (M := Places.Rfin K F)).2 inferInstance
    refine ⟨Z, ?_, fun φ hφ => hΛa _ ((hZx φ).1 hφ)⟩
    rw [hZc, hΛc]
    exact Nat.le_succ_of_le (Nat.le_mul_of_pos_right _ hn)

/-- **The configuration**: a `LawData` and point tuples `ta`, `tb` with point sets `a`, `b`, such that
`m(a,b) = c` (via `ν3(a+b+c0) = E`, `ν2(E+c1) = c`), `ν2(c+c1) = E`, `ν3(a+E+c0) = b`, `ν3(b+E+c0) = a`,
each data good there. -/
theorem exists_cfg : ∃ L : LawData K F, ∃ ta tb : Fin (genusFK K F) → (Places.Rfin K F →ₐ[K] K),
    ∃ a b E c : Finset (Places.Rfin K F →ₐ[K] K),
      ptSet (symPt ta) = a ∧ ptSet (symPt tb) = b ∧
      RoleOn L.Dm3 (a ∪ b ∪ Finset.univ.image L.c0) E ∧
      RoleOn L.Dm2 (E ∪ Finset.univ.image L.c1) c ∧
      RoleOn L.Dr2 (c ∪ Finset.univ.image L.c1) E ∧
      RoleOn L.Dl2 (c ∪ Finset.univ.image L.c1) E ∧
      RoleOn L.Dr3 (a ∪ E ∪ Finset.univ.image L.c0) b ∧
      RoleOn L.Dl3 (b ∪ E ∪ Finset.univ.image L.c0) a := by
  obtain ⟨a0, hfib, T, hT, hTa⟩ := exists_pool (K := K) (F := F)
  obtain ⟨a, b, E, c, haT, hbT, hET, hcT, ha, hb, hE, hc, hab, haE, -, hbE, -, hEc, hNa, hNb, hNE, hNc⟩ :=
    exists_four_nonspecial T hT
  obtain ⟨s3, Z3, hs30, hs3, hdeg3, hZ3, hU3⟩ := hfib (a ∪ b ∪ E) (fun φ hφ => hTa φ (by
    simp only [Finset.mem_union] at hφ
    rcases hφ with (h | h) | h
    exacts [haT h, hbT h, hET h]))
  obtain ⟨s2, Z2, hs20, hs2, hdeg2, hZ2, hU2⟩ := hfib (E ∪ c) (fun φ hφ => hTa φ (by
    rcases Finset.mem_union.1 hφ with h | h
    exacts [hET h, hcT h]))
  obtain ⟨r3, hr3⟩ : ∃ r, (Z3 \ (a ∪ b ∪ E)).card = r := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r, (Z2 \ (E ∪ c)).card = r := ⟨_, rfl⟩
  obtain ⟨c0, -, hc0⟩ := exists_enum _ hr3
  obtain ⟨c1, -, hc1⟩ := exists_enum _ hr2
  obtain ⟨ta, -, hta⟩ := exists_enum a ha
  obtain ⟨tb, -, htb⟩ := exists_enum b hb
  have hab' : (a ∪ b).card = genusFK K F + genusFK K F := by
    rw [Finset.card_union_of_disjoint hab, ha, hb]
  have haE' : (a ∪ E).card = genusFK K F + genusFK K F := by
    rw [Finset.card_union_of_disjoint haE, ha, hE]
  have hbE' : (b ∪ E).card = genusFK K F + genusFK K F := by
    rw [Finset.card_union_of_disjoint hbE, hb, hE]
  have hU3c : (a ∪ b ∪ E).card = genusFK K F + genusFK K F + genusFK K F := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨haE, hbE⟩), hab', hE]
  have hU2c : (E ∪ c).card = genusFK K F + genusFK K F := by
    rw [Finset.card_union_of_disjoint hEc, hE, hc]
  have hZ3c : Z3.card = genusFK K F + genusFK K F + r3 + genusFK K F := by
    rw [← Finset.card_sdiff_add_card_eq_card hU3, hr3, hU3c]
    omega
  have hZ2c : Z2.card = genusFK K F + r2 + genusFK K F := by
    rw [← Finset.card_sdiff_add_card_eq_card hU2, hr2, hU2c]
    omega
  have hd3 : (poleDiv (K := K) (incB K F s3)).deg =
      ((genusFK K F + genusFK K F + r3 + genusFK K F : ℕ) : ℤ) := by rw [hdeg3, hZ3c]
  have hd2 : (poleDiv (K := K) (incB K F s2)).deg = ((genusFK K F + r2 + genusFK K F : ℕ) : ℤ) := by
    rw [hdeg2, hZ2c]
  have hI3 := isInf_poleDiv (K := K) (F := F) s3
  have hI2 := isInf_poleDiv (K := K) (F := F) s2
  have h03 : (0 : Places.Divisor K F) ≤ poleDiv (K := K) (incB K F s3) := le_sup_right
  have h02 : (0 : Places.Divisor K F) ≤ poleDiv (K := K) (incB K F s2) := le_sup_right
  obtain ⟨Dm3, hHm3, hm3⟩ := exists_role_of (by omega) hI3 h03 hd3 hs30 hs3 hZ3 hZ3c hU3
    (X := a ∪ b) (W := E) rfl (Finset.disjoint_union_left.2 ⟨haE, hbE⟩) (by rw [hab', hr3]) hNE
  obtain ⟨Dr3, hHr3, hr3'⟩ := exists_role_of (by omega) hI3 h03 hd3 hs30 hs3 hZ3 hZ3c hU3
    (X := a ∪ E) (W := b) (Finset.union_right_comm a E b) (Finset.disjoint_union_left.2 ⟨hab, hbE.symm⟩)
    (by rw [haE', hr3]) hNb
  obtain ⟨Dl3, hHl3, hl3'⟩ := exists_role_of (by omega) hI3 h03 hd3 hs30 hs3 hZ3 hZ3c hU3
    (X := b ∪ E) (W := a) (by rw [Finset.union_comm (b ∪ E) a, ← Finset.union_assoc])
    (Finset.disjoint_union_left.2 ⟨hab.symm, haE.symm⟩) (by rw [hbE', hr3]) hNa
  obtain ⟨Dm2, hHm2, hm2⟩ := exists_role_of (by omega) hI2 h02 hd2 hs20 hs2 hZ2 hZ2c hU2
    (X := E) (W := c) rfl hEc (by rw [hE, hr2]) hNc
  obtain ⟨Dr2, hHr2, hr2'⟩ := exists_role_of (by omega) hI2 h02 hd2 hs20 hs2 hZ2 hZ2c hU2
    (X := c) (W := E) (Finset.union_comm c E) hEc.symm (by rw [hc, hr2]) hNE
  have e0 := image_enum c0 _ hc0
  have e1 := image_enum c1 _ hc1
  have ea : ptSet (symPt ta) = a := by rw [ptSet_symPt]; exact image_enum ta a hta
  have eb : ptSet (symPt tb) = b := by rw [ptSet_symPt]; exact image_enum tb b htb
  rw [← e0] at hm3 hr3' hl3'
  rw [← e1] at hm2 hr2'
  exact ⟨⟨r3, r2, c0, c1, Dm3, Dr3, Dl3, Dm2, Dr2, Dr2, hHr3.trans hHm3.symm, hHl3.trans hHm3.symm,
    hHr2.trans hHm2.symm, hHr2.trans hHm2.symm⟩, ta, tb, a, b, E, c, ea, eb, hm3, hm2, hr2', hr2', hr3', hl3'⟩

end GenCfg

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacFrob_BrC =====
section

/-!
# S4-JacFrob, part BrC (bridge 2): contraction of places of `F-bar` to the levels `F_{lev j}`

* generic (a constant field extension `h`): `isIntegral_algFin/Inf h` (the ring pairs are integral),
  `coe_algFin/Inf h` (the pair maps are the field inclusion);
* `coe_incF`; `finR_pair`, `infR_pair` (`finR m ∘ (pair map) = finR i` for `lev i ∣ lev m`);
* **`isIntegral_finR j`, `isIntegral_infR j`**: `Rfin(F-bar)` (`Rinf(F-bar)`) is integral over the level ring;
* generic `asIdeal_contFin/Inf h` (the level contraction is `comap` of the pair map);
* `contFinB j`, `contInfB j` (`w ↦ w ∩ Rfin_j` via `HeightOneSpectrum.under`), `asIdeal_contFinB/InfB` (`= comap (finR j)`),
  `mem_contFinB`, `mem_contInfB`; `contB_inl/inr`, `contractNN_inl/inr`;
* **`contB j : Place (F-bar) → Place (F_{lev j})`**; `isLeft_contB`; **`contractNN_contB`** (compatible with the
  contractions between levels); **`exists_contB_eq`** (lying over); **`finite_contB`** (finite fibres).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places

section PairInt

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

theorem isIntegral_algFin : letI := algFin h; Algebra.IsIntegral (Rfin Fq F) (Rfin L F') := by
  letI := algFin h; haveI := towerFin h
  exact isIntegral_AA' h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin

theorem isIntegral_algInf : letI := algInf h; Algebra.IsIntegral (Rinf Fq F) (Rinf L F') := by
  letI := algInf h; haveI := towerInf h
  exact isIntegral_AA' h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf

theorem coe_algFin (a : Rfin Fq F) :
    letI := algFin h
    ((algebraMap (Rfin Fq F) (Rfin L F') a : Rfin L F') : F') = algebraMap F F' (a : F) := by
  letI := algFin h; haveI := towerFin h
  exact (IsScalarTower.algebraMap_apply (Rfin Fq F) (Rfin L F') F' a).symm.trans
    (IsScalarTower.algebraMap_apply (Rfin Fq F) F F' a)

theorem coe_algInf (a : Rinf Fq F) :
    letI := algInf h
    ((algebraMap (Rinf Fq F) (Rinf L F') a : Rinf L F') : F') = algebraMap F F' (a : F) := by
  letI := algInf h; haveI := towerInf h
  exact (IsScalarTower.algebraMap_apply (Rinf Fq F) (Rinf L F') F' a).symm.trans
    (IsScalarTower.algebraMap_apply (Rinf Fq F) F F' a)

theorem asIdeal_contFin (v : HeightOneSpectrum (Rfin L F')) :
    letI := algFin h
    (contFin h v).asIdeal = v.asIdeal.comap (algebraMap (Rfin Fq F) (Rfin L F')) := rfl

theorem asIdeal_contInf (v : HeightOneSpectrum (Rinf L F')) :
    letI := algInf h
    (contInf h v).asIdeal = v.asIdeal.comap (algebraMap (Rinf Fq F) (Rinf L F')) := rfl

end PairInt

section Cont

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem coe_incF (j : ℕ) (y : Fc Fq F Ω (lev j)) : ((incF Fq F Ω j y : Fbar Fq F Ω) : Ω) = (y : Ω) :=
  IntermediateField.coe_inclusion _ y

variable (hk : constField Fq F = ⊥)

theorem finR_pair {i m : ℕ} [Fact (lev i ∣ lev m)] (a : Rfin (Lc Fq Ω (lev i)) (Fc Fq F Ω (lev i))) :
    letI := algFin (isConstExt_pair Fq F Ω hk (n := lev i) (N := lev m))
    finR Fq F Ω m (algebraMap _ (Rfin (Lc Fq Ω (lev m)) (Fc Fq F Ω (lev m))) a) = finR Fq F Ω i a := by
  letI := algFin (isConstExt_pair Fq F Ω hk (n := lev i) (N := lev m))
  apply Subtype.ext
  rw [coe_finR, coe_finR]
  apply Subtype.ext
  rw [coe_incF, coe_incF, coe_algFin, coe_algebraMap_FF]

theorem infR_pair {i m : ℕ} [Fact (lev i ∣ lev m)] (a : Rinf (Lc Fq Ω (lev i)) (Fc Fq F Ω (lev i))) :
    letI := algInf (isConstExt_pair Fq F Ω hk (n := lev i) (N := lev m))
    infR Fq F Ω m (algebraMap _ (Rinf (Lc Fq Ω (lev m)) (Fc Fq F Ω (lev m))) a) = infR Fq F Ω i a := by
  letI := algInf (isConstExt_pair Fq F Ω hk (n := lev i) (N := lev m))
  apply Subtype.ext
  rw [coe_infR, coe_infR]
  apply Subtype.ext
  rw [coe_incF, coe_incF, coe_algInf, coe_algebraMap_FF]

include hk in
/-- **`Rfin(F-bar)` is integral over the level ring** `Rfin(F_{lev j})`. -/
theorem isIntegral_finR (j : ℕ) :
    letI := (finR Fq F Ω j).toAlgebra
    Algebra.IsIntegral (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) := by
  letI := (finR Fq F Ω j).toAlgebra
  refine ⟨fun z => ?_⟩
  obtain ⟨j1, y, rfl⟩ := exists_finR Fq F Ω z
  obtain ⟨m, hjm, hj1m⟩ : ∃ m, j ≤ m ∧ j1 ≤ m := ⟨max j j1, le_max_left _ _, le_max_right _ _⟩
  haveI : Fact (lev j ∣ lev m) := ⟨lev_dvd_lev hjm⟩
  haveI : Fact (lev j1 ∣ lev m) := ⟨lev_dvd_lev hj1m⟩
  obtain ⟨y', hy'⟩ : ∃ y' : Rfin (Lc Fq Ω (lev m)) (Fc Fq F Ω (lev m)), finR Fq F Ω m y' = finR Fq F Ω j1 y :=
    ⟨_, finR_pair Fq F Ω hk (i := j1) (m := m) y⟩
  rw [← hy']
  letI := algFin (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev m))
  haveI := isIntegral_algFin (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev m))
  refine IsIntegral.map_of_comp_eq (RingHom.id _) (finR Fq F Ω m) (RingHom.ext fun a => ?_)
    (Algebra.IsIntegral.isIntegral y')
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.id_apply, RingHom.algebraMap_toAlgebra]
  exact (finR_pair Fq F Ω hk a).symm

include hk in
/-- **`Rinf(F-bar)` is integral over the level ring** `Rinf(F_{lev j})`. -/
theorem isIntegral_infR (j : ℕ) :
    letI := (infR Fq F Ω j).toAlgebra
    Algebra.IsIntegral (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) := by
  letI := (infR Fq F Ω j).toAlgebra
  refine ⟨fun z => ?_⟩
  obtain ⟨j1, y, rfl⟩ := exists_infR Fq F Ω z
  obtain ⟨m, hjm, hj1m⟩ : ∃ m, j ≤ m ∧ j1 ≤ m := ⟨max j j1, le_max_left _ _, le_max_right _ _⟩
  haveI : Fact (lev j ∣ lev m) := ⟨lev_dvd_lev hjm⟩
  haveI : Fact (lev j1 ∣ lev m) := ⟨lev_dvd_lev hj1m⟩
  obtain ⟨y', hy'⟩ : ∃ y' : Rinf (Lc Fq Ω (lev m)) (Fc Fq F Ω (lev m)), infR Fq F Ω m y' = infR Fq F Ω j1 y :=
    ⟨_, infR_pair Fq F Ω hk (i := j1) (m := m) y⟩
  rw [← hy']
  letI := algInf (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev m))
  haveI := isIntegral_algInf (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev m))
  refine IsIntegral.map_of_comp_eq (RingHom.id _) (infR Fq F Ω m) (RingHom.ext fun a => ?_)
    (Algebra.IsIntegral.isIntegral y')
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.id_apply, RingHom.algebraMap_toAlgebra]
  exact (infR_pair Fq F Ω hk a).symm

/-- Contraction of finite places of `F-bar` to the level `lev j`. -/
noncomputable def contFinB (j : ℕ) (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) :
    HeightOneSpectrum (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :=
  letI := (finR Fq F Ω j).toAlgebra
  haveI := isIntegral_finR Fq F Ω hk j
  w.under _

/-- Contraction of the places of `F-bar` over `∞` to the level `lev j`. -/
noncomputable def contInfB (j : ℕ) (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω))) :
    HeightOneSpectrum (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :=
  letI := (infR Fq F Ω j).toAlgebra
  haveI := isIntegral_infR Fq F Ω hk j
  w.under _

theorem asIdeal_contFinB (j : ℕ) (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) :
    (contFinB Fq F Ω hk j w).asIdeal = w.asIdeal.comap (finR Fq F Ω j) := by
  letI := (finR Fq F Ω j).toAlgebra
  haveI := isIntegral_finR Fq F Ω hk j
  show (w.under _).asIdeal = _
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, RingHom.algebraMap_toAlgebra]

theorem mem_contFinB (j : ℕ) (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω)))
    (a : Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    a ∈ (contFinB Fq F Ω hk j w).asIdeal ↔ finR Fq F Ω j a ∈ w.asIdeal := by
  rw [asIdeal_contFinB, Ideal.mem_comap]

theorem asIdeal_contInfB (j : ℕ) (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω))) :
    (contInfB Fq F Ω hk j w).asIdeal = w.asIdeal.comap (infR Fq F Ω j) := by
  letI := (infR Fq F Ω j).toAlgebra
  haveI := isIntegral_infR Fq F Ω hk j
  show (w.under _).asIdeal = _
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, RingHom.algebraMap_toAlgebra]

theorem mem_contInfB (j : ℕ) (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω)))
    (a : Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    a ∈ (contInfB Fq F Ω hk j w).asIdeal ↔ infR Fq F Ω j a ∈ w.asIdeal := by
  rw [asIdeal_contInfB, Ideal.mem_comap]

/-- **Contraction** of places of `F-bar` to the level `F_{lev j}`. -/
noncomputable def contB (j : ℕ) :
    Places.Place (kbar Fq Ω) (Fbar Fq F Ω) → Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) :=
  Sum.map (contFinB Fq F Ω hk j) (contInfB Fq F Ω hk j)

theorem contB_inl (j : ℕ) (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) :
    contB Fq F Ω hk j (Sum.inl w) = Sum.inl (contFinB Fq F Ω hk j w) := rfl

theorem contB_inr (j : ℕ) (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω))) :
    contB Fq F Ω hk j (Sum.inr w) = Sum.inr (contInfB Fq F Ω hk j w) := rfl

theorem isLeft_contB (j : ℕ) (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    (contB Fq F Ω hk j P).isLeft = P.isLeft := by
  rcases P with w | w
  · rw [contB_inl, Sum.isLeft_inl, Sum.isLeft_inl]
  · rw [contB_inr, Sum.isLeft_inr, Sum.isLeft_inr]

theorem contractNN_inl {n N : ℕ} [NeZero n] [NeZero N] [Fact (n ∣ N)]
    (v : HeightOneSpectrum (Rfin (Lc Fq Ω N) (Fc Fq F Ω N))) :
    contractNN Ω hk n N (Sum.inl v) = Sum.inl (contFin (isConstExt_pair Fq F Ω hk (n := n) (N := N)) v) := rfl

theorem contractNN_inr {n N : ℕ} [NeZero n] [NeZero N] [Fact (n ∣ N)]
    (v : HeightOneSpectrum (Rinf (Lc Fq Ω N) (Fc Fq F Ω N))) :
    contractNN Ω hk n N (Sum.inr v) = Sum.inr (contInf (isConstExt_pair Fq F Ω hk (n := n) (N := N)) v) := rfl

/-- **Compatibility** with the contractions between levels. -/
theorem contractNN_contB {i j : ℕ} [Fact (lev i ∣ lev j)] (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    contractNN Ω hk (lev i) (lev j) (contB Fq F Ω hk j P) = contB Fq F Ω hk i P := by
  rcases P with w | w
  · rw [contB_inl, contB_inl, contractNN_inl]
    congr 1
    apply HeightOneSpectrum.ext
    rw [asIdeal_contFin, asIdeal_contFinB, asIdeal_contFinB, Ideal.comap_comap]
    congr 1
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply]
    exact finR_pair Fq F Ω hk a
  · rw [contB_inr, contB_inr, contractNN_inr]
    congr 1
    apply HeightOneSpectrum.ext
    rw [asIdeal_contInf, asIdeal_contInfB, asIdeal_contInfB, Ideal.comap_comap]
    congr 1
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply]
    exact infR_pair Fq F Ω hk a

/-- **Lying over**: every place of a level is a contraction of a place of `F-bar`. -/
theorem exists_contB_eq (j : ℕ) (Q : Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    ∃ P, contB Fq F Ω hk j P = Q := by
  rcases Q with v | v
  · letI := (finR Fq F Ω j).toAlgebra
    letI : Module (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toModule
    haveI := isIntegral_finR Fq F Ω hk j
    haveI : Module.IsTorsionFree (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (by
        rw [RingHom.algebraMap_toAlgebra]; exact finR_injective Fq F Ω j)
    obtain ⟨w, hw⟩ := RamanujanPetersson.PicDescent.exists_under_eq (B := Rfin (kbar Fq Ω) (Fbar Fq F Ω)) v
    exact ⟨Sum.inl w, by rw [contB_inl]; exact congrArg Sum.inl hw⟩
  · letI := (infR Fq F Ω j).toAlgebra
    letI : Module (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toModule
    haveI := isIntegral_infR Fq F Ω hk j
    haveI : Module.IsTorsionFree (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (by
        rw [RingHom.algebraMap_toAlgebra]; exact infR_injective Fq F Ω j)
    obtain ⟨w, hw⟩ := RamanujanPetersson.PicDescent.exists_under_eq (B := Rinf (kbar Fq Ω) (Fbar Fq F Ω)) v
    exact ⟨Sum.inr w, by rw [contB_inr]; exact congrArg Sum.inr hw⟩

/-- **Finite fibres** of the contraction. -/
theorem finite_contB (j : ℕ) (Q : Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    {P | contB Fq F Ω hk j P = Q}.Finite := by
  rcases Q with v | v
  · letI := (finR Fq F Ω j).toAlgebra
    letI : Module (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toModule
    haveI := isIntegral_finR Fq F Ω hk j
    haveI : Module.IsTorsionFree (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (by
        rw [RingHom.algebraMap_toAlgebra]; exact finR_injective Fq F Ω j)
    refine ((RamanujanPetersson.PicDescent.finite_under (B := Rfin (kbar Fq Ω) (Fbar Fq F Ω)) v).image
      Sum.inl).subset ?_
    rintro (w | w) hw
    · rw [Set.mem_setOf_eq, contB_inl] at hw
      exact ⟨w, Sum.inl.inj hw, rfl⟩
    · rw [Set.mem_setOf_eq, contB_inr] at hw
      exact absurd hw Sum.inr_ne_inl
  · letI := (infR Fq F Ω j).toAlgebra
    letI : Module (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toModule
    haveI := isIntegral_infR Fq F Ω hk j
    haveI : Module.IsTorsionFree (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (by
        rw [RingHom.algebraMap_toAlgebra]; exact infR_injective Fq F Ω j)
    refine ((RamanujanPetersson.PicDescent.finite_under (B := Rinf (kbar Fq Ω) (Fbar Fq F Ω)) v).image
      Sum.inr).subset ?_
    rintro (w | w) hw
    · rw [Set.mem_setOf_eq, contB_inl] at hw
      exact absurd hw Sum.inl_ne_inr
    · rw [Set.mem_setOf_eq, contB_inr] at hw
      exact ⟨w, Sum.inr.inj hw, rfl⟩

end Cont

end RamanujanPetersson.JacFrob

end


