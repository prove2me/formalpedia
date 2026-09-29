-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.Leray.nonempty_HTot_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/10051d54-db18-5957-86cd-d637382b1f51

import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv.AlgebraicGeometry TopologicalSpace Opposite"

noncomputable section

set_option autoImplicit false

section

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme IsSeparated OModulePresheaf.Leray.LerayDblCpx Scheme.OrderedAffineCover OModulePresheaf OModulePresheaf.unit"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "Leray.LerayDblCpx cochain d H0 HSucc unit mk mk.injEq"
namespace Leray
p2m_export "AlgebraicGeometry.OModulePresheaf.Leray" "LerayDblCpx biAug dH dV rows_exact dV_comp_biAug"
namespace Stair
p2m_open "AlgebraicGeometry.OModulePresheaf.Leray AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section Generic

variable {R : Type u} [CommRing R] {D : DoubleComplex.Bounded R}

theorem dTot_single_apply_succ {n pp q : ℕ} (h : pp + 1 + q = n + 1)
    (j : DoubleComplex.Diag n) (x : D.C j.1.1 j.1.2) (hne : pp + 1 ≠ j.1.1) :
    DoubleComplex.dTot D n
        (Pi.single (M := fun i : DoubleComplex.Diag n => D.C i.1.1 i.1.2) j x)
        ⟨(pp + 1, q), h⟩
      = D.dH pp q (Pi.single (M := fun i : DoubleComplex.Diag n => D.C i.1.1 i.1.2)
          j x ⟨(pp, q), by omega⟩) := by
  match q, h with
  | 0, h => exact DoubleComplex.dTot_apply_succ_zero h _
  | q' + 1, h =>
    rw [DoubleComplex.dTot_apply_succ_succ]
    refine add_eq_left.mpr ?_
    rw [Pi.single_eq_of_ne (fun heq => hne (congrArg (fun i => i.1.1) heq)), map_zero, smul_zero]

end Generic

section Edge

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

local notation "DL" => LerayDblCpx p πZ K K'

def eK' (n : ℕ) :
    (OModulePresheaf.unit (p ≫ πZ)).cochain K' n →ₗ[R] DoubleComplex.Tot (DL) n :=
  (LinearMap.single R (fun i : DoubleComplex.Diag n => (DL).C i.1.1 i.1.2)
    ⟨(0, n), Nat.zero_add n⟩).comp (biAug p πZ K K' n)

theorem eK'_apply_zero {n : ℕ} (h : 0 + n = n) (y : (OModulePresheaf.unit (p ≫ πZ)).cochain K' n) :
    eK' p πZ K K' n y ⟨(0, n), h⟩ = biAug p πZ K K' n y :=
  Pi.single_eq_same (M := fun i : DoubleComplex.Diag n => (DL).C i.1.1 i.1.2) _ _

theorem eK'_apply_pos {n p' q : ℕ} (h : p' + 1 + q = n)
    (y : (OModulePresheaf.unit (p ≫ πZ)).cochain K' n) :
    eK' p πZ K K' n y ⟨(p' + 1, q), h⟩ = 0 := by
  show Pi.single (M := fun i : DoubleComplex.Diag n => (DL).C i.1.1 i.1.2)
    ⟨(0, n), Nat.zero_add n⟩ (biAug p πZ K K' n y) ⟨(p' + 1, q), h⟩ = 0
  exact Pi.single_eq_of_ne
    (fun heq => by simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq; omega) _

end Edge

section Main

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ] [IsSeparated (p ≫ πZ)]
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

local notation "DL" => LerayDblCpx p πZ K K'

theorem dH_biAug (b : ℕ) (y : (OModulePresheaf.unit (p ≫ πZ)).cochain K' b) :
    (DL).dH 0 b (biAug p πZ K K' b y) = 0 :=
  LinearMap.mem_ker.mp (((rows_exact p πZ K K').2.1 b).ge ⟨y, rfl⟩)

theorem eK'_chain (n : ℕ) :
    DoubleComplex.dTot (DL) n ∘ₗ eK' p πZ K K' n
      = eK' p πZ K K' (n + 1) ∘ₗ (OModulePresheaf.unit (p ≫ πZ)).d K' n := by
  refine LinearMap.ext fun y => funext fun ⟨⟨pp, q⟩, h⟩ => ?_
  show DoubleComplex.dTot (DL) n (eK' p πZ K K' n y) ⟨(pp, q), h⟩
    = eK' p πZ K K' (n + 1) ((OModulePresheaf.unit (p ≫ πZ)).d K' n y) ⟨(pp, q), h⟩
  match pp, q, h with
  | 0, q' + 1, h =>
    obtain rfl : q' = n := by omega
    rw [DoubleComplex.dTot_apply_zero_succ, eK'_apply_zero, eK'_apply_zero]
    exact LinearMap.congr_fun (dV_comp_biAug p πZ K K' q') y
  | p' + 1, 0, h =>
    obtain rfl : p' = n := by omega
    rw [DoubleComplex.dTot_apply_succ_zero, eK'_apply_pos]
    rcases p' with _ | p''
    · rw [eK'_apply_zero]
      exact dH_biAug p πZ K K' 0 y
    · rw [eK'_apply_pos, map_zero]
  | p' + 1, q' + 1, h =>
    rw [DoubleComplex.dTot_apply_succ_succ, eK'_apply_pos, eK'_apply_pos, map_zero, smul_zero, add_zero]
    rcases p' with _ | p''
    · obtain rfl : q' + 1 = n := by omega
      rw [eK'_apply_zero]
      exact dH_biAug p πZ K K' (q' + 1) y
    · rw [eK'_apply_pos, map_zero]

theorem stair_surj (n : ℕ)
    (c : DoubleComplex.Tot (DL) (n + 1)) (hc : DoubleComplex.dTot (DL) (n + 1) c = 0) :
    ∃ (y : (OModulePresheaf.unit (p ≫ πZ)).cochain K' (n + 1)) (bb : DoubleComplex.Tot (DL) n),
      (OModulePresheaf.unit (p ≫ πZ)).d K' (n + 1) y = 0 ∧
      c = eK' p πZ K K' (n + 1) y + DoubleComplex.dTot (DL) n bb := by
  suffices H : ∀ P, ∀ c : DoubleComplex.Tot (DL) (n + 1),
      DoubleComplex.dTot (DL) (n + 1) c = 0 →
      (∀ pp q h, P < pp → c ⟨(pp, q), h⟩ = 0) →
      ∃ y bb, (OModulePresheaf.unit (p ≫ πZ)).d K' (n + 1) y = 0 ∧
        c = eK' p πZ K K' (n + 1) y + DoubleComplex.dTot (DL) n bb from
    H (n + 1) c hc fun pp q hpq hp => absurd hpq (by omega)
  intro P
  induction P with
  | zero =>
    intro c hc htop
    have hdH : (DL).dH 0 (n + 1) (c ⟨(0, n + 1), by omega⟩) = 0 := by
      have h1 := congrFun hc ⟨(1, n + 1), by omega⟩
      rwa [Pi.zero_apply, DoubleComplex.dTot_apply_succ_succ,
        htop 1 n (by omega) one_pos, map_zero, smul_zero, add_zero] at h1
    obtain ⟨y, hy⟩ := ((rows_exact p πZ K K').2.1 (n + 1)).le (LinearMap.mem_ker.mpr hdH)
    have hdy : (OModulePresheaf.unit (p ≫ πZ)).d K' (n + 1) y = 0 := by
      have hcomm : (DL).dV 0 (n + 1) (biAug p πZ K K' (n + 1) y)
          = biAug p πZ K K' (n + 2) ((OModulePresheaf.unit (p ≫ πZ)).d K' (n + 1) y) :=
        LinearMap.congr_fun (dV_comp_biAug p πZ K K' (n + 1)) y
      refine (rows_exact p πZ K K').2.2 (n + 2) ?_
      rw [map_zero, ← hcomm, hy]
      have h0 := congrFun hc ⟨(0, n + 2), by omega⟩
      rwa [Pi.zero_apply, DoubleComplex.dTot_apply_zero_succ] at h0
    refine ⟨y, 0, hdy, funext fun ⟨⟨pp, q⟩, hpq⟩ => ?_⟩
    simp only [Pi.add_apply, map_zero, Pi.zero_apply, add_zero]
    match pp, hpq with
    | 0, hpq =>
      obtain rfl : q = n + 1 := by omega
      rw [eK'_apply_zero, hy]
    | p' + 1, hpq =>
      rw [htop (p' + 1) q hpq (Nat.succ_pos _), eK'_apply_pos]
  | succ P ih =>
    intro c hc htop
    by_cases hPn : P + 1 ≤ n + 1
    · have hdH : ∀ Q (hQ : P + 1 + Q = n + 1),
          (DL).dH (P + 1) Q (c ⟨(P + 1, Q), hQ⟩) = 0 :=
        fun Q hQ => by
          have h1 : DoubleComplex.dTot (DL) (n + 1) c ⟨(P + 2, Q), by omega⟩ = 0 := congrFun hc _
          match Q, hQ, h1 with
          | 0, hQ, h1 => rwa [DoubleComplex.dTot_apply_succ_zero] at h1
          | m + 1, hQ, h1 =>
            rwa [DoubleComplex.dTot_apply_succ_succ,
              htop (P + 2) m (by omega) (by omega), map_zero, smul_zero, add_zero] at h1
      obtain ⟨bτ, hbτ⟩ := (rows_exact p πZ K K').1 P (n - P)
        (LinearMap.mem_ker.mpr (hdH (n - P) (by omega)))
      set b' : DoubleComplex.Tot (DL) n :=
        Pi.single ⟨(P, n - P), by omega⟩ bτ
      have hb'ne : ∀ pp q h, (pp, q) ≠ (P, n - P) → b' ⟨(pp, q), h⟩ = 0 := fun pp q h hne =>
        Pi.single_eq_of_ne (fun heq => hne (by simp only [Subtype.mk.injEq] at heq; exact heq)) _
      have hdHb' : ∀ Q (hQ : P + 1 + Q = n + 1),
          DoubleComplex.dTot (DL) n b' ⟨(P + 1, Q), hQ⟩ = c ⟨(P + 1, Q), hQ⟩ := fun Q hQ => by
        obtain rfl : Q = n - P := by omega
        rw [show b' = _ from rfl,
          dTot_single_apply_succ hQ _ _ (by simp), Pi.single_eq_same]
        exact hbτ
      set c' := c - DoubleComplex.dTot (DL) n b'
      have hc' : DoubleComplex.dTot (DL) (n + 1) c' = 0 := by
        simp only [c', map_sub, hc, zero_sub, neg_eq_zero]
        exact LinearMap.congr_fun (DoubleComplex.dTot_comp_dTot (DL) n) b'
      have htop' : ∀ pp q h, P < pp → c' ⟨(pp, q), h⟩ = 0 := by
        intro pp q hpq hp
        simp only [c', Pi.sub_apply, sub_eq_zero]
        rcases (Nat.lt_iff_add_one_le.mp hp).eq_or_lt with heq | hlt
        · exact heq ▸ (hdHb' q (heq ▸ hpq)).symm
        · rw [htop pp q hpq (by omega)]
          match pp, q, hpq with
          | p' + 1, 0, _ =>
            rw [DoubleComplex.dTot_apply_succ_zero,
              hb'ne p' 0 (by omega) (by intro heq; injection heq; omega), map_zero]
          | p' + 1, q' + 1, _ =>
            rw [DoubleComplex.dTot_apply_succ_succ,
              hb'ne p' (q'+1) (by omega) (by intro heq; injection heq; omega),
              hb'ne (p'+1) q' (by omega) (by intro heq; injection heq; omega),
              map_zero, map_zero, smul_zero, add_zero]
      obtain ⟨y, b₀, hdy, hceq'⟩ := ih c' hc' htop'
      exact ⟨y, b₀ + b', hdy, by rw [map_add, ← add_assoc, ← hceq']; simp only [c', sub_add_cancel]⟩
    · exact ih c hc fun pp q hpq hp => htop pp q hpq (lt_of_le_of_lt (by omega) hp)

theorem stair_inj (n : ℕ) (y : (OModulePresheaf.unit (p ≫ πZ)).cochain K' (n + 1))
    (bb : DoubleComplex.Tot (DL) n)
    (hb : eK' p πZ K K' (n + 1) y = DoubleComplex.dTot (DL) n bb) :
    ∃ y', y = (OModulePresheaf.unit (p ≫ πZ)).d K' n y' := by
  suffices H : ∀ P, ∀ bb : DoubleComplex.Tot (DL) n,
      eK' p πZ K K' (n + 1) y = DoubleComplex.dTot (DL) n bb →
      (∀ pp q h, P < pp → bb ⟨(pp, q), h⟩ = 0) →
      ∃ y', y = (OModulePresheaf.unit (p ≫ πZ)).d K' n y' from
    H n bb hb fun pp q hpq hp => absurd hpq (by omega)
  intro P
  induction P with
  | zero =>
    intro bb hb htop
    have hdH : (DL).dH 0 n (bb ⟨(0, n), by omega⟩) = 0 := by
      have h1 := congrFun hb ⟨(1, n), by omega⟩
      rcases n with _ | n'
      · rwa [eK'_apply_pos, DoubleComplex.dTot_apply_succ_zero, eq_comm] at h1
      · rwa [eK'_apply_pos, DoubleComplex.dTot_apply_succ_succ,
          htop 1 n' (by omega) one_pos, map_zero, smul_zero, add_zero, eq_comm] at h1
    obtain ⟨w, hw⟩ := ((rows_exact p πZ K K').2.1 n).le (LinearMap.mem_ker.mpr hdH)
    refine ⟨w, (rows_exact p πZ K K').2.2 (n + 1) ?_⟩
    have h0 := congrFun hb ⟨(0, n + 1), by omega⟩
    rw [eK'_apply_zero, DoubleComplex.dTot_apply_zero_succ] at h0
    have hcomm : (DL).dV 0 n (biAug p πZ K K' n w)
        = biAug p πZ K K' (n + 1) ((OModulePresheaf.unit (p ≫ πZ)).d K' n w) :=
      LinearMap.congr_fun (dV_comp_biAug p πZ K K' n) w
    rw [← hcomm, hw]
    exact h0
  | succ P ih =>
    intro bb hb htop
    by_cases hPn : P + 1 ≤ n
    · rcases n with _ | n'
      · omega
      have hdH : ∀ Q (hQ : P + 1 + Q = n' + 1),
          (DL).dH (P + 1) Q (bb ⟨(P + 1, Q), hQ⟩) = 0 := fun Q hQ => by
        have h1 : DoubleComplex.dTot (DL) (n' + 1) bb ⟨(P + 2, Q), by omega⟩ = 0 := by
          rw [← congrFun hb _, eK'_apply_pos]
        match Q, hQ, h1 with
        | 0, hQ, h1 => rwa [DoubleComplex.dTot_apply_succ_zero] at h1
        | m + 1, hQ, h1 =>
          rwa [DoubleComplex.dTot_apply_succ_succ,
            htop (P + 2) m (by omega) (by omega), map_zero, smul_zero, add_zero] at h1
      obtain ⟨bτ, hbτ⟩ := (rows_exact p πZ K K').1 P (n' - P)
        (LinearMap.mem_ker.mpr (hdH (n' - P) (by omega)))
      set b'' : DoubleComplex.Tot (DL) n' :=
        Pi.single ⟨(P, n' - P), by omega⟩ bτ
      have hb''ne : ∀ pp q h, (pp, q) ≠ (P, n' - P) → b'' ⟨(pp, q), h⟩ = 0 := fun pp q h hne =>
        Pi.single_eq_of_ne (fun heq => hne (by simp only [Subtype.mk.injEq] at heq; exact heq)) _
      have hdHb'' : ∀ Q (hQ : P + 1 + Q = n' + 1),
          DoubleComplex.dTot (DL) n' b'' ⟨(P + 1, Q), hQ⟩ = bb ⟨(P + 1, Q), hQ⟩ := fun Q hQ => by
        obtain rfl : Q = n' - P := by omega
        rw [show b'' = _ from rfl,
          dTot_single_apply_succ hQ _ _ (by simp), Pi.single_eq_same]
        exact hbτ
      refine ih (bb - DoubleComplex.dTot (DL) n' b'') ?_ ?_
      · rw [map_sub, ← LinearMap.comp_apply, DoubleComplex.dTot_comp_dTot,
          LinearMap.zero_apply, sub_zero, hb]
      · intro pp q hpq hp
        simp only [Pi.sub_apply, sub_eq_zero]
        rcases (Nat.lt_iff_add_one_le.mp hp).eq_or_lt with heq | hlt
        · exact heq ▸ (hdHb'' q (heq ▸ hpq)).symm
        · rw [htop pp q hpq (by omega)]
          match pp, q, hpq with
          | p' + 1, 0, _ =>
            rw [DoubleComplex.dTot_apply_succ_zero,
              hb''ne p' 0 (by omega) (by intro heq; injection heq; omega), map_zero]
          | p' + 1, q' + 1, _ =>
            rw [DoubleComplex.dTot_apply_succ_succ,
              hb''ne p' (q'+1) (by omega) (by intro heq; injection heq; omega),
              hb''ne (p'+1) q' (by omega) (by intro heq; injection heq; omega),
              map_zero, map_zero, smul_zero, add_zero]
    · exact ih bb hb fun pp q hpq hp => htop pp q hpq (lt_of_le_of_lt (by omega) hp)

def HeK' (n : ℕ) :
    (OModulePresheaf.unit (p ≫ πZ)).HSucc K' n →ₗ[R] DoubleComplex.HTot (DL) (n + 1) :=
  Submodule.mapQ _ _
    ((eK' p πZ K K' (n + 1)).restrict fun y hy => LinearMap.mem_ker.mpr <| by
      have hy' : (OModulePresheaf.unit (p ≫ πZ)).d K' (n + 1) y = 0 := LinearMap.mem_ker.mp hy
      have hch := LinearMap.congr_fun (eK'_chain p πZ K K' (n + 1)) y
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hy', map_zero] at hch
      exact hch)
    (by
      rintro x ⟨y', hy'⟩
      refine ⟨eK' p πZ K K' n y', ?_⟩
      have hch := LinearMap.congr_fun (eK'_chain p πZ K K' n) y'
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hch
      exact hch.trans (congrArg _ hy'))

def HTotSuccEquiv (n : ℕ) :
    DoubleComplex.HTot (DL) (n + 1) ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).HSucc K' n :=
  (LinearEquiv.ofBijective (HeK' p πZ K K' n)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hmap
      obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      simp only [HeK', Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hmap
      obtain ⟨bb, hbb⟩ := hmap
      obtain ⟨y', hy'⟩ := stair_inj p πZ K K' n y bb hbb.symm
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y', hy'.symm⟩,
     fun x => by
      obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, bb, hdy, hceq⟩ := stair_surj p πZ K K' n c (LinearMap.mem_ker.mp hc)
      refine ⟨Submodule.Quotient.mk ⟨y, LinearMap.mem_ker.mpr hdy⟩, ?_⟩
      simp only [HeK', Submodule.mapQ_apply, Submodule.Quotient.eq]
      exact ⟨-bb, by
        show DoubleComplex.dTot (DL) n (-bb) = eK' p πZ K K' (n + 1) y - c
        rw [map_neg, hceq, sub_add_eq_sub_sub, sub_self, zero_sub]⟩⟩).symm

def HTotZeroEquiv :
    DoubleComplex.HTot (DL) 0 ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).H0 K' :=
  (Submodule.quotEquivOfEqBot _ rfl).trans
    (LinearEquiv.ofBijective
      (((eK' p πZ K K' 0).comp
        (LinearMap.ker ((OModulePresheaf.unit (p ≫ πZ)).d K' 0)).subtype).codRestrict
        (LinearMap.ker (DoubleComplex.dTot (DL) 0))
        fun y => LinearMap.mem_ker.mpr <| by
          have hch := LinearMap.congr_fun (eK'_chain p πZ K K' 0) y.1
          rw [LinearMap.comp_apply, LinearMap.comp_apply] at hch
          exact hch.trans ((congrArg _ (LinearMap.mem_ker.mp y.2)).trans (map_zero _)))
      ⟨fun y₁ y₂ hy => Subtype.ext ((rows_exact p πZ K K').2.2 0
          ((eK'_apply_zero p πZ K K' (Nat.zero_add 0) y₁.1).symm.trans
            ((congrFun (Subtype.ext_iff.mp hy) ⟨(0,0), Nat.zero_add 0⟩).trans
              (eK'_apply_zero p πZ K K' (Nat.zero_add 0) y₂.1)))),
       fun ⟨c, hc⟩ => by
          have hdH : (DL).dH 0 0 (c ⟨(0,0), Nat.zero_add 0⟩) = 0 := by
            have h1 := congrFun (LinearMap.mem_ker.mp hc) ⟨(1, 0), rfl⟩
            rwa [Pi.zero_apply, DoubleComplex.dTot_apply_succ_zero] at h1
          obtain ⟨y, hy⟩ := ((rows_exact p πZ K K').2.1 0).le (LinearMap.mem_ker.mpr hdH)
          have hdy : (OModulePresheaf.unit (p ≫ πZ)).d K' 0 y = 0 := by
            have hcomm : (DL).dV 0 0 (biAug p πZ K K' 0 y)
                = biAug p πZ K K' 1 ((OModulePresheaf.unit (p ≫ πZ)).d K' 0 y) :=
              LinearMap.congr_fun (dV_comp_biAug p πZ K K' 0) y
            refine (rows_exact p πZ K K').2.2 1 ?_
            rw [map_zero, ← hcomm, hy]
            have h0 := congrFun (LinearMap.mem_ker.mp hc) ⟨(0, 1), rfl⟩
            rwa [Pi.zero_apply, DoubleComplex.dTot_apply_zero_succ] at h0
          refine ⟨⟨y, LinearMap.mem_ker.mpr hdy⟩, Subtype.ext (funext fun ⟨⟨pp,q⟩,hpq⟩ => ?_)⟩
          obtain ⟨rfl, rfl⟩ : pp = 0 ∧ q = 0 := by omega
          exact (eK'_apply_zero p πZ K K' (Nat.zero_add 0) y).trans hy⟩).symm

end Main

end AlgebraicGeometry.OModulePresheaf.Leray.Stair

end

end

open _root_.AlgebraicGeometry.OModulePresheaf.Leray _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv.AlgebraicGeometry.OModulePresheaf.Leray in

theorem solution
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    [IsSeparated πZ] [IsSeparated (p ≫ πZ)] (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) :
    Nonempty (DoubleComplex.HTot (OModulePresheaf.Leray.LerayDblCpx p πZ K K') 0
        ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).H0 K') ∧
      ∀ n : ℕ, Nonempty (DoubleComplex.HTot (OModulePresheaf.Leray.LerayDblCpx p πZ K K') (n + 1)
        ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).HSucc K' n) :=
  ⟨⟨Stair.HTotZeroEquiv p πZ K K'⟩, fun n => ⟨Stair.HTotSuccEquiv p πZ K K' n⟩⟩

end S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv (solution)
