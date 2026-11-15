-- Prove2me | Definitions.Def_RPLib_S4_SwanRepQ
-- name    : RPLib_S4_SwanRepQ
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:22:37.619671+00:00
-- url     : https://prove2.me/theorems/be56f5fc-a00d-4c8c-a4ce-65db0c872f54
-- title:
--   The Swan conductor as an upper-numbering integral, and its compatibility with quotients
-- statement:
--   With the notation of the Swan conductor of a representation $\rho$ of a group with a ramification function, the file writes $$\mathrm{Sw}(\rho) = \int_0^\infty \operatorname{cod}\big(V^{G^v}\big)\, dv,$$ the integral of the codimension of the invariants of the upper ramification groups (a step function of $v \in \mathbb{R}$). Using Herbrand's theorem it proves that the Swan conductor of a representation inflated from a quotient $G/H$ equals the Swan conductor computed on $G/H$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter VI, Section 2; N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1

import Mathlib
import Definitions.Def_RPLib_S4_SwanRep

/-!
# S4-Swan (K2), part 4: Swan conductor as an upper-numbering integral; quotient compatibility

`G^v = G_{idxR v}` for real `v` (`idxR v` = least `m` with `v ≤ φ(m)`), and
`Sw(ρ) = ∫_0^T codim V^{G^v} dv` for `T ≥ φ(top)` (`swan_eq_integral`). With Herbrand's theorem (`map_upper`)
this gives the quotient compatibility `Sw_G(Infl ρ) = Sw_{G/H}(ρ)` over any field (`swan_comp`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

open Module MeasureTheory

theorem cod_mono {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) {H K : Subgroup G} (h : H ≤ K) : cod ρ H ≤ cod ρ K := by
  unfold cod
  have := Submodule.finrank_mono (fixd_anti ρ h)
  omega

namespace RamFn

variable {G : Type*} [Group G] [Fintype G] (R : RamFn G)

theorem exists_le_phiR (v : ℝ) : ∃ m : ℕ, v ≤ (R.phi m : ℝ) := by
  obtain ⟨m, hm⟩ := R.exists_le_phi ((⌈v⌉ : ℤ) : ℚ)
  refine ⟨m, (Int.le_ceil v).trans ?_⟩
  have : (((⌈v⌉ : ℤ) : ℚ) : ℝ) ≤ (R.phi m : ℝ) := by exact_mod_cast hm
  simpa using this

/-- Upper index for real `v`: the least `m` with `v ≤ φ(m)`, so `G^v = G_{idxR v}`. -/
def idxR (v : ℝ) : ℕ := Nat.find (R.exists_le_phiR v)

theorem idxR_le_iff (v : ℝ) (n : ℕ) : R.idxR v ≤ n ↔ v ≤ (R.phi n : ℝ) := by
  constructor
  · intro h
    exact (Nat.find_spec (R.exists_le_phiR v)).trans (by exact_mod_cast R.phi_strictMono.monotone h)
  · intro h
    exact Nat.find_min' _ h

theorem idxR_mono : Monotone R.idxR := fun v w h => by
  rw [R.idxR_le_iff]
  exact h.trans ((R.idxR_le_iff w _).1 le_rfl)

theorem idxR_eq {v : ℝ} {u : ℕ} (h1 : (R.phi u : ℝ) < v) (h2 : v ≤ (R.phi (u + 1) : ℝ)) :
    R.idxR v = u + 1 := by
  apply le_antisymm ((R.idxR_le_iff v _).2 h2)
  by_contra hlt
  have := (R.idxR_le_iff v u).1 (by omega)
  linarith

theorem idxR_ratCast (q : ℚ) : R.idxR q = R.upperIdx q := by
  apply le_antisymm
  · rw [R.idxR_le_iff]
    exact_mod_cast (R.upperIdx_le_iff q _).1 le_rfl
  · rw [R.upperIdx_le_iff]
    exact_mod_cast (R.idxR_le_iff q _).1 le_rfl

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (ρ : Representation k G V)

/-- `v ↦ codim V^{G^v}` for real `v`. -/
def codU (v : ℝ) : ℝ := cod ρ (R.lower (R.idxR v))

theorem codU_antitone : Antitone (R.codU ρ) := fun _ _ h => by
  unfold codU
  exact_mod_cast cod_mono ρ (R.lower_antitone (R.idxR_mono h))

theorem integral_codU_piece (u : ℕ) :
    ∫ v in (R.phi u : ℝ)..(R.phi (u + 1) : ℝ), R.codU ρ v =
      ((R.phi (u + 1) : ℝ) - R.phi u) * cod ρ (R.lower (u + 1)) := by
  have hle : (R.phi u : ℝ) ≤ R.phi (u + 1) := by exact_mod_cast (R.phi_lt_succ u).le
  rw [intervalIntegral.integral_congr_ae' (g := fun _ => (cod ρ (R.lower (u + 1)) : ℝ)) ?_ ?_,
    intervalIntegral.integral_const, smul_eq_mul]
  · exact Filter.Eventually.of_forall fun v hv => by
      unfold codU
      rw [R.idxR_eq hv.1 hv.2]
  · exact Filter.Eventually.of_forall fun v hv => absurd (hv.1.trans_le hv.2) (not_lt.2 hle)

theorem integral_codU_tail {T : ℝ} (hT : (R.phi R.top : ℝ) ≤ T) :
    ∫ v in (R.phi R.top : ℝ)..T, R.codU ρ v = 0 := by
  rw [intervalIntegral.integral_congr_ae' (g := fun _ => (0 : ℝ)) ?_ ?_, intervalIntegral.integral_zero]
  · exact Filter.Eventually.of_forall fun v hv => by
      unfold codU
      have h : R.top + 1 ≤ R.idxR v := by
        by_contra h
        have := (R.idxR_le_iff v R.top).1 (by omega)
        linarith [hv.1]
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
      rw [hd, show R.top + 1 + d = (R.top + d) + 1 by omega, R.lower_eq_bot (by omega), cod_bot]
      simp
  · exact Filter.Eventually.of_forall fun v hv => absurd (hv.1.trans_le hv.2) (not_lt.2 hT)

/-- `Sw(ρ) = ∫_0^T codim V^{G^v} dv` for any `T ≥ φ(top)`. -/
theorem swan_eq_integral {T : ℝ} (hT : (R.phi R.top : ℝ) ≤ T) :
    (R.swan ρ : ℝ) = ∫ v in (0 : ℝ)..T, R.codU ρ v := by
  have hI : ∀ a b : ℝ, IntervalIntegrable (R.codU ρ) volume a b := fun _ _ =>
    (R.codU_antitone ρ).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 (R.phi R.top)) (hI _ T),
    R.integral_codU_tail ρ hT, add_zero]
  have hs := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := R.codU ρ)
    (a := fun u => (R.phi u : ℝ)) (n := R.top) (fun u _ => hI _ _)
  simp only [R.phi_zero, Rat.cast_zero] at hs
  rw [← hs, R.swan_eq_phi ρ le_rfl]
  push_cast
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [R.integral_codU_piece ρ u]

section Quot

variable {Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q] (S : RamFn Q) {π : G →* Q}

theorem map_lower_idxR (hπ : Function.Surjective π) (hq : QuotFormula R S π) (v : ℝ) :
    (R.lower (R.idxR v)).map π = S.lower (S.idxR v) := by
  set q : ℚ := min (R.phi (R.idxR v)) (S.phi (S.idxR v))
  have hv : v ≤ (q : ℝ) := by
    rw [Rat.cast_min]
    exact le_min ((R.idxR_le_iff v _).1 le_rfl) ((S.idxR_le_iff v _).1 le_rfl)
  have hR : R.idxR q = R.idxR v := le_antisymm
    ((R.idxR_le_iff _ _).2 (by rw [Rat.cast_min]; exact min_le_left _ _)) (R.idxR_mono hv)
  have hS : S.idxR q = S.idxR v := le_antisymm
    ((S.idxR_le_iff _ _).2 (by rw [Rat.cast_min]; exact min_le_right _ _)) (S.idxR_mono hv)
  have h := R.map_upper S hπ hq q
  rw [upper, upper, ← R.idxR_ratCast, ← S.idxR_ratCast, hR, hS] at h
  exact h

variable {k' W : Type*} [Field k'] [AddCommGroup W] [Module k' W] [FiniteDimensional k' W]
  (ρ' : Representation k' Q W)

theorem codU_comp (hπ : Function.Surjective π) (hq : QuotFormula R S π) (v : ℝ) :
    R.codU (ρ'.comp π) v = S.codU ρ' v := by
  unfold codU
  rw [cod_comp, R.map_lower_idxR S hπ hq v]

/-- Quotient compatibility of the Swan conductor (Serre VI §2): inflation from `Q = G/H` preserves `Sw`,
over any field. -/
theorem swan_comp (hπ : Function.Surjective π) (hq : QuotFormula R S π) :
    R.swan (ρ'.comp π) = S.swan ρ' := by
  have h1 := R.swan_eq_integral (ρ'.comp π) (le_max_left (R.phi R.top : ℝ) (S.phi S.top))
  have h2 := S.swan_eq_integral ρ' (le_max_right (R.phi R.top : ℝ) (S.phi S.top))
  have h : (R.swan (ρ'.comp π) : ℝ) = S.swan ρ' := by
    rw [h1, h2]
    congr 1
    funext v
    exact R.codU_comp S ρ' hπ hq v
  exact_mod_cast h

end Quot

end RamFn

end

end Swan
end RamanujanPetersson


