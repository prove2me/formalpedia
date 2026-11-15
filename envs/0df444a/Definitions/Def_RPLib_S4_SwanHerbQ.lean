-- Prove2me | Definitions.Def_RPLib_S4_SwanHerbQ
-- name    : RPLib_S4_SwanHerbQ
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:18:28.664365+00:00
-- url     : https://prove2.me/theorems/5451631d-7ffd-42c6-808e-3bf30ea7ac56
-- title:
--   Herbrand's theorem: upper numbering is compatible with quotients
-- statement:
--   Let $\pi : G \to Q$ be a surjection of finite groups with kernel $H$, and let $i_G$, $i_Q$ be ramification functions on $G$ and $Q$. Suppose the quotient formula of Serre (Local Fields IV, Proposition 3) holds: $$i_Q(s)\,|H| = \sum_{\pi(\sigma) = s} i_G(\sigma) \qquad (s \ne 1).$$ Then the Herbrand functions satisfy $\varphi_G = \varphi_Q \circ \varphi_{H}$ (on the lower indices of the best representatives of the fibres), and Herbrand's theorem holds: $$Q^v = \pi(G^v) \quad \text{for all } v.$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV, Sections 1 and 3 (Herbrand's theorem)

import Mathlib
import Definitions.Def_RPLib_S4_SwanHerb

/-!
# S4-Swan (K2), part 2: Herbrand's theorem from the quotient formula

`π : G →* Q` surjective with kernel `H`, ramification functions `R` on `G` and `S` on `Q` satisfying Serre's
quotient formula (IV §1 Prop 3) `i_Q(s) |H| = ∑_{π σ = s} i_G(σ)` for `s ≠ 1` (`QuotFormula`). Then
(Serre IV §3 Lemma 5, Prop 15, Herbrand's theorem):
* `i_Q(s) - 1 = φ_H(i_G(σ_s) - 1)` for a lift `σ_s` of maximal `i` (`toNat_i_eq`);
* `φ_Q(φ_H(m)) = φ_G(m)` whenever `φ_H(m)` is a natural number (`phi_trans`);
* `π(G^v) = Q^v` (`map_upper`): upper numbering is compatible with quotients.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

namespace RamFn

theorem cast_min_enat (a b : ℕ) : ((min a b : ℕ) : ℕ∞) = min (a : ℕ∞) b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (Nat.cast_le.2 h)]
  · rw [min_eq_right h, min_eq_right (Nat.cast_le.2 h)]

variable {G Q : Type*} [Group G] [Group Q] [Fintype G] [Fintype Q] [DecidableEq Q]
  (R : RamFn G) (S : RamFn Q) (π : G →* Q)

/-- The fibre of `π` over `s`. -/
def fib (s : Q) : Finset G := Finset.univ.filter (fun σ => π σ = s)

/-- Serre IV §1 Prop 3: `i_Q(s) |H| = ∑_{π σ = s} i_G(σ)` for `s ≠ 1`. -/
def QuotFormula : Prop :=
  ∀ s : Q, s ≠ 1 → (S.i s).toNat * Nat.card π.ker = ∑ σ ∈ fib π s, (R.i σ).toNat

/-- `∑_σ w σ m = |G| (φ m + 1)`. -/
theorem sum_w {K : Type*} [Group K] [Fintype K] (T : RamFn K) (m : ℕ) :
    (∑ σ : K, (T.w σ m : ℚ)) = Nat.card K * (T.phi m + 1) := by
  rw [phi, sub_add_cancel, mul_div_cancel₀ _ (cardG_pos (G := K)).ne']

variable {π} (hπ : Function.Surjective π)
include R hπ

theorem fib_nonempty (s : Q) : (fib π s).Nonempty := by
  obtain ⟨σ, hσ⟩ := hπ s
  exact ⟨σ, by simp [fib, hσ]⟩

/-- A lift of `s` with maximal `i`. -/
def best (s : Q) : G :=
  Classical.choose (Finset.exists_max_image (fib π s) R.i (fib_nonempty R hπ s))

theorem best_spec (s : Q) :
    R.best hπ s ∈ fib π s ∧ ∀ σ ∈ fib π s, R.i σ ≤ R.i (R.best hπ s) :=
  Classical.choose_spec (Finset.exists_max_image (fib π s) R.i (fib_nonempty R hπ s))

theorem map_best (s : Q) : π (R.best hπ s) = s := by
  have h := (R.best_spec hπ s).1
  simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h

theorem best_one : R.best hπ 1 = 1 := by
  rw [← R.i_eq_top]
  have h := (R.best_spec hπ 1).2 1 (by simp [fib])
  rw [R.i_one] at h
  exact top_le_iff.1 h

theorem best_ne_one {s : Q} (hs : s ≠ 1) : R.best hπ s ≠ 1 := fun h => hs (by
  rw [← R.map_best hπ s, h, map_one])

theorem map_best_mul (s : Q) (τ : π.ker) : π (R.best hπ s * τ) = s := by
  rw [map_mul, R.map_best hπ s, (MonoidHom.mem_ker).1 τ.2, mul_one]

theorem i_best_mul (s : Q) (τ : π.ker) :
    R.i (R.best hπ s * τ) = min (R.i τ) (R.i (R.best hπ s)) :=
  R.i_mul_eq_min ((R.best_spec hπ s).2 _ (by simp [fib, R.map_best_mul hπ s τ]))

/-- The fibre over `s` is `σ_s H`. -/
theorem sum_fib {M : Type*} [AddCommMonoid M] (s : Q) (g : G → M) :
    ∑ σ ∈ fib π s, g σ = ∑ τ : π.ker, g (R.best hπ s * τ) := by
  symm
  refine Finset.sum_bij (fun τ _ => R.best hπ s * τ) (fun τ _ => ?_) (fun a _ b _ h => ?_)
    (fun σ hσ => ?_) (fun τ _ => rfl)
  · simp [fib, R.map_best_mul hπ s τ]
  · exact Subtype.ext (mul_left_cancel h)
  · simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨⟨(R.best hπ s)⁻¹ * σ, ?_⟩, Finset.mem_univ _, mul_inv_cancel_left _ _⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, R.map_best hπ s, hσ, inv_mul_cancel]

theorem sum_total {M : Type*} [AddCommMonoid M] (g : G → M) :
    ∑ σ : G, g σ = ∑ s : Q, ∑ τ : π.ker, g (R.best hπ s * τ) := by
  rw [← Finset.sum_fiberwise Finset.univ π g]
  exact Finset.sum_congr rfl fun s _ => R.sum_fib hπ s g

theorem card_eq : (Nat.card G : ℚ) = Nat.card Q * Nat.card π.ker := by
  have h := R.sum_total hπ (fun _ => (1 : ℚ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h]

/-- Serre IV §3 Lemma 5: `i_Q(s) = φ_H(i_G(σ_s) - 1) + 1`. -/
theorem toNat_i_eq (hq : QuotFormula R S π) {s : Q} (hs : s ≠ 1) :
    ((S.i s).toNat : ℚ) = (R.restrict π.ker).phi (R.jdx (R.best hπ s)) + 1 := by
  obtain ⟨n, hn1, hn⟩ := R.exists_i_eq (R.best_ne_one hπ hs)
  have h1 := hq s hs
  rw [R.sum_fib hπ s] at h1
  have h2 : ∀ τ : π.ker, (R.i (R.best hπ s * τ)).toNat = (R.restrict π.ker).w τ (R.jdx (R.best hπ s)) := by
    intro τ
    rw [R.i_best_mul hπ s τ, w, restrict_i, jdx, hn, ENat.toNat_coe, Nat.sub_add_cancel hn1]
  simp_rw [h2] at h1
  have h3 := sum_w (R.restrict π.ker) (R.jdx (R.best hπ s))
  have hH : (0 : ℚ) < Nat.card π.ker := cardG_pos (G := π.ker)
  have h4 : ((S.i s).toNat : ℚ) * Nat.card π.ker = Nat.card π.ker * ((R.restrict π.ker).phi
      (R.jdx (R.best hπ s)) + 1) := by
    rw [← h3]; exact_mod_cast h1
  rw [mul_comm] at h4
  exact mul_left_cancel₀ hH.ne' h4

/-- Serre IV §3 Prop 15 (at the points needed): `φ_Q(n) = φ_G(m)` when `n = φ_H(m)`. -/
theorem phi_trans (hq : QuotFormula R S π) (m n : ℕ) (hmn : (n : ℚ) = (R.restrict π.ker).phi m) :
    S.phi n = R.phi m := by
  have key : ∀ s : Q, ((S.w s n : ℕ) : ℚ) * Nat.card π.ker = ∑ τ : π.ker, (R.w (R.best hπ s * τ) m : ℚ) := by
    intro s
    by_cases hs : s = 1
    · subst hs
      rw [S.w_one, R.best_one hπ]
      simp_rw [one_mul]
      have : ∀ τ : π.ker, R.w τ m = (R.restrict π.ker).w τ m := fun τ => rfl
      simp_rw [this]
      rw [sum_w (R.restrict π.ker) m, ← hmn]; push_cast; ring
    · obtain ⟨a, ha1, ha⟩ := S.exists_i_eq hs
      obtain ⟨b, hb1, hb⟩ := R.exists_i_eq (R.best_ne_one hπ hs)
      have hta := R.toNat_i_eq S hπ hq hs
      rw [ha, ENat.toNat_coe, jdx, hb, ENat.toNat_coe] at hta
      have hk : ∀ τ : π.ker, R.w (R.best hπ s * τ) m = (R.restrict π.ker).w τ (min (b - 1) m) := by
        intro τ
        rw [w, w, R.i_best_mul hπ s τ, hb, restrict_i, min_assoc]
        congr 2
        rw [← cast_min_enat]; congr 1; omega
      simp_rw [hk]
      rw [sum_w (R.restrict π.ker), S.w_of_eq ha, Nat.cast_min]
      have hmono : (R.restrict π.ker).phi (min (b - 1) m) = min ((R.restrict π.ker).phi (b - 1)) ((R.restrict π.ker).phi m) :=
        (R.restrict π.ker).phi_strictMono.monotone.map_min
      rw [hmono, hta]; push_cast; rw [hmn, min_add_add_right]; ring
  have hsum : (∑ s : Q, (S.w s n : ℚ)) * Nat.card π.ker = ∑ σ : G, (R.w σ m : ℚ) := by
    rw [Finset.sum_mul, R.sum_total hπ]
    exact Finset.sum_congr rfl fun s _ => key s
  have hH : (0 : ℚ) < Nat.card π.ker := cardG_pos (G := π.ker)
  have hQ : (0 : ℚ) < Nat.card Q := cardG_pos (G := Q)
  rw [sum_w S, sum_w R, R.card_eq hπ] at hsum
  have : (S.phi n + 1) * (Nat.card Q * Nat.card π.ker) = (R.phi m + 1) * (Nat.card Q * Nat.card π.ker) := by
    linarith
  have := mul_right_cancel₀ (mul_pos hQ hH).ne' this
  linarith

theorem mem_upper_iff_best (hq : QuotFormula R S π) {s : Q} (hs : s ≠ 1) (v : ℚ) :
    s ∈ S.upper v ↔ R.best hπ s ∈ R.upper v := by
  obtain ⟨a, ha1, ha⟩ := S.exists_i_eq hs
  have hta := R.toNat_i_eq S hπ hq hs
  rw [ha, ENat.toNat_coe] at hta
  have hj : ((S.jdx s : ℕ) : ℚ) = (R.restrict π.ker).phi (R.jdx (R.best hπ s)) := by
    rw [jdx, ha, ENat.toNat_coe, Nat.cast_sub ha1]; push_cast; linarith
  rw [S.mem_upper hs, R.mem_upper (R.best_ne_one hπ hs), R.phi_trans S hπ hq _ _ hj]

/-- **Herbrand's theorem**: upper numbering is compatible with quotients, `π(G^v) = Q^v`. -/
theorem map_upper (hq : QuotFormula R S π) (v : ℚ) : (R.upper v).map π = S.upper v := by
  ext s
  rw [Subgroup.mem_map]
  by_cases hs : s = 1
  · subst hs; exact ⟨fun _ => Subgroup.one_mem _, fun _ => ⟨1, Subgroup.one_mem _, map_one π⟩⟩
  rw [R.mem_upper_iff_best S hπ hq hs]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have hle := (R.best_spec hπ (π σ)).2 σ (by simp [fib])
    have h1 : σ ≠ 1 := fun h => hs (by rw [h, map_one])
    show ((R.upperIdx v + 1 : ℕ) : ℕ∞) ≤ R.i (R.best hπ (π σ))
    exact le_trans hσ hle
  · intro h; exact ⟨_, h, R.map_best hπ s⟩

end RamFn

end

end Swan
end RamanujanPetersson


