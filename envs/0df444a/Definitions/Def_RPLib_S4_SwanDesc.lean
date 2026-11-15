-- Prove2me | Definitions.Def_RPLib_S4_SwanDesc
-- name    : RPLib_S4_SwanDesc
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:19:31.788619+00:00
-- url     : https://prove2.me/theorems/23717f47-3c2a-4631-80e0-98b888518d73
-- title:
--   Descent of a ramification function to a quotient group
-- statement:
--   Let $H \trianglelefteq G$ be finite groups and $m : G \to \mathbb{N}$ a function that is constant on cosets of $H$, invariant under inversion and conjugation, at least $1$, and satisfies $m(\sigma\tau) \ge \min(m(\sigma), m(\tau))$ off the identity coset. The file shows that $$i(\bar\sigma) = \begin{cases} \infty & \bar\sigma = 1 \\ m(\sigma) & \bar\sigma \ne 1 \end{cases}$$ is a well-defined ramification function on $G/H$ and computes it on representatives. This is how the ramification function of a quotient is produced from the quotient formula.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV, Sections 1 and 3

import Mathlib
import Definitions.Def_RPLib_S4_SwanHerbQ

/-!
# S4-Swan (K2), part 8: a ramification function descends to a quotient

`H` a normal subgroup of `G`, `m : G → ℕ` right-`H`-invariant with `1 ≤ m σ` off `H`, the ultrametric
inequality off `H`, and invariance under inversion and conjugation. Then `q ↦ (⊤ if q = 1, m σ if q = σH)` is
a `RamFn (G ⧸ H)` (`RamFn.desc`). Used with `m σ = v(σ ϖ_H - ϖ_H) / |H|` (`LocData.QData.ram`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

namespace RamFn

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] (m : G → ℕ)
  (hm : ∀ σ, ∀ h ∈ H, m (σ * h) = m σ)

/-- `m` on cosets. -/
def descFn (q : G ⧸ H) : ℕ :=
  Quotient.liftOn' q m fun a b hab => by
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.1 hab
    rw [show b = a * (a⁻¹ * b) by group, hm a _ hab']

omit [H.Normal] in
theorem descFn_mk (σ : G) : descFn H m hm (σ : G ⧸ H) = m σ := rfl

open Classical in
/-- `⊤` at `1`, `m` elsewhere. -/
def descI (q : G ⧸ H) : ℕ∞ := if q = 1 then ⊤ else (descFn H m hm q : ℕ∞)

theorem descI_one : descI H m hm 1 = ⊤ := if_pos rfl

theorem descI_mk {σ : G} (hσ : σ ∉ H) : descI H m hm (σ : G ⧸ H) = m σ := by
  rw [descI, if_neg (by rwa [QuotientGroup.eq_one_iff]), descFn_mk]

theorem descI_of_mem {σ : G} (hσ : σ ∈ H) : descI H m hm (σ : G ⧸ H) = ⊤ := by
  rw [(QuotientGroup.eq_one_iff σ).2 hσ, descI_one]

theorem conj_mem_iff (σ τ : G) : τ * σ * τ⁻¹ ∈ H ↔ σ ∈ H := by
  refine ⟨fun h => ?_, fun h => ‹H.Normal›.conj_mem σ h τ⟩
  have h2 := ‹H.Normal›.conj_mem _ h τ⁻¹
  rwa [show τ⁻¹ * (τ * σ * τ⁻¹) * τ⁻¹⁻¹ = σ by group] at h2

variable (h1 : ∀ σ, σ ∉ H → 1 ≤ m σ)
  (hmul : ∀ σ τ, σ ∉ H → τ ∉ H → σ * τ ∉ H → min (m σ) (m τ) ≤ m (σ * τ))
  (hinv : ∀ σ, m σ⁻¹ = m σ) (hconj : ∀ σ τ, m (τ * σ * τ⁻¹) = m σ)

/-- The descended ramification function on `G ⧸ H`. -/
def desc : RamFn (G ⧸ H) where
  i := descI H m hm
  i_eq_top q := by
    refine ⟨fun h => ?_, fun h => by rw [h]; exact descI_one H m hm⟩
    by_contra hq
    rw [descI, if_neg hq] at h
    exact ENat.natCast_ne_top _ h
  one_le q := by
    refine QuotientGroup.induction_on q fun σ => ?_
    by_cases hσ : σ ∈ H
    · rw [descI_of_mem H m hm hσ]; exact le_top
    · rw [descI_mk H m hm hσ]; exact Nat.one_le_cast.2 (h1 σ hσ)
  le_mul q r := by
    refine QuotientGroup.induction_on q fun σ => ?_
    refine QuotientGroup.induction_on r fun τ => ?_
    by_cases hσ : σ ∈ H
    · rw [(QuotientGroup.eq_one_iff σ).2 hσ, one_mul]; exact min_le_right _ _
    by_cases hτ : τ ∈ H
    · rw [(QuotientGroup.eq_one_iff τ).2 hτ, mul_one]; exact min_le_left _ _
    rw [← QuotientGroup.mk_mul]
    by_cases hστ : σ * τ ∈ H
    · rw [descI_of_mem H m hm hστ]; exact le_top
    rw [descI_mk H m hm hσ, descI_mk H m hm hτ, descI_mk H m hm hστ, ← cast_min_enat]
    exact Nat.cast_le.2 (hmul σ τ hσ hτ hστ)
  i_inv q := by
    refine QuotientGroup.induction_on q fun σ => ?_
    rw [← QuotientGroup.mk_inv]
    by_cases hσ : σ ∈ H
    · rw [descI_of_mem H m hm hσ, descI_of_mem H m hm (H.inv_mem hσ)]
    · rw [descI_mk H m hm hσ, descI_mk H m hm (fun h => hσ (H.inv_mem_iff.1 h)), hinv]
  i_conj q r := by
    refine QuotientGroup.induction_on q fun σ => ?_
    refine QuotientGroup.induction_on r fun τ => ?_
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    by_cases hσ : σ ∈ H
    · rw [descI_of_mem H m hm hσ, descI_of_mem H m hm ((conj_mem_iff H σ τ).2 hσ)]
    · rw [descI_mk H m hm hσ, descI_mk H m hm (fun h => hσ ((conj_mem_iff H σ τ).1 h)), hconj]

theorem desc_i_mk {σ : G} (hσ : σ ∉ H) :
    (desc H m hm h1 hmul hinv hconj).i (σ : G ⧸ H) = m σ :=
  descI_mk H m hm hσ

end RamFn

end

end Swan
end RamanujanPetersson


