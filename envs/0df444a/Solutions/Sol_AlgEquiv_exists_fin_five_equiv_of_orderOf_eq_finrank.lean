-- Prove2me | solution 1 for AlgEquiv.exists_fin_five_equiv_of_orderOf_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:40.544148+00:00
-- url     : https://prove2.me/submissions/5a01b949-9a2c-45d8-8aea-3ec276a48b12

import Mathlib

set_option autoImplicit false

namespace AlgEquiv

/-- An order-five automorphism of a degree-five field extension enumerates
the whole automorphism group, and the extension is Galois. -/
theorem _root_.solution
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E) (hσ : orderOf σ = 5) (hdegree : Module.finrank F E = 5) :
    IsGalois F E ∧ ∃ e : Fin 5 ≃ (E ≃ₐ[F] E), ∀ i, e i = σ ^ i.val := by
  classical
  let f : Fin 5 → (E ≃ₐ[F] E) := fun i => σ ^ i.val
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (by change i.val < orderOf σ; rw [hσ]; exact i.isLt)
      (by change j.val < orderOf σ; rw [hσ]; exact j.isLt) hij
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 5 := by
    simpa [hdegree] using (AlgEquiv.card_le : Fintype.card (E ≃ₐ[F] E) ≤ Module.finrank F E)
  have hge : 5 ≤ Fintype.card (E ≃ₐ[F] E) := by
    simpa using Fintype.card_le_of_injective f hinj
  have hcard : Fintype.card (E ≃ₐ[F] E) = 5 := Nat.le_antisymm hle hge
  have hgalois : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by
    rw [Nat.card_eq_fintype_card, hcard, hdegree])
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp [hcard]⟩
  exact ⟨hgalois, Equiv.ofBijective f hbij, fun _ => rfl⟩

end AlgEquiv
