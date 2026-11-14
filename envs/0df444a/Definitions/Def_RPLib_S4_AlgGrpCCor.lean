-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpCCor
-- name    : RPLib_S4_AlgGrpCCor
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T03:08:56.422202+00:00
-- url     : https://prove2.me/theorems/56816991-a753-4d3a-8760-22018ff8b44f
-- title:
--   Larsen's alternative library: the `G`-equivariant trace projection onto `Lie H`
-- statement:
--   Under the hypotheses of `trace_form_nondegenerate` (K algebraically closed of char 0, `G`
--   irreducible, `L = Lie H` stable under `Ad(G)`):
--
--   * `exists_trace_proj`: a linear `p` with `p x ∈ L` and `trace (p x * Y) = trace (x * Y)` for `Y ∈ L`;
--     it fixes `L` and commutes with `Ad(G)` (`trace_proj_conj`).
--   * `lieS_eq_bot_or_eq` (**the step of Larsen's alternative that uses complete reducibility**):
--     if `L ≤ E` and every `Ad(G)`-equivariant endomorphism preserving `E` is scalar on `E`,
--     then `L = ⊥` or `L = E`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpCMain

/-!
# S4-AlgGrpC, file Cor: the `G`-equivariant trace projection onto `Lie H`

Under the hypotheses of `trace_form_nondegenerate` (K algebraically closed of char 0, `G`
irreducible, `L = Lie H` stable under `Ad(G)`):

* `exists_trace_proj`: a linear `p` with `p x ∈ L` and `trace (p x * Y) = trace (x * Y)` for `Y ∈ L`;
  it fixes `L` and commutes with `Ad(G)` (`trace_proj_conj`).
* `lieS_eq_bot_or_eq` (**the step of Larsen's alternative that uses complete reducibility**):
  if `L ≤ E` and every `Ad(G)`-equivariant endomorphism preserving `E` is scalar on `E`,
  then `L = ⊥` or `L = E`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial
open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpC

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The trace pairing `X ↦ (Y ↦ trace (X * Y))` against a subspace `L`. -/
def trPair (L : Submodule K (Matrix n n K)) : Matrix n n K →ₗ[K] Module.Dual K L :=
  ((LinearMap.mul K (Matrix n n K)).compr₂ (Matrix.traceLinearMap n K K)).compl₂ L.subtype

theorem trPair_apply (L : Submodule K (Matrix n n K)) (X : Matrix n n K) (Y : L) :
    trPair L X Y = (X * (Y : Matrix n n K)).trace :=
  rfl

/-- `trace (g A g⁻¹ Y) = trace (A (g⁻¹ Y g))`. -/
theorem trace_conj_mul (g : Matrix.GeneralLinearGroup n K) (A Y : Matrix n n K) :
    ((g : Matrix n n K) * A * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * Y).trace =
      (A * (((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * Y * (g : Matrix n n K))).trace := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

variable [IsAlgClosed K] [CharZero K] {G H : Subgroup (Matrix.GeneralLinearGroup n K)}

/-- Elements of `Lie H` are determined by their trace pairing with `Lie H`. -/
theorem eq_of_trace_eq
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hL : ∀ g ∈ G, ∀ X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)),
      (g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ∈
        lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    {X X' : Matrix n n K} (hX : X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    (hX' : X' ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    (h : ∀ Y ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)), (X * Y).trace = (X' * Y).trace) :
    X = X' :=
  sub_eq_zero.1 (trace_form_nondegenerate hG hL (sub_mem hX hX') fun Y hY => by
    rw [Matrix.sub_mul, Matrix.trace_sub, h Y hY, sub_self])

/-- The trace projection onto `Lie H`. -/
theorem exists_trace_proj
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hL : ∀ g ∈ G, ∀ X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)),
      (g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ∈
        lieS (H : Set (Matrix.GeneralLinearGroup n K))) :
    ∃ p : Matrix n n K →ₗ[K] Matrix n n K,
      (∀ x, p x ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K))) ∧
      ∀ x, ∀ Y ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)), (p x * Y).trace = (x * Y).trace := by
  set L := lieS (H : Set (Matrix.GeneralLinearGroup n K))
  let τ : L →ₗ[K] Module.Dual K L := (trPair L).comp L.subtype
  have hinj : Function.Injective τ := fun a b hab =>
    Subtype.ext (eq_of_trace_eq hG hL a.2 b.2 fun Y hY => LinearMap.congr_fun hab ⟨Y, hY⟩)
  let e := LinearMap.linearEquivOfInjective τ hinj Subspace.dual_finrank_eq.symm
  refine ⟨L.subtype ∘ₗ e.symm.toLinearMap ∘ₗ trPair L, fun x => (e.symm (trPair L x)).2,
    fun x Y hY => ?_⟩
  have := LinearMap.congr_fun (e.apply_symm_apply (trPair L x)) ⟨Y, hY⟩
  exact this

/-- The trace projection fixes `Lie H` and commutes with `Ad(G)`. -/
theorem trace_proj_conj
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hL : ∀ g ∈ G, ∀ X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)),
      (g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ∈
        lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    {p : Matrix n n K →ₗ[K] Matrix n n K}
    (hpm : ∀ x, p x ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    (hpt : ∀ x, ∀ Y ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)), (p x * Y).trace = (x * Y).trace)
    {g : Matrix.GeneralLinearGroup n K} (hg : g ∈ G) (x : Matrix n n K) :
    p ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
      (g : Matrix n n K) * p x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) := by
  refine eq_of_trace_eq hG hL (hpm _) (hL g hg _ (hpm x)) fun Y hY => ?_
  have hY' : ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * Y * (g : Matrix n n K) ∈
      lieS (H : Set (Matrix.GeneralLinearGroup n K)) := by
    have := hL g⁻¹ (inv_mem hg) Y hY
    rwa [inv_inv] at this
  rw [hpt _ Y hY, trace_conj_mul, trace_conj_mul, hpt x _ hY']

/-- **Larsen's alternative, the complete-reducibility step.** If `Lie H ≤ E` and every
`Ad(G)`-equivariant endomorphism preserving `E` is a scalar on `E`, then `Lie H` is `0` or `E`. -/
theorem lieS_eq_bot_or_eq
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hL : ∀ g ∈ G, ∀ X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)),
      (g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ∈
        lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    {E : Submodule K (Matrix n n K)} (hLE : lieS (H : Set (Matrix.GeneralLinearGroup n K)) ≤ E)
    (hEnd : ∀ φ : Matrix n n K →ₗ[K] Matrix n n K, (∀ x ∈ E, φ x ∈ E) →
      (∀ g ∈ G, ∀ x ∈ E, φ ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
        (g : Matrix n n K) * φ x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) →
      ∃ c : K, ∀ x ∈ E, φ x = c • x) :
    lieS (H : Set (Matrix.GeneralLinearGroup n K)) = ⊥ ∨ lieS (H : Set (Matrix.GeneralLinearGroup n K)) = E := by
  obtain ⟨p, hpm, hpt⟩ := exists_trace_proj hG hL
  have hpL : ∀ x ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)), p x = x := fun x hx =>
    eq_of_trace_eq hG hL (hpm x) hx (hpt x)
  obtain ⟨c, hc⟩ := hEnd p (fun x _ => hLE (hpm x)) fun g hg x _ => trace_proj_conj hG hL hpm hpt hg x
  by_cases hL0 : lieS (H : Set (Matrix.GeneralLinearGroup n K)) = ⊥
  · exact Or.inl hL0
  right
  obtain ⟨X, hXL, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
  have hc1 : c = 1 := by
    have h0 : (c - 1) • X = 0 := by rw [sub_smul, one_smul, ← hc X (hLE hXL), hpL X hXL, sub_self]
    rcases smul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hX0
  refine le_antisymm hLE fun x hx => ?_
  have := hc x hx
  rw [hc1, one_smul] at this
  rw [← this]
  exact hpm x

end RamanujanPetersson.AlgGrpC


