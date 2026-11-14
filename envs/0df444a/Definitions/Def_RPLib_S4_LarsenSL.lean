-- Prove2me | Definitions.Def_RPLib_S4_LarsenSL
-- name    : RPLib_S4_LarsenSL
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T03:21:49.045198+00:00
-- url     : https://prove2.me/theorems/8ee87104-d331-41ed-9e1e-946babe40935
-- title:
--   Larsen's alternative library: Larsen's alternative, case (1) (`SL`)
-- statement:
--   `endSL_scalar` (`M4 ≤ 2` ⇒ `End_G(sl_n) = K`) and `larsen_sl`: `G` Zariski closed, irreducible, `det G` finite,
--   `dim V ≥ 2`, `M4 G = 2` ⇒ `G` finite or `SL_n ≤ G` with finite index (Katz, Arizona notes p.27).
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_LarsenM4

/-!
# S4-Larsen: Larsen's alternative, case (1) (`SL`)

`endSL_scalar` (`M4 ≤ 2` ⇒ `End_G(sl_n) = K`) and `larsen_sl`: `G` Zariski closed, irreducible, `det G` finite,
`dim V ≥ 2`, `M4 G = 2` ⇒ `G` finite or `SL_n ≤ G` with finite index (Katz, Arizona notes p.27).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

noncomputable section

namespace RamanujanPetersson.Larsen

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB RamanujanPetersson.AlgGrpC

attribute [local instance] RamanujanPetersson.AlgGrpA.zarTop

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

section SLEnd

variable [CharZero K]

theorem li_SL (hn : 2 ≤ Fintype.card n) :
    LinearIndependent K ![(piK : Matrix n n K →ₗ[K] Matrix n n K), piSL] := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (lt_of_lt_of_le one_lt_two hn)
  have : Nonempty n := ⟨i⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc' : c 0 • (piK : Matrix n n K →ₗ[K] Matrix n n K) + c 1 • piSL = 0 := by
    simpa [Fin.sum_univ_two] using hc
  have h1 := LinearMap.congr_fun hc' 1
  have h2 := LinearMap.congr_fun hc' (Matrix.single i j (1 : K))
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, piK_one, piSL_one, smul_zero,
    add_zero, LinearMap.zero_apply] at h1
  have ht : (Matrix.single i j (1 : K)).trace = 0 := Matrix.trace_single_eq_of_ne i j 1 hij
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, piK_eq_zero ht, piSL_of_trace ht,
    smul_zero, zero_add, LinearMap.zero_apply] at h2
  have c0 : c 0 = 0 := by simpa using congrFun (congrFun h1 i) i
  have c1 : c 1 = 0 := by simpa using congrFun (congrFun h2 i) j
  intro k
  fin_cases k
  · exact c0
  · exact c1

/-- `M4 ≤ 2` forces every `Ad(G)`-equivariant endomorphism of `sl_n` to be scalar. -/
theorem endSL_scalar (hn : 2 ≤ Fintype.card n) {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hM : M4 G ≤ 2) :
    ∀ φ : Matrix n n K →ₗ[K] Matrix n n K, (∀ x ∈ (slMat : Submodule K (Matrix n n K)), φ x ∈ slMat) →
      (∀ g ∈ G, ∀ x ∈ (slMat : Submodule K (Matrix n n K)),
        φ ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
          (g : Matrix n n K) * φ x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) →
      ∃ c : K, ∀ x ∈ (slMat : Submodule K (Matrix n n K)), φ x = c • x := by
  intro φ _ hφ
  obtain ⟨i, _, _⟩ := Fintype.exists_pair_of_one_lt_card (lt_of_lt_of_le one_lt_two hn)
  have : Nonempty n := ⟨i⟩
  have hΦ : φ ∘ₗ piSL ∈ adComm G := by
    intro g hg x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, piSL_mem_adComm G g hg x]
    exact hφ g hg _ (mem_slMat.2 (trace_piSL x))
  obtain ⟨c, hc⟩ := exists_coeffs hM ![(piK : Matrix n n K →ₗ[K] Matrix n n K), piSL]
    (fun k => by fin_cases k; exacts [piK_mem_adComm G, piSL_mem_adComm G]) (li_SL hn) hΦ
  refine ⟨c 1, fun x hx => ?_⟩
  have htr : x.trace = 0 := mem_slMat.1 hx
  have h := LinearMap.congr_fun hc x
  simp only [Fin.sum_univ_two, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, piK_eq_zero htr,
    piSL_of_trace htr, smul_zero, zero_add] at h
  exact h.symm

end SLEnd

section SLMain

variable [IsAlgClosed K] [CharZero K]

theorem isClosed_slSet : IsClosed (slSet : Set (Matrix.GeneralLinearGroup n K)) :=
  (IsRegFun.det (n := n) (K := K)).isClosed_eq (IsRegFun.const 1)

/-- `det|_G`, with kernel `G ∩ SL`. -/
def detG (G : Subgroup (Matrix.GeneralLinearGroup n K)) : G →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp G.subtype

theorem ker_detG (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    (detG G).ker = detOne.subgroupOf G := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_detOne, Units.ext_iff]
  rfl

theorem finite_range_detG {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hdet : ((fun g : Matrix.GeneralLinearGroup n K => (g : Matrix n n K).det) '' (G : Set _)).Finite) :
    Finite (detG G).range := by
  have hsub : ((detG G).range : Set Kˣ) ⊆
      (Units.val ⁻¹' ((fun g : Matrix.GeneralLinearGroup n K => (g : Matrix n n K).det) '' (G : Set _))) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨(g : Matrix.GeneralLinearGroup n K), g.2, rfl⟩
  exact ((hdet.preimage Units.val_injective.injOn).subset hsub).to_subtype

theorem finiteIndex_detOne {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hdet : ((fun g : Matrix.GeneralLinearGroup n K => (g : Matrix n n K).det) '' (G : Set _)).Finite) :
    (detOne.subgroupOf G).FiniteIndex := by
  have := finite_range_detG hdet
  rw [← ker_detG]
  infer_instance

/-- **Larsen's alternative (1)** (`M4 ≤ 2` form). -/
theorem larsen_sl_of_le (hn : 2 ≤ Fintype.card n) {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hGc : IsClosed (G : Set (Matrix.GeneralLinearGroup n K)))
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hdet : ((fun g : Matrix.GeneralLinearGroup n K => (g : Matrix n n K).det) '' (G : Set _)).Finite)
    (hM : M4 G ≤ 2) :
    Finite G ∨ (detOne ≤ G ∧ (detOne.subgroupOf G).FiniteIndex) := by
  have hfi := finiteIndex_detOne hdet
  rcases lieS_inf_sl_eq_bot_or_eq hG (endSL_scalar hn hM) with h | h
  · left
    have hfin : Finite (G ⊓ detOne : Subgroup (Matrix.GeneralLinearGroup n K)) :=
      finite_of_lieS_eq_bot _ (by rw [coe_inf_detOne]; exact h)
    have hfin' : Finite (detOne.subgroupOf G) :=
      Finite.of_injective (fun k : detOne.subgroupOf G =>
        (⟨((k : G) : Matrix.GeneralLinearGroup n K), (k : G).2, Subgroup.mem_subgroupOf.1 k.2⟩ :
          (G ⊓ detOne : Subgroup (Matrix.GeneralLinearGroup n K))))
        (fun a b hab => by
          have h' : ((a : G) : Matrix.GeneralLinearGroup n K) = ((b : G) : Matrix.GeneralLinearGroup n K) :=
            congrArg (fun x : (G ⊓ detOne : Subgroup (Matrix.GeneralLinearGroup n K)) =>
              (x : Matrix.GeneralLinearGroup n K)) hab
          exact Subtype.ext (Subtype.ext h'))
    exact (Subgroup.finite_iff_finite_and_finiteIndex (detOne.subgroupOf G)).2 ⟨hfin', hfi⟩
  · right
    refine ⟨fun g hg => ?_, hfi⟩
    have hH : IsClosed ((G ⊓ detOne : Subgroup (Matrix.GeneralLinearGroup n K)) :
        Set (Matrix.GeneralLinearGroup n K)) := by
      rw [coe_inf_detOne]
      exact hGc.inter isClosed_slSet
    have hE : ∀ i j : n, i ≠ j → Matrix.single i j (1 : K) ∈
        lieS ((G ⊓ detOne : Subgroup (Matrix.GeneralLinearGroup n K)) : Set (Matrix.GeneralLinearGroup n K)) := by
      intro i j hij
      rw [coe_inf_detOne, h]
      exact mem_slMat.2 (Matrix.trace_single_eq_of_ne i j 1 hij)
    have hm := toGL_mem_of_single_mem_lieS hH hE ⟨(g : Matrix n n K), mem_detOne.1 hg⟩
    have e : Matrix.SpecialLinearGroup.toGL
        (⟨(g : Matrix n n K), mem_detOne.1 hg⟩ : Matrix.SpecialLinearGroup n K) = g := Units.ext rfl
    rw [e] at hm
    exact (Subgroup.mem_inf.1 hm).1

/-- **Larsen's alternative (1)** (Katz p.27): `M4 = 2` ⇒ `G` finite or `SL_n ≤ G` with finite index. -/
theorem larsen_sl (hn : 2 ≤ Fintype.card n) {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hGc : IsClosed (G : Set (Matrix.GeneralLinearGroup n K)))
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hdet : ((fun g : Matrix.GeneralLinearGroup n K => (g : Matrix n n K).det) '' (G : Set _)).Finite)
    (hM : M4 G = 2) :
    Finite G ∨ (detOne ≤ G ∧ (detOne.subgroupOf G).FiniteIndex) :=
  larsen_sl_of_le hn hGc hG hdet hM.le

end SLMain

end RamanujanPetersson.Larsen


