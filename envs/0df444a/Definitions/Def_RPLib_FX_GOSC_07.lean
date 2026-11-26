-- Prove2me | Definitions.Def_RPLib_FX_GOSC_07
-- name    : RPLib_FX_GOSC_07
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:21:00.163318+00:00
-- url     : https://prove2.me/theorems/34cb98c9-637e-4896-8c1d-2f71824e5b5f
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 07 of 14
-- statement:
--   File 07 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_PtCount`: S4-Lefschetz, L5b: counting Frobenius-fixed points of an intermediate cover
--   * `S4.Def_RP_GOS_B_Seq`: S4-GOS-B, part Seq: the twisted Frobenius trace sequence of the perfect complex
--   * `S4.Def_RP_GOS_B_Rank`: S4-GOS-B, part Rank: the ranks of the perfect complex do not change under reduction `Λ → Λ'`
--   * `S4.Def_RP_GOS_B_Bij`: S4-GOS-B, part Bij: the Frobenius of the perfect complex is bijective
--   * `S4.Def_RP_GOS_B_Lift`: S4-GOS-B, part Lift: an `l`-independent integer lift of the character of the perfect complex
--   * `S4.Def_RP_GOS_B_Ass`: S4-GOS-B, part Ass: the character of the perfect complex is `Φ`, given the subgroup sums (O6) and `hfin`
--   * `S4.Def_RP_GOS_C_B1c`: S4-GOS-C, part B1c: characters of projective modules vanish on `l`-singular elements
--   * `S4.Def_RP_GOS_C_C0`: S4-GOS-C, part C0: traces agree on two lifts of the same module
--   * `S4.Def_RP_GOS_C_LIFTa`: S4-GOS-C, part LIFTa: permutation modules and reduction maps for lifting projective modules
--   * `S4.Def_RP_GOS_C_LIFTb`: S4-GOS-C, part LIFTb: lifting the idempotent of a projective module
--   * `S4.Def_RP_GOS_C_LIFTc`: S4-GOS-C, part LIFTc: projective modules lift
--   * `S4.Def_RP_GOS_C_BETA`: S4-GOS-C, part BETA: the Brauer trace function `β`
--   * `S4.Def_RP_GOS_C_HSR`: S4-GOS-C, part HSR: the sum of the character of a projective module
--   * `S4.Def_RP_GOS_C_HSR2`: S4-GOS-C, part HSR2: coinvariants of a lift
--   * `S4.Def_RP_GOS_C_B2`: S4-GOS-C, part B2: Brauer's formula for `dim (P' ⊗ M)_G` and subgroup sums of `β`
--   * `S4.Def_RP_GOS_C_PCB`: S4-GOS-C, part PCB: Brauer's formula for the perfect complex `PC`
--   * `S4.Def_RP_GOS_B_PlKc`: S4-GOS-B, part PlKc: a function field over `𝔽_q` and over its full constant field `k_E` (O6d glue)
--   * `S4.Def_RP_GOS_B_WeilE`: S4-GOS-B, part WeilE: the affine point counts of any function field satisfy an integer recurrence (O6d)
--   * `S4.Def_RP_GOS_C_GOSF2`: S4-GOS-C, part GOSF2: Grothendieck-Ogg-Shafarevich on `𝔸¹`
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_F2_041
import Definitions.Def_RPLib_F2_071
import Definitions.Def_RPLib_FX_GOSC_06

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 07 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_PtCount`: S4-Lefschetz, L5b: counting Frobenius-fixed points of an intermediate cover
* `S4.Def_RP_GOS_B_Seq`: S4-GOS-B, part Seq: the twisted Frobenius trace sequence of the perfect complex
* `S4.Def_RP_GOS_B_Rank`: S4-GOS-B, part Rank: the ranks of the perfect complex do not change under reduction `Λ → Λ'`
* `S4.Def_RP_GOS_B_Bij`: S4-GOS-B, part Bij: the Frobenius of the perfect complex is bijective
* `S4.Def_RP_GOS_B_Lift`: S4-GOS-B, part Lift: an `l`-independent integer lift of the character of the perfect complex
* `S4.Def_RP_GOS_B_Ass`: S4-GOS-B, part Ass: the character of the perfect complex is `Φ`, given the subgroup sums (O6) and `hfin`
* `S4.Def_RP_GOS_C_B1c`: S4-GOS-C, part B1c: characters of projective modules vanish on `l`-singular elements
* `S4.Def_RP_GOS_C_C0`: S4-GOS-C, part C0: traces agree on two lifts of the same module
* `S4.Def_RP_GOS_C_LIFTa`: S4-GOS-C, part LIFTa: permutation modules and reduction maps for lifting projective modules
* `S4.Def_RP_GOS_C_LIFTb`: S4-GOS-C, part LIFTb: lifting the idempotent of a projective module
* `S4.Def_RP_GOS_C_LIFTc`: S4-GOS-C, part LIFTc: projective modules lift
* `S4.Def_RP_GOS_C_BETA`: S4-GOS-C, part BETA: the Brauer trace function `β`
* `S4.Def_RP_GOS_C_HSR`: S4-GOS-C, part HSR: the sum of the character of a projective module
* `S4.Def_RP_GOS_C_HSR2`: S4-GOS-C, part HSR2: coinvariants of a lift
* `S4.Def_RP_GOS_C_B2`: S4-GOS-C, part B2: Brauer's formula for `dim (P' ⊗ M)_G` and subgroup sums of `β`
* `S4.Def_RP_GOS_C_PCB`: S4-GOS-C, part PCB: Brauer's formula for the perfect complex `PC`
* `S4.Def_RP_GOS_B_PlKc`: S4-GOS-B, part PlKc: a function field over `𝔽_q` and over its full constant field `k_E` (O6d glue)
* `S4.Def_RP_GOS_B_WeilE`: S4-GOS-B, part WeilE: the affine point counts of any function field satisfy an integer recurrence (O6d)
* `S4.Def_RP_GOS_C_GOSF2`: S4-GOS-C, part GOSF2: Grothendieck-Ogg-Shafarevich on `𝔸¹`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_PtCount =====
section

/-!
# S4-Lefschetz, L5b: counting Frobenius-fixed points of an intermediate cover

`B / A` with a finite group `G` (`A = B^G`, unramified), a subgroup `H`, an intermediate ring `C` with `C = B^H`,
an algebraically closed field `Ω` with an endomorphism `Fr`, a point `u : A → Ω` and a lift `w0 : B → Ω` of `u` with
`Fr ∘ w0 = w0 ∘ F` (`F ∈ G`). Then (`card_fixed_ptRes`)

  `#{x ∈ G | x⁻¹ F x ∈ H} = #{v : C → Ω over u | Fr ∘ v = v} * |H|`,

via the restrictions `ptRes C w0 x : c ↦ w0 (x • c)` (fibers = left cosets `x H`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

section PtCountGen

end PtCountGen

section PtCount

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {G : Type} [Group G] [MulSemiringAction G B]
  {Ω : Type} [Field Ω]

variable [Finite G] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  (H : Subgroup G) {C : Type} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [SMulCommClass H C B] [Algebra.IsInvariant C B H]

/-- **L5b: the count.** For a lift `w0` of `u` with `Fr ∘ w0 = w0 ∘ F`:
`#{x ∈ G | x⁻¹ F x ∈ H} = #{v : C → Ω over u | Fr ∘ v = v} * |H|`. -/
theorem card_fixed_ptRes (hun : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) [IsAlgClosed Ω] [FaithfulSMul C B]
    (Fr : Ω →+* Ω) (u : A →+* Ω)
    (hfin : ∀ w : B →+* Ω, w.comp (algebraMap A B) = u → Finite (B ⧸ RingHom.ker w))
    (w0 : B →+* Ω) (hw0 : w0.comp (algebraMap A B) = u) (F : G) (hF : ∀ b, Fr (w0 b) = w0 (F • b)) :
    Nat.card {x : G // x⁻¹ * F * x ∈ H} =
      Nat.card {v : C →+* Ω // v.comp (algebraMap A C) = u ∧ Fr.comp v = v} * Nat.card H := by
  refine pt_card_eq_mul H (fun x => x⁻¹ * F * x ∈ H)
    (fun v : C →+* Ω => v.comp (algebraMap A C) = u ∧ Fr.comp v = v) (ptRes C w0) ?_ ?_ ?_ ?_
  · intro x0 x _
    exact ptRes_eq_iff H hun u hfin w0 hw0 x x0
  · intro x h hx hh
    have h1 : (x * h)⁻¹ * F * (x * h) = h⁻¹ * (x⁻¹ * F * x) * h := by group
    show (x * h)⁻¹ * F * (x * h) ∈ H
    rw [h1]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh
  · rintro v ⟨hvu, hvF⟩
    haveI : Algebra.IsIntegral C B := Algebra.IsInvariant.isIntegral C B H
    obtain ⟨w, hw⟩ := exists_hom_extend (B := B) v
    have hwu : w.comp (algebraMap A B) = u := by
      rw [IsScalarTower.algebraMap_eq A C B, ← RingHom.comp_assoc, hw, hvu]
    haveI := hfin w hwu
    obtain ⟨x, hx⟩ := hom_smul_trans (A := A) (G := G) w0 w (hw0.trans hwu.symm)
    have hFu : (Fr.comp w).comp (algebraMap A B) = u := by
      rw [RingHom.comp_assoc, hwu, ← hvu, ← RingHom.comp_assoc, hvF]
    haveI := hfin (Fr.comp w) hFu
    have hwC : w.comp (algebraMap C B) = (Fr.comp w).comp (algebraMap C B) := by
      rw [RingHom.comp_assoc, hw, hvF]
    obtain ⟨h, hh⟩ := hom_smul_trans (A := C) (G := H) w (Fr.comp w) hwC
    have hFx : F * x = x * h := pt_smul_eq hun w0 fun b => by
      rw [mul_smul, mul_smul, ← hF, ← hx, ← hx]
      exact hh b
    refine ⟨x, ?_, ?_⟩
    · show x⁻¹ * F * x ∈ H
      have : x⁻¹ * F * x = h := by rw [mul_assoc, hFx, inv_mul_cancel_left]
      rw [this]
      exact h.2
    · refine RingHom.ext fun c => ?_
      show w0 (x • algebraMap C B c) = v c
      rw [← hx, ← RingHom.comp_apply, hw]
  · intro x hx
    refine ⟨?_, ?_⟩
    · refine RingHom.ext fun a => ?_
      show w0 (x • algebraMap C B (algebraMap A C a)) = u a
      rw [← IsScalarTower.algebraMap_apply, smul_algebraMap]
      exact RingHom.congr_fun hw0 a
    · refine RingHom.ext fun c => ?_
      show Fr (w0 (x • algebraMap C B c)) = w0 (x • algebraMap C B c)
      have hfix : (x⁻¹ * F * x) • algebraMap C B c = algebraMap C B c :=
        smul_algebraMap (⟨x⁻¹ * F * x, hx⟩ : H) c
      have hFx : F * x = x * (x⁻¹ * F * x) := by group
      rw [hF, ← mul_smul, hFx, mul_smul, hfix]

end PtCount

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_GOS_B_Seq =====
section

/-!
# S4-GOS-B, part Seq: the twisted Frobenius trace sequence of the perfect complex

`pcSeq Λ π Γ I ψ t h hI g m = Σ_{i<3} (-1)^i Tr(ρPC_i(g⁻¹) ∘ F_i^m)` (`F = frobPC`).

* `prodMap_pow'`; `pcSeq_eq_trace`: `pcSeq` is one trace on `PC₀ × (PC₁ × PC₂)`;
* **`pcSeq_rec`**: a monic linear recurrence of order `finrank (PC₀ × (PC₁ × PC₂))` (Cayley–Hamilton);
* **`pcSeq_periodic`**: `pcSeq` is periodic in `m` when `Λ` is finite and every `F_i` is injective.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open PerfectCx CurveCoh

section PC

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

variable (Λ) in
/-- The twisted alternating Frobenius trace sequence of `PC`. -/
def pcSeq (g : Gf) (m : ℕ) : Λ :=
  ∑ i ∈ Finset.range 3, (-1 : Λ) ^ i *
    LinearMap.trace Λ (PC Λ π Γ I i) (ρPC Λ π Γ I i g⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI i ^ m)

theorem pcSeq_eq_trace [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (g : Gf) (m : ℕ) :
    pcSeq Λ π Γ I ψ t h hI g m = LinearMap.trace Λ (PC Λ π Γ I 0 × (PC Λ π Γ I 1 × PC Λ π Γ I 2))
      ((ρPC Λ π Γ I 0 g⁻¹).prodMap ((-ρPC Λ π Γ I 1 g⁻¹).prodMap (ρPC Λ π Γ I 2 g⁻¹)) *
        ((frobPC Λ π Γ I ψ t h hI 0).prodMap
          ((frobPC Λ π Γ I ψ t h hI 1).prodMap (frobPC Λ π Γ I ψ t h hI 2))) ^ m) := by
  rw [prodMap_pow', prodMap_pow', LinearMap.prodMap_mul, LinearMap.prodMap_mul, LinearMap.trace_prodMap',
    LinearMap.trace_prodMap', pcSeq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, one_mul, neg_mul,
    map_neg, Module.End.mul_eq_comp, even_two, Even.neg_pow, one_pow]
  ring

theorem pcSeq_rec [Nontrivial Λ] [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (g : Gf) :
    ∃ c : Fin (Module.finrank Λ (PC Λ π Γ I 0 × (PC Λ π Γ I 1 × PC Λ π Γ I 2))) → Λ, ∀ k,
      pcSeq Λ π Γ I ψ t h hI g (k + Module.finrank Λ (PC Λ π Γ I 0 × (PC Λ π Γ I 1 × PC Λ π Γ I 2))) =
        ∑ j, c j * pcSeq Λ π Γ I ψ t h hI g (k + j) := by
  obtain ⟨c, hc⟩ := trace_rec_of_charpoly (R := Λ)
    ((ρPC Λ π Γ I 0 g⁻¹).prodMap ((-ρPC Λ π Γ I 1 g⁻¹).prodMap (ρPC Λ π Γ I 2 g⁻¹)))
    ((frobPC Λ π Γ I ψ t h hI 0).prodMap ((frobPC Λ π Γ I ψ t h hI 1).prodMap (frobPC Λ π Γ I ψ t h hI 2)))
  exact ⟨c, fun k => by simp only [pcSeq_eq_trace]; exact hc k⟩

theorem pcSeq_periodic [Finite Λ] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (hF : ∀ i, Function.Injective (frobPC Λ π Γ I ψ t h hI i)) :
    ∃ T, 0 < T ∧ ∀ g m, pcSeq Λ π Γ I ψ t h hI g (m + T) = pcSeq Λ π Γ I ψ t h hI g m := by
  have hex : ∀ i, ∃ T, 0 < T ∧ frobPC Λ π Γ I ψ t h hI i ^ T = 1 := fun i => by
    have : Finite (PC Λ π Γ I i) := Module.finite_of_finite Λ
    exact exists_pow_eq_one _ (hF i)
  choose T hT0 hT using hex
  refine ⟨T 0 * T 1 * T 2, Nat.mul_pos (Nat.mul_pos (hT0 0) (hT0 1)) (hT0 2), fun g m => ?_⟩
  unfold pcSeq
  refine Finset.sum_congr rfl fun i hi => ?_
  have hTi : frobPC Λ π Γ I ψ t h hI i ^ (T 0 * T 1 * T 2) = 1 := by
    have : i = 0 ∨ i = 1 ∨ i = 2 := by simp only [Finset.mem_range] at hi; omega
    rcases this with rfl | rfl | rfl
    · rw [mul_assoc, pow_mul, hT 0, one_pow]
    · rw [mul_comm (T 0), mul_assoc, pow_mul, hT 1, one_pow]
    · rw [mul_comm, pow_mul, hT 2, one_pow]
  rw [pow_add, hTi, mul_one]

end PC

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Rank =====
section

/-!
# S4-GOS-B, part Rank: the ranks of the perfect complex do not change under reduction `Λ → Λ'`

* **`finrank_pc3_red`**: `finrank Λ' (PC₀ × (PC₁ × PC₂))` over `Λ'` equals the one over `Λ`
  (`pcRed0/1/2 : Λ' ⊗ PC_Λ ≃ PC_Λ'` + `Module.finrank_baseChange`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open PerfectCx CurveCoh

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] {G : Type} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
variable [Finite Λ] [Fintype Gf] {ϖ : Λ} (hsurj : Function.Surjective (algebraMap Λ Λ'))
  (ht : algebraMap Λ Λ' ϖ = 0) (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = ϖ * s) {l N : ℕ}
  (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

include hsurj ht hk hΛ hall hallI hπ in
theorem finrank_pc3_red [Nontrivial Λ] [Nontrivial Λ'] [∀ i, Module.Free Λ (PC Λ π Γ I i)]
    [∀ i, Module.Finite Λ (PC Λ π Γ I i)] [∀ i, Module.Free Λ' (PC Λ' π Γ I i)]
    [∀ i, Module.Finite Λ' (PC Λ' π Γ I i)] :
    Module.finrank Λ' (PC Λ' π Γ I 0 × (PC Λ' π Γ I 1 × PC Λ' π Γ I 2)) =
      Module.finrank Λ (PC Λ π Γ I 0 × (PC Λ π Γ I 1 × PC Λ π Γ I 2)) := by
  have f0 : Module.Free Λ (MonoidAlgebra Λ Gf) := (inferInstance : Module.Free Λ (PC Λ π Γ I 0))
  have f1 : Module.Free Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) :=
    (inferInstance : Module.Free Λ (PC Λ π Γ I 1))
  have f2 : Module.Free Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :=
    (inferInstance : Module.Free Λ (PC Λ π Γ I 2))
  have h0 : Module.finrank Λ' (PC Λ' π Γ I 0) = Module.finrank Λ (PC Λ π Γ I 0) := by
    show Module.finrank Λ' (MonoidAlgebra Λ' Gf) = Module.finrank Λ (MonoidAlgebra Λ Gf)
    rw [← (pcRed0 (Gf := Gf) hsurj ht hk).finrank_eq, Module.finrank_baseChange]
  have h1 : Module.finrank Λ' (PC Λ' π Γ I 1) = Module.finrank Λ (PC Λ π Γ I 1) := by
    show Module.finrank Λ' (Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf)) =
      Module.finrank Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf))
    rw [← (pcRed1 π Γ (S := S) hsurj ht hk hΛ hall hπ).finrank_eq, Module.finrank_baseChange]
  have h2 : Module.finrank Λ' (PC Λ' π Γ I 2) = Module.finrank Λ (PC Λ π Γ I 2) := by
    show Module.finrank Λ' ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) =
      Module.finrank Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s))
    rw [← (pcRed2 π Γ I hsurj ht hk hΛ hallI hπ).finrank_eq, Module.finrank_baseChange]
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, h0, h1, h2]

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Bij =====
section

/-!
# S4-GOS-B, part Bij: the Frobenius of the perfect complex is bijective

* `frob1_surjective`: `frob1 ψ t h` is onto for bijective `t` (explicit right inverse via `frob1_comp`);
* `frobPC_surjective`: every `frobPC Λ π Γ I ψ t h hI i` is onto (bijective `t`, exact boundary conjugation);
* **`frobPC_bijective_true`**: for the true boundary data of any `ψ` and finite `Λ`, every `frobPC` is bijective.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace RamanujanPetersson.GOS

open CurveCoh PerfectCx Lefschetz CupDuality

section Gen

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M)
variable (Γ : Subgroup G) [Γ.Normal] {S : Type}

theorem frob1_surjective (ψ : G) (t : S → S) (h : S → Γ) (ht : Function.Bijective t) :
    Function.Surjective (frob1 ρ Γ ψ t h) := by
  set e := Equiv.ofBijective t ht with he
  set h' : S → Γ := fun u => (conjΓ Γ ψ⁻¹ (h (e.symm u)))⁻¹ with hh'
  have hc := frob1_comp ρ Γ ψ ψ⁻¹ t e.symm h h'
  have h0 := frob1_pow_zero ρ Γ ψ t h
  have key : frob1 ρ Γ (ψ * ψ⁻¹) (e.symm ∘ t) (fun s => conjΓ Γ ψ⁻¹ (h s) * h' (t s)) =
      frob1 ρ Γ (ψ ^ 0) t^[0] (hpow Γ ψ t h 0) := by
    have e1 : ψ * ψ⁻¹ = ψ ^ 0 := by rw [mul_inv_cancel, pow_zero]
    have e2 : e.symm ∘ t = t^[0] := by
      funext s
      simp only [Function.comp_apply, Function.iterate_zero, id_eq]
      exact e.symm_apply_apply s
    have e3 : (fun s => conjΓ Γ ψ⁻¹ (h s) * h' (t s)) = hpow Γ ψ t h 0 := by
      funext s
      have : e.symm (t s) = s := e.symm_apply_apply s
      simp only [hh', this, mul_inv_cancel]
      rfl
    rw [e1, e2, e3]
  intro y
  refine ⟨frob1 ρ Γ ψ⁻¹ e.symm h' y, ?_⟩
  rw [← LinearMap.comp_apply, hc, key, h0, LinearMap.id_apply]

end Gen

section PC

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

theorem frobPC_surjective (ht : Function.Bijective t)
    (hex : ∀ s (g : G), g ∈ Γ → g ∈ I (t s) → (ψ * h s) * g * (ψ * h s)⁻¹ ∈ I s) :
    ∀ i, Function.Surjective (frobPC Λ π Γ I ψ t h hI i)
  | 0 => regRep_surjective (Λ := Λ) π ψ
  | 1 => frob1_surjective (regRep Λ π) Γ ψ t h ht
  | 2 => frob2_surjective (regRep Λ π) Γ I ψ t h hI ht hex
  | _ + 3 => fun y => ⟨y, Subsingleton.elim (α := PUnit) _ _⟩

theorem frobPC_bijective [Finite Λ] [∀ i, Module.Finite Λ (PC Λ π Γ I i)] (ht : Function.Bijective t)
    (hex : ∀ s (g : G), g ∈ Γ → g ∈ I (t s) → (ψ * h s) * g * (ψ * h s)⁻¹ ∈ I s) (i : ℕ) :
    Function.Bijective (frobPC Λ π Γ I ψ t h hI i) := by
  have : Finite (PC Λ π Γ I i) := Module.finite_of_finite Λ
  have hs := frobPC_surjective (Λ := Λ) π Γ I ψ t h hI ht hex i
  exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩

end PC

section True

open Places Residue CP4a
open scoped Polynomial

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

set_option maxHeartbeats 800000 in
theorem frobPC_bijective_true {Λ : Type} [CommRing Λ] [Finite Λ] {Gf : Type} [Group Gf]
    (π : Pi1 (Rfin Fq F) F →* Gf) {S : Type} [Finite S]
    (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S) (ψ : Pi1 (Rfin Fq F) F)
    [∀ i, Module.Finite Λ (PC Λ π (pi1geo (Rfin Fq F) F (Fintype.card Fq)) D.inertia i)] (i : ℕ) :
    Function.Bijective (frobPC Λ π (pi1geo (Rfin Fq F) F (Fintype.card Fq)) D.inertia ψ (trueTau D ψ)
      (trueH D ψ) (trueCompat D ψ) i) :=
  frobPC_bijective (Λ := Λ) π _ D.inertia ψ _ _ _ (trueTw_ht D ψ)
    (fun s g _ hg => (inert_conj_iff (trueTau_smul D ψ s) g).1 hg) i

end True

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Lift =====
section

/-!
# S4-GOS-B, part Lift: an `l`-independent integer lift of the character of the perfect complex

`chiPC Λ … g = Σ_{i<3} (-1)^i Tr(ρPC_i g)`.
* `pcSeq_zero`: `pcSeq … g 0 = chiPC … g⁻¹`.
* `exists_rec_ptSeq`: the counts `ptSeq g` satisfy a nonzero integer recurrence from position `1` (Hankel argument
  `exists_rec_of_mod_pow` at one prime `l₀ ∤ q`, orders fixed by `finrank_lev`, recurrences by `pcSeq_rec`).
* `exists_mul_chi_eq`: `a · chi^{l,n}(g⁻¹) = u` with `a ≠ 0`, `u` integers independent of `l ∤ q`, `n > 0`
  (periodicity `pcSeq_periodic` + `mul_zero_eq_of_periodic`).
* **`exists_int_lift`**: `∃ b₀ ≠ 0, ∃ r : Gf → ℤ, ∀ l ∤ q prime, n > 0, g: r g = b₀ · chi^{l,n}(g)` in `ℤ/l^n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Chi

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

variable (Λ) in
/-- The character of the perfect complex: `Σ_{i<3} (-1)^i Tr(ρPC_i g)`. -/
def chiPC (g : Gf) : Λ :=
  ∑ i ∈ Finset.range 3, (-1 : Λ) ^ i * LinearMap.trace Λ (PC Λ π Γ I i) (ρPC Λ π Γ I i g)

theorem pcSeq_zero [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (g : Gf) :
    pcSeq Λ π Γ I ψ t h hI g 0 = chiPC Λ π Γ I g⁻¹ := by
  simp only [pcSeq, chiPC, pow_zero, Module.End.one_eq_id, LinearMap.comp_id]

end Chi

section Lift

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
  [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
  {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
  (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
  {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
  (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
  {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)

end Lift

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_Ass =====
section

/-!
# S4-GOS-B, part Ass: the character of the perfect complex is `Φ`, given the subgroup sums (O6) and `hfin`

* `exists_int_chi_two`: `chi^{l,n}(g)` and `chi^{l,n'}(g)` are casts of one integer (a common period of `pcSeq`).
* `chiPC_pow_prime_one`: `chi^{l,1}(g^l) = chi^{l,1}(g)` (`chi_pow_prime` over `ℤ/l`).
* `chiPC_eq_of_lift`: `r g = b₀ P` and `r ≡ b₀ chi^{l,n}` for all `n` give `chi^{l,n}(g) = P` (level shift by `v_l(b₀)`).
* **`chiPC_eq_Phi_of`**: for a Galois `G`-cover `L/𝔽_q(t)` with trivial finite inertia, `ι : G →* Gf`, and the cyclic
  subgroup sums `∑_{h ∈ ⟨τ⟩} chi^{l,1}(ι h) = |⟨τ⟩| χ_c(L^⟨τ⟩)` for all large `l`:
  `chi^{l,n}(ι σ) = Φ(σ)` in `ℤ/l^n` for every prime `l ∤ q` and `n > 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Ass

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
  [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
  {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
  (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
  {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
  (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
  {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)

omit [Fintype Gf] in
/-- `chi^{l,1}(g^l) = chi^{l,1}(g)`. -/
theorem chiPC_pow_prime_one (l : ℕ) [Fact l.Prime]
    [∀ i, Module.Free (ZMod (l ^ 1))
      (PC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    [∀ i, Module.Finite (ZMod (l ^ 1))
      (PC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)] (g : Gf) :
    chiPC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia (g ^ l) =
      chiPC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia g := by
  have key : ∀ N : ℕ, N = l → ∀ [∀ i, Module.Free (ZMod N)
      (PC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
      [∀ i, Module.Finite (ZMod N)
      (PC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)],
      chiPC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia (g ^ l) =
        chiPC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia g := by
    intro N hN
    subst hN
    intro _ _
    exact chi_pow_prime _ 2 g
  exact key (l ^ 1) (pow_one l)

end Ass

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_C_B1c =====
section

/-!
# S4-GOS-C, part B1c: characters of projective modules vanish on `l`-singular elements

**`trace_eq_zero_of_dvd_orderOf`**: for a finite group `G`, a free finite `Λ`-module `Y` with `l ^ N = 0` in `Λ` and a
projective (Higman) representation `ρ`, `Tr(ρ g) = 0` whenever `l ∣ orderOf g`. Proof: restrict to `C = ⟨g⟩`
(`isHigman_res`), project onto the `l'`-part by `x ↦ x ^ t`, `t = (l ^ α) ^ φ(m)` (`trace_eq_zero_of_proj`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings

variable {Λ : Type*} [CommRing Λ] {Y : Type*} [AddCommGroup Y] [Module Λ Y] [Module.Free Λ Y]
  [Module.Finite Λ Y] {G : Type*} [Group G] [Fintype G]

/-- **Characters of projective modules vanish on `l`-singular elements** (over `Λ` with `l ^ N = 0`). -/
theorem trace_eq_zero_of_dvd_orderOf {ρ : Representation Λ G Y} (hρ : IsProj ρ) {l N : ℕ} (hl : l.Prime)
    (hΛ : ((l ^ N : ℕ) : Λ) = 0) (g : G) (hg : l ∣ orderOf g) : LinearMap.trace Λ Y (ρ g) = 0 := by
  classical
  obtain ⟨E, hE⟩ := hρ
  set C := Subgroup.zpowers g with hCdef
  haveI : Fintype (G ⧸ C) := Fintype.ofFinite _
  have hC := zpowers_comm g
  set g' : C := ⟨g, Subgroup.mem_zpowers g⟩ with hg'
  have hyn : ∀ y : C, y ^ orderOf g = 1 := fun y => by
    rw [← Nat.card_zpowers]; exact pow_card_eq_one'
  obtain ⟨α, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' l hl.one_lt.ne'
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
  set t := (l ^ α) ^ Nat.totient m with ht
  have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (pow_ne_zero _ hl.ne_zero))
  have htm : m ∣ t - 1 := (Nat.modEq_iff_dvd' ht1).mp
    (Nat.ModEq.pow_totient (Nat.Coprime.pow_left α ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm))).symm
  obtain ⟨q, hq⟩ := htm
  have htq : t = m * q + 1 := (Nat.sub_eq_iff_eq_add ht1).mp hq
  have hb : (g' ^ m) ^ (l ^ α) = 1 := by rw [← pow_mul, mul_comm m, ← hn, hyn]
  have hφ : ∀ x : C, ∃ j : ℕ, powHom hC t x = x * (g' ^ m) ^ j := by
    intro x
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr x.2 : (x : G) ∈ Submonoid.powers g)
    have hx : x = g' ^ k := Subtype.ext (by rw [← hk, SubgroupClass.coe_pow])
    refine ⟨k * q, ?_⟩
    show x ^ t = _
    rw [hx, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    rw [htq]
    ring
  have hrange : g'⁻¹ ∉ Set.range (powHom hC t) := by
    rintro ⟨y, hy⟩
    have h1 : y ^ (t * m) = 1 := by
      obtain ⟨c, hc⟩ : orderOf g ∣ t * m := by
        rw [hn]; exact Nat.mul_dvd_mul_right (dvd_pow_self (l ^ α) (Nat.totient_pos.mpr hm0).ne') m
      rw [hc, pow_mul, hyn, one_pow]
    have h2 : (g'⁻¹) ^ m = 1 := by
      rw [← hy]
      show (y ^ t) ^ m = 1
      rw [← pow_mul, h1]
    have h3 : g' ^ m = 1 := by rw [← inv_eq_one, ← inv_pow]; exact h2
    have h4 := congrArg Subtype.val h3
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h4
    exact hm (hg.trans (orderOf_dvd_of_pow_eq_one h4))
  exact trace_eq_zero_of_proj hl hC (isHigman_res hE C) hΛ (powHom hC t) hb hφ g' hrange

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_C0 =====
section

/-!
# S4-GOS-C, part C0: traces agree on two lifts of the same module

A *lift* of a `Λ`-module `Y` with `G`-action `σ` is a `G`-equivariant surjection `f : X → Y` with `ker f ⊆ t • X`
(`t` nilpotent). **`trace_eq_of_lifts`**: if `X₁`, `X₂` are free finite lifts and `X₁` is projective (Higman), then
`Tr(ρ₁ g) = Tr(ρ₂ g)` for every `g`: an equivariant lift `X₁ → X₂` of the identity of `Y` is bijective, since it is
invertible up to endomorphisms with range in `t • X` (nilpotent).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings

section Nil

variable {Λ : Type*} [CommRing Λ] {X : Type*} [AddCommGroup X] [Module Λ X]

end Nil

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] [Fintype G]

/-- **Two free lifts of the same module, one projective, have the same character.** -/
theorem trace_eq_of_lifts {X₁ X₂ Y : Type*} [AddCommGroup X₁] [Module Λ X₁] [Module.Free Λ X₁]
    [Module.Finite Λ X₁] [AddCommGroup X₂] [Module Λ X₂] [Module.Free Λ X₂] [Module.Finite Λ X₂]
    [AddCommGroup Y] [Module Λ Y] {ρ₁ : Representation Λ G X₁} {ρ₂ : Representation Λ G X₂}
    {σ : Representation Λ G Y} (hρ₁ : IsProj ρ₁) {t : Λ} {N : ℕ} (ht : t ^ N = 0)
    {f₁ : X₁ →ₗ[Λ] Y} {f₂ : X₂ →ₗ[Λ] Y} (hf₁ : IsEquivariant ρ₁ σ f₁) (hf₂ : IsEquivariant ρ₂ σ f₂)
    (hs₁ : Function.Surjective f₁) (hs₂ : Function.Surjective f₂)
    (hk₁ : ∀ x, f₁ x = 0 → ∃ y, x = t • y) (hk₂ : ∀ x, f₂ x = 0 → ∃ y, x = t • y) (g : G) :
    LinearMap.trace Λ X₁ (ρ₁ g) = LinearMap.trace Λ X₂ (ρ₂ g) := by
  obtain ⟨E, hE⟩ := hρ₁
  obtain ⟨φ, hφe, hφ⟩ := exists_equivariant_lift hE hf₂ hs₂ hf₁
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property f₁ f₂ hs₁
  have hb := bijective_of_lifts ht hk₁ hk₂ hφ hψ
  set e := LinearEquiv.ofBijective φ hb with he
  rw [← LinearMap.trace_conj' (ρ₁ g) e]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := e.surjective y
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun (hφe g) x

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_LIFTa =====
section

/-!
# S4-GOS-C, part LIFTa: permutation modules and reduction maps for lifting projective modules

* `leftAct`: `G` acts on `G × ι` by left multiplication on `G` (freely, `leftAct_free`);
* `permRepM`: the permutation representation on `X → M` over `Λ`;
* `red X : (X → Λ) → (X → Λ')` (coefficientwise `algebraMap`): equivariant, onto, kernel `t • _`;
* `pMap σ' b : (G × ι → Λ') → Y'`, `f ↦ ∑ f (h, i) • σ' h (b i)`: equivariant and onto for a basis `b`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings

attribute [local instance] leftAct

section Red

variable {Λ Λ' : Type*} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ']

theorem red_ker {t : Λ} (hker : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s) (X : Type*) (f : X → Λ)
    (hf : red (Λ' := Λ') X f = 0) : ∃ g, f = t • g := by
  choose s hs using fun x => hker (f x) (congrFun hf x)
  exact ⟨s, funext fun x => hs x⟩

end Red

section PMap

variable {Λ' : Type*} [CommRing Λ'] {G : Type*} [Group G] [Fintype G] {Y' : Type*} [AddCommGroup Y']
  [Module Λ' Y'] {ι : Type*} [Fintype ι]

end PMap

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_LIFTb =====
section

/-!
# S4-GOS-C, part LIFTb: lifting the idempotent of a projective module

For `Λ → Λ'` onto with kernel `t Λ`, `t ^ N = 0`, a free finite `Λ'`-module `Y'` with basis `b` and a projective
(Higman) `Λ'`-representation `σ'`: **`exists_idem_lift`** gives an equivariant section `s'` of `pMap σ' b` and an
equivariant idempotent `e` of the free permutation module `G × ι → Λ` with `red ∘ e = (s' ∘ pMap) ∘ red`
(lift `s' ∘ pMap` equivariantly, then correct it to an idempotent by `1 - (1 - x ^ n) ^ n`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings

attribute [local instance] leftAct

section Int

variable {Λ Λ' : Type*} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {X : Type*}

end Int

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {G : Type} [Group G] [Fintype G]
  {Y' : Type} [AddCommGroup Y'] [Module Λ' Y'] [Module.Free Λ' Y'] {ι : Type} [Fintype ι]

/-- **Lifting the idempotent of a projective module** to an equivariant idempotent over `Λ`. -/
theorem exists_idem_lift (t : Λ) (hsurj : Function.Surjective (algebraMap Λ Λ'))
    (hker : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s) {N : ℕ} (htN : t ^ N = 0)
    (b : Module.Basis ι Λ' Y') {σ' : Representation Λ' G Y'} (hσ' : IsProj σ') :
    ∃ (e : Module.End Λ (G × ι → Λ)) (s' : Y' →ₗ[Λ'] (G × ι → Λ')),
      IsIdempotentElem e ∧ (∀ g, Commute e (permRep Λ G (G × ι) g)) ∧
      IsEquivariant σ' (permRep Λ' G (G × ι)) s' ∧ pMap σ' b ∘ₗ s' = LinearMap.id ∧
      red (G × ι) ∘ₗ e = ((s' ∘ₗ pMap σ' b).restrictScalars Λ) ∘ₗ red (G × ι) := by
  obtain ⟨E', hE'⟩ := hσ'
  obtain ⟨s', hs'e, hs'⟩ := exists_equivariant_lift hE' (pMap_equivariant σ' b) (pMap_surjective σ' b)
    (isEquivariant_id (ρ := σ'))
  set eb : Module.End Λ' (G × ι → Λ') := s' ∘ₗ pMap σ' b with heb
  have hebi : IsIdempotentElem eb := by
    show (s' ∘ₗ pMap σ' b) ∘ₗ (s' ∘ₗ pMap σ' b) = s' ∘ₗ pMap σ' b
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc (pMap σ' b), hs', LinearMap.id_comp]
  set eL : Module.End Λ (G × ι → Λ') := eb.restrictScalars Λ with heL
  have heLi : IsIdempotentElem eL := LinearMap.ext fun f => LinearMap.congr_fun hebi.eq f
  have hebe : IsEquivariant (permRep Λ' G (G × ι)) (permRep Λ' G (G × ι)) eb := fun g =>
    LinearMap.ext fun f => by
      have h1 := LinearMap.congr_fun (pMap_equivariant σ' b g) f
      have h2 := LinearMap.congr_fun (hs'e g) (pMap σ' b f)
      simp only [heb, LinearMap.comp_apply] at h1 h2 ⊢
      rw [h1, h2]
  have hu : IsEquivariant (permRep Λ G (G × ι)) (permRepM Λ G (G × ι) Λ') (eL ∘ₗ red (G × ι)) := fun g =>
    LinearMap.ext fun f => LinearMap.congr_fun (hebe g) (red (G × ι) f)
  obtain ⟨EF, hEF⟩ := isProj_permRep (R := Λ) (G := G) (X := G × ι) (fun g x hx => leftAct_free g x hx)
  obtain ⟨x, hxe, hx⟩ := exists_equivariant_lift hEF (red_equivariant (G × ι)) (red_surjective hsurj _) hu
  have hred : ∀ f, ∃ y, ((x - x ^ 2 : Module.End Λ (G × ι → Λ))) f = t • y := fun f => by
    refine red_ker hker _ _ ?_
    have h := LinearMap.congr_fun (int_sub (a := x) (b := x ^ 2) hx (int_pow hx 2)) f
    rw [LinearMap.comp_apply] at h
    rw [h, pow_two, heLi.eq, sub_self, LinearMap.zero_comp, LinearMap.zero_apply]
  have hnil : (x - x ^ 2) ^ (N + 1) = 0 := LinearMap.ext fun f => by
    obtain ⟨y, hy⟩ := pow_apply_mem_smul hred (N + 1) f
    rw [hy, pow_succ, htN, zero_mul, zero_smul, LinearMap.zero_apply]
  have hc : ∀ g, Commute x (permRep Λ G (G × ι) g) := fun g => hxe g
  refine ⟨1 - (1 - x ^ (N + 1)) ^ (N + 1), s', isIdempotentElem_one_sub_one_sub_pow_pow x _ hnil,
    fun g => (Commute.one_left _).sub_left (((Commute.one_left _).sub_left ((hc g).pow_left _)).pow_left _),
    hs'e, hs', ?_⟩
  have h := int_sub int_one (int_pow (int_sub int_one (int_pow hx (N + 1))) (N + 1))
  rw [h, heLi.pow_succ_eq, heLi.one_sub.pow_succ_eq, sub_sub_cancel]

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_LIFTc =====
section

/-!
# S4-GOS-C, part LIFTc: projective modules lift

**`exists_proj_lift`**: for `Λ → Λ'` onto with kernel `t Λ`, `t ^ N = 0`, `Λ` local, every projective (Higman)
representation `σ'` on a free finite `Λ'`-module `Y'` has a *lift*: a free finite `Λ`-module `X` with a projective
representation `ρ` and an equivariant `Λ`-linear surjection `f : X → Y'` with `ker f ⊆ t • X`
(`X` = range of the lifted idempotent of `exists_idem_lift`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings

attribute [local instance] leftAct

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {G : Type} [Group G] [Fintype G]
  {Y' : Type} [AddCommGroup Y'] [Module Λ' Y'] [Module.Free Λ' Y'] [Module Λ Y'] [IsScalarTower Λ Λ' Y']
  {ι : Type} [Fintype ι]

/-- **Projective modules lift** along `Λ → Λ'` (nilpotent kernel `t Λ`, `Λ` local). -/
theorem exists_proj_lift [IsLocalRing Λ] (t : Λ) (hsurj : Function.Surjective (algebraMap Λ Λ'))
    (hker : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s) {N : ℕ} (htN : t ^ N = 0)
    (b : Module.Basis ι Λ' Y') {σ' : Representation Λ' G Y'} (hσ' : IsProj σ') :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module Λ X) (_ : Module.Free Λ X) (_ : Module.Finite Λ X)
      (ρ : Representation Λ G X) (f : X →ₗ[Λ] Y'), IsProj ρ ∧ Function.Surjective f ∧
      (∀ x, f x = 0 → ∃ y, x = t • y) ∧ (∀ g x, f (ρ g x) = σ' g (f x)) := by
  obtain ⟨e, s', hei, hec, -, hs', hred⟩ := exists_idem_lift t hsurj hker htN b hσ'
  have hfix : ∀ x : LinearMap.range e, e x = x := fun x => by
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp x.2
    rw [← hy, ← Module.End.mul_apply, hei.eq]
  have hri : e.rangeRestrict ∘ₗ (LinearMap.range e).subtype = LinearMap.id :=
    LinearMap.ext fun x => Subtype.ext (hfix x)
  have hi : IsEquivariant (rangeRep (permRep Λ G (G × ι)) e hec) (permRep Λ G (G × ι))
      (LinearMap.range e).subtype := fun _ => LinearMap.ext fun _ => rfl
  have hr : IsEquivariant (permRep Λ G (G × ι)) (rangeRep (permRep Λ G (G × ι)) e hec) e.rangeRestrict :=
    fun g => LinearMap.ext fun y => Subtype.ext (LinearMap.congr_fun (hec g).eq y)
  have hF := isProj_permRep (R := Λ) (G := G) (X := G × ι) (fun g x hx => leftAct_free g x hx)
  obtain ⟨hfree, hfin⟩ := free_finite_of_retract (P := G × ι → Λ) hri
  set f : LinearMap.range e →ₗ[Λ] Y' :=
    ((pMap σ' b).restrictScalars Λ) ∘ₗ red (G × ι) ∘ₗ (LinearMap.range e).subtype with hf
  refine ⟨LinearMap.range e, inferInstance, inferInstance, hfree, hfin, rangeRep (permRep Λ G (G × ι)) e hec, f,
    IsProj.retract hF hi hr hri, fun y => ?_, fun x hx => ?_, fun g x => ?_⟩
  · obtain ⟨z, hz⟩ := red_surjective (Λ := Λ) hsurj (G × ι) (s' y)
    refine ⟨e.rangeRestrict z, ?_⟩
    have h := LinearMap.congr_fun hred z
    simp only [LinearMap.comp_apply] at h
    simp only [hf, LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.coe_subtype,
      LinearMap.codRestrict_apply, LinearMap.rangeRestrict]
    rw [h, LinearMap.restrictScalars_apply, LinearMap.comp_apply, hz, ← LinearMap.comp_apply (pMap σ' b) s',
      hs', LinearMap.id_apply, ← LinearMap.comp_apply (pMap σ' b) s', hs', LinearMap.id_apply]
  · have h0 : red (Λ' := Λ') (G × ι) (x : G × ι → Λ) = 0 := by
      have h := LinearMap.congr_fun hred (x : G × ι → Λ)
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h
      rw [← hfix x, h]
      have hx' : pMap σ' b (red (G × ι) (x : G × ι → Λ)) = 0 := hx
      rw [hx', map_zero]
    obtain ⟨z, hz⟩ := red_ker hker (G × ι) _ h0
    refine ⟨e.rangeRestrict z, Subtype.ext ?_⟩
    rw [← hfix x, hz, map_smul]
    rfl
  · show pMap σ' b (red (G × ι) (permRep Λ G (G × ι) g (x : G × ι → Λ))) =
      σ' g (pMap σ' b (red (G × ι) (x : G × ι → Λ)))
    rw [← LinearMap.comp_apply (red (G × ι)), red_equivariant (G × ι) g, LinearMap.comp_apply]
    exact LinearMap.congr_fun (pMap_equivariant σ' b g) _

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_BETA =====
section

/-!
# S4-GOS-C, part BETA: the Brauer trace function `β`

* `isProj_of_card_unit`: `|G|` a unit ⇒ every representation is projective (Higman element `|G|⁻¹ • 1`);
* `isProj_tprod`: `P` projective ⇒ `P ⊗ M` projective;
* `resRep τ`: a `Λ'`-representation viewed as a `Λ`-representation;
* **`IsBeta t l τ β`**: `β g = 0` for `l`-singular `g`; for `l`-regular `g`, `β g` is the trace of `g` on every free
  finite lift of `τ|⟨g⟩` to `Λ` (well defined by C0);
* **`exists_beta`**: such a `β` exists (projective lifts of `τ|⟨g⟩` exist by LIFT, `|⟨g⟩|` a unit in `Λ'`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings

section Gen

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module R V]

theorem isProj_of_card_unit {ρ : Representation R G V} (hu : IsUnit (Fintype.card G : R)) : IsProj ρ := by
  obtain ⟨u, hu⟩ := hu
  refine ⟨((u⁻¹ : Rˣ) : R) • LinearMap.id, ?_⟩
  unfold IsHigman
  refine LinearMap.ext fun x => ?_
  have hx : ∀ h : G, ρ h (ρ h⁻¹ x) = x := fun h => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, hx, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, ← hu, Units.mul_inv, one_smul]

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem isProj_tprod {ρ : Representation R G V} {τ : Representation R G M} (hρ : IsProj ρ) :
    IsProj (ρ.tprod τ) := by
  obtain ⟨E, hE⟩ := hρ
  refine ⟨TensorProduct.map E LinearMap.id, ?_⟩
  unfold IsHigman
  rw [← sum_tw_eq_id (τ := τ) hE]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun h => by simp only [Equiv.inv_apply, inv_inv])

end Gen

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {G : Type} [Group G]
  {M : Type} [AddCommGroup M] [Module Λ' M] [Module Λ M] [IsScalarTower Λ Λ' M]

/-- `|⟨g⟩|` is a unit in `Λ'` for `l`-regular `g`, so `τ|⟨g⟩` is projective. -/
theorem isProj_zpowers [Finite G] {l : ℕ} (hl' : ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : Λ')) (τ : Representation Λ' G M)
    (g : G) (hg : ¬ l ∣ orderOf g) [Fintype (Subgroup.zpowers g)] :
    IsProj (τ.comp (Subgroup.zpowers g).subtype) :=
  isProj_of_card_unit (by rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]; exact hl' _ hg)

/-- **Existence of the Brauer trace function.** -/
theorem exists_beta [Fintype G] [IsLocalRing Λ] [Nontrivial Λ'] [Module.Free Λ' M] [Module.Finite Λ' M]
    (t : Λ) (hsurj : Function.Surjective (algebraMap Λ Λ')) (hker : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s)
    {N : ℕ} (htN : t ^ N = 0) {l : ℕ} (hl' : ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : Λ')) (τ : Representation Λ' G M) :
    ∃ β : G → Λ, IsBeta t l τ β := by
  classical
  have key : ∀ g : G, ∃ b : Λ, (l ∣ orderOf g → b = 0) ∧ (¬ l ∣ orderOf g → ∀ (X : Type) [AddCommGroup X]
      [Module Λ X] [Module.Free Λ X] [Module.Finite Λ X] (ρ : Representation Λ (Subgroup.zpowers g) X)
      (f : X →ₗ[Λ] M), Function.Surjective f → (∀ x, f x = 0 → ∃ y, x = t • y) →
      (∀ c x, f (ρ c x) = τ c (f x)) → LinearMap.trace Λ X (ρ ⟨g, Subgroup.mem_zpowers g⟩) = b) := by
    intro g
    by_cases hg : l ∣ orderOf g
    · exact ⟨0, fun _ => rfl, fun h => absurd hg h⟩
    · obtain ⟨X, i1, i2, i3, i4, ρ, f, hρ, hfs, hfk, hfe⟩ :=
        exists_proj_lift t hsurj hker htN (Module.Free.chooseBasis Λ' M) (isProj_zpowers hl' τ g hg)
      refine ⟨LinearMap.trace Λ X (ρ ⟨g, Subgroup.mem_zpowers g⟩), fun h => absurd h hg, ?_⟩
      intro _ X₂ _ _ _ _ ρ₂ f₂ hs₂ hk₂ he₂
      exact (trace_eq_of_lifts hρ htN (σ := resRep (τ.comp (Subgroup.zpowers g).subtype))
        (fun c => LinearMap.ext fun x => hfe c x) (fun c => LinearMap.ext fun x => he₂ c x)
        hfs hs₂ hfk hk₂ _).symm
  choose β hβ using key
  exact ⟨β, hβ⟩

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_HSR =====
section

/-!
# S4-GOS-C, part HSR: the sum of the character of a projective module

For a projective (Higman) representation `ρ` of a finite group on a free finite module over a local ring,
the coinvariants are free finite (`coinv_free_finite_of_proj`, a retract via `[x] ↦ ∑_h E (ρ h x)`) and
**`sum_trace_eq_card_mul_finrank`**: `∑_g Tr(ρ g) = |G| · rank X_G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings Representation

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] [Fintype G]
  {X : Type*} [AddCommGroup X] [Module Λ X]

theorem mk_coinvSecE {ρ : Representation Λ G X} {E : X →ₗ[Λ] X} (hE : IsHigman ρ E) (y : Coinvariants ρ) :
    Coinvariants.mk ρ (coinvSecE ρ E y) = y := by
  induction y using Coinvariants.induction_on with
  | h x =>
    rw [coinvSecE_mk, map_sum]
    conv_rhs => rw [← hE.apply_inv x]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Coinvariants.mk_self_apply]

theorem coinv_free_finite_of_proj [IsLocalRing Λ] [Module.Free Λ X] [Module.Finite Λ X]
    {ρ : Representation Λ G X} (hρ : IsProj ρ) :
    Module.Free Λ (Coinvariants ρ) ∧ Module.Finite Λ (Coinvariants ρ) := by
  obtain ⟨E, hE⟩ := hρ
  exact free_finite_of_retract (i := coinvSecE ρ E) (r := Coinvariants.mk ρ)
    (LinearMap.ext fun y => mk_coinvSecE hE y)

theorem norm_coinvSecE_mk {ρ : Representation Λ G X} {E : X →ₗ[Λ] X} (hE : IsHigman ρ E) (x : X) :
    ∑ g : G, ρ g (coinvSecE ρ E (Coinvariants.mk ρ x)) = ∑ g : G, ρ g x := by
  rw [coinvSecE_mk]
  simp only [map_sum]
  rw [Finset.sum_comm]
  have h1 : ∀ h : G, ∑ g : G, ρ g (E (ρ h x)) = ∑ g : G, ρ g (ρ h⁻¹ (E (ρ h x))) := fun h =>
    Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => by
      simp [map_mul, Module.End.mul_apply, rep_apply_inv_apply])
  rw [Fintype.sum_congr _ _ h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [← map_sum, hE.apply_inv]

/-- **`∑_g Tr(ρ g) = |G| · rank X_G`** for a projective representation over a local ring. -/
theorem sum_trace_eq_card_mul_finrank [IsLocalRing Λ] [Module.Free Λ X] [Module.Finite Λ X]
    {ρ : Representation Λ G X} (hρ : IsProj ρ) :
    ∑ g : G, LinearMap.trace Λ X (ρ g) =
      (Fintype.card G : Λ) * (Module.finrank Λ (Coinvariants ρ) : Λ) := by
  obtain ⟨hF, hFin⟩ := coinv_free_finite_of_proj hρ
  haveI := hF
  haveI := hFin
  obtain ⟨E, hE⟩ := hρ
  set N : Module.End Λ X := ∑ g : G, ρ g with hN
  have hfac : (N ∘ₗ coinvSecE ρ E) ∘ₗ Coinvariants.mk ρ = N := LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, hN, LinearMap.sum_apply]
    exact norm_coinvSecE_mk hE x
  have hmk : Coinvariants.mk ρ ∘ₗ (N ∘ₗ coinvSecE ρ E) = (Fintype.card G : Λ) • LinearMap.id :=
    LinearMap.ext fun y => by
      simp only [LinearMap.comp_apply, hN, LinearMap.sum_apply, map_sum, Coinvariants.mk_self_apply,
        mk_coinvSecE hE, Finset.sum_const, Finset.card_univ, LinearMap.smul_apply, LinearMap.id_apply]
      rw [Nat.cast_smul_eq_nsmul]
  rw [← map_sum (LinearMap.trace Λ X), ← hN, ← hfac, LinearMap.trace_comp_comm', hmk, map_smul, LinearMap.trace_id, smul_eq_mul]

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_HSR2 =====
section

/-!
# S4-GOS-C, part HSR2: coinvariants of a lift

For `Λ → Λ'` onto with kernel `t Λ` and a lift `f : X → Y'` (onto, kernel in `t • X`, equivariant) of a
`Λ'`-representation `σ'` by a projective `Λ`-representation `ρ` on a free finite module (`Λ` local):
**`finrank_coinv_lift`**: `finrank Λ' (Coinvariants σ') = finrank Λ (Coinvariants ρ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings Representation

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {G : Type} [Group G]
  {X Y' : Type} [AddCommGroup X] [Module Λ X] [AddCommGroup Y'] [Module Λ' Y'] [Module Λ Y']
  [IsScalarTower Λ Λ' Y']

/-- **Coinvariants of a lift**: equal ranks at both levels. -/
theorem finrank_coinv_lift [Fintype G] [IsLocalRing Λ] [Nontrivial Λ'] [Module.Free Λ X] [Module.Finite Λ X]
    (t : Λ) (hsurj : Function.Surjective (algebraMap Λ Λ')) (ht : algebraMap Λ Λ' t = 0)
    {ρ : Representation Λ G X} (hρ : IsProj ρ) {σ' : Representation Λ' G Y'} {f : X →ₗ[Λ] Y'}
    (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → ∃ y, x = t • y) (hfρ : ∀ g x, f (ρ g x) = σ' g (f x)) :
    Module.finrank Λ' (Coinvariants σ') = Module.finrank Λ (Coinvariants ρ) := by
  obtain ⟨hfree, hfin⟩ := coinv_free_finite_of_proj hρ
  let K : Submodule Λ' Y' := Coinvariants.ker σ'
  have hinv : ∀ g : G, (K.mkQ.restrictScalars Λ ∘ₗ f) ∘ₗ ρ g = K.mkQ.restrictScalars Λ ∘ₗ f :=
    fun g => LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.mkQ_apply, hfρ]
      exact (Submodule.Quotient.eq K).mpr (Coinvariants.sub_mem_ker g (f x))
  let F : Coinvariants ρ →ₗ[Λ] Y' ⧸ K := Coinvariants.lift ρ (K.mkQ.restrictScalars Λ ∘ₗ f) hinv
  have hF : ∀ x, F (Coinvariants.mk ρ x) = Submodule.Quotient.mk (f x) := fun x =>
    Coinvariants.lift_mk ρ _ hinv x
  have hFs : Function.Surjective F := fun y => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨Coinvariants.mk ρ x, hF x⟩
  have hFk : ∀ z, F z = 0 → ∃ w, z = t • w := fun z hz => by
    obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective ρ z
    rw [hF, Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨x0, hx0, hfx0⟩ := exists_ker_lift hsurj hf hfρ hz
    obtain ⟨y, hy⟩ := hk (x - x0) (by rw [map_sub, hfx0, sub_self])
    refine ⟨Coinvariants.mk ρ y, ?_⟩
    have h0 : Coinvariants.mk ρ x0 = 0 := (Coinvariants.mk_eq_zero ρ).mpr hx0
    rw [← map_smul, ← hy, map_sub, h0, sub_zero]
  let e := PerfectCx.redEquiv t hsurj ht F hFs hFk
  show Module.finrank Λ' (Y' ⧸ K) = _
  rw [← e.finrank_eq, Module.finrank_baseChange]

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_B2 =====
section

/-!
# S4-GOS-C, part B2: Brauer's formula for `dim (P' ⊗ M)_G` and subgroup sums of `β`

`Λ → Λ'` onto with kernel `t Λ`, `t ^ N = 0`, `Λ` local with `l ^ n = 0`; `|C|` a unit in `Λ'` when `l ∤ |C|`.
* **`brauer_B2`**: for `P'` projective over `Λ'[G]` with a free lift `ρP` on `P`, any `M` and any Brauer trace
  function `β` of `M` (`IsBeta`): `|G| · dim (P' ⊗ M)_G = Σ_g Tr(g | P) β(g)` in `Λ`;
* **`sum_beta_subgroup`**: for `H ≤ G` with `l ∤ |H|`: `Σ_{h ∈ H} β h = |H| · dim (M|_H)_H`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings Representation TensorProduct

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {G : Type} [Group G] [Fintype G]
  [IsLocalRing Λ] [Nontrivial Λ']
  {M : Type} [AddCommGroup M] [Module Λ' M] [Module Λ M] [IsScalarTower Λ Λ' M] [Module.Free Λ' M]
  [Module.Finite Λ' M]

/-- **Brauer's formula** `|G| dim (P' ⊗ M)_G = Σ_g Tr(g | P) β(g)`. -/
theorem brauer_B2 (t : Λ) (hsurj : Function.Surjective (algebraMap Λ Λ')) (ht : algebraMap Λ Λ' t = 0)
    (hker : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s) {N : ℕ} (htN : t ^ N = 0) {l n : ℕ} (hl : l.Prime)
    (hΛ : ((l ^ n : ℕ) : Λ) = 0) (hl' : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : Λ'))
    {P : Type} [AddCommGroup P] [Module Λ P] [Module.Free Λ P] [Module.Finite Λ P]
    {P' : Type} [AddCommGroup P'] [Module Λ' P'] [Module Λ P'] [IsScalarTower Λ Λ' P'] [Module.Free Λ' P']
    [Module.Finite Λ' P'] {ρP : Representation Λ G P} {σP : Representation Λ' G P'} (hσP : IsProj σP)
    (τ : Representation Λ' G M) (fP : P →ₗ[Λ] P') (hfP : Function.Surjective fP)
    (hkP : ∀ x, fP x = 0 → ∃ y, x = t • y) (heP : ∀ g x, fP (ρP g x) = σP g (fP x))
    {β : G → Λ} (hβ : IsBeta t l τ β) :
    (Fintype.card G : Λ) * (Module.finrank Λ' (Coinvariants (σP.tprod τ)) : Λ) =
      ∑ g, LinearMap.trace Λ P (ρP g) * β g := by
  classical
  obtain ⟨X, _, _, _, _, ρ, f, hρ, hfs, hfk, hfe⟩ := exists_proj_lift t hsurj hker htN
    (Module.Free.chooseBasis Λ' (P' ⊗[Λ'] M)) (isProj_tprod (τ := τ) hσP)
  rw [finrank_coinv_lift t hsurj ht hρ hfs hfk hfe, ← sum_trace_eq_card_mul_finrank hρ]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : l ∣ orderOf g
  · rw [trace_eq_zero_of_dvd_orderOf hρ hl hΛ g hg, (hβ g).1 hg, mul_zero]
  set C := Subgroup.zpowers g
  obtain ⟨Mt, _, _, _, _, ρM, fM, -, hfMs, hfMk, hfMe⟩ :=
    exists_proj_lift t hsurj hker htN (Module.Free.chooseBasis Λ' M) (isProj_zpowers hl' τ g hg)
  obtain ⟨T, hT, hTs, hTk⟩ := exists_tensor_lift t hsurj ht hker fP hfP hkP fM hfMs hfMk
  have hβg := (hβ g).2 hg Mt ρM fM hfMs hfMk hfMe
  obtain ⟨E, hE⟩ := hρ
  have hres : IsProj (ρ.comp C.subtype) := ⟨_, isHigman_res hE C⟩
  have key := trace_eq_of_lifts (G := C) hres htN (σ := resRep ((σP.tprod τ).comp C.subtype))
    (ρ₂ := Representation.tprod (ρP.comp C.subtype) ρM) (f₁ := f) (f₂ := T) (fun c => LinearMap.ext fun x => hfe c x)
    (fun c => TensorProduct.ext' fun p m => by
      simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul, hT, resRep_apply,
        MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
      rw [heP, hfMe]
      try rfl)
    hfs hTs hfk hTk ⟨g, Subgroup.mem_zpowers g⟩
  have hg' : ρ g = (ρ.comp C.subtype) ⟨g, Subgroup.mem_zpowers g⟩ := rfl
  rw [hg', key, Representation.tprod_apply, LinearMap.trace_tensorProduct', hβg]
  try rfl

/-- **Subgroup sums of `β`**: `Σ_{h ∈ H} β h = |H| dim (M|_H)_H` for `l ∤ |H|`. -/
theorem sum_beta_subgroup (t : Λ) (hsurj : Function.Surjective (algebraMap Λ Λ')) (ht : algebraMap Λ Λ' t = 0)
    (hker : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s) {N : ℕ} (htN : t ^ N = 0) {l : ℕ}
    (hl' : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : Λ')) (τ : Representation Λ' G M) {β : G → Λ}
    (hβ : IsBeta t l τ β) (H : Subgroup G) [Fintype H] (hH : ¬ l ∣ Fintype.card H) :
    ∑ h : H, β h = (Fintype.card H : Λ) * (Module.finrank Λ' (Coinvariants (τ.comp H.subtype)) : Λ) := by
  classical
  obtain ⟨MH, _, _, _, _, ρH, fH, hρH, hfs, hfk, hfe⟩ := exists_proj_lift t hsurj hker htN
    (Module.Free.chooseBasis Λ' M) (isProj_of_card_unit (ρ := τ.comp H.subtype) (hl' _ hH))
  rw [finrank_coinv_lift t hsurj ht hρH hfs hfk hfe, ← sum_trace_eq_card_mul_finrank hρH]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hle : Subgroup.zpowers (h : G) ≤ H := (Subgroup.zpowers_le (H := H)).mpr h.2
  have hreg : ¬ l ∣ orderOf (h : G) := fun hd => hH (hd.trans (by
    rw [Subgroup.orderOf_coe]; exact orderOf_dvd_card))
  have hb := (hβ h).2 hreg MH (ρH.comp (Subgroup.inclusion hle)) fH hfs hfk (fun c x => hfe (Subgroup.inclusion hle c) x)
  rw [← hb]
  try rfl

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_PCB =====
section

/-!
# S4-GOS-C, part PCB: Brauer's formula for the perfect complex `PC`

For `Λ → Λ'` onto with kernel `ϖ Λ` (`ϖ ^ N = 0`, `Λ` finite local, `l ^ n = 0` in `Λ`) and the `H²`-vanishing
inputs of `RedPC`, the reductions `redA`, `red1`, `red2` lift `PC Λ'` to `PC Λ`. **`brauer_PC`**: if every `ρPC Λ' i`
is projective, then for any `Λ'`-representation `τ` on a free finite `M` and any Brauer trace function `β`,
`|Gf| · Σ_i (-1)^i dim (PC Λ' i ⊗ M)_{Gf} = Σ_g chiPC Λ g · β g` in `Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings Representation PerfectCx CurveCoh

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] [Fintype Gf]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type}
  (I : S → Subgroup G) [IsLocalRing Λ] [Nontrivial Λ'] [Finite Λ]
  {M : Type} [AddCommGroup M] [Module Λ' M] [Module Λ M] [IsScalarTower Λ Λ' M] [Module.Free Λ' M]
  [Module.Finite Λ' M]

/-- **Brauer's formula for the perfect complex.** -/
theorem brauer_PC {ϖ : Λ} (hsurj : Function.Surjective (algebraMap Λ Λ')) (ht : algebraMap Λ Λ' ϖ = 0)
    (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = ϖ * s) {N : ℕ} (hϖN : ϖ ^ N = 0) {l n : ℕ} (hl : l.Prime)
    (hΛ : ((l ^ n : ℕ) : Λ) = 0) (hl' : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : Λ'))
    (hall : H2All Λ G Γ l n) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l n) (hπ : IsOpen (π.ker : Set G))
    [hF : ∀ i, Module.Free Λ (PC Λ π Γ I i)] [hT : ∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    [hF' : ∀ i, Module.Free Λ' (PC Λ' π Γ I i)] [hT' : ∀ i, Module.Finite Λ' (PC Λ' π Γ I i)]
    (hρ' : ∀ i, IsProj (ρPC Λ' π Γ I i)) (τ : Representation Λ' Gf M) {β : Gf → Λ} (hβ : IsBeta ϖ l τ β) :
    (Fintype.card Gf : Λ) * ((∑ i ∈ Finset.range 3, (-1 : ℤ) ^ i *
      (Module.finrank Λ' (Coinvariants ((ρPC Λ' π Γ I i).tprod τ)) : ℤ) : ℤ) : Λ) =
      ∑ g, chiPC Λ π Γ I g * β g := by
  classical
  haveI : Module.Free Λ (MonoidAlgebra Λ Gf) := hF 0
  haveI : Module.Finite Λ (MonoidAlgebra Λ Gf) := hT 0
  haveI : Module.Free Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) := hF 1
  haveI : Module.Finite Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) := hT 1
  haveI : Module.Free Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) := hF 2
  haveI : Module.Finite Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) := hT 2
  haveI : Module.Free Λ' (MonoidAlgebra Λ' Gf) := hF' 0
  haveI : Module.Finite Λ' (MonoidAlgebra Λ' Gf) := hT' 0
  haveI : Module.Free Λ' (Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf)) := hF' 1
  haveI : Module.Finite Λ' (Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf)) := hT' 1
  haveI : Module.Free Λ' ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) := hF' 2
  haveI : Module.Finite Λ' ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) := hT' 2
  have h0 : (Fintype.card Gf : Λ) * (Module.finrank Λ' (Coinvariants ((ρPC Λ' π Γ I 0).tprod τ)) : Λ) =
      ∑ g, LinearMap.trace Λ (PC Λ π Γ I 0) (ρPC Λ π Γ I 0 g) * β g :=
    brauer_B2 ϖ hsurj ht hk hϖN hl hΛ hl' (P := MonoidAlgebra Λ Gf) (P' := MonoidAlgebra Λ' Gf)
      (ρP := rRep Λ Gf) (σP := rRep Λ' Gf) (hρ' 0) τ (redA Λ Λ' Gf) (redA_surjective hsurj) (redA_ker hk)
      (fun g x => redA_rRep g x) hβ
  have h1 : (Fintype.card Gf : Λ) * (Module.finrank Λ' (Coinvariants ((ρPC Λ' π Γ I 1).tprod τ)) : Λ) =
      ∑ g, LinearMap.trace Λ (PC Λ π Γ I 1) (ρPC Λ π Γ I 1 g) * β g :=
    brauer_B2 ϖ hsurj ht hk hϖN hl hΛ hl' (P := Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf))
      (P' := Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf)) (ρP := rho1 Λ π Γ S) (σP := rho1 Λ' π Γ S)
      (hρ' 1) τ (red1 Λ Λ' π Γ) (red1_surjective π Γ hsurj hΛ hall hπ) (red1_ker π Γ hk hΛ hall hπ)
      (fun g x => red1_rho1 π Γ g x) hβ
  have h2 : (Fintype.card Gf : Λ) * (Module.finrank Λ' (Coinvariants ((ρPC Λ' π Γ I 2).tprod τ)) : Λ) =
      ∑ g, LinearMap.trace Λ (PC Λ π Γ I 2) (ρPC Λ π Γ I 2 g) * β g :=
    brauer_B2 ϖ hsurj ht hk hϖN hl hΛ hl' (P := (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s))
      (P' := (s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) (ρP := rho2 Λ π Γ I) (σP := rho2 Λ' π Γ I)
      (hρ' 2) τ (red2 Λ Λ' π Γ I) (red2_surjective π Γ I hsurj hΛ hallI hπ) (red2_ker π Γ I hk hΛ hallI hπ)
      (fun g x => red2_rho2 π Γ I g x) hβ
  have hchi : ∀ g, chiPC Λ π Γ I g = LinearMap.trace Λ (PC Λ π Γ I 0) (ρPC Λ π Γ I 0 g) -
      LinearMap.trace Λ (PC Λ π Γ I 1) (ρPC Λ π Γ I 1 g) +
      LinearMap.trace Λ (PC Λ π Γ I 2) (ρPC Λ π Γ I 2 g) := fun g => by
    simp only [chiPC, Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  calc (Fintype.card Gf : Λ) * ((∑ i ∈ Finset.range 3, (-1 : ℤ) ^ i *
        (Module.finrank Λ' (Coinvariants ((ρPC Λ' π Γ I i).tprod τ)) : ℤ) : ℤ) : Λ)
      = (Fintype.card Gf : Λ) * (Module.finrank Λ' (Coinvariants ((ρPC Λ' π Γ I 0).tprod τ)) : Λ) -
        (Fintype.card Gf : Λ) * (Module.finrank Λ' (Coinvariants ((ρPC Λ' π Γ I 1).tprod τ)) : Λ) +
        (Fintype.card Gf : Λ) * (Module.finrank Λ' (Coinvariants ((ρPC Λ' π Γ I 2).tprod τ)) : Λ) := by
        push_cast [Finset.sum_range_succ, Finset.sum_range_zero]
        ring
    _ = ∑ g, chiPC Λ π Γ I g * β g := by
        rw [h0, h1, h2, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun g _ => by rw [hchi g]; ring

end RamanujanPetersson.GOS

end

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

/-- Places of `E` over `k_E` ≃ places over `𝔽_q`. -/
def plKc : Place (Kc Fq E) E ≃ Place Fq E :=
  Equiv.sumCongr (HeightOneSpectrum.equivOfRingEquiv (rfinKcEquiv Fq E))
    (HeightOneSpectrum.equivOfRingEquiv (rinfKcEquiv Fq E))

theorem deg_plKc (P : Place (Kc Fq E) E) :
    (plKc Fq E P).deg = Module.finrank Fq (Kc Fq E) * P.deg := by
  rcases P with P | P
  · exact deg_equivOfRingEquiv (rfinKcEquiv Fq E) P
  · exact deg_equivOfRingEquiv (rinfKcEquiv Fq E) P

/-- **Point counts over the full constant field**: `N_m(E/𝔽_q) = [d ∣ m] d N_{m/d}(E/k_E)`. -/
theorem numPoints_Kc (m : ℕ) : (numPoints Fq E m : ℤ) =
    dil (Module.finrank Fq (Kc Fq E)) (fun j => (numPoints (Kc Fq E) E j : ℤ)) m := by
  classical
  set d := Module.finrank Fq (Kc Fq E) with hd
  by_cases hm : m = 0
  · subst hm
    simp [dil, numPoints]
  by_cases hdm : d ∣ m
  · have hd0 : 0 < d := Module.finrank_pos
    have hmd : m / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm) hd0).ne'
    rw [dil, if_pos hdm, numPoints, dif_neg hm, numPoints, dif_neg hmd]
    push_cast
    rw [Finset.mul_sum]
    refine (Finset.sum_equiv (plKc Fq E) (fun P => ?_) (fun P _ => ?_)).symm
    · rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Set.mem_ofPred_eq, deg_plKc,
        ← hd, Nat.dvd_div_iff_mul_dvd hdm]
    · rw [deg_plKc, ← hd]
      push_cast
      ring
  · rw [dil, if_neg hdm, numPoints, dif_neg hm, Nat.cast_eq_zero]
    refine Finset.sum_eq_zero fun P hP => absurd ?_ hdm
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hP
    exact dvd_trans (finrank_constField_dvd Fq E P) hP

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

/-- `a j = N_j(E/k_E)` for `j > 0`, `a 0 = 2 - 2 g(E/k_E)`. -/
def weilA (j : ℕ) : ℤ := if j = 0 then 2 - 2 * (genusF (Kc Fq E) E : ℤ) else (numPoints (Kc Fq E) E j : ℤ)

/-- The extended affine point counts of `E/𝔽_q`. -/
def weilSeq (m : ℕ) : ℤ :=
  dil (Module.finrank Fq (Kc Fq E)) (weilA Fq E) m -
    ∑ R : HeightOneSpectrum (Rinf Fq E), if Places.deg Fq R ∣ m then (Places.deg Fq R : ℤ) else 0

theorem weilSeq_pos {m : ℕ} (hm : 0 < m) (L : Type) [Field L] [Algebra Fq L] [Finite L]
    (hL : Module.finrank Fq L = m) : weilSeq Fq E m = Nat.card (Rfin Fq E →ₐ[Fq] L) := by
  classical
  subst hL
  have h1 := numPoints_eq_card_algHom Fq E L
  rw [card_algHom_Rinf Fq E L] at h1
  have h2 : dil (Module.finrank Fq (Kc Fq E)) (weilA Fq E) (Module.finrank Fq L) =
      (numPoints Fq E (Module.finrank Fq L) : ℤ) := by
    rw [numPoints_Kc Fq E, dil, dil]
    split_ifs with hdm
    · have hd0 : 0 < Module.finrank Fq (Kc Fq E) := Module.finrank_pos
      have hmd : Module.finrank Fq L / Module.finrank Fq (Kc Fq E) ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd hm hdm) hd0).ne'
      rw [weilA, if_neg hmd]
    · rfl
  have h3 : ∑ R : HeightOneSpectrum (Rinf Fq E),
      (if Places.deg Fq R ∣ Module.finrank Fq L then (Places.deg Fq R : ℤ) else 0) =
      ((∑ P ∈ (finite_deg_dvd_of Fq (fun N hN => piInf_pow_ne_self Fq E hN)
        (Module.finrank_pos (R := Fq) (M := L)).ne').toFinset, Places.deg Fq P : ℕ) : ℤ) := by
    rw [← Finset.sum_filter, Nat.cast_sum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext P
    rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    simp
  rw [weilSeq, h2, h3, h1]
  push_cast
  ring

/-- **The Weil recurrence of the affine point counts.** -/
theorem exists_weil_rec : ∃ D : ℕ, ∃ b : Fin (D + 1) → ℤ, (∀ k, ∑ j, b j * weilSeq Fq E (k + j) = 0) ∧
    ∀ l : ℕ, l.Prime → ¬ l ∣ Fintype.card Fq → ¬ (l : ℤ) ∣ b 0 := by
  classical
  obtain ⟨c, hcard, -, hprod, hN, -, -, -, P0, -, hP0⟩ :=
    CP4a.zeta_RH_FE (Fq := Kc Fq E) (F := E) (constField_eq_bot Fq E)
  have hd0 : 0 < Module.finrank Fq (Kc Fq E) := Module.finrank_pos
  have ha : ∀ j, (weilA Fq E j : ℂ) = 1 + (Fintype.card (Kc Fq E) : ℂ) ^ j - (c.map (· ^ j)).sum := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [weilA, if_pos rfl]
      simp only [pow_zero, Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul, mul_one]
      push_cast
      ring
    · rw [weilA, if_neg hj.ne', Int.cast_natCast, hN j hj]
  obtain ⟨D, b, hb, hbl⟩ := exists_rec_weil_fin hd0 (Fintype.card (Kc Fq E)) (genusF (Kc Fq E) E) c hprod P0 hP0
    (weilA Fq E) ha (fun R : HeightOneSpectrum (Rinf Fq E) => Places.deg Fq R)
    (fun R => Places.deg_pos Fq R) (weilSeq Fq E) (fun m => rfl)
  refine ⟨D, b, hb, fun l hl hlq => hbl l hl fun h => hlq ?_⟩
  rw [Module.card_eq_pow_finrank (K := Fq) (V := Kc Fq E)] at h
  exact hl.dvd_of_dvd_pow h

end WeilE

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_C_GOSF2 =====
section

/-!
# S4-GOS-C, part GOSF2: Grothendieck-Ogg-Shafarevich on `𝔸¹`

`K = 𝔽_q(x)`, `M_f/K` the trivialising cover with group `G ≅ Gf`, `τ` a representation of `Gf` on a finite
`ℤ/l`-module `M` (`l ∤ q`). From `gos_int`, `χ = h²_c - h¹_c` (`chi_eq_h2c_sub_h1c`), `|I_Q| Sw_Q = Σ_j ...`
(`card_mul_swanQ`), the places over `∞` being conjugate (one place of `K` over `∞`) and
`Σ_Q deg Q |I_Q| = |G|` (`χ_c(𝔸¹) = 1`, `chiC_rat`):
**`gos_A1`**: `h²_c(M) - h¹_c(M) = dim M - Sw_{Q₀}(M)` for any place `Q₀ | ∞` of `M_f`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial IsDedekindDomain
open scoped Pointwise

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section GOSF2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {p e : ℕ} [Fact p.Prime] [CharP (RatFunc Fq) p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable [Fintype (BdryS (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq) (Rinf Fq (RatFunc Fq)))]
  [DecidableEq (BdryS (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq) (Rinf Fq (RatFunc Fq)))]
  {Mf : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))} [FiniteDimensional (RatFunc Fq) Mf]
  [IsGalois (RatFunc Fq) Mf] (hM : Mf ∈ unramSet (Rfin Fq (RatFunc Fq)) (RatFunc Fq))
  (hMU : Mf ≤ maxUnram (Rfin Fq (RatFunc Fq)) (RatFunc Fq))
  {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq) →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
  (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)))) (hπs : Function.Surjective π)
  {φ : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)}
  (hφ : IsFrobLift (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq) φ)

/-- `Σ_{Q | ∞} deg Q |I_Q| = |G|` over `𝔽_q(x)`. -/
theorem sum_deg_card_inertia_rat :
    letI := actRinf Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf)
    ∑ Q : HeightOneSpectrum (Rinf Fq Mf), (Places.deg Fq Q : ℚ) * Nat.card (Q.asIdeal.inertia
      (Mf ≃ₐ[RatFunc Fq] Mf)) = Nat.card (Mf ≃ₐ[RatFunc Fq] Mf) := by
  letI := actRinf Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf)
  have h := sum_card_inertia_deg_all Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf)
  rw [sum_deg_rat, mul_one] at h
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  rw [← h']
  exact Finset.sum_congr rfl fun Q _ => mul_comm _ _

/-- All places of `M_f` over `∞` are conjugate. -/
theorem conj_rat (Q0 Q : HeightOneSpectrum (Rinf Fq Mf)) :
    letI := actRinf Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf)
    ∃ σ : Mf ≃ₐ[RatFunc Fq] Mf, σ • Q0.asIdeal = Q.asIdeal := by
  letI := actRinf Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf)
  haveI := isGaloisGroup_rinf Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf)
  have : Algebra.IsInvariant (Rinf Fq (RatFunc Fq)) (Rinf Fq Mf) (Mf ≃ₐ[RatFunc Fq] Mf) :=
    IsGaloisGroup.isInvariant
  have : Algebra.IsIntegral (Rinf Fq (RatFunc Fq)) (Rinf Fq Mf) :=
    Algebra.IsInvariant.isIntegral (Rinf Fq (RatFunc Fq)) (Rinf Fq Mf) (Mf ≃ₐ[RatFunc Fq] Mf)
  exact exists_smul_eq_rinf Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) Q0 Q
    (congrArg HeightOneSpectrum.asIdeal
      (Subsingleton.elim (Q0.under (Rinf Fq (RatFunc Fq))) (Q.under (Rinf Fq (RatFunc Fq)))))

end GOSF2

end

end RamanujanPetersson.GOS


end


