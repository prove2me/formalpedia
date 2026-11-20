-- Prove2me | Definitions.Def_RPLib_F2_069
-- name    : RPLib_F2_069
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T23:24:07.524728+00:00
-- url     : https://prove2.me/theorems/ec276586-35fa-4ade-94e0-3d4f9a52d629
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 069 of 70
-- statement:
--   File 069 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_BlockPt2`: S4-Lefschetz, L3f2b (part 2): `block_count`
--   * `S4.Def_RP_Lefschetz_BlockClose`: S4-Lefschetz, L3f3b: the alternating trace of `γ⁻¹ ∘ F^m` as a sum of block counts
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_068

/-!
# Ramanujan-Petersson curve library (flat edition), file 069 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_BlockPt2`: S4-Lefschetz, L3f2b (part 2): `block_count`
* `S4.Def_RP_Lefschetz_BlockClose`: S4-Lefschetz, L3f3b: the alternating trace of `γ⁻¹ ∘ F^m` as a sum of block counts
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_BlockPt2 =====
section

/-!
# S4-Lefschetz, L3f2b (part 2): `block_count`

For a block `[a]` fixed by `π(φ⁻¹^m) · γ` with block cover `E` (data of `exists_blockCover`):
`Σ_i (-1)^i Tr(P_[a] ∘ ρPC γ⁻¹ ∘ frobPC^m | PC^i) = #(R_E →ₐ[k'_E] k'_E)`, from `block_euler`, `trace_block_H1`
(part 1) and `lefschetz_cover` at `m = 1`, `L = k'_E`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation
open scoped Pointwise

section BlockPt2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- **One fixed block counts the points of its cover**: `Σ_i (-1)^i Tr(P_[a] ρPC γ⁻¹ frobPC^m | PC^i) =
#(R_E →ₐ[k'_E] k'_E)` for the block cover `E` (data as produced by `exists_blockCover`). -/
def block_count (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = l ^ n)
    (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    [Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s).map π)]
    [∀ i, Module.Free (ZMod N) (PC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    [∀ i, Module.Finite (ZMod N) (PC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    (Hr : ResHyp (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia)
    {φ : Pi1 (Rfin Fq K) K}
    (hTW : ∀ s (e : Z1 (regRep (ZMod N) π) (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓
        (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s))),
      (e : ↥(pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s)) →
          MonoidAlgebra (ZMod N) Gf)
        (conjSub (φ⁻¹ * (trueH (bdryInf Fq K) φ⁻¹ s : Pi1 (Rfin Fq K) K))
          (bdry_mem _ _ _ _ _ (trueCompat (bdryInf Fq K) φ⁻¹) s) (Hr.sg s)) =
        (Fintype.card Fq : ZMod N) •
          (e : ↥(pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s)) →
            MonoidAlgebra (ZMod N) Gf) (Hr.sg (trueTau (bdryInf Fq K) φ⁻¹ s)))
    (γ a : Gf) (m : ℕ)
    (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram Fq[X] K) [FiniteDimensional K E]
    [Algebra.IsSeparable K E] (σ : Pi1 (Rfin (Kc Fq E) E) E)
    (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m)
    {c0 : Pi1 (Rfin Fq K) K} (hc0 : c0 ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq))
    (hσ : thetaE Fq K E hE σ = (c0⁻¹ * φ⁻¹ ^ m)⁻¹)
    (hσF : IsFrobLift (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) σ)
    (hHΓ : ∀ x ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq), x ∈ (thetaE Fq K E hE).range ↔ π x = 1)
    (hπg : π (c0⁻¹ * φ⁻¹ ^ m) = a * γ⁻¹ * a⁻¹) :
    ∑ i ∈ Finset.range (2 + 1), (-1 : ZMod N) ^ i *
        LinearMap.trace (ZMod N) _
          (PB (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia
              (blk ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) a) i *
            (ρPC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i γ⁻¹ ∘ₗ
              frobPC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
                (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) i ^ m)) =
      (Nat.card (Rfin (Kc Fq E) E →ₐ[Kc Fq E] Kc Fq E) : ZMod N) := by
  have hlp : l.Prime := Fact.out
  have : IsLocalRing (ZMod N) := by rw [hN]; exact isLocalRing_zmod_pow l n hlp hn
  have : Nonempty (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K)) := nonempty_bdryS (Fq := Fq) (F := K)
  -- the ambient `G' = H ⊔ Γ`, `H = range thetaE`
  have hHo : IsOpen ((thetaE Fq K E hE).range : Set (Pi1 (Rfin Fq K) K)) := isOpen_range_thetaE Fq K E hE
  have hG'o : IsOpen (((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq) :
      Subgroup (Pi1 (Rfin Fq K) K)) : Set (Pi1 (Rfin Fq K) K)) :=
    Subgroup.isOpen_mono le_sup_left hHo
  have : CompactSpace ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq) :
      Subgroup (Pi1 (Rfin Fq K) K)) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ hG'o).isCompact
  have hΓ : pi1geo (Rfin Fq K) K (Fintype.card Fq) ≤
      (thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq) := le_sup_right
  have hH : (thetaE Fq K E hE).range ≤
      (thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq) := le_sup_left
  have hcov' : ∀ x ∈ (thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq),
      ∃ a ∈ (thetaE Fq K E hE).range, ∃ b ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq), x = a * b :=
    hcov'_of_le_sup le_rfl
  have hcov : ∀ y ∈ (thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq),
      ∃ c ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq), y * c⁻¹ ∈ (thetaE Fq K E hE).range := by
    intro y hy
    obtain ⟨a', ha', b, hb, hab⟩ := hcov' y hy
    exact ⟨b, hb, by rw [hab, mul_inv_cancel_right]; exact ha'⟩
  have hR := exists_cosetReps_E Fq K E hE
  obtain ⟨R⟩ := hR
  have hfree := free_h1cSub Fq K E hE hq he l n hN hlq hΓ hH hcov' R
  have : Module.Free (ZMod N) (H1c (σB ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
        (downH (thetaE Fq K E hE).range ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq)))))
      ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).subgroupOf
        ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq)))
      (fun s => ((bdryInf Fq K).inertia s).subgroupOf
        ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq)))) := hfree.1
  have : Module.Finite (ZMod N) (H1c (σB ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
        (downH (thetaE Fq K E hE).range ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq)))))
      ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).subgroupOf
        ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq)))
      (fun s => ((bdryInf Fq K).inertia s).subgroupOf
        ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq)))) := hfree.2
  have hσB := isOpen_ker_coind_triv (((thetaE Fq K E hE).range).subgroupOf
      ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq)))
    ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
      (downH (thetaE Fq K E hE).range ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq))))
    (fun _ => rfl) (isOpen_sub hHo)
  -- the block factorisation `φ⁻¹^m = c0 g`, `g = thetaE σ⁻¹ ∈ H`
  have hgH : c0⁻¹ * φ⁻¹ ^ m ∈ (thetaE Fq K E hE).range := ⟨σ⁻¹, by rw [map_inv, hσ, inv_inv]⟩
  have hψ : φ⁻¹ ^ m = c0 * (c0⁻¹ * φ⁻¹ ^ m) := by group
  have hmem : φ⁻¹ ^ m ∈ (thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq) := by
    rw [hψ]
    exact Subgroup.mul_mem _ (hΓ hc0) (hH hgH)
  have hI' := bdryCompat_sub hΓ ⟨φ⁻¹ ^ m, hmem⟩ _ _
    (bdryCompat_pow (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia
      (trueCompat (bdryInf Fq K) φ⁻¹) m)
  have hEu := block_euler π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia
    ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
      (downH (thetaE Fq K E hE).range ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq))))
    hπ hσB hΓ hHΓ hcov (fun _ => rfl) a Hr γ φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹)
    (trueCompat (bdryInf Fq K) φ⁻¹) (Fintype.card Fq : ZMod N) (trueTw_hD π (bdryInf Fq K) φ⁻¹)
    (trueTw_ht (bdryInf Fq K) φ⁻¹) hTW m hmem hI' hc0 hgH hψ hπg
  have hH1 := trace_block_H1 Fq K hq he N E hE hΓ hH hmem σ hc0 hσ hI'
  -- `lefschetz_cover` at `m = 1`, `L = k'_E`, and its `H²` term
  have hcv := lefschetz_cover Fq K E hE hq he l n hn hN hlq hΓ hH hcov' σ hσF 1 le_rfl (Kc Fq E)
    (Module.finrank_self _)
  have h2' := trace_frobH2c_ind ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
      (downH (thetaE Fq K E hE).range ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq))))
      (fun _ => rfl) (cosetReps_sub hΓ R) (hcov_sub hΓ hH hcov')
      ((upH hH (rangeElt (thetaE Fq K E hE) σ⁻¹) : ((thetaE Fq K E hE).range).subgroupOf
        ((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq))) :
          ↥((thetaE Fq K E hE).range ⊔ pi1geo (Rfin Fq K) K (Fintype.card Fq)))
      (Fintype.card (Kc Fq E) : ZMod N) 1
  -- (flat edition, P1) elaborate `trace_frobH2c_ind` without the expected type and match it to `trH2Sub` with
  -- reducible transparency: the default-transparency check of the same statement took ~70 s of instance unfolding.
  have h2 : trH2Sub Fq K E hE N hH σ⁻¹ (Fintype.card (Kc Fq E) : ZMod N) 1 =
      (Fintype.card (Kc Fq E) : ZMod N) ^ 1 := by
    unfold trH2Sub
    with_reducible exact h2'
  have hc' : (Fintype.card (Kc Fq E) : ZMod N) ^ 1 = (Fintype.card Fq : ZMod N) ^ m := by
    rw [pow_one, hcard, Nat.cast_pow]
  exact hEu.trans (sub_eq_of_tr hH1 hcv h2 hc')

end BlockPt2

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockClose =====
section

/-!
# S4-Lefschetz, L3f3b: the alternating trace of `γ⁻¹ ∘ F^m` as a sum of block counts

`exists_blockCover'`: `exists_blockCover` together with the description `range thetaE = blkH π g ζ hζ` of the
block cover (needed for the point count, L5).

`euler_eq_sum_cover`: `Σ_i (-1)^i Tr(ρPC γ⁻¹ ∘ frobPC^m | PC^i) = Σ_{ω fixed} cnt ω`, where for every block `ω` fixed
by `ω ↦ π(φ⁻¹^m) ω γ`, `cnt ω = #(R_E →ₐ[k'_E] k'_E)` for a block cover `E` of `ω` (all its data exposed).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation

section BlockClose

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- **L3 closure**: the alternating trace of `γ⁻¹ ∘ F^m` on the perfect complex is the sum, over the blocks `ω`
fixed by `ω ↦ π(φ⁻¹^m) ω γ`, of `cnt ω = #(R_E →ₐ[k'_E] k'_E)` for a block cover `E` of `ω`. -/
def euler_eq_sum_cover (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = l ^ n)
    (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    [Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s).map π)]
    [∀ i, Module.Free (ZMod N) (PC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    [∀ i, Module.Finite (ZMod N) (PC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    (Hr : ResHyp (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia)
    {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    (hTW : ∀ s (e : Z1 (regRep (ZMod N) π) (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓
        (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s))),
      (e : ↥(pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s)) →
          MonoidAlgebra (ZMod N) Gf)
        (conjSub (φ⁻¹ * (trueH (bdryInf Fq K) φ⁻¹ s : Pi1 (Rfin Fq K) K))
          (bdry_mem _ _ _ _ _ (trueCompat (bdryInf Fq K) φ⁻¹) s) (Hr.sg s)) =
        (Fintype.card Fq : ZMod N) •
          (e : ↥(pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s)) →
            MonoidAlgebra (ZMod N) Gf) (Hr.sg (trueTau (bdryInf Fq K) φ⁻¹ s)))
    (γ : Gf) {m : ℕ} (hm : 0 < m) :
    ∃ cnt : Blk ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) → ℕ,
      (∀ ω, blkShift ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) (π (φ⁻¹ ^ m)) γ
          (map_mem_normalizer π (φ⁻¹ ^ m)) ω = ω →
        ∃ (a : Gf) (c0 : Pi1 (Rfin Fq K) K) (E : IntermediateField K (AlgebraicClosure K))
          (hE : E ≤ maxUnram Fq[X] K) (_ : FiniteDimensional K E) (_ : Algebra.IsSeparable K E)
          (σ : Pi1 (Rfin (Kc Fq E) E) E),
          blk ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) a = ω ∧
          c0 ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq) ∧ π (c0⁻¹ * φ⁻¹ ^ m) = a * γ⁻¹ * a⁻¹ ∧
          Fintype.card (Kc Fq E) = Fintype.card Fq ^ m ∧ thetaE Fq K E hE σ = (c0⁻¹ * φ⁻¹ ^ m)⁻¹ ∧
          IsFrobLift (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) σ ∧
          (∃ (Nζ : ℕ) (_ : NeZero Nζ) (ζ : maxUnram (Rfin Fq K) K) (hζ : IsPrimitiveRoot ζ Nζ),
            Nζ = (Fintype.card Fq ^ m) ^ Fintype.card Gf - 1 ∧
            ∀ τ, τ ∈ (thetaE Fq K E hE).range ↔ τ ∈ blkH π (c0⁻¹ * φ⁻¹ ^ m) ζ hζ) ∧
          cnt ω = Nat.card (Rfin (Kc Fq E) E →ₐ[Kc Fq E] Kc Fq E)) ∧
      ∑ i ∈ Finset.range (2 + 1), (-1 : ZMod N) ^ i *
          LinearMap.trace (ZMod N) _
            (ρPC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i γ⁻¹ ∘ₗ
              frobPC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
                (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) i ^ m) =
        ∑ ω ∈ Finset.univ.filter (fun ω => blkShift ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)
            (π (φ⁻¹ ^ m)) γ (map_mem_normalizer π (φ⁻¹ ^ m)) ω = ω), (cnt ω : ZMod N) := by
  have key : ∀ ω, blkShift ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) (π (φ⁻¹ ^ m)) γ
      (map_mem_normalizer π (φ⁻¹ ^ m)) ω = ω →
    ∃ c : ℕ, (∃ (a : Gf) (c0 : Pi1 (Rfin Fq K) K) (E : IntermediateField K (AlgebraicClosure K))
          (hE : E ≤ maxUnram Fq[X] K) (_ : FiniteDimensional K E) (_ : Algebra.IsSeparable K E)
          (σ : Pi1 (Rfin (Kc Fq E) E) E),
          blk ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) a = ω ∧
          c0 ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq) ∧ π (c0⁻¹ * φ⁻¹ ^ m) = a * γ⁻¹ * a⁻¹ ∧
          Fintype.card (Kc Fq E) = Fintype.card Fq ^ m ∧ thetaE Fq K E hE σ = (c0⁻¹ * φ⁻¹ ^ m)⁻¹ ∧
          IsFrobLift (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) σ ∧
          (∃ (Nζ : ℕ) (_ : NeZero Nζ) (ζ : maxUnram (Rfin Fq K) K) (hζ : IsPrimitiveRoot ζ Nζ),
            Nζ = (Fintype.card Fq ^ m) ^ Fintype.card Gf - 1 ∧
            ∀ τ, τ ∈ (thetaE Fq K E hE).range ↔ τ ∈ blkH π (c0⁻¹ * φ⁻¹ ^ m) ζ hζ) ∧
          c = Nat.card (Rfin (Kc Fq E) E →ₐ[Kc Fq E] Kc Fq E)) ∧
      ∑ i ∈ Finset.range (2 + 1), (-1 : ZMod N) ^ i *
        LinearMap.trace (ZMod N) _
          (PB (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia ω i *
            (ρPC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i γ⁻¹ ∘ₗ
              frobPC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
                (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) i ^ m)) =
        (c : ZMod N) := by
    intro ω hω
    have hsurj := blk_surjective ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) ω
    obtain ⟨a, rfl⟩ := hsurj
    have hfix := (blkShift_fixed_iff ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) (π (φ⁻¹ ^ m)) γ
      (map_mem_normalizer π (φ⁻¹ ^ m)) a).1 hω
    have h0 := exists_block_c0 π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) hfix
    obtain ⟨c0, hc0, -, hπg⟩ := h0
    have h1 := exists_blockCover' Fq K hq he hφ π hπ hm hc0
    obtain ⟨E, hE, hfd, hsep, σ, hcard, hσ, hσF, hHΓ, hζ⟩ := h1
    have hb := block_count Fq K hq he l n hn hN hlq π hπ Hr hTW γ a m E hE σ hcard hc0 hσ hσF hHΓ hπg
    exact ⟨_, ⟨a, c0, E, hE, hfd, hsep, σ, rfl, hc0, hπg, hcard, hσ, hσF, hζ, rfl⟩, hb⟩
  let cnt : Blk ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) → ℕ := fun ω =>
    if hω : blkShift ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) (π (φ⁻¹ ^ m)) γ
      (map_mem_normalizer π (φ⁻¹ ^ m)) ω = ω then (key ω hω).choose else 0
  have hc : ∀ ω (hω : blkShift ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) (π (φ⁻¹ ^ m)) γ
      (map_mem_normalizer π (φ⁻¹ ^ m)) ω = ω), cnt ω = (key ω hω).choose := fun ω hω => dif_pos hω
  have hEu := euler_eq_sum_fixed (Λ := ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
      (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) γ m
  refine ⟨cnt, fun ω hω => ?_, hEu.trans (Finset.sum_congr rfl fun ω hω => ?_)⟩
  · have hs := (key ω hω).choose_spec.1
    rw [hc ω hω]
    exact hs
  · have hω' := (Finset.mem_filter.1 hω).2
    exact (key ω hω').choose_spec.2.trans (congrArg Nat.cast (hc ω hω').symm)

end BlockClose

end

end Lefschetz
end RamanujanPetersson


end


