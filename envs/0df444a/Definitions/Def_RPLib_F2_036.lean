-- Prove2me | Definitions.Def_RPLib_F2_036
-- name    : RPLib_F2_036
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T12:59:39.716006+00:00
-- url     : https://prove2.me/theorems/4dba2270-6ab7-47e9-8322-5a883b5f890a
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 036 of 70
-- statement:
--   File 036 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_BlockE2`: S4-Lefschetz, L3d3b part 2: the constant field and the Frobenius of the block cover `E`
--   * `S4.Def_RP_Lefschetz_BlockCov`: S4-Lefschetz, L3f2a: block data in the `Rfin` chart
--   * `S4.Def_RP_Lefschetz_ConeEuler`: S4-Lefschetz, L3e2a: Euler characteristic of the cone Frobenius
--   * `S4.Def_RP_Lefschetz_BlockLef`: S4-Lefschetz, L3f1: the Euler characteristic of one fixed block
--   * `S4.Def_RP_Lefschetz_FrobSpec`: S4-Lefschetz, L4h part 3: Frobenius data at the boundary
--   * `S4.Def_RP_Lefschetz_H2Sh`: S4-Lefschetz, L4i3: `H²_c` of an induced trivial module
--   * `S4.Def_RP_Lefschetz_PtLift`: S4-Lefschetz, L5c4a: the block count through `π₁(U)` (generic), block subgroup lemmas, open fixers
--   * `S4.Def_RP_Lefschetz_CurveTr1`: S4-Lefschetz, L4i part 2a: `π₁(E)` and `π₁^geo(E)` inside `π₁(U)` as topological groups
--   * `S4.Def_RP_Lefschetz_CurveTr2`: S4-Lefschetz, L4i part 2b: Frobenius traces on `H¹_c` of a cover `E ⊆ K_U` inside `π₁(U)`
--   * `S4.Def_RP_Lefschetz_SubFrob`: S4-Lefschetz, L3e2b: the block Frobenius on `H¹_c` of an open subgroup is the canonical one
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_035

/-!
# Ramanujan-Petersson curve library (flat edition), file 036 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_BlockE2`: S4-Lefschetz, L3d3b part 2: the constant field and the Frobenius of the block cover `E`
* `S4.Def_RP_Lefschetz_BlockCov`: S4-Lefschetz, L3f2a: block data in the `Rfin` chart
* `S4.Def_RP_Lefschetz_ConeEuler`: S4-Lefschetz, L3e2a: Euler characteristic of the cone Frobenius
* `S4.Def_RP_Lefschetz_BlockLef`: S4-Lefschetz, L3f1: the Euler characteristic of one fixed block
* `S4.Def_RP_Lefschetz_FrobSpec`: S4-Lefschetz, L4h part 3: Frobenius data at the boundary
* `S4.Def_RP_Lefschetz_H2Sh`: S4-Lefschetz, L4i3: `H²_c` of an induced trivial module
* `S4.Def_RP_Lefschetz_PtLift`: S4-Lefschetz, L5c4a: the block count through `π₁(U)` (generic), block subgroup lemmas, open fixers
* `S4.Def_RP_Lefschetz_CurveTr1`: S4-Lefschetz, L4i part 2a: `π₁(E)` and `π₁^geo(E)` inside `π₁(U)` as topological groups
* `S4.Def_RP_Lefschetz_CurveTr2`: S4-Lefschetz, L4i part 2b: Frobenius traces on `H¹_c` of a cover `E ⊆ K_U` inside `π₁(U)`
* `S4.Def_RP_Lefschetz_SubFrob`: S4-Lefschetz, L3e2b: the block Frobenius on `H¹_c` of an open subgroup is the canonical one
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_BlockE2 =====
section

/-!
# S4-Lefschetz, L3d3b part 2: the constant field and the Frobenius of the block cover `E`

For an open `H ≤ π₁(U)` with cover `E` (`exists_E_of_open`) containing `g` with `g⁻¹ x = x^(q^m)` on constants,
fixing every `y` with `y^(q^m) = y`, and a primitive `(q^m - 1)`-th root of unity in `K_U`:
`card_Kc_block`: the full constant field of `E` has `q^m` elements; `exists_frobE`: `g⁻¹ = thetaE σ` for a
Frobenius lift `σ` of `E` over its constant field.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a

section BlockE2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

include hE in
/-- **The constant field of the block cover**: `#k'_E = q^m`. -/
theorem card_Kc_block (H : Subgroup (Pi1 (Rfin Fq K) K))
    (hfixH : ∀ τ ∈ H, ∀ y : maxUnram (Rfin Fq K) K, (y : AlgebraicClosure K) ∈ E → τ y = y)
    (hfixE : ∀ y : maxUnram (Rfin Fq K) K, (∀ τ ∈ H, τ y = y) → (y : AlgebraicClosure K) ∈ E)
    {g : Pi1 (Rfin Fq K) K} (hgH : g ∈ H) {m : ℕ} (hm : 0 < m)
    (hg : ∀ x : maxUnram (Rfin Fq K) K, IsConst (Fintype.card Fq) x → g⁻¹ x = x ^ (Fintype.card Fq ^ m))
    (hHfix : ∀ τ ∈ H, ∀ y : maxUnram (Rfin Fq K) K, y ^ (Fintype.card Fq ^ m) = y → τ y = y)
    (z : maxUnram (Rfin Fq K) K) (hz : IsPrimitiveRoot z (Fintype.card Fq ^ m - 1)) :
    Fintype.card (Kc Fq E) = Fintype.card Fq ^ m := by
  have hB := card_Kc_le_block Fq K E hm (kc_pow_fix Fq K E hE H hfixH hgH hg)
  have hC := dvd_finrank_Kc_block Fq K E H hfixE hm hHfix z hz
  have hf0 := finrank_Kc_pos Fq E
  rw [card_Kc_eq_pow Fq E] at hB ⊢
  exact le_antisymm hB (Nat.pow_le_pow_right Fintype.card_pos (Nat.le_of_dvd hf0 hC))

/-- **The Frobenius of the block cover**: `g⁻¹ = thetaE σ` with `σ` a Frobenius lift of `E` over `k'_E`. -/
theorem exists_frobE (H : Subgroup (Pi1 (Rfin Fq K) K))
    (hrange : ∀ τ, τ ∈ (thetaE Fq K E hE).range ↔ τ ∈ H)
    {g : Pi1 (Rfin Fq K) K} (hgH : g ∈ H) {m : ℕ} (hm : 0 < m)
    (hg : ∀ x : maxUnram (Rfin Fq K) K, IsConst (Fintype.card Fq) x → g⁻¹ x = x ^ (Fintype.card Fq ^ m))
    (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m) :
    ∃ σ : Pi1 (Rfin (Kc Fq E) E) E, thetaE Fq K E hE σ = g⁻¹ ∧
      IsFrobLift (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) σ := by
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.1 ((hrange g⁻¹).2 (H.inv_mem hgH))
  refine ⟨σ, hσ, ?_⟩
  rw [← thetaE_isFrobLift_iff Fq K E hE, hσ, hcard]
  exact fun x hx => hg x ((isConst_pow_iff (Fintype.card Fq) hm x).1 hx)

end BlockE2

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockCov =====
section

/-!
# S4-Lefschetz, L3f2a: block data in the `Rfin` chart

`coind_triv_eq_one` / `isOpen_ker_coind_triv`: the coinduced trivial representation from an open subgroup of a compact
group has open kernel. `isLocalRing_zmod_pow`: `ℤ/l^n` is local. `exists_block_c0`: a fixed block gives
`ψ^m = c0 g` with `c0 ∈ Γ`, `π g = a γ⁻¹ a⁻¹`. `exists_blockCover`: for `g = c0⁻¹ φ⁻¹^m` the cover `E` with
`#k'_E = q^m`, a Frobenius lift `σ` of `E` with `thetaE σ = g⁻¹`, and `x ∈ range thetaE ↔ π x = 1` on `Γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a Representation

section CoindKer

variable {k G' : Type} [CommRing k] [Group G'] (U : Subgroup G') (σH : Representation k U k) (hσ : ∀ h, σH h = 1)

end CoindKer

section BlockCover

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
/-- **The block cover**: for `g = c0⁻¹ φ⁻¹^m` (`c0 ∈ Γ`), a finite separable `E ⊆ K_U` with `#k'_E = q^m`,
`thetaE σ = g⁻¹` for a Frobenius lift `σ` of `E`, and `x ∈ range thetaE ↔ π x = 1` for `x ∈ Γ`. -/
theorem exists_blockCover {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K))) {m : ℕ} (hm : 0 < m) {c0 : Pi1 (Rfin Fq K) K}
    (hc0 : c0 ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram Fq[X] K) (_ : FiniteDimensional K E)
      (_ : Algebra.IsSeparable K E) (σ : Pi1 (Rfin (Kc Fq E) E) E),
      Fintype.card (Kc Fq E) = Fintype.card Fq ^ m ∧ thetaE Fq K E hE σ = (c0⁻¹ * φ⁻¹ ^ m)⁻¹ ∧
      IsFrobLift (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) σ ∧
      (∀ x ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq), x ∈ (thetaE Fq K E hE).range ↔ π x = 1) := by
  have hq2 : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  have hg := ginv_apply hφ hc0 m
  obtain ⟨ζ, hζ⟩ := exists_zeta_level (Fq := Fq) (F := K) he (m * Fintype.card Gf)
    (Nat.mul_pos hm Fintype.card_pos)
  rw [← hq, pow_mul] at hζ
  have h1 : 1 < (Fintype.card Fq ^ m) ^ Fintype.card Gf :=
    Nat.one_lt_pow Fintype.card_pos.ne' (Nat.one_lt_pow hm.ne' hq2)
  have : NeZero ((Fintype.card Fq ^ m) ^ Fintype.card Gf - 1) := ⟨Nat.sub_ne_zero_of_lt h1⟩
  obtain ⟨z, hz⟩ := exists_zeta_level (Fq := Fq) (F := K) he m hm
  rw [← hq] at hz
  obtain ⟨E, hE, hfd, hsep, hrange, hfixH, hfixE⟩ :=
    exists_E_of_open Fq K (blkH π (c0⁻¹ * φ⁻¹ ^ m) ζ hζ) (isOpen_blkH π _ ζ hζ hπ)
  have hgH := g_mem_blkH π (c0⁻¹ * φ⁻¹ ^ m) ζ hζ
  have hcard := card_Kc_block Fq K E hE _ hfixH hfixE hgH hm hg
    (fun τ hτ y hy => blkH_fix π _ ζ hq2 hm hg hζ hτ hy) z hz
  obtain ⟨σ, hσ, hσF⟩ := exists_frobE Fq K E hE _ hrange hgH hm hg hcard
  exact ⟨E, hE, hfd, hsep, σ, hcard, hσ, hσF,
    fun x hx => (hrange x).trans (mem_blkH_geo_iff π _ ζ hq2 hm hg hζ hx)⟩

end BlockCover

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ConeEuler =====
section

/-!
# S4-Lefschetz, L3e2a: Euler characteristic of the cone Frobenius

For the cone `K(M) = [M → Z¹(Γ; M) × M^S → Π_s Z¹(Γ ⊓ I s; M)]` (`cx0`, `cx1`) with its Frobenius
(`ρ ψ`, `frob1`, `frob2`): `H¹` of the cone in the form of `Def_RP_Lefschetz_Euler` is `H¹_c` (`hc1Equiv`), and over a
local ring with free finite terms, `H¹_c` and `H²(K)`:
* `cone_euler`: `Tr(F | K⁰) - Tr(F | K¹) + Tr(F | K²) = Tr(frobH2K) - Tr(frobH1c)`;
* `cone_euler_tri`: the same as `Σ_{i<3} (-1)^i Tr(triMap .. i)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G) {S : Type}
  (I : S → Subgroup G) (hρ : IsOpen (ρ.ker : Set G))

theorem cx1_cx0 (m : M) : cx1 ρ Γ I hρ (cx0 ρ Γ S hρ m) = 0 :=
  LinearMap.congr_fun (cx1_comp_cx0 ρ Γ I hρ) m

/-- `H¹ = ker d¹ / im d⁰` of the cone is `H¹_c`. -/
def hc1Equiv : Hc1 (cx0 ρ Γ S hρ) (cx1 ρ Γ I hρ) (cx1_cx0 ρ Γ I hρ) ≃ₗ[k] H1c ρ Γ I :=
  (Submodule.Quotient.equiv _ _ (kerEquivZ1c ρ Γ I hρ) (by
    rw [cx0c, LinearMap.range_comp]
    rfl)).trans (h1Equiv ρ Γ I hρ)

variable [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ)

/-- **Euler characteristic of the cone Frobenius.** -/
theorem cone_euler [IsLocalRing k] [Nonempty S] [Module.Free k M] [Module.Finite k M]
    [Module.Free k (Z1 ρ Γ × (S → M))] [Module.Finite k (Z1 ρ Γ × (S → M))]
    [Module.Free k ((s : S) → Z1 ρ (Γ ⊓ I s))] [Module.Finite k ((s : S) → Z1 ρ (Γ ⊓ I s))]
    [Module.Free k (H1c ρ Γ I)] [Module.Finite k (H1c ρ Γ I)]
    [Module.Free k (H2K ρ Γ I hρ)] [Module.Finite k (H2K ρ Γ I hρ)] (hI : BdryCompat Γ I ψ t h) :
    LinearMap.trace k M (ρ ψ) - LinearMap.trace k _ (frob1 ρ Γ ψ t h) +
        LinearMap.trace k _ (frob2 ρ Γ I ψ t h hI) =
      LinearMap.trace k _ (frobH2K ρ Γ I ψ t h hρ hI) - LinearMap.trace k _ (frobH1c ρ Γ I ψ t h hI) := by
  have h0 : ∀ x, frob1 ρ Γ ψ t h (cx0 ρ Γ S hρ x) = cx0 ρ Γ S hρ (ρ ψ x) := fun x =>
    (LinearMap.congr_fun (cx0_frob ρ Γ ψ t h hρ) x).symm
  have h1 : ∀ x, frob2 ρ Γ I ψ t h hI (cx1 ρ Γ I hρ x) = cx1 ρ Γ I hρ (frob1 ρ Γ ψ t h x) := fun x =>
    (LinearMap.congr_fun (cx1_frob ρ Γ I ψ t h hρ hI) x).symm
  have : Module.Free k (Hc1 (cx0 ρ Γ S hρ) (cx1 ρ Γ I hρ) (cx1_cx0 ρ Γ I hρ)) :=
    Module.Free.of_equiv (hc1Equiv ρ Γ I hρ).symm
  have : Module.Finite k (Hc1 (cx0 ρ Γ S hρ) (cx1 ρ Γ I hρ) (cx1_cx0 ρ Γ I hρ)) :=
    Module.Finite.equiv (hc1Equiv ρ Γ I hρ).symm
  rw [euler3 (cx1_cx0 ρ Γ I hρ) (cx0_injective ρ Γ S hρ) h0 h1]
  exact congrArg₂ (· - ·) rfl
    (trace_intw (hc1Equiv ρ Γ I hρ) fun v => Submodule.Quotient.induction_on _ v fun _ => rfl)

/-- `cone_euler` as an alternating sum over the `Tri` family. -/
theorem cone_euler_tri [IsLocalRing k] [Nonempty S] [Module.Free k M] [Module.Finite k M]
    [Module.Free k (Z1 ρ Γ × (S → M))] [Module.Finite k (Z1 ρ Γ × (S → M))]
    [Module.Free k ((s : S) → Z1 ρ (Γ ⊓ I s))] [Module.Finite k ((s : S) → Z1 ρ (Γ ⊓ I s))]
    [Module.Free k (H1c ρ Γ I)] [Module.Finite k (H1c ρ Γ I)]
    [Module.Free k (H2K ρ Γ I hρ)] [Module.Finite k (H2K ρ Γ I hρ)] (hI : BdryCompat Γ I ψ t h) :
    ∑ i ∈ Finset.range (2 + 1), (-1 : k) ^ i *
        LinearMap.trace k _ (triMap (ρ ψ) (frob1 ρ Γ ψ t h) (frob2 ρ Γ I ψ t h hI) i) =
      LinearMap.trace k _ (frobH2K ρ Γ I ψ t h hρ hI) - LinearMap.trace k _ (frobH1c ρ Γ I ψ t h hI) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, one_mul,
    neg_one_mul, neg_one_sq, one_mul, ← sub_eq_add_neg]
  exact cone_euler ρ Γ I hρ ψ t h hI

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockLef =====
section

/-!
# S4-Lefschetz, L3f1: the Euler characteristic of one fixed block

For a block `ω = [a]` of `Gf` fixed by `π(ψ^m) · γ` with `ψ^m = c0 g` (`c0 ∈ Γ`, `g ∈ H`, `π g = a γ⁻¹ a⁻¹`):
the alternating trace of `P_ω ∘ ρPC γ⁻¹ ∘ frobPC^m` on the total perfect complex equals `c^m - Tr(F | H¹_c)` of the
`G'`-cone with coefficients `coind_{H ∩ G'}^{G'} σH` (`block_euler`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx MonoidAlgebra Representation

section BlockEuler

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S]
  (I : S → Subgroup G) [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  {H G' : Subgroup G} (σH : Representation Λ (H.subgroupOf G') Λ) (hπ : IsOpen (π.ker : Set G))
  (hσB : IsOpen ((σB σH).ker : Set G'))
  (hΓ : Γ ≤ G') (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
  (hσ : ∀ h, σH h = 1) (a : Gf)

include hHΓ hcov hσ in
/-- `Tr(P_ω ∘ ρPC γ⁻¹ ∘ frobPC^m | PC^i)` is the trace of the `G'`-cone Frobenius at `ψ^m`. -/
theorem trace_block_pow [IsLocalRing Λ] [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (γ : Gf) (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (m : ℕ) (hmem : ψ ^ m ∈ G')
    (hI' : BdryCompat (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') (⟨ψ ^ m, hmem⟩ : G') t^[m]
      (fun s => liftΓh hΓ (hpow Γ ψ t h m s)))
    {c0 g : G} (hc0 : c0 ∈ Γ) (hg : g ∈ H) (hψ : ψ ^ m = c0 * g) (hπg : π g = a * γ⁻¹ * a⁻¹) (i : ℕ) :
    LinearMap.trace Λ _ (PB Λ π Γ I (blk (Γ.map π) a) i * (ρPC Λ π Γ I i γ⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI i ^ m)) =
      LinearMap.trace Λ _ (frobKN Γ I σH (⟨ψ ^ m, hmem⟩ : G') t^[m] (fun s => liftΓh hΓ (hpow Γ ψ t h m s)) hI' i) := by
  have : ∀ i, Module.Free Λ (KN Γ I σH i) := KN_free π Γ I σH hΓ hHΓ hcov hσ a
  have : ∀ i, Module.Finite Λ (KN Γ I σH i) := KN_finite π Γ I σH hΓ hHΓ hcov hσ a
  rw [frobPC_pow π Γ I hI m i]
  exact trace_block_eq π Γ I σH hΓ hHΓ hcov hσ a (⟨ψ ^ m, hmem⟩ : G') t^[m] (hpow Γ ψ t h m)
    (bdryCompat_pow Γ I hI m) hI' hc0 hg hψ hπg i

include hπ hσB hHΓ hcov hσ in
/-- **Euler characteristic of a fixed block**: `Σ_i (-1)^i Tr(P_ω ρPC γ⁻¹ frobPC^m | PC^i) = c^m - Tr(F | H¹_c(G'))`. -/
theorem block_euler [IsLocalRing Λ] [Nonempty S] [∀ i, Module.Free Λ (PC Λ π Γ I i)]
    [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    [Module.Free Λ (H1c (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G'))]
    [Module.Finite Λ (H1c (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G'))]
    (Hr : ResHyp Λ π Γ I) (γ : Gf) (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (c : Λ)
    (hD : ∀ s d, d ∈ (Γ ⊓ I (t s)).map π ↔ π (ψ * h s) * d * (π (ψ * h s))⁻¹ ∈ (Γ ⊓ I s).map π)
    (ht : Function.Bijective t)
    (hTW : ∀ s (e : Z1 (regRep Λ π) (Γ ⊓ I (t s))),
      (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) (Hr.sg s)) =
        c • (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (Hr.sg (t s)))
    (m : ℕ) (hmem : ψ ^ m ∈ G')
    (hI' : BdryCompat (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') (⟨ψ ^ m, hmem⟩ : G') t^[m]
      (fun s => liftΓh hΓ (hpow Γ ψ t h m s)))
    {c0 g : G} (hc0 : c0 ∈ Γ) (hg : g ∈ H) (hψ : ψ ^ m = c0 * g) (hπg : π g = a * γ⁻¹ * a⁻¹) :
    ∑ i ∈ Finset.range (2 + 1), (-1 : Λ) ^ i *
        LinearMap.trace Λ _ (PB Λ π Γ I (blk (Γ.map π) a) i *
          (ρPC Λ π Γ I i γ⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI i ^ m)) =
      c ^ m - LinearMap.trace Λ _ (frobH1c (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G')
        (⟨ψ ^ m, hmem⟩ : G') t^[m] (fun s => liftΓh hΓ (hpow Γ ψ t h m s)) hI') := by
  have : Module.Free Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) := h2K_free hπ Hr
  have : Module.Finite Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) := h2K_finite hπ Hr
  have := h2KN_free π Γ I σH hπ hσB hΓ hHΓ hcov hσ a
  have := h2KN_finite π Γ I σH hπ hσB hΓ hHΓ hcov hσ a
  have : Module.Free Λ (NB σH) := KN_free π Γ I σH hΓ hHΓ hcov hσ a 0
  have : Module.Finite Λ (NB σH) := KN_finite π Γ I σH hΓ hHΓ hcov hσ a 0
  have : Module.Free Λ (Z1 (σB σH) (Γ.subgroupOf G') × (S → NB σH)) := KN_free π Γ I σH hΓ hHΓ hcov hσ a 1
  have : Module.Finite Λ (Z1 (σB σH) (Γ.subgroupOf G') × (S → NB σH)) :=
    KN_finite π Γ I σH hΓ hHΓ hcov hσ a 1
  have : Module.Free Λ ((s : S) → Z1 (σB σH) (Γ.subgroupOf G' ⊓ (I s).subgroupOf G')) :=
    KN_free π Γ I σH hΓ hHΓ hcov hσ a 2
  have : Module.Finite Λ ((s : S) → Z1 (σB σH) (Γ.subgroupOf G' ⊓ (I s).subgroupOf G')) :=
    KN_finite π Γ I σH hΓ hHΓ hcov hσ a 2
  have e2 : ∑ i ∈ Finset.range (2 + 1), (-1 : Λ) ^ i *
        LinearMap.trace Λ _ (PB Λ π Γ I (blk (Γ.map π) a) i *
          (ρPC Λ π Γ I i γ⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI i ^ m)) =
      ∑ i ∈ Finset.range (2 + 1), (-1 : Λ) ^ i *
        LinearMap.trace Λ _ (frobKN Γ I σH (⟨ψ ^ m, hmem⟩ : G') t^[m]
          (fun s => liftΓh hΓ (hpow Γ ψ t h m s)) hI' i) :=
    Finset.sum_congr rfl fun i _ => by
      rw [trace_block_pow π Γ I σH hΓ hHΓ hcov hσ a γ ψ t h hI m hmem hI' hc0 hg hψ hπg i]
  have e3 := cone_euler_tri (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') hσB
    (⟨ψ ^ m, hmem⟩ : G') t^[m] (fun s => liftΓh hΓ (hpow Γ ψ t h m s)) hI'
  have e4 := trace_h2_block π Γ I σH hπ hσB hΓ hHΓ hcov hσ a (⟨ψ ^ m, hmem⟩ : G') t^[m] (hpow Γ ψ t h m)
    (bdryCompat_pow Γ I hI m) hI' hc0 hg hψ hπg
  have e5 := trace_h2_tot_blk hπ Hr γ ψ t h hI c hD ht hTW a m (hfix_of_block π Γ a hc0 hψ hπg)
  rw [e2]
  exact e3.trans (congrArg (fun x => x - LinearMap.trace Λ _ (frobH1c (σB σH) (Γ.subgroupOf G')
    (fun s => (I s).subgroupOf G') (⟨ψ ^ m, hmem⟩ : G') t^[m] (fun s => liftΓh hΓ (hpow Γ ψ t h m s)) hI'))
    (e4.symm.trans e5))

end BlockEuler

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_FrobSpec =====
section

/-!
# S4-Lefschetz, L4h part 3: Frobenius data at the boundary

For boundary data `D` (points `P s` of the pro-chart, inertia `D.inertia s`):
* `FrobSpec D ψ τ h`: `ψ⁻¹ • P s = h_s • P (τ s)` (the defining property of `trueTau`/`trueH`);
  `frobSpec_true`, `frobSpec_compat` (gives `BdryCompat`), `frobSpec_mul_geo`, `frobSpec_pow` (with `hpow`);
* `frobSpec_disj`, `frobSpec_unique` (geometric stabilisers of boundary points lie in inertia);
  `frobH1c_eq_true`: the Frobenius on `H¹_c` of any `FrobSpec` datum is the one of `trueTau`/`trueH`;
* `geoLift`, `gen_frobMatch`, `gen_bdryCompat`: for a cover (ShapGen setting of `Def_RP_Lefschetz_ShapData`), Frobenius
  data on the cover and on the base satisfy `FrobMatch` (the hypothesis of `shapiroH1c_frob`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh CP4a

noncomputable section

section Spec

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  {q : ℕ} {S : Type} (D : BdryData A K q R0 S)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- If `a • P s = b • P s'` with `a, b` geometric, then `s' = s` and `b⁻¹ a` lies in the inertia at `s`. -/
theorem frobSpec_disj (hstabD : ∀ s, ∀ σ ∈ pi1geo A K q, σ • D.P s = D.P s → σ ∈ D.inertia s)
    {a b : Pi1 A K} {s s' : S} (ha : a ∈ pi1geo A K q) (hb : b ∈ pi1geo A K q)
    (he : a • D.P s = b • D.P s') : s' = s ∧ b⁻¹ * a ∈ D.inertia s := by
  have hg : b⁻¹ * a ∈ pi1geo A K q := (pi1geo A K q).mul_mem ((pi1geo A K q).inv_mem hb) ha
  have key : D.P s' = (b⁻¹ * a) • D.P s := by
    calc D.P s' = b⁻¹ • (b • D.P s') := (inv_smul_smul b (D.P s')).symm
      _ = b⁻¹ • (a • D.P s) := by rw [he]
      _ = _ := (mul_smul b⁻¹ a (D.P s)).symm
  have hss : s = s' := D.disj s s' _ hg key
  refine ⟨hss.symm, hstabD s _ hg ?_⟩
  rw [← key, hss]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- Uniqueness of Frobenius data up to inertia. -/
theorem frobSpec_unique (hstabD : ∀ s, ∀ σ ∈ pi1geo A K q, σ • D.P s = D.P s → σ ∈ D.inertia s)
    {ψ : Pi1 A K} {τ τ' : S → S} {h h' : S → pi1geo A K q} (hS : FrobSpec D ψ τ h)
    (hS' : FrobSpec D ψ τ' h') :
    τ' = τ ∧ ∀ s, (((h s)⁻¹ * h' s : pi1geo A K q) : Pi1 A K) ∈ D.inertia (τ s) := by
  have key : ∀ s, τ' s = τ s ∧ ((h' s : Pi1 A K))⁻¹ * (h s : Pi1 A K) ∈ D.inertia (τ s) := fun s =>
    frobSpec_disj D hstabD (h s).2 (h' s).2 ((hS s).symm.trans (hS' s))
  refine ⟨funext fun s => (key s).1, fun s => ?_⟩
  have h1 := (D.inertia (τ s)).inv_mem (key s).2
  rw [mul_inv_rev, inv_inv] at h1
  exact h1

end Spec

section Match

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
variable {A' K' R0' : Type} [CommRing A'] [Field K'] [Algebra A' K'] [CommRing R0'] [Algebra R0' K']
  [Algebra R0' (maxUnram A' K')] [IsScalarTower R0' K' (maxUnram A' K')]
variable {q q' : ℕ} {S T : Type} (D : BdryData A K q R0 S) (D' : BdryData A' K' q' R0' T)
  (f : proChart A K R0 ≃+* proChart A' K' R0')
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q) (hD'B : ∀ Q, D'.B Q ↔ IsBdryPrime A' K' R0' Q)
  (r : Pi1 A' K' →* Pi1 A K) (hf : ∀ σ x, f (r σ • x) = σ • f x)
  (hgeo : ∀ σ, r σ ∈ pi1geo A K q ↔ σ ∈ pi1geo A' K' q')

/-- Geometric correcting elements of the cover, as elements of `Γ ∩ H`. -/
def geoLift (h'' : T → pi1geo A' K' q') (t : T) : geoU (pi1geo A K q) r.range :=
  ⟨⟨r (h'' t), MonoidHom.mem_range.2 ⟨_, rfl⟩⟩, Subgroup.mem_subgroupOf.2 ((hgeo _).2 (h'' t).2)⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
include hf in
/-- Frobenius data on the base (`r ψ'`) and on the cover (`ψ'`) match. -/
theorem gen_frobMatch (hstabD : ∀ s, ∀ σ ∈ pi1geo A K q, σ • D.P s = D.P s → σ ∈ D.inertia s)
    (ψ' : Pi1 A' K') {τ : S → S} {h : S → pi1geo A K q} {τ' : T → T} {h'' : T → pi1geo A' K' q'}
    (hS : FrobSpec D (r ψ') τ h) (hS' : FrobSpec D' ψ' τ' h'') :
    FrobMatch (pi1geo A K q) r.range D.inertia (gπ D D' f hDB hD'B) (gxT D D' f hDB hD'B)
      (rangeElt r ψ') τ h τ' (geoLift r hgeo h'') := by
  intro t
  have e3 : (ψ'⁻¹ • D'.P t).comap f =
      (r ψ')⁻¹ • ((gxT D D' f hDB hD'B t : Pi1 A K) • D.P (gπ D D' f hDB hD'B t)) := by
    rw [comap_smul_equiv f r hf, gxT_spec D D' f hDB hD'B t, map_inv]
  have e4 : (ψ'⁻¹ • D'.P t).comap f =
      r (h'' t) • ((gxT D D' f hDB hD'B (τ' t) : Pi1 A K) • D.P (gπ D D' f hDB hD'B (τ' t))) := by
    rw [hS' t, comap_smul_equiv f r hf, gxT_spec D D' f hDB hD'B (τ' t)]
  have e5 : ((r ψ')⁻¹ * (gxT D D' f hDB hD'B t : Pi1 A K) * r ψ' *
      (h (gπ D D' f hDB hD'B t) : Pi1 A K)) • D.P (τ (gπ D D' f hDB hD'B t)) =
      (r (h'' t) * (gxT D D' f hDB hD'B (τ' t) : Pi1 A K)) • D.P (gπ D D' f hDB hD'B (τ' t)) := by
    calc _ = ((r ψ')⁻¹ * (gxT D D' f hDB hD'B t : Pi1 A K) * r ψ') •
          ((h (gπ D D' f hDB hD'B t) : Pi1 A K) • D.P (τ (gπ D D' f hDB hD'B t))) :=
          mul_smul ((r ψ')⁻¹ * (gxT D D' f hDB hD'B t : Pi1 A K) * r ψ')
            (h (gπ D D' f hDB hD'B t) : Pi1 A K) (D.P (τ (gπ D D' f hDB hD'B t)))
      _ = ((r ψ')⁻¹ * (gxT D D' f hDB hD'B t : Pi1 A K) * r ψ') •
          ((r ψ')⁻¹ • D.P (gπ D D' f hDB hD'B t)) := by rw [← hS (gπ D D' f hDB hD'B t)]
      _ = (r ψ')⁻¹ • ((gxT D D' f hDB hD'B t : Pi1 A K) • D.P (gπ D D' f hDB hD'B t)) := by
          rw [smul_smul ((r ψ')⁻¹ * (gxT D D' f hDB hD'B t : Pi1 A K) * r ψ') (r ψ')⁻¹, mul_inv_cancel_right]
          exact mul_smul (r ψ')⁻¹ (gxT D D' f hDB hD'B t : Pi1 A K) (D.P (gπ D D' f hDB hD'B t))
      _ = r (h'' t) • ((gxT D D' f hDB hD'B (τ' t) : Pi1 A K) • D.P (gπ D D' f hDB hD'B (τ' t))) :=
          e3.symm.trans e4
      _ = _ := (mul_smul (r (h'' t)) (gxT D D' f hDB hD'B (τ' t) : Pi1 A K)
          (D.P (gπ D D' f hDB hD'B (τ' t)))).symm
  have ha : (r ψ')⁻¹ * (gxT D D' f hDB hD'B t : Pi1 A K) * r ψ' * (h (gπ D D' f hDB hD'B t) : Pi1 A K) ∈
      pi1geo A K q :=
    (pi1geo A K q).mul_mem (conjΓ (pi1geo A K q) (r ψ') (gxT D D' f hDB hD'B t)).2 (h _).2
  have hb : r (h'' t) * (gxT D D' f hDB hD'B (τ' t) : Pi1 A K) ∈ pi1geo A K q :=
    (pi1geo A K q).mul_mem ((hgeo _).2 (h'' t).2) (gxT D D' f hDB hD'B (τ' t)).2
  exact frobSpec_disj D hstabD ha hb e5

end Match

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_H2Sh =====
section

/-!
# S4-Lefschetz, L4i3: `H²_c` of an induced trivial module

For `G = H·Γ` with finitely many cosets (`R : CosetReps Γ H`) and `σ` the trivial representation of `H` on `k`,
`H²_c(Γ; Ind_H^G k) = (Ind_H^G k)_Γ ≃ k` by summing over the coset representatives, and every Frobenius
`frobH2c ψ χ` acts there as `χ`.

* `indH` (the indicator of `H`), `sumMap`, `coind_decomp`, `sumMap_rho`, `mk_eq_smul`;
* `h2ShEquiv : H2c (pushRep H σ) Γ ≃ₗ[k] k`, `frobH2c_ind : frobH2c (pushRep H σ) Γ ψ χ = χ • 1`;
* **`trace_frobH2c_ind`**: `Tr(frobH2c ψ χ ^ m | H²_c(Γ; Ind_H^G k)) = χ ^ m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh Representation

section H2Sh

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {Γ H : Subgroup G} (σ : Representation k H k) (hσ : ∀ h : H, σ h = 1)

include hσ in
theorem coind_triv_mul (F : coindV H.subtype σ) (h : H) (x : G) :
    (F : G → k) ((h : G) * x) = (F : G → k) x := by
  rw [coind_mul_apply, hσ]
  rfl

variable (R : CosetReps Γ H)

variable (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ)

variable [IsTopologicalGroup G] [Γ.Normal]

end H2Sh

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtLift =====
section

/-!
# S4-Lefschetz, L5c4a: the block count through `π₁(U)` (generic), block subgroup lemmas, open fixers

* `liftHom r hr π hker : G →* Gf` (`π` through a surjection `r` with `ker r ≤ ker π`), `liftHom_apply`;
* `card_fixed_blk_lift`: `card_fixed_blk` with `Γ`, `F`, `π` given upstairs (in `P`, e.g. `π₁(U)`), through
  `r : P →* G`: the count is `#{p ∈ π(Γ) | (p a)⁻¹ π(F) (p a) = γ}`;
* `mem_blkH_of_fix_iff` (`x ζ = ζ`: `x ∈ H_ω ↔ π x = 1`), `mem_blkH_of_ginv_iff` (`x ζ = g⁻¹ ζ`:
  `x ∈ H_ω ↔ π x = π g⁻¹`);
* `mem_fixRestrict_iff`, `isOpen_fixRestrict`, `resPt_eq_one_of_fix`: the fixer of a finite level `L ≤ K_U` is open
  and is `ker resPt`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open GalCover CurveCoh

section LiftHom

variable {P G Gf : Type} [Group P] [Group G] [Group Gf]

end LiftHom

section PtLift

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {G : Type} [Group G] [MulSemiringAction G B]
  {Ω : Type} [Field Ω]
variable [Finite G] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  (H : Subgroup G) {C : Type} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [SMulCommClass H C B] [Algebra.IsInvariant C B H]

end PtLift

section BlkFix

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
variable {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 A K →* Gf) (g : Pi1 A K) (ζ : maxUnram A K)

end BlkFix

section FixRestrict

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
variable {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)

theorem isOpen_fixRestrict [FiniteDimensional K L] :
    IsOpen ((IntermediateField.restrict hLU).fixingSubgroup : Set (Pi1 A K)) := by
  haveI : FiniteDimensional K (IntermediateField.restrict hLU) :=
    LinearEquiv.finiteDimensional (IntermediateField.restrictAlgEquiv hLU).toLinearEquiv
  exact IntermediateField.fixingSubgroup_isOpen _

end FixRestrict

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_CurveTr1 =====
section

/-!
# S4-Lefschetz, L4i part 2a: `π₁(E)` and `π₁^geo(E)` inside `π₁(U)` as topological groups

For a finite `E ⊆ K_U` (constant field `k' = Kc Fq E`), with `H = range thetaE ≤ π₁(U)`:

* `isOpen_range_theta`, `isOpen_range_thetaE`: `H` is open;
* `thE : π₁(E) ≃ₜ* H` (compact to Hausdorff), `eE : π₁^geo(E) ≃ₜ* Γ ∩ H` (its restriction);
* `intwE`, `intwIE`: `eE` intertwines the trivial coefficients and the boundary inertia (`bdJE`);
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a CupDuality Representation

section RangeOpen

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram A K)

/-- The fixing group of a finite `E ⊆ K_U` is open. -/
theorem isOpen_range_theta [FiniteDimensional K E] :
    IsOpen ((theta A K E hE).range : Set (Pi1 A K)) := by
  let b := Module.finBasis K E
  let W : Set (Pi1 A K) :=
    ⋂ i, (fixElt A K ⟨(b i : AlgebraicClosure K), hE (b i).2⟩ : Set (Pi1 A K))
  have hW : IsOpen W := isOpen_iInter_of_finite fun i => fixElt_isOpen A K _
  have heq : ((theta A K E hE).range : Set (Pi1 A K)) = W := by
    ext τ
    rw [SetLike.mem_coe, mem_range_theta A K E hE τ]
    constructor
    · intro h
      exact Set.mem_iInter.2 fun i => h _ (b i).2
    · intro h x hx
      have hi : ∀ i, τ (IntermediateField.inclusion hE (b i)) = IntermediateField.inclusion hE (b i) :=
        fun i => Set.mem_iInter.1 h i
      have hlin : τ.toLinearMap ∘ₗ (IntermediateField.inclusion hE).toLinearMap =
          (IntermediateField.inclusion hE).toLinearMap :=
        b.ext fun i => hi i
      exact LinearMap.congr_fun hlin ⟨x, hx⟩
  rw [heq]
  exact hW

end RangeOpen

section CurveTr

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

theorem thetaE_continuous : Continuous (thetaE Fq K E hE) :=
  (pi1Congr (maxUnram_rfin Fq K).symm).continuous.comp
    ((theta_continuous Fq[X] K E hE).comp (pi1Kc Fq E).continuous)

/-- `H = range thetaE` is open in `π₁(U)`. -/
theorem isOpen_range_thetaE : IsOpen ((thetaE Fq K E hE).range : Set (Pi1 (Rfin Fq K) K)) := by
  have h1 : ((thetaE Fq K E hE).range : Set (Pi1 (Rfin Fq K) K)) =
      (pi1Congr (maxUnram_rfin Fq K).symm).symm ⁻¹' ((theta Fq[X] K E hE).range : Set (Pi1 Fq[X] K)) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_range]
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨pi1Kc Fq E σ, by rw [thetaE_eq, ContinuousMulEquiv.symm_apply_apply]⟩
    · rintro ⟨τ, hτ⟩
      refine ⟨(pi1Kc Fq E).symm τ, ?_⟩
      rw [thetaE_eq, ContinuousMulEquiv.apply_symm_apply, hτ, ContinuousMulEquiv.apply_symm_apply]
  rw [h1]
  exact (isOpen_range_theta Fq[X] K E hE).preimage (pi1Congr (maxUnram_rfin Fq K).symm).symm.continuous

/-- `π₁(E) ≃* range thetaE`. -/
def thEq : Pi1 (Rfin (Kc Fq E) E) E ≃* (thetaE Fq K E hE).range :=
  MonoidHom.ofInjective (thetaE_injective Fq K E hE)

theorem thEq_coe (σ : Pi1 (Rfin (Kc Fq E) E) E) :
    ((thEq Fq K E hE σ : (thetaE Fq K E hE).range) : Pi1 (Rfin Fq K) K) = thetaE Fq K E hE σ := rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- **`π₁(E) ≃ₜ* range thetaE`** (compact to Hausdorff). -/
def thE : Pi1 (Rfin (Kc Fq E) E) E ≃ₜ* (thetaE Fq K E hE).range :=
  have hc : Continuous (thEq Fq K E hE) := continuous_induced_rng.2 (thetaE_continuous Fq K E hE)
  have : T2Space (Pi1 (Rfin Fq K) K) := krullTopology_t2
  { thEq Fq K E hE with
    continuous_toFun := hc
    continuous_invFun :=
      (Continuous.homeoOfEquivCompactToT2 (f := (thEq Fq K E hE).toEquiv) hc).symm.continuous }

theorem thE_coe (σ : Pi1 (Rfin (Kc Fq E) E) E) :
    ((thE Fq K E hE σ : (thetaE Fq K E hE).range) : Pi1 (Rfin Fq K) K) = thetaE Fq K E hE σ := rfl

theorem thE_symm_coe (y : (thetaE Fq K E hE).range) :
    thetaE Fq K E hE ((thE Fq K E hE).symm y) = (y : Pi1 (Rfin Fq K) K) := by
  have h := congrArg Subtype.val ((thE Fq K E hE).apply_symm_apply y)
  exact h

/-- **`π₁^geo(E) ≃ₜ* Γ ∩ range thetaE`**: the restriction of `thE`. -/
def eE : pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) ≃ₜ*
    geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range where
  toFun g := ⟨thE Fq K E hE g, Subgroup.mem_subgroupOf.2 ((thetaE_mem_pi1geo_iff Fq K E hE g).2 g.2)⟩
  invFun y := ⟨(thE Fq K E hE).symm y, (thetaE_mem_pi1geo_iff Fq K E hE _).1 (by
    rw [thE_symm_coe]
    exact Subgroup.mem_subgroupOf.1 y.2)⟩
  left_inv g := Subtype.ext ((thE Fq K E hE).symm_apply_apply (g : Pi1 (Rfin (Kc Fq E) E) E))
  right_inv y := Subtype.ext ((thE Fq K E hE).apply_symm_apply (y : (thetaE Fq K E hE).range))
  map_mul' a b := Subtype.ext (map_mul (thE Fq K E hE) (a : Pi1 (Rfin (Kc Fq E) E) E) b)
  continuous_toFun := continuous_induced_rng.2
    (show Continuous fun g : pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) =>
        thE Fq K E hE (g : Pi1 (Rfin (Kc Fq E) E) E) from
      (thE Fq K E hE).continuous.comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.2
    (show Continuous fun y : geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range =>
        (thE Fq K E hE).symm (y : (thetaE Fq K E hE).range) from
      (thE Fq K E hE).symm.continuous.comp continuous_subtype_val)

theorem eE_coe (g : pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E))) :
    ((eE Fq K E hE g : geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range) :
      (thetaE Fq K E hE).range) = thEq Fq K E hE g := rfl

theorem intwE (N : ℕ) :
    Intw (Representation.trivial (ZMod N) (Pi1 (Rfin (Kc Fq E) E) E) (ZMod N))
      (Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)) (eE Fq K E hE) := fun _ => rfl

end CurveTr

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_CurveTr2 =====
section

/-!
# S4-Lefschetz, L4i part 2b: Frobenius traces on `H¹_c` of a cover `E ⊆ K_U` inside `π₁(U)`

* `trace_cover_eq`: `Tr(F^m | H¹_c(E))` (true Frobenius data of `E`) equals the trace on `H¹_c(Γ ∩ H; Λ)`
  (`H = range thetaE`) with the Frobenius data `rangeElt`/`geoLift` of the Shapiro setting;
* **`trace_cover_sub`**: inside any ambient `G' = H·Γ`, `Tr(F^m | H¹_c(Γ ∩ G'; Ind_H^{G'} Λ))` with the true
  Frobenius data of `U` at `thetaE ψ` equals `Tr(F^m | H¹_c(E))` with the true data of `E` at `ψ`
  (stated with the trace definitions `trH1Sub` / `trH1E`).

Big intermediate statements are `private` and the headline is stated through `def`s: the olean export step
(`LibrarySuggestions` symbol frequencies) folds over the type of every public theorem, and on the unwrapped
statements of this file it ran for hours (session 16).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a CupDuality Representation

section BdryTr

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂] [IsTopologicalGroup G₁]
  {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂} [Δ₁.Normal] {e : Δ₁ ≃ₜ* Δ₂} {S : Type}
  {I₁ : S → Subgroup G₁} {I₂ : S → Subgroup G₂}

/-- `BdryCompat` is transported along `e : Δ₁ ≃ₜ* Δ₂` restricting an ambient `E : G₁ ≃* G₂`. -/
theorem bdryCompat_tr (hI : IntwI I₁ I₂ e) (E : G₁ ≃* G₂) (hE : ∀ g : Δ₁, ((e g : Δ₂) : G₂) = E g)
    {ψ : G₁} {τ : S → S} {h₁ : S → Δ₁} (hI₁ : BdryCompat Δ₁ I₁ ψ τ h₁) :
    BdryCompat Δ₂ I₂ (E ψ) τ (fun s => e (h₁ s)) := by
  intro s g hg
  have hg₁ : ((e.symm g : Δ₁) : G₁) ∈ I₁ s :=
    (hI s (e.symm g)).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact hg)
  have h2 := (hI (τ s) _).1 (bdryCompat_mem Δ₁ I₁ hI₁ s (e.symm g) hg₁)
  have key : E ((e.symm g : Δ₁) : G₁) = (g : G₂) := by rw [← hE, ContinuousMulEquiv.apply_symm_apply]
  have e1 : ((e ((h₁ s)⁻¹ * conjΓ Δ₁ ψ (e.symm g) * h₁ s) : Δ₂) : G₂) =
      ((e (h₁ s) : Δ₂) : G₂)⁻¹ * ((E ψ)⁻¹ * (g : G₂) * E ψ) * ((e (h₁ s) : Δ₂) : G₂) := by
    rw [hE, hE (h₁ s)]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjΓ_val, map_mul, map_inv, key]
  rw [e1] at h2
  exact h2

end BdryTr

section CurveTr2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end CurveTr2

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_SubFrob =====
section

/-!
# S4-Lefschetz, L3e2b: the block Frobenius on `H¹_c` of an open subgroup is the canonical one

On the cone of an open subgroup `G' ⊇ π₁^geo` (geometric part `geoU`, inertia `I s ∩ G'`), the Frobenius of a
Frobenius datum `(ψ', τ, h)` of `ψ' = c0 g'` (`c0` geometric) equals the Frobenius of `g'` with its canonical datum
`(trueTau g', trueH g')` (`frobH1c_sub_true`): `frobSpec_mul_geo` + `frobSpec_unique` at the level of `π₁`, then
`frobH1c_mul_geo` + `frobH1c_congr_h` on `G'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx
open scoped Pointwise

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  {q : ℕ} {S : Type} (D : BdryData A K q R0 S)
  {k M : Type} [CommRing k] [AddCommGroup M] [Module k M] {G' : Subgroup (Pi1 A K)}
  (ρ' : Representation k G' M) (hΓ : pi1geo A K q ≤ G')

/-- **The block Frobenius on `H¹_c` of `G'` is the canonical Frobenius of `g'`.** -/
theorem frobH1c_sub_true (hstabD : ∀ s, ∀ σ ∈ pi1geo A K q, σ • D.P s = D.P s → σ ∈ D.inertia s)
    {ψ' g' : G'} (c0 : pi1geo A K q) (hψ : (ψ' : Pi1 A K) = c0 * g') {τ : S → S} {h : S → pi1geo A K q}
    (hS : FrobSpec D ψ' τ h)
    (hI1 : BdryCompat (geoU (pi1geo A K q) G') (fun s => (D.inertia s).subgroupOf G') ψ' τ
      (fun s => liftΓh hΓ (h s)))
    (hI2 : BdryCompat (geoU (pi1geo A K q) G') (fun s => (D.inertia s).subgroupOf G') g' (trueTau D g')
      (fun s => liftΓ hΓ (trueH D g' s))) :
    frobH1c ρ' (geoU (pi1geo A K q) G') (fun s => (D.inertia s).subgroupOf G') ψ' τ
        (fun s => liftΓh hΓ (h s)) hI1 =
      frobH1c ρ' (geoU (pi1geo A K q) G') (fun s => (D.inertia s).subgroupOf G') g' (trueTau D g')
        (fun s => liftΓ hΓ (trueH D g' s)) hI2 := by
  set γ0 : pi1geo A K q := ⟨(g' : Pi1 A K)⁻¹ * c0 * g', conj_mem_normal (pi1geo A K q) (g' : Pi1 A K) c0 c0.2⟩
    with hγ0
  have hg : (ψ' : Pi1 A K) * ((γ0⁻¹ : pi1geo A K q) : Pi1 A K) = g' := by
    rw [hψ, Subgroup.coe_inv, hγ0]
    group
  have hS' : FrobSpec D g' τ (fun s => γ0 * h s) := by
    have := frobSpec_mul_geo D hS γ0⁻¹
    rw [hg] at this
    simpa only [inv_inv] using this
  obtain ⟨hτ, hh⟩ := frobSpec_unique D hstabD (frobSpec_true D g') hS'
  subst hτ
  have hI3 := bdryCompat_sub hΓ g' (trueTau D g') (fun s => γ0 * h s) (frobSpec_compat D hS')
  have hI4 := bdryCompat_mul_geo (Γ := geoU (pi1geo A K q) G') (I := fun s => (D.inertia s).subgroupOf G') hI3
    (liftΓ hΓ γ0)
  have e1 : ψ' = g' * (liftΓ hΓ γ0 : G') := Subtype.ext (by
    rw [hψ]
    show (c0 : Pi1 A K) * g' = (g' : Pi1 A K) * ((g' : Pi1 A K)⁻¹ * c0 * g')
    group)
  have e2 : (fun s => liftΓh hΓ (h s)) = (fun s => (liftΓ hΓ γ0)⁻¹ * liftΓ hΓ (γ0 * h s)) :=
    funext fun s => Subtype.ext (Subtype.ext (by
      show ((h s : pi1geo A K q) : Pi1 A K) = ((γ0 : Pi1 A K))⁻¹ * ((γ0 : Pi1 A K) * h s)
      group))
  calc frobH1c ρ' (geoU (pi1geo A K q) G') (fun s => (D.inertia s).subgroupOf G') ψ' (trueTau D g')
        (fun s => liftΓh hΓ (h s)) hI1
      = frobH1c ρ' (geoU (pi1geo A K q) G') (fun s => (D.inertia s).subgroupOf G') (g' * (liftΓ hΓ γ0 : G'))
          (trueTau D g') (fun s => (liftΓ hΓ γ0)⁻¹ * liftΓ hΓ (γ0 * h s)) hI4 :=
        frobH1c_congr ρ' _ _ e1 rfl e2 hI1 hI4
    _ = frobH1c ρ' (geoU (pi1geo A K q) G') (fun s => (D.inertia s).subgroupOf G') g' (trueTau D g')
          (fun s => liftΓ hΓ (γ0 * h s)) hI3 :=
        frobH1c_mul_geo ρ' _ _ hI3 (liftΓ hΓ γ0) hI4
    _ = _ := frobH1c_congr_h ρ' _ _ (g' : G') (trueTau D g') _ _
        (fun s => Subgroup.mem_subgroupOf.2 (hh s)) hI2 hI3

end

end Lefschetz
end RamanujanPetersson


end


