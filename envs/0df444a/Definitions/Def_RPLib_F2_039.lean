-- Prove2me | Definitions.Def_RPLib_F2_039
-- name    : RPLib_F2_039
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T13:14:16.640409+00:00
-- url     : https://prove2.me/theorems/cfe849ad-b42e-465a-8642-58724c309305
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 039 of 70
-- statement:
--   File 039 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_Pow`: S4-Lefschetz L0: the Lefschetz trace formula for the powers of the Frobenius
--   * `S4.Def_RP_Lefschetz_ClassCount`: S4-Lefschetz L2b: class traces of `F^m` from twisted counts
--   * `S4.Def_RP_Lefschetz_H1Les`: S4-Lefschetz, L3e2d1: `H¹_c` with constant coefficients is finite free
--   * `S4.Def_RP_Lefschetz_H2Sh`: S4-Lefschetz, L4i3: `H²_c` of an induced trivial module
--   * `S4.Def_RP_Lefschetz_CurveTr2`: S4-Lefschetz, L4i part 2b: Frobenius traces on `H¹_c` of a cover `E ⊆ K_U` inside `π₁(U)`
--   * `S4.Def_RP_Lefschetz_CoverLef`: S4-Lefschetz, L4 assembly: the Lefschetz formula of a cover `E ⊆ K_U`, read inside `π₁(U)`
--   * `S4.Def_RP_Lefschetz_ResK`: S4-Lefschetz, L3 (i): the residue hypothesis of the total cone, with its Frobenius twist
--   * `S4.Def_RP_Lefschetz_BlockPt`: S4-Lefschetz, L3f2b: one fixed block counts the points of its cover
--   * `S4.Def_RP_Lefschetz_BlockSum`: S4-Lefschetz, L3f3a: the alternating trace of `γ⁻¹ ∘ F^m` is a sum over fixed blocks
--   * `S4.Def_RP_Lefschetz_BlockClose`: S4-Lefschetz, L3f3b: the alternating trace of `γ⁻¹ ∘ F^m` as a sum of block counts
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_026
import Definitions.Def_RPLib_F2_036

/-!
# Ramanujan-Petersson curve library (flat edition), file 039 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_Pow`: S4-Lefschetz L0: the Lefschetz trace formula for the powers of the Frobenius
* `S4.Def_RP_Lefschetz_ClassCount`: S4-Lefschetz L2b: class traces of `F^m` from twisted counts
* `S4.Def_RP_Lefschetz_H1Les`: S4-Lefschetz, L3e2d1: `H¹_c` with constant coefficients is finite free
* `S4.Def_RP_Lefschetz_H2Sh`: S4-Lefschetz, L4i3: `H²_c` of an induced trivial module
* `S4.Def_RP_Lefschetz_CurveTr2`: S4-Lefschetz, L4i part 2b: Frobenius traces on `H¹_c` of a cover `E ⊆ K_U` inside `π₁(U)`
* `S4.Def_RP_Lefschetz_CoverLef`: S4-Lefschetz, L4 assembly: the Lefschetz formula of a cover `E ⊆ K_U`, read inside `π₁(U)`
* `S4.Def_RP_Lefschetz_ResK`: S4-Lefschetz, L3 (i): the residue hypothesis of the total cone, with its Frobenius twist
* `S4.Def_RP_Lefschetz_BlockPt`: S4-Lefschetz, L3f2b: one fixed block counts the points of its cover
* `S4.Def_RP_Lefschetz_BlockSum`: S4-Lefschetz, L3f3a: the alternating trace of `γ⁻¹ ∘ F^m` is a sum over fixed blocks
* `S4.Def_RP_Lefschetz_BlockClose`: S4-Lefschetz, L3f3b: the alternating trace of `γ⁻¹ ∘ F^m` as a sum of block counts
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_Pow =====
section

/-!
# S4-Lefschetz L0: the Lefschetz trace formula for the powers of the Frobenius

`lefschetz_frob` (S4-PD) is the twisted trace formula for the Frobenius `F` itself. Here it is extended to every power
`F^m`: equivariance is stable under powers (`isEquivariant_pow`), intertwinings iterate (`intertwine_pow`), the map
induced on coinvariants by `φ^m ⊗ id` is the `m`-th power of the map induced by `φ ⊗ id` (`coinvMap_tensor_pow`), so
`Tr(F^m | M) - Tr(F^m | K¹(M)) + Tr(F^m | K²(M)) = Σ_c L(frobPC^m)[c] · Tr(τ(c)⁻¹ | M)` (`lefschetz_frob_pow`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open CurveCoh MonoidAlgebra HattoriStallings Representation TensorProduct PerfectCx

noncomputable section

section Gen

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G] {P : Type*} [AddCommGroup P] [Module R P]

/-- Equivariant endomorphisms are stable under powers. -/
theorem isEquivariant_pow {ρ : Representation R G P} {f : P →ₗ[R] P} (hf : IsEquivariant ρ ρ f) :
    ∀ m : ℕ, IsEquivariant ρ ρ (f ^ m)
  | 0 => by rw [pow_zero, Module.End.one_eq_id]; exact isEquivariant_id
  | m + 1 => fun g => by
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc, isEquivariant_pow hf m g,
      ← LinearMap.comp_assoc, hf g, LinearMap.comp_assoc]

variable {V : Type*} [AddCommGroup V] [Module R V]

theorem coinvMap_congr (θ : Representation R G V) {F F' : V →ₗ[R] V} (hF : IsEquivariant θ θ F)
    (hF' : IsEquivariant θ θ F') (e : F = F') : coinvMap θ F hF = coinvMap θ F' hF' := by
  subst e; rfl

/-- The map induced on coinvariants by `F^m` is the `m`-th power of the map induced by `F`. -/
theorem coinvMap_pow (θ : Representation R G V) {F : V →ₗ[R] V} (hF : IsEquivariant θ θ F) (m : ℕ)
    (hFm : IsEquivariant θ θ (F ^ m)) : coinvMap θ (F ^ m) hFm = coinvMap θ F hF ^ m := by
  refine LinearMap.ext fun u => ?_
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective θ u
  rw [coinvMap_mk]
  exact intertwine_pow (⇑(Coinvariants.mk θ)) (fun v => (coinvMap_mk θ F hF v).symm) m x

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- `(φ^m ⊗ id)_G = ((φ ⊗ id)_G)^m` on the coinvariants of `P ⊗ M`. -/
theorem coinvMap_tensor_pow (ρ : Representation R G P) (τ : Representation R G M) {φ : P →ₗ[R] P}
    (hφ : IsEquivariant ρ ρ φ) (m : ℕ)
    (h : IsEquivariant (ρ.tprod τ) (ρ.tprod τ) (TensorProduct.map (φ ^ m) LinearMap.id)) :
    coinvMap (ρ.tprod τ) (TensorProduct.map (φ ^ m) LinearMap.id) h =
      coinvMap (ρ.tprod τ) (TensorProduct.map φ LinearMap.id) (isEquivariant_tensorMap hφ isEquivariant_id) ^ m := by
  rw [← coinvMap_pow (ρ.tprod τ) (isEquivariant_tensorMap hφ isEquivariant_id) m
    (isEquivariant_pow (isEquivariant_tensorMap hφ isEquivariant_id) m)]
  exact coinvMap_congr _ _ _ (by rw [TensorProduct.map_pow, Module.End.id_pow])

end Gen

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)
  [Finite Λ] [Fintype Gf] {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M)
  {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

variable (m : ℕ)

theorem trace_pow0 :
    LinearMap.trace Λ _ (coinvMap ((ρPC Λ π Γ I 0).tprod τ) (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 0 ^ m)
      LinearMap.id) (isEquivariant_tensorMap (isEquivariant_pow (frobPC_equiv π Γ I ψ t h hI 0) m)
        isEquivariant_id)) = LinearMap.trace Λ M (τ (π ψ) ^ m) := by
  rw [coinvMap_tensor_pow _ τ (frobPC_equiv π Γ I ψ t h hI 0) m]
  exact trace_eq_of_intertwine _ _ _ (intertwine_pow _ (pcIso0_frob (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t)
    (h := h) (hI := hI) (τ := τ)) m)

include hΛ hall hπ in
theorem trace_pow1 [Fintype S] [DecidableEq S] :
    LinearMap.trace Λ _ (coinvMap ((ρPC Λ π Γ I 1).tprod τ) (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 1 ^ m)
      LinearMap.id) (isEquivariant_tensorMap (isEquivariant_pow (frobPC_equiv π Γ I ψ t h hI 1) m)
        isEquivariant_id)) = LinearMap.trace Λ _ (frob1 (τ.comp π) Γ ψ t h ^ m) := by
  rw [coinvMap_tensor_pow _ τ (frobPC_equiv π Γ I ψ t h hI 1) m]
  exact trace_eq_of_intertwine _ _ _ (intertwine_pow _ (pcIso1_frob (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t)
    (h := h) (hI := hI) (τ := τ) (hΛ := hΛ) (hall := hall) (hπ := hπ)) m)

include hΛ hallI hπ in
theorem trace_pow2 [Fintype S] [DecidableEq S] :
    LinearMap.trace Λ _ (coinvMap ((ρPC Λ π Γ I 2).tprod τ) (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 2 ^ m)
      LinearMap.id) (isEquivariant_tensorMap (isEquivariant_pow (frobPC_equiv π Γ I ψ t h hI 2) m)
        isEquivariant_id)) = LinearMap.trace Λ _ (frob2 (τ.comp π) Γ I ψ t h hI ^ m) := by
  rw [coinvMap_tensor_pow _ τ (frobPC_equiv π Γ I ψ t h hI 2) m]
  exact trace_eq_of_intertwine _ _ _ (intertwine_pow _ (pcIso2_frob (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t)
    (h := h) (hI := hI) (τ := τ) (hΛ := hΛ) (hallI := hallI) (hπ := hπ)) m)

include hΛ hall hallI hπ in
/-- **Lefschetz trace formula for the powers of the Frobenius** on the cone complex:
`Tr(F^m | M) - Tr(F^m | K¹(M)) + Tr(F^m | K²(M)) = Σ_c L(frobPC^m)[c] · Tr(τ(c)⁻¹ | M)`. -/
theorem lefschetz_frob_pow [IsLocalRing Λ] [Fintype (ConjClasses Gf)] [Fintype S] [DecidableEq S]
    [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (hρ : ∀ i, IsProj (ρPC Λ π Γ I i)) [Module.Free Λ M] [Module.Finite Λ M] :
    LinearMap.trace Λ M (τ (π ψ) ^ m) - LinearMap.trace Λ _ (frob1 (τ.comp π) Γ ψ t h ^ m) +
      LinearMap.trace Λ _ (frob2 (τ.comp π) Γ I ψ t h hI ^ m) =
      ∑ c : ConjClasses Gf, lefschetz (ρPC Λ π Γ I) 2 (fun i => frobPC Λ π Γ I ψ t h hI i ^ m) c *
        twChar τ LinearMap.id c := by
  have H := lefschetz_PC π Γ I hρ (M := M) (τ := τ) (φ := fun i => frobPC Λ π Γ I ψ t h hI i ^ m)
    (fun i => isEquivariant_pow (frobPC_equiv π Γ I ψ t h hI i) m) (ψ := LinearMap.id) (isEquivariant_id (ρ := τ))
  beta_reduce at H
  rw [trace_pow0 π Γ I ψ t h hI τ m, trace_pow1 π Γ I ψ t h hI τ hΛ hall hπ m,
    trace_pow2 π Γ I ψ t h hI τ hΛ hallI hπ m] at H
  exact H

end Model

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ClassCount =====
section

/-!
# S4-Lefschetz L2b: class traces of `F^m` from twisted counts

The Lefschetz numbers of the powers of the Frobenius reduce along `Λ → Λ/(ϖ)` (`lefschetz_frob_pow_red`). Combined
with the centraliser formula `Σ (-1)^i Tr(γ⁻¹ ∘ F^m | PC^i) = |Z(γ)| · L(F^m)[γ]` (Hattori–Stallings) at the level
`ℤ/l^(n+k)` and the cancellation of the non-unit `|Z(γ)|` (`cast_eq_of_mul_eq'`), a twisted count
`Σ (-1)^i Tr(γ⁻¹ ∘ F^m | PC^i) = |Z(γ)| · N_γ` at level `n + k` gives `L(F^m)[γ] = N_γ` at level `n`
(`lefschetz_pow_eq_count`), as soon as `l^k` kills the `l`-part of `|Gf|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open CurveCoh MonoidAlgebra HattoriStallings TensorProduct PerfectCx

noncomputable section

/-- Cancellation of any nonzero factor whose `l`-adic valuation is at most `k` (its prime-to-`l` part is a unit). -/
theorem cast_eq_of_mul_eq' {l : ℕ} (hl : l.Prime) (n k a : ℕ) (ha : a ≠ 0) (hv : a.factorization l ≤ k)
    (x y : ZMod (l ^ (n + k))) (h : (a : ZMod (l ^ (n + k))) * x = a * y) :
    ZMod.castHom (lvl_dvd l n k) (ZMod (l ^ n)) x = ZMod.castHom (lvl_dvd l n k) (ZMod (l ^ n)) y := by
  have hau := (Nat.ordProj_mul_ordCompl_eq_self a l).symm
  have hcop : Nat.Coprime (a / l ^ a.factorization l) (l ^ (n + k)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_ordCompl hl ha).symm
  have hu : IsUnit ((a / l ^ a.factorization l : ℕ) : ZMod (l ^ (n + k))) := by
    rw [← ZMod.coe_unitOfCoprime _ hcop]
    exact Units.isUnit _
  apply cast_eq_of_mul_eq hl.pos n k (l ^ a.factorization l) (pow_dvd_pow l hv) x y
  apply hu.mul_left_cancel
  have e : (a : ZMod (l ^ (n + k))) =
      ((a / l ^ a.factorization l : ℕ) : ZMod (l ^ (n + k))) * ((l ^ a.factorization l : ℕ) : ZMod _) := by
    conv_lhs => rw [hau]
    rw [Nat.cast_mul, mul_comm]
  rw [← mul_assoc, ← mul_assoc, ← e, h]

/-- `|Z_G(γ)|` divides `|G|`. -/
theorem card_centralizer_dvd {Gf : Type*} [Group Gf] [Fintype Gf] (γ : Gf) :
    Nat.card {z : Gf // z⁻¹ * γ * z = γ} ∣ Fintype.card Gf := by
  have e : {z : Gf // z⁻¹ * γ * z = γ} ≃ Subgroup.centralizer ({γ} : Set Gf) :=
    Equiv.subtypeEquivRight fun z => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hz
        calc z * γ = z * (z⁻¹ * γ * z) := by rw [hz]
          _ = γ * z := by group
      · intro hz
        calc z⁻¹ * γ * z = z⁻¹ * (γ * z) := by group
          _ = z⁻¹ * (z * γ) := by rw [hz]
          _ = γ := by group
  rw [Nat.card_congr e, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_subgroup_dvd_card _

section Red

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] {G : Type} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  [Finite Λ] [Fintype Gf] {ϖ : Λ} (hsurj : Function.Surjective (algebraMap Λ Λ'))
  (ht : algebraMap Λ Λ' ϖ = 0) (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = ϖ * s) {l N : ℕ}
  (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G)) [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (m : ℕ)

end Red

section Count

variable {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ)
  (hI : BdryCompat Γ I ψ t h) {l : ℕ} (hl : l.Prime) (n k : ℕ)
  (hall : H2All (ZMod (l ^ (n + k))) G Γ l (n + k)) (hallI : ∀ s, H2All (ZMod (l ^ (n + k))) G (Γ ⊓ I s) l (n + k))
  (hπ : IsOpen (π.ker : Set G))

end Count

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_H1Les =====
section

/-!
# S4-Lefschetz, L3e2d1: `H¹_c` with constant coefficients is finite free

* `free_finite_of_les`: in an exact `0 → H₀ → B → C → P → 0` with `B` finite, `B / H₀` free and `P` finite free,
  `C` is finite free (`C ≅ B / H₀ × P`: the sequence splits since `P` is projective).
* `free_H1c_triv`: `H¹_c(Γ, {I_s}; Λ)` is finite free when `H¹_par` is (`0 → H⁰ → ⊕_s Λ → H¹_c → H¹_par → 0`).
* `free_curveH1c`: for a curve `U/𝔽_q` with full constant field, `H¹_c(Ū, ℤ/l^n)` is finite free (CP4a's
  `free_curveH1par` with Core B discharged by `CoreB.coreBHyp_proved`, as in `CP4.lefschetz_point_count`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover CP4a

section Les

variable {R : Type*} [CommRing R]

end Les

section Pair

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)

/-- **Constant coefficients**: `H¹_c` is finite free when `H¹_par` is. -/
theorem free_H1c_triv [Fintype S] [DecidableEq S] [Nonempty S]
    (hP : Module.Free k (H1par (Representation.trivial k G k) Γ I) ∧
      Module.Finite k (H1par (Representation.trivial k G k) Γ I)) :
    Module.Free k (H1c (Representation.trivial k G k) Γ I) ∧
      Module.Finite k (H1c (Representation.trivial k G k) Γ I) :=
  free_finite_of_les (h0ToBdry (Representation.trivial k G k) Γ I) (bdryToH1c (Representation.trivial k G k) Γ I)
    (h1cToH1par (k := k) Γ I) (exact_h0ToBdry_bdryToH1c (Representation.trivial k G k) Γ I)
    (exact_codRestrict _ _ _ _ (exact_bdryToH1c_h1cToH1 (Representation.trivial k G k) Γ I))
    (surjective_codRestrict _ _ _ (range_h1cToH1 (Representation.trivial k G k) Γ I))
    (Module.Finite.equiv (bdryTrivEquiv Γ I).symm)
    (Module.Free.of_equiv (constQuotEquiv (Representation.trivial k G k) Γ I (Classical.arbitrary S)
      (fun _ => rfl)).symm) hP

end Pair

section Curve

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end Curve

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

variable (R : CosetReps Γ H)

theorem cr_r_of_mem (c : Γ) (hc : c ∈ Set.range R.r) : R.r c = c := by
  obtain ⟨y, rfl⟩ := hc
  simpa using R.r_r_mul y 1

theorem cr_mem_iff (c y : Γ) (hc : c ∈ Set.range R.r) : (c : G) * (y : G)⁻¹ ∈ H ↔ c = R.r y := by
  constructor
  · intro h
    rw [← cr_r_of_mem R c hc]
    exact R.coset y c h
  · rintro rfl
    have h := H.inv_mem (R.mem y)
    rwa [mul_inv_rev, inv_inv] at h

/-- Sum over the coset representatives. -/
def sumMap : coindV H.subtype σ →ₗ[k] k where
  toFun F := ∑ c ∈ R.fin.toFinset, (F : G → k) c
  map_add' F F' := by
    simp only [Submodule.coe_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a F := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

theorem sumMap_apply (F : coindV H.subtype σ) : sumMap σ R F = ∑ c ∈ R.fin.toFinset, (F : G → k) c := rfl

variable (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ)

include hcov in
theorem sumMap_indH (g : G) : sumMap σ R (pushRep H σ g (indH σ hσ)) = 1 := by
  classical
  obtain ⟨h, γ, hg⟩ := hcov g⁻¹
  have hg' : g = (γ : G)⁻¹ * (h : G)⁻¹ := by rw [← mul_inv_rev, ← hg, inv_inv]
  have key : ∀ c ∈ R.fin.toFinset,
      ((pushRep H σ g (indH σ hσ) : coindV H.subtype σ) : G → k) c = if c = R.r γ then 1 else 0 := by
    intro c hc
    have hc' : c ∈ Set.range R.r := R.fin.mem_toFinset.mp hc
    have e : (c : G) * g ∈ H ↔ c = R.r γ := by
      rw [hg', ← mul_assoc, H.mul_mem_cancel_right (H.inv_mem h.2), cr_mem_iff R c γ hc']
    show ((indH σ hσ : coindV H.subtype σ) : G → k) ((c : G) * g) = _
    rw [indH_apply]
    simp only [e]
  rw [sumMap_apply, Finset.sum_congr rfl key, Finset.sum_ite_eq',
    if_pos (R.fin.mem_toFinset.mpr ⟨γ, rfl⟩)]

include hcov in
theorem coind_decomp (F : coindV H.subtype σ) :
    F = ∑ c ∈ R.fin.toFinset, (F : G → k) c • pushRep H σ ((c : G)⁻¹) (indH σ hσ) := by
  classical
  refine coind_ext_Γ Γ H σ hcov fun y => ?_
  rw [Submodule.coe_sum, Finset.sum_apply]
  have key : ∀ c ∈ R.fin.toFinset,
      (((F : G → k) c • pushRep H σ ((c : G)⁻¹) (indH σ hσ) : coindV H.subtype σ) : G → k) y =
        if c = R.r y then (F : G → k) c else 0 := by
    intro c hc
    have hc' : c ∈ Set.range R.r := R.fin.mem_toFinset.mp hc
    have e : (y : G) * (c : G)⁻¹ ∈ H ↔ c = R.r y := by
      rw [← cr_mem_iff R c y hc', ← H.inv_mem_iff, mul_inv_rev, inv_inv]
    show (F : G → k) c * ((indH σ hσ : coindV H.subtype σ) : G → k) ((y : G) * (c : G)⁻¹) = _
    rw [indH_apply]
    simp only [e, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq', if_pos (R.fin.mem_toFinset.mpr ⟨y, rfl⟩)]
  have h1 : (F : G → k) ((y : G) * (R.r y : G)⁻¹ * R.r y) = (F : G → k) (R.r y) :=
    coind_triv_mul σ hσ F ⟨_, R.mem y⟩ _
  rwa [inv_mul_cancel_right] at h1

include hσ hcov in
theorem sumMap_rho (g : G) (F : coindV H.subtype σ) : sumMap σ R (pushRep H σ g F) = sumMap σ R F := by
  have h : ∀ c : Γ, sumMap σ R (pushRep H σ g ((F : G → k) c • pushRep H σ ((c : G)⁻¹) (indH σ hσ))) =
      (F : G → k) c := by
    intro c
    rw [map_smul, map_smul, rep_mul_apply, sumMap_indH σ hσ R hcov, smul_eq_mul, mul_one]
  conv_lhs => rw [coind_decomp σ hσ R hcov F, map_sum, map_sum]
  rw [Finset.sum_congr rfl fun c _ => h c]
  rfl

variable [IsTopologicalGroup G] [Γ.Normal]

theorem mk_rho_inv (c : Γ) :
    Coinvariants.mk ((pushRep H σ).comp Γ.subtype) (pushRep H σ ((c : G)⁻¹) (indH σ hσ)) =
      Coinvariants.mk ((pushRep H σ).comp Γ.subtype) (indH σ hσ) :=
  Coinvariants.mk_self_apply ((pushRep H σ).comp Γ.subtype) c⁻¹ (indH σ hσ)

include hcov in
theorem mk_eq_smul (F : coindV H.subtype σ) :
    Coinvariants.mk ((pushRep H σ).comp Γ.subtype) F =
      sumMap σ R F • Coinvariants.mk ((pushRep H σ).comp Γ.subtype) (indH σ hσ) := by
  conv_lhs => rw [coind_decomp σ hσ R hcov F]
  simp only [map_sum, map_smul, mk_rho_inv σ hσ]
  rw [← Finset.sum_smul]
  rfl

/-- `H²_c(Γ; Ind_H^G k) → k`, summing over the coset representatives. -/
def h2Sum : H2c (pushRep H σ) Γ →ₗ[k] k :=
  Coinvariants.lift _ (sumMap σ R) (fun g => LinearMap.ext fun F => sumMap_rho σ hσ R hcov (g : G) F)

theorem h2Sum_mk (F : coindV H.subtype σ) :
    h2Sum σ hσ R hcov (Coinvariants.mk _ F) = sumMap σ R F := rfl

/-- **`H²_c(Γ; Ind_H^G k) ≃ k`** for `G = H·Γ` with finitely many cosets. -/
def h2ShEquiv : H2c (pushRep H σ) Γ ≃ₗ[k] k :=
  LinearEquiv.ofLinearMap (h2Sum σ hσ R hcov)
    (LinearMap.toSpanSingleton k _ (Coinvariants.mk ((pushRep H σ).comp Γ.subtype) (indH σ hσ)))
    (LinearMap.ext_ring (by
      simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, one_smul, LinearMap.id_apply]
      rw [h2Sum_mk]
      have h1 := sumMap_indH σ hσ R hcov 1
      rwa [map_one, Module.End.one_apply] at h1))
    (Coinvariants.hom_ext (LinearMap.ext fun F => by
      show sumMap σ R F • Coinvariants.mk ((pushRep H σ).comp Γ.subtype) (indH σ hσ) =
        Coinvariants.mk ((pushRep H σ).comp Γ.subtype) F
      rw [mk_eq_smul σ hσ R hcov F]))

include hσ hcov R in
theorem frobH2c_ind (ψ : G) (χ : k) : frobH2c (pushRep H σ) Γ ψ χ = χ • 1 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨F, rfl⟩ := Coinvariants.mk_surjective _ x
  rw [LinearMap.smul_apply, Module.End.one_apply, frobH2c_mk, mk_eq_smul σ hσ R hcov (pushRep H σ ψ F),
    sumMap_rho σ hσ R hcov, ← mk_eq_smul σ hσ R hcov]

include hσ hcov R in
/-- **`Tr(frobH2c ψ χ ^ m | H²_c(Γ; Ind_H^G k)) = χ ^ m`.** -/
theorem trace_frobH2c_ind (ψ : G) (χ : k) (m : ℕ) :
    LinearMap.trace k (H2c (pushRep H σ) Γ) (frobH2c (pushRep H σ) Γ ψ χ ^ m) = χ ^ m := by
  rw [frobH2c_ind σ hσ R hcov, smul_pow, one_pow, map_smul,
    CP4a.trace_one_of_equiv (h2ShEquiv σ hσ R hcov), smul_eq_mul, mul_one]

end H2Sh

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

end BdryTr

section CurveTr2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

theorem thEq_eq_rangeElt (ψ : Pi1 (Rfin (Kc Fq E) E) E) :
    thEq Fq K E hE ψ = rangeElt (thetaE Fq K E hE) ψ := Subtype.ext rfl

theorem eE_eq_geoLift {T : Type} (h : T → pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E))) :
    (fun t => eE Fq K E hE (h t)) = geoLift (thetaE Fq K E hE) (thetaE_mem_pi1geo_iff Fq K E hE) h :=
  funext fun _ => Subtype.ext (Subtype.ext rfl)

set_option synthInstance.maxHeartbeats 400000 in
/-- `Tr(F^m | H¹_c(E))` with the true Frobenius data of `E` at `ψ` (`E` over its full constant field). -/
def trH1E (N : ℕ) (ψ : Pi1 (Rfin (Kc Fq E) E) E) (m : ℕ) : ZMod N :=
  LinearMap.trace (ZMod N) _ (frobH1c (Representation.trivial (ZMod N) (Pi1 (Rfin (Kc Fq E) E) E) (ZMod N))
      (pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E))) (bdryInf (Kc Fq E) E).inertia ψ
      (trueTau (bdryInf (Kc Fq E) E) ψ) (trueH (bdryInf (Kc Fq E) E) ψ)
      (trueCompat (bdryInf (Kc Fq E) E) ψ) ^ m)

set_option synthInstance.maxHeartbeats 400000 in
/-- `Tr(F^m | H¹_c(Γ ∩ G'; Ind_H^{G'} Λ))` (`H = range thetaE`) with the true Frobenius data of `U`
at `thetaE ψ`. -/
def trH1Sub (N : ℕ) {G' : Subgroup (Pi1 (Rfin Fq K) K)}
    (hΓ : pi1geo (Rfin Fq K) K (Fintype.card Fq) ≤ G') (hH : (thetaE Fq K E hE).range ≤ G')
    (ψ : Pi1 (Rfin (Kc Fq E) E) E) (m : ℕ) : ZMod N :=
  LinearMap.trace (ZMod N) _ (frobH1c (pushRep ((thetaE Fq K E hE).range.subgroupOf G')
      ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
        (downH (thetaE Fq K E hE).range G')))
      (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) G') (fun s => ((bdryInf Fq K).inertia s).subgroupOf G')
      ((upH hH (rangeElt (thetaE Fq K E hE) ψ) : (thetaE Fq K E hE).range.subgroupOf G') : G')
      (trueTau (bdryInf Fq K) (thetaE Fq K E hE ψ))
      (fun s => liftΓ hΓ (trueH (bdryInf Fq K) (thetaE Fq K E hE ψ) s))
      (bdryCompat_sub hΓ (upH hH (rangeElt (thetaE Fq K E hE) ψ) : G') _ _
        (trueCompat (bdryInf Fq K) (thetaE Fq K E hE ψ))) ^ m)

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end CurveTr2

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_CoverLef =====
section

/-!
# S4-Lefschetz, L4 assembly: the Lefschetz formula of a cover `E ⊆ K_U`, read inside `π₁(U)`

For a finite separable `E/K` inside `K_U` with full constant field `k' = Kc Fq E`, an ambient `G' = H·Γ`
(`H = range thetaE`) and a Frobenius lift `φ` of `E` over `k'`:
`Tr(F^m | H²_c(Γ ∩ G'; Ind_H^{G'} Λ)) - Tr(F^m | H¹_c(Γ ∩ G'; Ind_H^{G'} Λ)) = #(Spec R_E)(𝔽_{q'^m})`,
with `F` the Frobenius at `thetaE φ⁻¹` (true boundary data of `U`) and `χ = #k'` on `H²_c`.

* `hlq_Kc`: `l ∤ q ⇒ l ∤ #k'`; `exists_cosetReps_E`; `trH2Sub` (the `H²_c` trace on the `G'` side);
* **`lefschetz_cover`** (CP4 on `E` + `trace_cover_sub` + `trace_frobH2c_ind`), stated with `trH2Sub` /
  `trH1Sub` (the olean export step folds over every public theorem type: keep them small).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a CupDuality Representation

section CoverLef

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

theorem hlq_Kc (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) : ¬ l ∣ Fintype.card (Kc Fq E) := by
  rw [card_Kc_eq_pow Fq E]
  exact fun h => hlq ((Fact.out : l.Prime).dvd_of_dvd_pow h)

/-- Coset representatives of `(Γ ∩ H) \ Γ` exist (`H = range thetaE` is open, `Γ` is compact). -/
theorem exists_cosetReps_E :
    Nonempty (CosetReps (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range) := by
  have ho : IsOpen (((thetaE Fq K E hE).range.subgroupOf (pi1geo (Rfin Fq K) K (Fintype.card Fq)) :
      Subgroup (pi1geo (Rfin Fq K) K (Fintype.card Fq))) : Set (pi1geo (Rfin Fq K) K (Fintype.card Fq))) :=
    (isOpen_range_thetaE Fq K E hE).preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ ho
  have := Subgroup.finiteIndex_of_finite_quotient
    (H := (thetaE Fq K E hE).range.subgroupOf (pi1geo (Rfin Fq K) K (Fintype.card Fq)))
  exact exists_cosetReps _ _

set_option synthInstance.maxHeartbeats 400000 in
/-- `Tr(F^m | H²_c(Γ ∩ G'; Ind_H^{G'} Λ))` (`H = range thetaE`), Frobenius at `thetaE ψ`, twist `χ`. -/
def trH2Sub (N : ℕ) {G' : Subgroup (Pi1 (Rfin Fq K) K)} (hH : (thetaE Fq K E hE).range ≤ G')
    (ψ : Pi1 (Rfin (Kc Fq E) E) E) (χ : ZMod N) (m : ℕ) : ZMod N :=
  LinearMap.trace (ZMod N) _ (frobH2c (pushRep ((thetaE Fq K E hE).range.subgroupOf G')
      ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
        (downH (thetaE Fq K E hE).range G')))
      (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) G')
      ((upH hH (rangeElt (thetaE Fq K E hE) ψ) : (thetaE Fq K E hE).range.subgroupOf G') : G') χ ^ m)

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end CoverLef

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ResK =====
section

/-!
# S4-Lefschetz, L3 (i): the residue hypothesis of the total cone, with its Frobenius twist

For `π` cut out by a finite unramified `M` (S3 chart, true boundary permutation): `exists_resHyp_tw` gives a
`ResHyp Λ π π₁^geo I` together with the twist clause `hTW` of `h2Equiv_frob` / `trace_h2_tot` at `ψ = φ⁻¹`,
`t = trueTau`, `h = trueH`, `c = q`, for every Frobenius lift `φ` (the first half of `h2Equiv_S3`'s proof).
`trueTw_hD` and `trueTw_ht` are the other two side conditions (`hD`, `ht`), for every `ψ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh Kummer CP4a Residue PerfectCx
open scoped Pointwise Polynomial

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

set_option maxHeartbeats 800000 in
/-- The side condition `hD` of `h2Equiv_frob` for the true boundary permutation of any `ψ`. -/
theorem trueTw_hD {Gf : Type} [Group Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf) {S : Type}
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (ψ : Pi1 (Places.Rfin Fq F) F) (s : S) (d : Gf) :
    d ∈ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia (trueTau D ψ s)).map π ↔
      π (ψ * (trueH D ψ s : Pi1 (Places.Rfin Fq F) F)) * d * (π (ψ * (trueH D ψ s : Pi1 (Places.Rfin Fq F) F)))⁻¹ ∈
        (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map π :=
  map_inf_conj_iff (I1 := D.inertia (trueTau D ψ s)) (I2 := D.inertia s) π _ _
    (fun y => inert_conj_iff (trueTau_smul D ψ s) y) d

set_option maxHeartbeats 800000 in
/-- The side condition `ht` of `h2Equiv_frob`: the true boundary permutation is a bijection. -/
theorem trueTw_ht {S : Type} [Finite S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S) (ψ : Pi1 (Places.Rfin Fq F) F) :
    Function.Bijective (trueTau D ψ) :=
  tt_bijective D.P _ D.disj ψ (trueTau D ψ) (trueH D ψ) (trueTau_spec D ψ)

end S3

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockPt =====
section

/-!
# S4-Lefschetz, L3f2b: one fixed block counts the points of its cover

For a block `[a]` of `Gf` fixed by `π(φ⁻¹^m) · γ`, with block data `c0 ∈ π₁^geo`, `g = c0⁻¹ φ⁻¹^m`, a cover `E` with
`#k'_E = q^m`, a Frobenius lift `σ` of `E` with `thetaE σ = g⁻¹` and `range thetaE ∩ π₁^geo = ker π ∩ π₁^geo`:
`Σ_i (-1)^i Tr(P_[a] ∘ ρPC γ⁻¹ ∘ frobPC^m | PC^i) = #(R_E →ₐ[k'_E] k'_E)` (`block_count`).
Route: `block_euler` in the ambient `G' = range thetaE ⊔ π₁^geo`, `frobH1c_sub_true` (the block Frobenius is the
canonical one of `thetaE σ⁻¹`), and `lefschetz_cover` at `m = 1`, `L = k'_E`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation
open scoped Pointwise

section BlockPt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

/-- Generic coercion of `upH (rangeElt r x)` (proved by `rfl` once, for any `r`; never unfold a concrete `thetaE`). -/
theorem coe_upH_rangeElt {A K' A' K'' : Type} [CommRing A] [Field K'] [Algebra A K'] [CommRing A'] [Field K'']
    [Algebra A' K''] (r : Pi1 A' K'' →* Pi1 A K') {G' : Subgroup (Pi1 A K')} (hH : r.range ≤ G') (x : Pi1 A' K'') :
    (((upH hH (rangeElt r x) : r.range.subgroupOf G') : G') : Pi1 A K') = r x := rfl

/-- Bookkeeping for `block_count` (no rewriting inside the large goal). -/
theorem sub_eq_of_tr {R : Type} [CommRing R] {c T T1 T2 H c' : R} (h1 : T = T1) (hcv : T2 - T1 = H) (h2 : T2 = c')
    (hc : c' = c) : c - T = H := by
  rw [h1, ← hc, ← h2]
  exact hcv

end BlockPt

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockSum =====
section

/-!
# S4-Lefschetz, L3f3a: the alternating trace of `γ⁻¹ ∘ F^m` is a sum over fixed blocks

`euler_eq_sum_fixed`: `Σ_i (-1)^i Tr(ρPC γ⁻¹ ∘ frobPC^m | PC^i) = Σ_{ω fixed} Σ_i (-1)^i Tr(P_ω ∘ ρPC γ⁻¹ ∘ frobPC^m)`,
the blocks `ω` of `Gf` (right `π(Γ)`-cosets) running over those fixed by `ω ↦ π(ψ^m) ω γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx

section BlockSum

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Finite Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)

/-- **Block decomposition of the alternating trace of `γ⁻¹ ∘ F^m`**: only the blocks fixed by `ω ↦ π(ψ^m) ω γ`
contribute. -/
theorem euler_eq_sum_fixed [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (γ : Gf) (m : ℕ) :
    ∑ i ∈ Finset.range (2 + 1), (-1 : Λ) ^ i *
        LinearMap.trace Λ _ (ρPC Λ π Γ I i γ⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI i ^ m) =
      ∑ ω ∈ Finset.univ.filter
          (fun ω => blkShift (Γ.map π) (π (ψ ^ m)) γ (map_mem_normalizer π (ψ ^ m)) ω = ω),
        ∑ i ∈ Finset.range (2 + 1), (-1 : Λ) ^ i *
          LinearMap.trace Λ _ (PB Λ π Γ I ω i * (ρPC Λ π Γ I i γ⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI i ^ m)) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, frobPC_pow π Γ I hI m i,
    trace_op_eq_sum_fixed π Γ I (ψ ^ m) t^[m] (hpow Γ ψ t h m) (bdryCompat_pow Γ I hI m) γ i]

end BlockSum

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
/-- **The block cover, with its range**: `exists_blockCover` plus `range thetaE = blkH π g ζ hζ` for a primitive
`((q^m)^|Gf| - 1)`-th root of unity `ζ`, `g = c0⁻¹ φ⁻¹^m`. -/
def exists_blockCover' {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K))) {m : ℕ} (hm : 0 < m) {c0 : Pi1 (Rfin Fq K) K}
    (hc0 : c0 ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram Fq[X] K) (_ : FiniteDimensional K E)
      (_ : Algebra.IsSeparable K E) (σ : Pi1 (Rfin (Kc Fq E) E) E),
      Fintype.card (Kc Fq E) = Fintype.card Fq ^ m ∧ thetaE Fq K E hE σ = (c0⁻¹ * φ⁻¹ ^ m)⁻¹ ∧
      IsFrobLift (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) σ ∧
      (∀ x ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq), x ∈ (thetaE Fq K E hE).range ↔ π x = 1) ∧
      ∃ (Nζ : ℕ) (_ : NeZero Nζ) (ζ : maxUnram (Rfin Fq K) K) (hζ : IsPrimitiveRoot ζ Nζ),
        Nζ = (Fintype.card Fq ^ m) ^ Fintype.card Gf - 1 ∧
        ∀ τ, τ ∈ (thetaE Fq K E hE).range ↔ τ ∈ blkH π (c0⁻¹ * φ⁻¹ ^ m) ζ hζ := by
  have hq2 : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  have hg := ginv_apply hφ hc0 m
  obtain ⟨ζ, hζ⟩ := exists_zeta_level (Fq := Fq) (F := K) he (m * Fintype.card Gf)
    (Nat.mul_pos hm Fintype.card_pos)
  rw [← hq, pow_mul] at hζ
  have h1 : 1 < (Fintype.card Fq ^ m) ^ Fintype.card Gf :=
    Nat.one_lt_pow Fintype.card_pos.ne' (Nat.one_lt_pow hm.ne' hq2)
  have hNZ : NeZero ((Fintype.card Fq ^ m) ^ Fintype.card Gf - 1) := ⟨Nat.sub_ne_zero_of_lt h1⟩
  obtain ⟨z, hz⟩ := exists_zeta_level (Fq := Fq) (F := K) he m hm
  rw [← hq] at hz
  obtain ⟨E, hE, hfd, hsep, hrange, hfixH, hfixE⟩ :=
    exists_E_of_open Fq K (blkH π (c0⁻¹ * φ⁻¹ ^ m) ζ hζ) (isOpen_blkH π _ ζ hζ hπ)
  have hgH := g_mem_blkH π (c0⁻¹ * φ⁻¹ ^ m) ζ hζ
  have hcard := card_Kc_block Fq K E hE _ hfixH hfixE hgH hm hg
    (fun τ hτ y hy => blkH_fix π _ ζ hq2 hm hg hζ hτ hy) z hz
  obtain ⟨σ, hσ, hσF⟩ := exists_frobE Fq K E hE _ hrange hgH hm hg hcard
  exact ⟨E, hE, hfd, hsep, σ, hcard, hσ, hσF,
    fun x hx => (hrange x).trans (mem_blkH_geo_iff π _ ζ hq2 hm hg hζ hx),
    _, hNZ, ζ, hζ, rfl, hrange⟩

end BlockClose

end

end Lefschetz
end RamanujanPetersson


end


