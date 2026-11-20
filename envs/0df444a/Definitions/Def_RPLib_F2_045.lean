-- Prove2me | Definitions.Def_RPLib_F2_045
-- name    : RPLib_F2_045
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T14:16:29.426946+00:00
-- url     : https://prove2.me/theorems/feb6b921-ab04-4746-b886-762302d0db43
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 045 of 70 (hypothesis bridge for the Lefschetz trace formula)
-- statement:
--   File 045 of 70 of the flat curve library: hypothesis bridge for the Lefschetz trace formula. It restates the solution of the corresponding problem with the library's main theorem as an explicit hypothesis `MAIN`, together with the elementary translation lemmas it needs.
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_041

/-!
# Lefschetz trace formula library: the trace formula on cochains in elementary terms

Companion of the Lefschetz trace formula library packages (`Def_RPLib_S4_LefPack*`), whose main result is
`RamanujanPetersson.Lefschetz.lefschetz_main`. `LefschetzSol.bridge` restates that theorem with every library object
(the maximal extension `K_U` unramified over `A`, the geometric subgroup, the cocycle modules, the boundary data at
infinity, the Frobenius maps on the cone complex) described by explicit defining conditions in Mathlib terms: for a
finite free `ZMod (l ^ n)`-module with an action of `Gal(K_U/F)` through a finite quotient, the alternating trace of
the `m`-th power of geometric Frobenius on the compactly supported cochain complex equals the sum of the traces of
the geometric Frobenius elements at the `F_{q^m}`-points of the curve. The helpers `unram_iff`, `mem_smul_iff` and
`mem_inertia_iff` restate the library's predicates (unramified subextension, Galois action on ideals, inertia)
explicitly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LefschetzSol

open RamanujanPetersson
open scoped Pointwise

theorem unram_iff (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (L : IntermediateField K (AlgebraicClosure K)) :
    IsUnramifiedSub A K L ↔ ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
      (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1 := by
  refine forall_congr' fun P => forall_congr' fun _ => ?_
  rw [Subgroup.eq_bot_iff_forall]
  refine forall_congr' fun σ => imp_congr_left ?_
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
  have : c = σ • b - b := Subtype.ext he
  rwa [← this]

theorem mem_smul_iff {A K : Type} [CommRing A] [Field K] [Algebra A K] (R0 : Type) [CommRing R0]
    [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
    (g : Pi1 A K) (Q : Ideal (CurveCoh.proChart A K R0)) (b : CurveCoh.proChart A K R0) :
    b ∈ g • Q ↔ ∃ c ∈ Q, (b : maxUnram A K) = g (c : maxUnram A K) := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hb
    refine ⟨_, hb, ?_⟩
    show (b : maxUnram A K) = g (g⁻¹ • (b : maxUnram A K))
    rw [← AlgEquiv.smul_def, smul_inv_smul]
  · rintro ⟨c, hc, he⟩
    have : g⁻¹ • b = c := Subtype.ext (by
      show g⁻¹ • (b : maxUnram A K) = c
      rw [he, ← AlgEquiv.smul_def, inv_smul_smul])
    rwa [this]

theorem mem_inertia_iff {A K : Type} [CommRing A] [Field K] [Algebra A K] (R0 : Type) [CommRing R0]
    [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
    (Q : Ideal (CurveCoh.proChart A K R0)) (g : Pi1 A K) :
    g ∈ Q.inertia (Pi1 A K) ↔ ∀ b : CurveCoh.proChart A K R0, ∃ c ∈ Q, (c : maxUnram A K) = g (b : maxUnram A K) - b := by
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
  have : c = g • b - b := Subtype.ext he
  rwa [← this]

end LefschetzSol



namespace RamanujanPetersson
namespace Lefschetz

open Polynomial
open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue

set_option synthInstance.maxHeartbeats 400000 in
/-- The statement of `RamanujanPetersson.Lefschetz.lefschetz_main` (copied verbatim), so that `LefschetzSol.bridge` can take it as a hypothesis. -/
def LefSolMainStmt : Prop :=
  ∀ (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K] [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K] [Algebra.IsSeparable (RatFunc Fq) K] {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e) (l n k : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] [Fintype (ConjClasses Gf)] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    [Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s).map π)]
    {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    (hkv : (Fintype.card Gf).factorization l ≤ k)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [Module.Free (ZMod (l ^ n)) M]
    [Module.Finite (ZMod (l ^ n)) M] (τ : Representation (ZMod (l ^ n)) Gf M)
    {m : ℕ} (hm : 0 < m) {r : ℕ} (hmr : m * Fintype.card Gf ∣ r) (hQ : 1 < p ^ (e * r))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (ιS : kStar (Rfin Fq K) K hq r →+* Ω) (S : Finset (Rfin Fq K →+* Ω))
    (hS : ∀ u, u ∈ S ↔ (u.comp (algebraMap Fq (Rfin Fq K)) = ιS.comp (algebraMap Fq (kStar (Rfin Fq K) K hq r)) ∧
      Fr.comp u = u))
    (Fu : (Rfin Fq K →+* Ω) → Pi1 (Rfin Fq K) K)
    (hFu : ∀ u ∈ S, ∃ w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω,
      w.comp (algebraMap (Rfin Fq K) _) = u ∧ (∀ b, w (Fu u • b) = Fr (w b)) ∧
        ∀ x, w (incStar (Rfin Fq K) K hq r hQ x) = ιS x),
    LinearMap.trace (ZMod (l ^ n)) M (τ (π φ⁻¹) ^ m) -
            LinearMap.trace (ZMod (l ^ n)) _ (frob1 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) φ⁻¹
              (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) ^ m) +
            LinearMap.trace (ZMod (l ^ n)) _ (frob2 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq))
              (bdryInf Fq K).inertia φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹)
              (trueCompat (bdryInf Fq K) φ⁻¹) ^ m) =
          ∑ u ∈ S, LinearMap.trace (ZMod (l ^ n)) M (τ (π (Fu u))⁻¹)

end Lefschetz
end RamanujanPetersson

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 8000000 in
theorem LefschetzSol.bridge (MAIN : RamanujanPetersson.Lefschetz.LefSolMainStmt)
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (p e : ℕ) [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
    (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    (KU : IntermediateField F (AlgebraicClosure F))
    (hKU : KU = ⨆ L : {L : IntermediateField F (AlgebraicClosure F) //
        FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1}, L.1)
    (Γ : Subgroup (KU ≃ₐ[F] KU))
    (hΓ : ∀ g : KU ≃ₐ[F] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → g x = x)
    (φ : KU ≃ₐ[F] KU)
    (hφ : ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → φ x = x ^ Fintype.card Fq)
    (Mf : IntermediateField F (AlgebraicClosure F))
    (hMf : FiniteDimensional F Mf ∧ IsGalois F Mf ∧
      ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) Mf), P.IsPrime →
        ∀ g : Mf ≃ₐ[F] Mf,
          (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) Mf, ∃ c ∈ P, (c : Mf) = g b - b) →
            g = 1)
    (hMfU : Mf ≤ KU)
    (Gf : Type) [Group Gf] [Fintype Gf] (π : (KU ≃ₐ[F] KU) →* Gf)
    (hπ : ∀ σ : KU ≃ₐ[F] KU, π σ = 1 ↔ ∀ x : KU, (x : AlgebraicClosure F) ∈ Mf → σ x = x)
    (hπo : IsOpen (π.ker : Set (KU ≃ₐ[F] KU)))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Module.Free (ZMod (l ^ n)) M]
    [Module.Finite (ZMod (l ^ n)) M] (τ : Representation (ZMod (l ^ n)) Gf M)
    (Z1 : Submodule (ZMod (l ^ n)) (Γ → M))
    (hZ1 : ∀ c : Γ → M, c ∈ Z1 ↔ IsLocallyConstant c ∧ ∀ g h : Γ, c (g * h) = c g + τ (π g) (c h))
    (m : ℕ) (hm : 0 < m) (r : ℕ) (hr : 0 < r) (hmr : m * Fintype.card Gf ∣ r)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (Cr : Subfield KU) (hCr : ∀ x : KU, x ∈ Cr ↔ x ^ (Fintype.card Fq ^ r) = x) (ιS : Cr →+* Ω)
    (S : Finset (FunctionField.ringOfIntegers Fq F →+* Ω))
    (hS : ∀ u, u ∈ S ↔ (∀ (c : Fq) (x : Cr), (x : KU) = algebraMap F KU (algebraMap Fq F c) →
        u (algebraMap Fq (FunctionField.ringOfIntegers Fq F) c) = ιS x) ∧ Fr.comp u = u)
    (Fu : (FunctionField.ringOfIntegers Fq F →+* Ω) → (KU ≃ₐ[F] KU))
    (hFu : ∀ u ∈ S, ∃ w : integralClosure (FunctionField.ringOfIntegers Fq F) KU →+* Ω,
      (∀ a : FunctionField.ringOfIntegers Fq F, w (algebraMap _ _ a) = u a) ∧
      (∀ b b' : integralClosure (FunctionField.ringOfIntegers Fq F) KU,
        (b' : KU) = Fu u (b : KU) → w b' = Fr (w b)) ∧
      ∀ (x : Cr) (b : integralClosure (FunctionField.ringOfIntegers Fq F) KU), (b : KU) = x → w b = ιS x) :
    ∃ (B : Type) (P : B → Ideal (integralClosure
        (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU)),
      Finite B ∧ (∀ s, (P s).IsPrime ∧ P s ≠ ⊥) ∧
      (∀ Q : Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU),
        Q.IsPrime → Q ≠ ⊥ → ∃ s, ∃ g ∈ Γ,
          ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU,
            b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) ∧
      (∀ s s', ∀ g ∈ Γ,
        (∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU,
          b ∈ P s' ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) → s = s') ∧
      ∃ (t : B → B) (h : B → Γ),
        (∀ s (b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU),
          (∃ c ∈ P s, (b : KU) = φ (c : KU)) ↔
            ∃ c ∈ P (t s), (b : KU) = (h s : KU ≃ₐ[F] KU) (c : KU)) ∧
        ∀ I : B → Subgroup (KU ≃ₐ[F] KU),
          (∀ s (g : KU ≃ₐ[F] KU), g ∈ I s ↔
            ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU,
              ∃ c ∈ P s, (c : KU) = g (b : KU) - b) →
        ∀ Z2 : (s : B) → Submodule (ZMod (l ^ n)) (↥(Γ ⊓ I s) → M),
          (∀ s (c : ↥(Γ ⊓ I s) → M), c ∈ Z2 s ↔
            IsLocallyConstant c ∧ ∀ g h : ↥(Γ ⊓ I s), c (g * h) = c g + τ (π g) (c h)) →
        ∃ (F1 : (↥Z1 × (B → M)) →ₗ[ZMod (l ^ n)] (↥Z1 × (B → M)))
          (F2 : ((s : B) → ↥(Z2 s)) →ₗ[ZMod (l ^ n)] ((s : B) → ↥(Z2 s))),
          (∀ (c : ↥Z1) (y : B → M) (g g' : Γ), (g' : KU ≃ₐ[F] KU) = φ * g * φ⁻¹ →
            ((F1 (c, y)).1 : Γ → M) g = τ (π φ⁻¹) ((c : Γ → M) g')) ∧
          (∀ (c : ↥Z1) (y : B → M) (s : B),
            (F1 (c, y)).2 s = τ (π φ⁻¹) (τ (π (h s)) (y (t s)) - (c : Γ → M) (h s))) ∧
          (∀ (x : (s : B) → ↥(Z2 s)) (s : B) (g : ↥(Γ ⊓ I s)) (g' : ↥(Γ ⊓ I (t s))),
            (g' : KU ≃ₐ[F] KU) = (h s : KU ≃ₐ[F] KU)⁻¹ * φ * g * φ⁻¹ * h s →
            ((F2 x s : ↥(Z2 s)) : ↥(Γ ⊓ I s) → M) g =
              τ (π (φ⁻¹ * h s)) (((x (t s) : ↥(Z2 (t s))) : ↥(Γ ⊓ I (t s)) → M) g')) ∧
          LinearMap.trace (ZMod (l ^ n)) M (τ (π φ⁻¹) ^ m) -
              LinearMap.trace (ZMod (l ^ n)) (↥Z1 × (B → M)) (F1 ^ m) +
              LinearMap.trace (ZMod (l ^ n)) ((s : B) → ↥(Z2 s)) (F2 ^ m) =
            ∑ u ∈ S, LinearMap.trace (ZMod (l ^ n)) M (τ (π (Fu u))⁻¹) := by
  classical
  -- `K_U = maxUnram`, `Γ = π₁^geo`, `Z¹`, `kStar`
  have hset : RamanujanPetersson.unramSet (FunctionField.ringOfIntegers Fq F) F =
      {L : IntermediateField F (AlgebraicClosure F) | FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1} := by
    ext L
    exact and_congr Iff.rfl (and_congr Iff.rfl (LefschetzSol.unram_iff _ F L))
  have hKU' : KU = RamanujanPetersson.maxUnram (FunctionField.ringOfIntegers Fq F) F := by
    rw [hKU, RamanujanPetersson.maxUnram, hset]
    rfl
  subst hKU'
  have hΓ' : Γ = RamanujanPetersson.CurveCoh.pi1geo (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq) := by
    ext g
    rw [hΓ, RamanujanPetersson.CurveCoh.mem_pi1geo]
    rfl
  subst hΓ'
  have hZ1' : Z1 = RamanujanPetersson.CurveCoh.Z1 (τ.comp π)
      (RamanujanPetersson.CurveCoh.pi1geo (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq)) := by
    ext c
    rw [hZ1, RamanujanPetersson.CurveCoh.mem_Z1]
    rfl
  subst hZ1'
  have hCr' : Cr = RamanujanPetersson.Lefschetz.kStar (FunctionField.ringOfIntegers Fq F) F hq r := by
    ext x
    rw [hCr, RamanujanPetersson.Lefschetz.mem_kStar]
  subst hCr'
  -- library hypotheses
  have hM : Mf ∈ RamanujanPetersson.unramSet (FunctionField.ringOfIntegers Fq F) F := by
    rw [hset]
    exact hMf
  have hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMfU).fixingSubgroup := by
    intro σ
    rw [hπ σ, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun H y hy => H y ((IntermediateField.mem_restrict _ y).1 hy),
      fun H y hy => H y ((IntermediateField.mem_restrict _ y).2 hy)⟩
  have hφ' : RamanujanPetersson.CurveCoh.IsFrobLift (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq) φ :=
    fun x hx => hφ x hx
  have hQ : 1 < p ^ (e * r) := Nat.one_lt_pow (Nat.mul_ne_zero he.ne' hr.ne') (Fact.out : p.Prime).one_lt
  have hS' : ∀ u, u ∈ S ↔ u.comp (algebraMap Fq (FunctionField.ringOfIntegers Fq F)) =
      ιS.comp (algebraMap Fq (RamanujanPetersson.Lefschetz.kStar (FunctionField.ringOfIntegers Fq F) F hq r)) ∧
        Fr.comp u = u := by
    intro u
    rw [hS u]
    refine and_congr ⟨fun H => RingHom.ext fun c => H c _ rfl, fun H c x hx => ?_⟩ Iff.rfl
    have hx' : x = algebraMap Fq _ c := Subtype.ext hx
    subst hx'
    exact RingHom.congr_fun H c
  have hFu' : ∀ u ∈ S, ∃ w : RamanujanPetersson.CurveCoh.proChart (FunctionField.ringOfIntegers Fq F) F
        (FunctionField.ringOfIntegers Fq F) →+* Ω,
      w.comp (algebraMap (FunctionField.ringOfIntegers Fq F) _) = u ∧ (∀ b, w (Fu u • b) = Fr (w b)) ∧
        ∀ x, w (RamanujanPetersson.Lefschetz.incStar (FunctionField.ringOfIntegers Fq F) F hq r hQ x) = ιS x := by
    intro u hu
    obtain ⟨w, h1, h2, h3⟩ := hFu u hu
    exact ⟨w, RingHom.ext h1, fun b => h2 b _ rfl, fun x => h3 x _ rfl⟩
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Finite M := Module.finite_of_finite (ZMod (l ^ n))
  haveI : Fintype (ConjClasses Gf) := Fintype.ofFinite _
  haveI : Finite (RamanujanPetersson.CP4a.BdryS (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)) :=
    RamanujanPetersson.CP4a.finite_bdryS hq he
  haveI : Fintype (RamanujanPetersson.CP4a.BdryS (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)) := Fintype.ofFinite _
  have key := MAIN Fq F hq he l n ((Fintype.card Gf).factorization l) hn hlq
    hM hMfU π hπM hπo hφ' le_rfl τ hm hmr hQ Fr hFr ιS S hS' Fu hFu'
  -- boundary data: `bdryInf`, its true Frobenius permutation for `φ⁻¹`
  refine ⟨_, (RamanujanPetersson.CP4a.bdryInf Fq F).P, RamanujanPetersson.CP4a.finite_bdryS hq he,
    fun s => (RamanujanPetersson.CP4a.bdryInf Fq F).mem s, ?_, ?_,
    RamanujanPetersson.CP4a.trueTau (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹,
    RamanujanPetersson.CP4a.trueH (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹, ?_, ?_⟩
  · intro Q h1 h2
    obtain ⟨s, g, hg, hQ⟩ := (RamanujanPetersson.CP4a.bdryInf Fq F).cover Q ⟨h1, h2⟩
    refine ⟨s, g, hg, fun b => ?_⟩
    subst hQ
    exact LefschetzSol.mem_smul_iff _ g _ b
  · intro s s' g hg H
    exact (RamanujanPetersson.CP4a.bdryInf Fq F).disj s s' g hg
      (Ideal.ext fun b => (H b).trans (LefschetzSol.mem_smul_iff _ g _ b).symm)
  · intro s b
    have hsp := RamanujanPetersson.CP4a.trueTau_spec (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹ s
    have h1 := LefschetzSol.mem_smul_iff (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) φ⁻¹⁻¹
      ((RamanujanPetersson.CP4a.bdryInf Fq F).P s) b
    have h2 := LefschetzSol.mem_smul_iff (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
      ((RamanujanPetersson.CP4a.trueH (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹ s : _) : _)
      ((RamanujanPetersson.CP4a.bdryInf Fq F).P
        (RamanujanPetersson.CP4a.trueTau (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹ s)) b
    exact h1.symm.trans ((Iff.of_eq (congrArg (fun J => b ∈ J) hsp)).trans h2)
  intro I hI Z2 hZ2
  have hI' : I = (RamanujanPetersson.CP4a.bdryInf Fq F).inertia := funext fun s => Subgroup.ext fun g =>
    (hI s g).trans (LefschetzSol.mem_inertia_iff _ ((RamanujanPetersson.CP4a.bdryInf Fq F).P s) g).symm
  subst hI'
  have hZ2' : Z2 = fun s => RamanujanPetersson.CurveCoh.Z1 (τ.comp π)
      (RamanujanPetersson.CurveCoh.pi1geo (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq) ⊓
        (RamanujanPetersson.CP4a.bdryInf Fq F).inertia s) :=
    funext fun s => Submodule.ext fun c => (hZ2 s c).trans (RamanujanPetersson.CurveCoh.mem_Z1 (τ.comp π) _ c).symm
  subst hZ2'
  refine ⟨RamanujanPetersson.PerfectCx.frob1 (τ.comp π) _ φ⁻¹
      (RamanujanPetersson.CP4a.trueTau (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹)
      (RamanujanPetersson.CP4a.trueH (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹),
    RamanujanPetersson.PerfectCx.frob2 (τ.comp π) _ (RamanujanPetersson.CP4a.bdryInf Fq F).inertia φ⁻¹
      (RamanujanPetersson.CP4a.trueTau (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹)
      (RamanujanPetersson.CP4a.trueH (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹)
      (RamanujanPetersson.CP4a.trueCompat (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹), ?_, fun c y s => rfl, ?_, key⟩
  · intro c y g g' hg'
    have hc : RamanujanPetersson.PerfectCx.conjSub φ⁻¹ (RamanujanPetersson.PerfectCx.conj_mem_normal _ φ⁻¹) g = g' :=
      Subtype.ext ((RamanujanPetersson.PerfectCx.conjSub_val _ _ g).trans (by rw [inv_inv]; exact hg'.symm))
    exact congrArg (fun z => (τ.comp π) φ⁻¹ ((c : _ → M) z)) hc
  · intro x s g g' hg'
    have hc : RamanujanPetersson.PerfectCx.conjSub
        (φ⁻¹ * (RamanujanPetersson.CP4a.trueH (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹ s : _))
        (RamanujanPetersson.PerfectCx.bdry_mem _ (RamanujanPetersson.CP4a.bdryInf Fq F).inertia φ⁻¹ _ _
          (RamanujanPetersson.CP4a.trueCompat (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹) s) g = g' :=
      Subtype.ext ((RamanujanPetersson.PerfectCx.conjSub_val _ _ g).trans (by rw [hg']; group))
    exact congrArg (fun z => (τ.comp π)
      (φ⁻¹ * (RamanujanPetersson.CP4a.trueH (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹ s : _))
      ((x (RamanujanPetersson.CP4a.trueTau (RamanujanPetersson.CP4a.bdryInf Fq F) φ⁻¹ s) : _ → M) z)) hc


