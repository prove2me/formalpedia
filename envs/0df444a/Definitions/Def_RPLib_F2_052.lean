-- Prove2me | Definitions.Def_RPLib_F2_052
-- name    : RPLib_F2_052
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T18:04:36.757577+00:00
-- url     : https://prove2.me/theorems/4d273dd2-274a-40cf-ae86-08d5c88dc0a5
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 052 of 70
-- statement:
--   File 052 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CP4a_Bridge`: S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)
--   * `S4.Def_RP_CP4a_Lef`: S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)
--   * `S4.Def_RP_CoreB_Key`: Core B, O6: `‖deg F‖_l = ‖det F(M)‖_l` through Tate coordinates (for `deg F ≠ 0`)
--   * `S4.Def_RP_CupDuality_KumPicDiv`: S4-CurveDuality, O5b (ii): `Pic⁰(X̄)` is `l^n`-divisible for `l ∤ q`
--   * `S4.Def_RP_Lefschetz_ResK`: S4-Lefschetz, L3 (i): the residue hypothesis of the total cone, with its Frobenius twist
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_025
import Definitions.Def_RPLib_F2_043

/-!
# Ramanujan-Petersson curve library (flat edition), file 052 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CP4a_Bridge`: S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)
* `S4.Def_RP_CP4a_Lef`: S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)
* `S4.Def_RP_CoreB_Key`: Core B, O6: `‖deg F‖_l = ‖det F(M)‖_l` through Tate coordinates (for `deg F ≠ 0`)
* `S4.Def_RP_CupDuality_KumPicDiv`: S4-CurveDuality, O5b (ii): `Pic⁰(X̄)` is `l^n`-divisible for `l ∤ q`
* `S4.Def_RP_Lefschetz_ResK`: S4-Lefschetz, L3 (i): the residue hypothesis of the total cone, with its Frobenius twist
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CP4a_Bridge =====
section

/-!
# S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)

* `tatePicN`: the CoreA Tate coordinates at level `n` as a map `(ℤ/l^n)^s → Pic⁰(X̄)[l^n]`; bijective when
  `A = Pic(X̄)[l^∞]` is divisible (CB1), and `π` acts by `M mod l^n` (`tatePic_frob`).
* `CoreBHyp`: Core B (CB1 + CB2) as an explicit `Prop`: `A` is `l`-divisible, and every CoreA Tate matrix of `π`
  has characteristic polynomial `Π (X - ω_i) ∈ ℤ[X]` for the zeta roots `ω`.
* `trace_of_picEquiv`: for any `ZMod (l^n)`-module `H` with an additive `Φ : H ≃ Pic⁰(X̄)[l^n]` such that
  `π (Φ (f x)) = q Φ x`, `Tr(f^m | H) = 1 + q^m - N_m` (via `exists_tateEquivN`, `coords_key`, `trace_pow_of_coords`).
* `trace_frobPar` (review R4): with the F-equivariant Kummer isomorphism `H¹_par ≃ Pic⁰(X̄)[l^n]` (S4-Kummer),
  `Tr(F^m | H¹_par(Ū, ℤ/l^n)) = 1 + q^m - N_m` for the geometric Frobenius `F`, all `m ≥ 1`.
-/

set_option autoImplicit false

open Polynomial Matrix

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer

section LinAlg

variable {R : Type*} [CommRing R] {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

end LinAlg

section Abstract

variable {H : Type*} [AddCommGroup H] {L : ℕ} [Module (ZMod L) H] {s : ℕ}

end Abstract

section Tate

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)
variable {l : ℕ} [Fact l.Prime] {k0 : ℕ}
  (hdiv : ∀ y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, ∃ z, l • z = y) {s : ℕ}
  (b1 : Fin s → (smulHom (Aℓ Ω hk l) (l ^ k0)).range) (hb1 : ∀ i, l • b1 i = 0)

end Tate

section Frob

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)

/-- **Trace from a Frobenius-equivariant `H ≃ Pic⁰(X̄)[l^n]`** (Core B as a hypothesis): if `π (Φ (f x)) = q Φ x`,
then `Tr(f^m | H) = 1 + q^m - N_m` for every `m ≥ 1`. -/
theorem trace_of_picEquiv (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} (hN : N = l ^ n)
    (hlq : ¬ l ∣ Fintype.card Fq) (hB : CoreBHyp hk l) {H : Type*} [AddCommGroup H] [Module (ZMod N) H]
    (f : Module.End (ZMod N) H) (Φ : H ≃+ PicBar0N (AlgebraicClosure F) hk N)
    (hΦ : ∀ x, piBar (AlgebraicClosure F) hk (Φ (f x) : PicBar (AlgebraicClosure F) hk) =
      Fintype.card Fq • (Φ x : PicBar (AlgebraicClosure F) hk)) (m : ℕ) (hm : 1 ≤ m) :
    LinearMap.trace (ZMod N) H (f ^ m) =
      (((1 + (Fintype.card Fq : ℤ) ^ m - (numPoints Fq F m : ℤ)) : ℤ) : ZMod N) := by
  have : Fact (1 < N) := ⟨hN ▸ Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt⟩
  have hqu : IsUnit ((Fintype.card Fq : ℕ) : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime, hN]
    exact Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hlq))
  obtain ⟨k0, hdiv, b1, hb1, M, hTate, hM, -, -, htopiff, -, -⟩ :=
    tate_module_Pic (Ω := AlgebraicClosure F) hk l hlq
  obtain ⟨c, hcard, -, -, hNm, h0, -, hfe, -⟩ := zeta_RH_FE hk
  obtain ⟨P0, hP0c, hMP⟩ := hB.2 k0 hdiv b1 hb1 M (fun j => (hTate j).1) hM c hcard.le hNm
  have hP0 : P0.Monic := by
    refine Polynomial.monic_of_injective (f := Int.castRingHom ℂ) Int.cast_injective ?_
    rw [hP0c]
    exact monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  obtain ⟨E, Mn, hMn, hE⟩ := exists_tateEquivN hk hdiv b1 hb1 (fun j => (hTate j).1) (fun j => (hTate j).2)
    (htopiff.mpr hB.1) hM n N hN P0 hMP
  obtain ⟨sk, hs⟩ := trace_pow_of_coords (Φ.trans E.symm) f Mn _ hqu
    (coords_key Φ E f (piBar (AlgebraicClosure F) hk) Mn _ hΦ hE) P0 hP0 c hP0c hMn h0 hfe
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [(hs k).1]
  have h := hNm (k + 1) (by omega)
  rw [(hs k).2] at h
  have h' : ((sk k : ℤ) : ℂ) = ((1 + (Fintype.card Fq : ℤ) ^ (k + 1) - (numPoints Fq F (k + 1) : ℤ) : ℤ) : ℂ) := by
    push_cast
    linear_combination h
  have h'' : sk k = 1 + (Fintype.card Fq : ℤ) ^ (k + 1) - (numPoints Fq F (k + 1) : ℤ) := by exact_mod_cast h'
  rw [h'']

variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

end Frob

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Lef =====
section

/-!
# S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)

* `free_of_picEquiv`, `free_curveH1par`: `H¹_par(Ū, ℤ/l^n) ≅ Pic⁰(X̄)[l^n]` is finite free over `ℤ/l^n`.
* `trace_frobH1c_curve`: `Tr(F^m | H¹_c(Ū, ℤ/l^n)) = #Fix(τ^m) - 1 + (1 + q^m - N_m)`, where `τ` is the
  permutation of the boundary `S` in any boundary-compatible geometric Frobenius `T_{φ⁻¹, τ, h}` (from the exact sequence `0 → H⁰ → ⊕_S Λ → H¹_c → H¹_par → 0`).
* `trace_geomFrobH2c_triv`: `Tr(F^m | H²_c(Ū, ℤ/l^n)) = q^m`.
* `lefschetz_triv`: `Tr(F^m | H²_c) - Tr(F^m | H¹_c) = N_m - #Fix(τ^m)` in `ℤ/l^n`, every `m ≥ 1`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer

section Lef

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)

/-- A module additively isomorphic to `Pic⁰(X̄)[l^n]` is finite free over `ℤ/l^n` (CoreA + divisibility). -/
theorem free_of_picEquiv (l n : ℕ) [Fact l.Prime] {N : ℕ} (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq)
    (hB : CoreBHyp hk l) {H : Type*} [AddCommGroup H] [Module (ZMod N) H]
    (Φ : H ≃+ PicBar0N (AlgebraicClosure F) hk N) : Module.Free (ZMod N) H ∧ Module.Finite (ZMod N) H := by
  subst hN
  obtain ⟨k0, hdiv, b1, hb1, M, hTate, hM, -, -, htopiff, -, -⟩ :=
    tate_module_Pic (Ω := AlgebraicClosure F) hk l hlq
  obtain ⟨E, -⟩ := exists_tateEquiv hk hdiv b1 hb1 (fun j => (hTate j).1) (fun j => (hTate j).2)
    (htopiff.mpr hB.1) hM n
  let Ψ := Φ.trans E.symm
  let ΨL : H ≃ₗ[ZMod (l ^ n)] (Fin (2 * genusF Fq F) → ZMod (l ^ n)) := Ψ.toLinearEquiv (ZMod.map_smul Ψ)
  exact ⟨Module.Free.of_equiv ΨL.symm, Module.Finite.equiv ΨL.symm⟩

variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

end Lef

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CoreB_Key =====
section

/-!
# Core B, O6: `‖deg F‖_l = ‖det F(M)‖_l` through Tate coordinates (for `deg F ≠ 0`)

* Tate matrices are closed under `0`, `-`, `+`, integer constants and polynomial evaluation (`isTateMat_aeval`).
* `h1inj_of_injective`, `h1span_of_card`: the basis hypotheses of CoreA from injectivity of `tateMap 1` and the count
  `#D[l] ≤ l^s`.
* `iotaG`: `D = l^k0 A ↪ Pic⁰(X̄)`, `π`-equivariant; `card_kerD`: `#ker F(π|D) = l ^ v_l(#ker F(π))`.
* `norm_deg_eq_norm_det` (hkey for `deg F ≠ 0`).
-/

set_option autoImplicit false

open Polynomial
open scoped Matrix

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.CoreA

section Gen

variable {G : Type*} [AddCommGroup G] {l : ℕ} [Fact l.Prime]
variable (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G) (hb1 : ∀ i, l • b1 i = 0)

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

variable (l k0 : ℕ) [hl : Fact l.Prime]

theorem iotaG_endD (x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range) :
    iotaG Fq F Ω hk l k0 (endD (piA Ω hk l) (l ^ k0) x) = piBar0 Fq F Ω hk (iotaG Fq F Ω hk l k0 x) :=
  Subtype.ext rfl

theorem iotaG_aeval (P : ℤ[X]) (x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range) :
    iotaG Fq F Ω hk l k0 (aeval (endD (piA Ω hk l) (l ^ k0)) P x) =
      aeval (piBar0 Fq F Ω hk) P (iotaG Fq F Ω hk l k0 x) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have e : (aeval (endD (piA Ω hk l) (l ^ k0)) (P + Q)) x =
        aeval (endD (piA Ω hk l) (l ^ k0)) P x + aeval (endD (piA Ω hk l) (l ^ k0)) Q x := by
      rw [map_add]; rfl
    rw [e, map_add, hP, hQ, map_add, LinearMap.add_apply]
  | monomial n a =>
    have e1 : ∀ y, (aeval (endD (piA Ω hk l) (l ^ k0)) (monomial n a)) y =
        a • (endD (piA Ω hk l) (l ^ k0))^[n] y := fun y => by
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_X, aeval_C, algebraMap_int_eq,
        Int.coe_castRingHom]
      show (a : AddMonoid.End _) ((endD (piA Ω hk l) (l ^ k0) ^ n) y) = _
      rw [AddMonoid.End.intCast_apply, AddMonoid.End.coe_pow]
    have e2 : ∀ y, (aeval (piBar0 Fq F Ω hk) (monomial n a)) y = a • (piBar0 Fq F Ω hk)^[n] y := fun y => by
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_X, aeval_C, algebraMap_int_eq,
        Int.coe_castRingHom, Module.End.mul_apply, Module.End.intCast_apply, Module.End.coe_pow]
    rw [e1, e2, map_zsmul,
      Function.Semiconj.iterate_right (fun y => iotaG_endD Fq F Ω hk l k0 y) n x]

/-- `#ker F(π|D) = #(ker F(π) on Pic⁰(X̄))[l^∞] = l ^ v_l(#ker F(π))` (`A` divisible, so `D = A`). -/
theorem card_kerD (hA : ∀ y : Aℓ Ω hk l, ∃ z, l • z = y) (P : ℤ[X])
    [Finite (LinearMap.ker (aeval (piBar0 Fq F Ω hk) P))] :
    Nat.card {x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range // aeval (endD (piA Ω hk l) (l ^ k0)) P x = 0} =
      l ^ padicValNat l (Nat.card (LinearMap.ker (aeval (piBar0 Fq F Ω hk) P))) := by
  rw [← card_primaryComponent l]
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨⟨iotaG Fq F Ω hk l k0 x.1, ?_⟩, ?_⟩) ⟨?_, ?_⟩)
  · rw [LinearMap.mem_ker, ← iotaG_aeval, x.2]
    exact map_zero _
  · obtain ⟨k, hx⟩ := AddCommGroup.mem_primaryComponent.mp x.1.1.2
    exact AddCommGroup.mem_primaryComponent.mpr ⟨k, Subtype.ext (Subtype.ext (by
      simp only [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero]; exact hx))⟩
  · intro a b h
    exact Subtype.ext (iotaG_injective Fq F Ω hk l k0 (congrArg (fun z => z.1.1) h))
  · intro y
    have hyA : (y.1.1.1 : PicBar Ω hk) ∈ AddCommGroup.primaryComponent (PicBar Ω hk) l := by
      obtain ⟨k, hy⟩ := AddCommGroup.mem_primaryComponent.mp y.2
      have h1 := congrArg (fun z => (z.1.1 : PicBar Ω hk)) hy
      simp only [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero] at h1
      exact AddCommGroup.mem_primaryComponent.mpr ⟨k, h1⟩
    let w : (smulHom (Aℓ Ω hk l) (l ^ k0)).range := ⟨⟨y.1.1.1, hyA⟩, mem_range_pow hA k0 _⟩
    have hw : iotaG Fq F Ω hk l k0 w = y.1.1 := Subtype.ext rfl
    refine ⟨⟨w, ?_⟩, ?_⟩
    · apply iotaG_injective Fq F Ω hk l k0
      rw [iotaG_aeval, hw, LinearMap.mem_ker.mp y.1.2, map_zero (iotaG Fq F Ω hk l k0)]
    · exact Subtype.ext (Subtype.ext hw)

end Spec

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_CupDuality_KumPicDiv =====
section

/-!
# S4-CurveDuality, O5b (ii): `Pic⁰(X̄)` is `l^n`-divisible for `l ∤ q`

CB1 (`CoreB.divisible_Aℓ`) divides only the `l`-primary part. Here:
* `exists_pow_smul_of_torsion` (generic): in an abelian group whose `l`-primary part is `l`-divisible, a torsion element
  of a subgroup `H ⊇ G[l^∞]` is `l^n`-divisible inside `H`;
* `ofBar_mem_fixedBar`, **`torsion_PicBar0`**: `Pic⁰(X̄)` is torsion (each class lies in the finite `Pic⁰(X̄)^(π^m)`);
* **`pic0Bar_divisible`**, **`pic0K_divisible`**: every class of `Pic⁰(X̄)`, resp. of `Pic⁰(F̄ / k̄)`, is `l^n`-divisible.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.CupDuality

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.CoreA

section Gen

variable {G : Type*} [AddCommGroup G]

end Gen

section Pic

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- **`Pic⁰(X̄)` is torsion.** -/
theorem torsion_PicBar0 (x : PicBar Ω hk) (hx : x ∈ PicBar0 Ω hk) : ∃ m : ℕ, 0 < m ∧ m • x = 0 := by
  revert hx
  refine AddCommGroup.DirectLimit.induction_on x fun j y => ?_
  intro hx
  obtain ⟨c, -, -, -, h4⟩ := classNumber_bar (Ω := Ω) hk
  have := (h4 (lev j)).1
  have hmem : ofBar Ω hk j y ∈ (fixedBar Ω hk (lev j) ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)) :=
    AddSubgroup.mem_inf.2 ⟨ofBar_mem_fixedBar Fq F Ω hk j y, hx⟩
  refine ⟨Nat.card (fixedBar Ω hk (lev j) ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)), Nat.card_pos, ?_⟩
  have h0 := card_nsmul_eq_zero'
    (x := (⟨_, hmem⟩ : (fixedBar Ω hk (lev j) ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk))))
  have h1 := congrArg (AddSubgroup.subtype (fixedBar Ω hk (lev j) ⊓ PicBar0 Ω hk)) h0
  rw [map_nsmul, map_zero] at h1
  exact h1

end Pic

end RamanujanPetersson.CupDuality


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

include hq he in
set_option maxHeartbeats 1600000 in
/-- **The total cone's residue hypothesis with the Frobenius twist** (S3 chart, `π` cut out by `M`): a `ResHyp` whose
generators satisfy `hTW` of `h2Equiv_frob` at `ψ = φ⁻¹`, `trueTau`, `trueH`, `c = q` for every Frobenius lift `φ`. -/
theorem exists_resHyp_tw {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Λ : Type} [CommRing Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    [Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map π)] :
    ∃ H : ResHyp Λ π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia,
      ∀ φ : Pi1 (Places.Rfin Fq F) F, IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) φ →
        ∀ s (e : Z1 (regRep Λ π) (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia (trueTau D φ⁻¹ s))),
          (e : ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia (trueTau D φ⁻¹ s)) →
              MonoidAlgebra Λ Gf)
            (conjSub (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F))
              (bdry_mem (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ (trueTau D φ⁻¹)
                (trueH D φ⁻¹) (trueCompat D φ⁻¹) s) (H.sg s)) =
            (Fintype.card Fq : Λ) •
              (e : ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia (trueTau D φ⁻¹ s)) →
                MonoidAlgebra Λ Gf) (H.sg (trueTau D φ⁻¹ s)) := by
  let _ : Fintype (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Fintype.ofFinite _
  let _ : DecidableEq (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Classical.decEq _
  have hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (D.P s) := fun s => (hDB _).1 (D.mem s)
  have hcov : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q →
      ∃ s, ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), Q = g • D.P s :=
    fun Q hQ => D.cover Q ((hDB Q).2 hQ)
  have hNF : ((l ^ n : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨D', hTWD⟩ := exists_resDat_tw hq he hNF hPic hM hMU π hπM D.P hP hcov D.disj D.inertia (fun _ => rfl)
  have hMo : ∀ m : MonoidAlgebra Λ Gf, (l ^ n) • m = 0 := fun m => by
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  refine ⟨D'.toResHyp hΛ hπ, fun φ hφ s e => ?_⟩
  have hu := fun s => trueTau_smul D φ⁻¹ s
  have hg : IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq)
      (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F))⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact isFrobLift_geo_mul (inv_mem (trueH D φ⁻¹ s).2) hφ
  have hc : (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F))⁻¹ * D'.σ s *
      (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F)) ∈ D'.J (trueTau D φ⁻¹ s) :=
    (D'.hJ _ _).2 ⟨bdry_mem _ D.inertia φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹) (trueCompat D φ⁻¹) s _ (D'.hσ s),
      by rw [map_mul, map_mul, D'.hσπ s, mul_one, map_inv, inv_mul_cancel]⟩
  have h1 := hTWD s (trueTau D φ⁻¹ s) (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F)) hg (hu s)
    (MonoidAlgebra Λ Gf) hMo (resK π _ (D'.J (trueTau D φ⁻¹ s)) (D'.hJ (trueTau D φ⁻¹ s)) e)
    (resK_lc π _ _ _ e) (resK_add π _ _ _ e) hc
  exact h1.trans (Nat.cast_smul_eq_nsmul Λ _ _).symm

end S3

end

end Lefschetz
end RamanujanPetersson


end


