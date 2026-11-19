-- Prove2me | Definitions.Def_RPLib_S4_CDPack14d
-- name    : RPLib_S4_CDPack14d
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:11:48.162619+00:00
-- url     : https://prove2.me/theorems/3ad30ae1-7ff4-419a-bd1b-04a1bcb561b5
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 14d of 71
-- statement:
--   Part 14d of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CP4a_Lef`: S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack14c
import Definitions.Def_RPLib_S4_CDPack12

/-!
# Curve-duality library package, part 14d of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CP4a_Lef`: S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)
-/

set_option autoImplicit false

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

include hq he hNf hNi hζ hζΓ hDB hlift hNF in
theorem free_curveH1par (l n : ℕ) [Fact l.Prime] (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq)
    (hB : CoreBHyp hk l) :
    Module.Free (ZMod N) (curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) ∧
      Module.Finite (ZMod N) (curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :=
  (exists_kummerPicEquiv_frob hk hq he hNf hNi hζ hζΓ D hDB hlift hNF).elim fun Φ _ =>
    free_of_picEquiv hk l n hN hlq hB Φ

include hq he hNf hNi hζ hζΓ hDB hlift hNF in
set_option maxHeartbeats 1000000 in
/-- **`Tr(F^m | H¹_c(Ū, ℤ/l^n)) = #Fix(τ^m) - 1 + (1 + q^m - N_m)`** (Core B as a hypothesis). -/
theorem trace_frobH1c_curve [Fintype S] [DecidableEq S] [Nonempty S] (l n : ℕ) [Fact l.Prime] (hn : 0 < n)
    (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq) (hB : CoreBHyp hk l) (φ : Pi1 (Rfin Fq F) F)
    (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ) (τ : S → S)
    (h : S → pi1geo (Rfin Fq F) F (Fintype.card Fq))
    (hI : BdryCompat (pi1geo (Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ τ h) (m : ℕ) (hm : 1 ≤ m) :
    LinearMap.trace (ZMod N) (curveH1c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D)
        (frobH1c (triv F (maxUnram (Rfin Fq F) F) N) (pi1geo (Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ τ h hI
          ^ m) =
      ((Finset.univ.filter fun s => τ^[m] s = s).card : ZMod N) - 1 +
        (((1 + (Fintype.card Fq : ℤ) ^ m - (numPoints Fq F m : ℤ)) : ℤ) : ZMod N) := by
  refine trace_frobH1c_triv (pi1geo (Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ τ h hI (frobPar D φ) ?_ ?_ m ?_
  · exact h1cToH1_frobH1c (triv F (maxUnram (Rfin Fq F) F) N) (pi1geo (Rfin Fq F) F (Fintype.card Fq)) D.inertia
      φ⁻¹ τ h hI
  · exact free_curveH1par hk hq he hNf hNi hζ hζΓ D hDB hlift hNF l n hN hlq hB
  · exact trace_frobPar hk hq he hNf hNi hζ hζΓ D hDB hlift hNF l n hn hN hlq hB φ hφ m hm

/-- **`Tr(F^m | H²_c(Ū, ℤ/N)) = q^m`**. -/
theorem trace_geomFrobH2c_triv (φ : Pi1 (Rfin Fq F) F) (m : ℕ) :
    LinearMap.trace (ZMod N) (curveH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N))
        (geomFrobH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ ^ m) =
      ((Fintype.card Fq : ℕ) : ZMod N) ^ m :=
  trace_frobH2c_triv (pi1geo (Rfin Fq F) F (Fintype.card Fq)) φ⁻¹ _ m

include hq he hNf hNi hζ hζΓ hDB hlift hNF in
set_option maxHeartbeats 1000000 in
/-- **Lefschetz mod `l^n` for constant coefficients** (Core B as a hypothesis): for every `m ≥ 1`,
`Tr(F^m | H²_c) - Tr(F^m | H¹_c) = N_m - #{s ∈ S | τ^m s = s}` in `ℤ/l^n`. -/
theorem lefschetz_triv [Fintype S] [DecidableEq S] [Nonempty S] (l n : ℕ) [Fact l.Prime] (hn : 0 < n)
    (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq) (hB : CoreBHyp hk l) (φ : Pi1 (Rfin Fq F) F)
    (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ) (τ : S → S)
    (h : S → pi1geo (Rfin Fq F) F (Fintype.card Fq))
    (hI : BdryCompat (pi1geo (Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ τ h) (m : ℕ) (hm : 1 ≤ m) :
    LinearMap.trace (ZMod N) (curveH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N))
        (geomFrobH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ ^ m) -
      LinearMap.trace (ZMod N) (curveH1c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D)
        (frobH1c (triv F (maxUnram (Rfin Fq F) F) N) (pi1geo (Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ τ h hI
          ^ m) =
      (numPoints Fq F m : ZMod N) - ((Finset.univ.filter fun s => τ^[m] s = s).card : ZMod N) :=
  lefschetz_combine _ _ _ m (trace_geomFrobH2c_triv φ m)
    (trace_frobH1c_curve hk hq he hNf hNi hζ hζΓ D hDB hlift hNF l n hn hN hlq hB φ hφ τ h hI m hm)

end Lef

end RamanujanPetersson.CP4a

end


