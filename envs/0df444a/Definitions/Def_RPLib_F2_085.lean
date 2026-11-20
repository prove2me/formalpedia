-- Prove2me | Definitions.Def_RPLib_F2_085
-- name    : RPLib_F2_085
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T18:50:58.664189+00:00
-- url     : https://prove2.me/theorems/6470c183-8dd7-409d-811c-7e281c142744
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 085 (part 2 of file 063 of 70)
-- statement:
--   File 085 (part 2 of file 063 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CP4a_Lef`: S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)
--   * `S4.Def_RP_CP4a_BdryInf`: S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_048
import Definitions.Def_RPLib_F2_052
import Definitions.Def_RPLib_F2_084

/-!
# Ramanujan-Petersson curve library (flat edition), file 085 (part 2 of file 063 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CP4a_Lef`: S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)
* `S4.Def_RP_CP4a_BdryInf`: S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`
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

variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

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

-- ===== S4.Def_RP_CP4a_BdryInf =====
section

/-!
# S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`

For the chart `Rinf` at infinity of a function field `F/𝔽_q`, with `𝔽_{q^m} ⊆ K_U` for all `m` (`hζc`):
* `good_inf`: residue rings of boundary primes are finite of `q`-power order.
* `card_fix_inf`: `#{s | τ^m s = s} = #Hom_{𝔽_q}(Rinf, 𝔽_{q^m})` for the true boundary permutation `τ` of `φ⁻¹`.
* `numPoints_eq_add_fix`: `N_m = #U(𝔽_{q^m}) + #{s | τ^m s = s}`, `#U(L) := #Hom_{𝔽_q}(Rfin, L)`, `[L : 𝔽_q] = m`.
* `lefschetz_count`: `Tr(F^m | H²_c) - Tr(F^m | H¹_c) = #U(𝔽_{q^m})` in `ℤ/l^n` (Core B as a hypothesis).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover

noncomputable section

section BdryInf

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hk hq he hNf hNi hζ hζΓ hDB hlift hNF hζc in
set_option maxHeartbeats 1000000 in
/-- **Lefschetz with the point count** (Core B as a hypothesis): for the true boundary-compatible geometric
Frobenius and every `m ≥ 1`, `Tr(F^m | H²_c) - Tr(F^m | H¹_c) = #U(𝔽_{q^m})` in `ℤ/l^n`. -/
theorem lefschetz_count [Fintype S] [DecidableEq S] [Nonempty S] (l n : ℕ) [Fact l.Prime] (hn : 0 < n)
    (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq) (hB : CoreBHyp hk l) (φ : Pi1 (Rfin Fq F) F)
    (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ) (m : ℕ) (hm : 1 ≤ m)
    (L : Type) [Field L] [Algebra Fq L] [Finite L] (hL : Module.finrank Fq L = m) :
    LinearMap.trace (ZMod N) (curveH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N))
        (geomFrobH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ ^ m) -
      LinearMap.trace (ZMod N) (curveH1c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D)
        (frobH1c (triv F (maxUnram (Rfin Fq F) F) N) (pi1geo (Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹
          (trueTau D φ⁻¹) (trueH D φ⁻¹) (trueCompat D φ⁻¹) ^ m) =
      (Nat.card (Rfin Fq F →ₐ[Fq] L) : ZMod N) := by
  refine (lefschetz_triv hk hq he hNf hNi hζ hζΓ D hDB hlift hNF l n hn hN hlq hB φ hφ (trueTau D φ⁻¹)
    (trueH D φ⁻¹) (trueCompat D φ⁻¹) m hm).trans ?_
  rw [numPoints_eq_add_fix hq he D hDB hζc hφ m (by omega) L hL, Nat.cast_add, add_sub_cancel_right]

end BdryInf

end

end RamanujanPetersson.CP4a


end


