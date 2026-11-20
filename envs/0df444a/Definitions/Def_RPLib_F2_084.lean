-- Prove2me | Definitions.Def_RPLib_F2_084
-- name    : RPLib_F2_084
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T18:31:20.779302+00:00
-- url     : https://prove2.me/theorems/dc6344d3-b1a6-4e59-ab77-5677d182cf68
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 084 (part 1 of file 063 of 70)
-- statement:
--   File 084 (part 1 of file 063 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CP4a_Bridge`: S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)
--   * `S4.Def_RP_CP4a_Lef`: S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_048
import Definitions.Def_RPLib_F2_052

/-!
# Ramanujan-Petersson curve library (flat edition), file 084 (part 1 of file 063 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CP4a_Bridge`: S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)
* `S4.Def_RP_CP4a_Lef`: S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)
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

variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

include hq he hNf hNi hζ hζΓ hDB hlift hNF in
set_option maxHeartbeats 1000000 in
/-- **Trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)`** (Core B as a hypothesis; review R4):
`Tr(F^m | H¹_par) = 1 + q^m - N_m` for every `m ≥ 1`. (Instance unification on `H¹_par` is slow, about 14 s.) -/
theorem trace_frobPar (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq)
    (hB : CoreBHyp hk l) (φ : Pi1 (Rfin Fq F) F) (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    (m : ℕ) (hm : 1 ≤ m) :
    LinearMap.trace (ZMod N) _ (frobPar D φ ^ m) =
      (((1 + (Fintype.card Fq : ℤ) ^ m - (numPoints Fq F m : ℤ)) : ℤ) : ZMod N) :=
  (exists_kummerPicEquiv_frob hk hq he hNf hNi hζ hζΓ D hDB hlift hNF).elim fun Φ hΦ =>
    trace_of_picEquiv hk l n hn hN hlq hB (frobPar D φ) Φ (fun x => hΦ.2 φ hφ x.1 x.2) m hm

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

end Lef

end RamanujanPetersson.CP4a


end


