-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_Supplement_integerOutput
-- name    : UnaryParityLifting_Exact_Supplement_integerOutput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:46:39.014473+00:00
-- url     : https://prove2.me/theorems/86eeec01-92dc-41bd-998b-363b279c20f7
-- title:
--   Integer constant certificates, term counts and lifting degree
-- statement:
--   Use the unchanged real constant-multiplier certificate, its formal identity, termwise degree and mass W. Integer output means every nonnegative axiom coefficient and every collected conical coefficient is a natural number. M counts nonzero coefficients on both sides. Fix unary output size as W plus the positive binary listing cost of each used clause and term and a coefficient separator; no unused input clauses are charged.
--
--   $$T_{N,d}=\sum_{j=0}^{\min(d,N)}2^j\binom Nj,\quad T=(mN+2)S,\quad R=\min\{N,\max\{w,\lceil c_g^{-1}\log_2(2T)\rceil\}\}.$$
--
--   The two quantities T and T_(N,d) remain separate. The constant c_g is the published gadgetExponent, exactly (3.3). Terms are collected before support is counted, and the empty term is included. Natural ceiling agrees with the integer ceiling in the positive source domain. These definitions assert no conversion theorem.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), pp.6–7, Definition 2.2; p.15, equation (4.7); pp.24–25, Lemma A.1 and equation (A.1)

import Definitions.Def_UnaryParityLifting_Exact_Supplement_encoding
import Definitions.Def_UnaryParityLifting_Exact_conicalRepresentations
import Definitions.Def_UnaryParityLifting_Exact_averaging

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Integrality is a property of the unchanged real certificate data. -/
def IntegerOutput {V : Type} {F : LiftSAParity.CNF V} (q : RealCertificate F) : Prop :=
  (∀ C, ∃ a : ℕ, (q.axiomCoefficient C : ℝ) = a) ∧
  (∀ t, ∃ a : ℕ, (q.conical.coefficient t : ℝ) = a)
def coefficientCount {V : Type} [Fintype V] {F : LiftSAParity.CNF V}
    (q : RealCertificate F) : ℕ :=
  q.axiomSupport + (Finset.univ.filter (fun t => q.conical.coefficient t ≠ 0)).card
def termCount (N d : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min d N + 1), 2 ^ j * Nat.choose N j
/-- Fixed ordinary term listing with unary weights; zero coefficients are omitted. -/
def termBits {V : Type} [Fintype V] (t : Term V) : ℕ :=
  2 + termDegree t * (2 + indexBits V)
def unaryOutputSize {V : Type} [Fintype V] {F : LiftSAParity.CNF V}
    (q : RealCertificate F) : ℝ :=
  q.mass +
    (∑ C : {C // C ∈ F}, if q.axiomCoefficient C = 0 then 0 else (clauseBits C.val + 2 : ℕ)) +
    (∑ t : Term V, if q.conical.coefficient t = 0 then 0 else (termBits t + 2 : ℕ))
/-- Exactly (4.7), with ceil to a natural and the full-degree cap. -/
def liftingDegree {m : ℕ} (g : (Fin m → Bool) → Bool) (N w S : ℕ) : ℕ :=
  min N (max w ⌈(gadgetExponent g)⁻¹ * Real.logb 2 (2 * (normalizationBudget m N S : ℝ))⌉₊)

end UnaryParityLifting.Exact.Supplement


