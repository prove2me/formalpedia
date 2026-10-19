-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P15
-- name    : QAlgorithms_Papers_Independent_Frontier18_P15
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:03:52.922536+00:00
-- url     : https://prove2.me/theorems/8a52f76e-aa45-40dd-8503-3b54f7ef4d12
-- title:
--   Definitions for A Resource Framework for Quantum Shannon Theory
-- statement:
--   The objects the formalized statements of *A Resource Framework for Quantum Shannon Theory* (arXiv:quant-ph/0512015) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `EntropicQuantity`: The five entropy expressions introduced on PDF p.7, with arbitrary grouping of finite systems. Conditioning systems can be one dimensional.
--   - `entropicValue`: Evaluate the p.7 quantities on A(BX). The first four use the bipartition A : BX, while the last uses A : B conditioned on X. All entropies are in bits. The accepted marginalAX traces the final factor of A(XB), so its argument explicitly swaps B and X on both matrix indices before tracing B.
--   - `coherentLift`: Square-root amplitudes for a law in its labelled orthonormal basis. Source: PDF p.9.
--   - `onAlice`: Apply a channel to Alice while preserving the entire passive second factor, including off-diagonal blocks. Source: PDF pp.5,7,10.
--   - `UnitProgram`: A finite one-way program. Local CPTP maps are free; each send consumes exactly one noiseless qubit or cbit channel. Source: PDF pp.10–14, specialized to p.11 units. The four indices are initial and final Alice/Bob memory sizes in qubits.
--   - `UnitProgram.quantumUses`: Quantum channel uses counted in the syntax, independently of local processing. Source: PDF pp.2,11,13–14.
--   - `UnitProgram.classicalUses`: Classical channel uses counted separately. Source: PDF pp.2,11,13–14.
--   - `beforeSend`: Pull an output basis configuration back across a send: the first Bob bit was formerly the first Alice bit. Source: PDF p.11, identity-channel convention.
--   - `UnitProgram.run`: Evaluation on joint density operators. Classical sends dephase the transmitted bit; quantum sends preserve every matrix entry. Local maps preserve the other party. Source: PDF pp.5,11,13–14.
--   - `unitCodeInput`: Insert e initial Bell pairs, with all external messages on Alice. The initial state contains no other shared resource. Source: PDF pp.11,13–14.
--   - `unitCodeTarget`: Joint ideal output: classical identity on c bits, quantum identity on q qubits, and e final Bell pairs, as one tensor product. The messages are on Bob and the Bell pairs are split between Alice and Bob. Source: PDF pp.8,11–14,30.
--   - `UnitConversionCode`: A simultaneous finite unit-conversion code, with separately specified initial and final Bell counts. The consumed channel counts are computed from program syntax. The code is fixed before any reference or input state. Source: PDF pp.11–14,30.
--   - `UnitConversionCode.channel`: The implemented external channel, including returned entanglement. Source: PDF pp.13–14; unit-only specialization.
--   - `UnitConversionCode.HasErrorAtMost`: One joint full-trace-norm approximation test for both messages and final Bell pairs, for every reference and every joint input. Source: PDF p.8 eq.(4), pp.13–14. Using one joint ideal target forces the returned Bell resource to be decoupled.
--   - `UnitConversionCode.net`: Net outputs minus consumed resources, in the order (cbit, qubit, ebit), without natural-number truncation. Source: PDF p.30, signed-resource convention (29).
--   - `UnitRateAchievable`: Vanishing-error/slack achievability for simultaneous signed unit conversions. For every error and rate slack, every sufficiently large positive blocklength has one code passing the joint test and achieving all three net rates simultaneously. Source: PDF pp.22,29–30, specialized to unit resources; this explicit operational presentation is introduced for the supporting-paper objective, not a quoted theorem. No TP/SD/ED cone or theorem is used in the definition.
--   - `operationalUnitRegion`: Closed operational signed unit-resource region, independent of the cone of teleportation, dense coding and entanglement distribution. Source: PDF pp.22,30; compare arXiv:0901.3038v3, Definition 2, PDF p.4. Equivalence with either paper's abstract signed RI remains an explicit deferred bridge, not a defining assumption.
-- source:
--   A Resource Framework for Quantum Shannon Theory, arXiv:quant-ph/0512015v1, https://arxiv.org/abs/quant-ph/0512015v1

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P03

/-!
Statements from Devetak–Harrow–Winter, arXiv:quant-ph/0512015v1.
All page citations are PDF pages. The local unit-code model specializes the operational
rules of pp.10–14 to noiseless unit resources (p.11), with the signed-rate convention
of p.30. It does not define the TP/SD/ED cone or identify it with an operational region.
The full generalized-resource calculus is deferred; see this unit's GAPS.json.
Source correction reserved for deferred Lemma 4.1(3), PDF p.29: the printed N ∘ M
has incompatible displayed types. The intended target is (M ⊗ id_Bprime) ∘ N,
retaining Bob's output. No theorem using the printed composition is asserted.
Compilation is pending the batch mechanical handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Frontier18.P15

/-- The five entropy expressions introduced on PDF p.7, with arbitrary grouping of
finite systems. Conditioning systems can be one dimensional. -/
inductive EntropicQuantity where
  | entropy
  | conditionalEntropy
  | mutualInformation
  | coherentInformation
  | conditionalMutualInformation
  deriving DecidableEq

/-- Evaluate the p.7 quantities on A(BX). The first four use the bipartition A : BX,
while the last uses A : B conditioned on X. All entropies are in bits.
The accepted marginalAX traces the final factor of A(XB), so its argument explicitly
swaps B and X on both matrix indices before tracing B. -/
def entropicValue {a b x : ℕ} (quantity : EntropicQuantity)
    (rho : Matrix (Fin a × (Fin b × Fin x)) (Fin a × (Fin b × Fin x)) ℂ) : ℝ :=
  match quantity with
  | .entropy => vnEntropy rho
  | .conditionalEntropy => vnEntropy rho - vnEntropy (traceLeft rho)
  | .mutualInformation =>
      vnEntropy (traceRight rho) + vnEntropy (traceLeft rho) - vnEntropy rho
  | .coherentInformation => vnEntropy (traceLeft rho) - vnEntropy rho
  | .conditionalMutualInformation =>
      vnEntropy (QAlgorithms.Papers.Independent.Dependency50.P03.marginalAX
        (fun (i j : Fin a × (Fin x × Fin b)) =>
          rho (i.1, (i.2.2, i.2.1)) (j.1, (j.2.2, j.2.1)))) +
        vnEntropy (traceLeft rho) - vnEntropy rho -
        vnEntropy (traceLeft (traceLeft rho))

/-- Square-root amplitudes for a law in its labelled orthonormal basis. Source: PDF p.9. -/
def coherentLift {d : ℕ} (p : Fin d → ℝ) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun i => (Real.sqrt (p i) : ℂ)

/-- Apply a channel to Alice while preserving the entire passive second factor,
including off-diagonal blocks. Source: PDF pp.5,7,10. -/
def onAlice {A Aout B : Type*} (E : Superop A Aout) :
    Superop (A × B) (Aout × B) :=
  fun rho i j => E (fun a a' => rho (a, i.2) (a', j.2)) i.1 j.1

/-! ## Operational signed unit conversions

These definitions instantiate the paper's primitive operations and full reference-extended
distance for the unit-only specialization requested by the supporting-paper objective.
They are not a replacement definition of the full resource class R. Initial and final Bell
registers and both kinds of communication are counted separately. All memory sizes and all
local CPTP maps are finite but unrestricted. Qubits 0 is a one-dimensional null register.
-/

/-- A finite one-way program. Local CPTP maps are free; each send consumes exactly
one noiseless qubit or cbit channel. Source: PDF pp.10–14, specialized to p.11 units.
The four indices are initial and final Alice/Bob memory sizes in qubits. -/
inductive UnitProgram : ℕ → ℕ → ℕ → ℕ → Type where
  | skip (a b : ℕ) : UnitProgram a b a b
  | alice {a aout b : ℕ} (E : Superop (Qubits a) (Qubits aout))
      (hE : IsChannel E) : UnitProgram a b aout b
  | bob {a b bout : ℕ} (D : Superop (Qubits b) (Qubits bout))
      (hD : IsChannel D) : UnitProgram a b a bout
  | sendQuantum (a b : ℕ) : UnitProgram (a + 1) b a (b + 1)
  | sendClassical (a b : ℕ) : UnitProgram (a + 1) b a (b + 1)
  | thenDo {a b c d e f : ℕ} (P : UnitProgram a b c d)
      (Q : UnitProgram c d e f) : UnitProgram a b e f

/-- Quantum channel uses counted in the syntax, independently of local processing.
Source: PDF pp.2,11,13–14. -/
def UnitProgram.quantumUses {a b c d : ℕ} : UnitProgram a b c d → ℕ
  | .skip _ _ => 0
  | .alice _ _ => 0
  | .bob _ _ => 0
  | .sendQuantum _ _ => 1
  | .sendClassical _ _ => 0
  | .thenDo P Q => P.quantumUses + Q.quantumUses

/-- Classical channel uses counted separately. Source: PDF pp.2,11,13–14. -/
def UnitProgram.classicalUses {a b c d : ℕ} : UnitProgram a b c d → ℕ
  | .skip _ _ => 0
  | .alice _ _ => 0
  | .bob _ _ => 0
  | .sendQuantum _ _ => 0
  | .sendClassical _ _ => 1
  | .thenDo P Q => P.classicalUses + Q.classicalUses

/-- Pull an output basis configuration back across a send: the first Bob bit was
formerly the first Alice bit. Source: PDF p.11, identity-channel convention. -/
def beforeSend {a b : ℕ} (z : Qubits a × Qubits (b + 1)) :
    Qubits (a + 1) × Qubits b :=
  (Fin.cases (z.2 0) z.1, fun i => z.2 i.succ)

/-- Evaluation on joint density operators. Classical sends dephase the transmitted
bit; quantum sends preserve every matrix entry. Local maps preserve the other party.
Source: PDF pp.5,11,13–14. -/
def UnitProgram.run {a b c d : ℕ} : UnitProgram a b c d →
    Superop (Qubits a × Qubits b) (Qubits c × Qubits d)
  | .skip _ _ => fun rho => rho
  | .alice E _ => onAlice E
  | .bob D _ => idTensorSuperop D
  | .sendQuantum _ _ => fun rho i j => rho (beforeSend i) (beforeSend j)
  | .sendClassical _ _ => fun rho i j =>
      if i.2 0 = j.2 0 then rho (beforeSend i) (beforeSend j) else 0
  | .thenDo P Q => Q.run ∘ P.run

/-- Insert e initial Bell pairs, with all external messages on Alice. The initial
state contains no other shared resource. Source: PDF pp.11,13–14. -/
def unitCodeInput (messages e : ℕ) :
    Superop (Qubits messages) (Qubits (messages + e) × Qubits e) :=
  fun rho i j =>
    rho (fun k => i.1 (Fin.castAdd e k)) (fun k => j.1 (Fin.castAdd e k)) *
      pureDensity (maxEntangled e)
        ((fun k => i.1 (Fin.natAdd messages k)), i.2)
        ((fun k => j.1 (Fin.natAdd messages k)), j.2)

/-- Joint ideal output: classical identity on c bits, quantum identity on q qubits,
and e final Bell pairs, as one tensor product. The messages are on Bob and the
Bell pairs are split between Alice and Bob. Source: PDF pp.8,11–14,30. -/
def unitCodeTarget (c q e : ℕ) :
    Superop (Qubits (c + q)) (Qubits e × Qubits ((c + q) + e)) :=
  fun rho i j =>
    if (fun k : Fin c => i.2 (Fin.castAdd e (Fin.castAdd q k))) =
        (fun k : Fin c => j.2 (Fin.castAdd e (Fin.castAdd q k))) then
      rho (fun k => i.2 (Fin.castAdd e k)) (fun k => j.2 (Fin.castAdd e k)) *
        pureDensity (maxEntangled e)
          (i.1, fun k => i.2 (Fin.natAdd (c + q) k))
          (j.1, fun k => j.2 (Fin.natAdd (c + q) k))
    else 0

/-- A simultaneous finite unit-conversion code, with separately specified initial
and final Bell counts. The consumed channel counts are computed from program syntax.
The code is fixed before any reference or input state. Source: PDF pp.11–14,30. -/
structure UnitConversionCode (classicalOutput quantumOutput initialBell finalBell : ℕ) where
  program : UnitProgram ((classicalOutput + quantumOutput) + initialBell) initialBell
    finalBell ((classicalOutput + quantumOutput) + finalBell)

/-- The implemented external channel, including returned entanglement.
Source: PDF pp.13–14; unit-only specialization. -/
def UnitConversionCode.channel {c q ei eo : ℕ} (code : UnitConversionCode c q ei eo) :
    Superop (Qubits (c + q)) (Qubits eo × Qubits ((c + q) + eo)) :=
  code.program.run ∘ unitCodeInput (c + q) ei

/-- One joint full-trace-norm approximation test for both messages and final Bell
pairs, for every reference and every joint input. Source: PDF p.8 eq.(4), pp.13–14.
Using one joint ideal target forces the returned Bell resource to be decoupled. -/
def UnitConversionCode.HasErrorAtMost {c q ei eo : ℕ}
    (code : UnitConversionCode c q ei eo) (epsilon : ℝ) : Prop :=
  0 ≤ epsilon ∧ ∀ (r : ℕ), 0 < r →
    ∀ xi : Matrix (Fin r × Qubits (c + q)) (Fin r × Qubits (c + q)) ℂ,
      IsDensityMatrix xi →
      traceNorm (idTensorSuperop code.channel xi -
        idTensorSuperop (unitCodeTarget c q eo) xi) ≤ epsilon

/-- Net outputs minus consumed resources, in the order (cbit, qubit, ebit), without
natural-number truncation. Source: PDF p.30, signed-resource convention (29). -/
def UnitConversionCode.net {c q ei eo : ℕ} (code : UnitConversionCode c q ei eo) :
    Fin 3 → ℝ :=
  ![(c : ℝ) - (code.program.classicalUses : ℝ),
    (q : ℝ) - (code.program.quantumUses : ℝ), (eo : ℝ) - (ei : ℝ)]

/-- Vanishing-error/slack achievability for simultaneous signed unit conversions.
For every error and rate slack, every sufficiently large positive blocklength has
one code passing the joint test and achieving all three net rates simultaneously.
Source: PDF pp.22,29–30, specialized to unit resources; this explicit operational
presentation is introduced for the supporting-paper objective, not a quoted theorem.
No TP/SD/ED cone or theorem is used in the definition. -/
def UnitRateAchievable (rate : Fin 3 → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ (c q ei eo : ℕ) (code : UnitConversionCode c q ei eo),
        code.HasErrorAtMost epsilon ∧
          ∀ i : Fin 3, (n : ℝ) * (rate i - delta) ≤ code.net i

/-- Closed operational signed unit-resource region, independent of the cone of
teleportation, dense coding and entanglement distribution. Source: PDF pp.22,30;
compare arXiv:0901.3038v3, Definition 2, PDF p.4. Equivalence with either paper's
abstract signed RI remains an explicit deferred bridge, not a defining assumption. -/
def operationalUnitRegion : Set (Fin 3 → ℝ) :=
  closure {rate | UnitRateAchievable rate}

/-! ### Sanity examples for the new definitions -/

example {A B : Type*} [Fintype B] :
    traceRight (0 : Matrix (A × B) (A × B) ℂ) = 0 := by
  ext i j
  simp [traceRight]

example {a b x : ℕ}
    (rho : Matrix (Fin a × (Fin b × Fin x)) (Fin a × (Fin b × Fin x)) ℂ) :
    entropicValue .coherentInformation rho = vnEntropy (traceLeft rho) - vnEntropy rho := by
  rfl

example {d : ℕ} (p : Fin d → ℝ) (i : Fin d) :
    coherentLift p i = (Real.sqrt (p i) : ℂ) := by
  rfl

example {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ) :
    onAlice (fun x : Matrix A A ℂ => x) rho = rho := by
  rfl

example (a b : ℕ) :
    (UnitProgram.thenDo (.sendClassical (a + 1) b) (.sendQuantum a (b + 1))).classicalUses = 1 ∧
    (UnitProgram.thenDo (.sendClassical (a + 1) b) (.sendQuantum a (b + 1))).quantumUses = 1 := by
  constructor <;> rfl

example (a b : ℕ) (rho : Matrix (Qubits a × Qubits b) (Qubits a × Qubits b) ℂ) :
    (UnitProgram.skip a b).run rho = rho := by
  rfl

example (i j : Qubits 0 × Qubits 1) (rho : Matrix (Qubits 1 × Qubits 0)
    (Qubits 1 × Qubits 0) ℂ) (h : i.2 0 ≠ j.2 0) :
    (UnitProgram.sendClassical 0 0).run rho i j = 0 := by
  simp [UnitProgram.run, h]

example (c q ei eo : ℕ) (code : UnitConversionCode c q ei eo) :
    code.net 2 = (eo : ℝ) - (ei : ℝ) := by
  rfl

example : IsClosed operationalUnitRegion := by
  exact isClosed_closure

end QAlgorithms.Papers.Independent.Frontier18.P15


