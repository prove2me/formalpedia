-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCompilerBounds
-- name    : QMAPerfectCompleteness_Proof_RepetitionCompilerBounds
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:59:58.429285+00:00
-- url     : https://prove2.me/theorems/de70304e-e38d-41ac-b9a4-104aac86ad8c
-- title:
--   Polynomial bounds for the fixed-count repetition transducer
-- statement:
--   Provides the arithmetic estimates needed to package the concrete repetition transducer as a timed computation. Bounds cover unary address remapping, per-gate and per-copy execution, output lengths, the AND suffix, and total running time. The repetition count is a fixed parameter; these auxiliary bounds do not infer running time from output size.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RepetitionCompilerBounds.lean, lines 10–219.

/- Generated from Solutions.RepetitionCompilerBounds by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClassTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_FixedBlockCopy
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Polynomial bounds for the concrete fixed-count repetition transducer. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace QMAPerfectCompleteness.Main.Repetition.CompilerTM
open QAlgorithms.Complexity (Str encNat)

lemma loadedValues_le (kind : Fin 4) (a : Fin 3 → ℕ) (R : ℕ)
    (ha : ∀ i, a i ≤ R) (i : Fin 3) : loadedValues kind a i ≤ R := by
  unfold loadedValues
  split_ifs
  · exact ha i
  · exact Nat.zero_le _

lemma readTime_le (kind : Fin 4) (a : Fin 3 → ℕ) (R : ℕ)
    (ha : ∀ i, a i ≤ R) : readTime kind a ≤ 3*(R+1) := by
  unfold readTime
  split_ifs <;> have h0 := ha 0 <;> have h1 := ha 1 <;> have h2 := ha 2 <;> omega

lemma gateTime_le (n : ℕ) (j : Fin (n+1)) (kind : Fin 4) (a : Fin 3 → ℕ) (m b R : ℕ)
    (ha : ∀ i, a i ≤ R) : gateTime n j kind a m b ≤ 100*(n+1)*(m+b+R+1) := by
  have hT (i : Fin 3) : addressTime n (.body j kind i) m b (a i) ≤ 20*(n+1)*(m+b+R+1) :=
    (addressTime_le n _ m b (a i)).trans (Nat.mul_le_mul_left _ (by have := ha i; omega))
  have h0 := hT 0
  have h1 := hT 1
  have h2 := hT 2
  have hv0 := loadedValues_le kind a R ha 0
  have hv1 := loadedValues_le kind a R ha 1
  have hv2 := loadedValues_le kind a R ha 2
  have hr := readTime_le kind a R ha
  have hk := kind.isLt
  unfold gateTime mappingTime
  split_ifs <;> nlinarith

lemma bodyTime_le (n : ℕ) (j : Fin (n+1)) (m b R : ℕ) (rs : List Recipe)
    (ha : ∀ r ∈ rs, ∀ i, r.2 i ≤ R) :
    bodyTime n j m b rs ≤ rs.length*(100*(n+1)*(m+b+R+1)) := by
  induction rs with
  | nil => simp [bodyTime]
  | cons r rs ih =>
    have h := gateTime_le n j r.1 r.2 m b R (ha r (by simp))
    have hi := ih (by intro s hs; exact ha s (by simp [hs]))
    simp only [bodyTime,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

lemma sumTime_static_le (n m b o : ℕ) (task : SumTask n)
    (hcopies : ∀ i, task.copies i ≤ n+1) :
    sumTime n task ![m,b,o] ≤ 20*(n+1)*(m+b+o+1) := by
  have h0 := Nat.mul_le_mul_right (2*m+3) (hcopies 0)
  have h1 := Nat.mul_le_mul_right (2*b+3) (hcopies 1)
  have h2 := Nat.mul_le_mul_right (2*o+3) (hcopies 2)
  change task.copies 0*(2*m+3)+1+(task.copies 1*(2*b+3)+1)+
    (task.copies 2*(2*o+3)+1)+1 ≤ _
  nlinarith

lemma andTime_le (n : ℕ) (j : Fin (n+1)) (m b o : ℕ) :
    andTime n j m b o ≤ 200*(n+1)*(m+b+o+1) := by
  have h0 := sumTime_static_le n m b b (.andFirst j) (copies_le n _)
  have h1 := sumTime_static_le n o b b (.loadOutput j) (copies_le n _)
  have h2 := addressTime_le n (.output j) m b o
  have h3 := sumTime_static_le n m b b (.andLast j) (copies_le n _)
  unfold andTime
  nlinarith

lemma copiesTime_le (n m b o R : ℕ) (rs : List Recipe)
    (ha : ∀ r ∈ rs, ∀ i, r.2 i ≤ R) (j r : ℕ) :
    copiesTime n m b o rs j r ≤ r*((m+b+o+3)+(rs.length+2)+
      rs.length*(100*(n+1)*(m+b+R+1))) := by
  induction r generalizing j with
  | zero => simp [copiesTime]
  | succ r ih =>
    have ht := bodyTime_le n (Fin.ofNat (n+1) j) m b R rs ha
    have hi := ih (j+1)
    simp only [copiesTime,packetTime]
    nlinarith

lemma andSeriesTime_le (n m b o j r : ℕ) :
    andSeriesTime n m b o j r ≤ r*(200*(n+1)*(m+b+o+1)) := by
  induction r generalizing j with
  | zero => simp [andSeriesTime]
  | succ r ih =>
    have ht := andTime_le n (Fin.ofNat (n+1) j) m b o
    have hi := ih (j+1)
    simp only [andSeriesTime]
    nlinarith

lemma remapWire_le (m b n j w : ℕ) (hj : j ≤ n) :
    Encoding.remapWire m b n j w ≤ (n+1)*(m+b+w+1) := by
  have hm := Nat.mul_le_mul_left m hj
  have hb := Nat.mul_le_mul_left b hj
  unfold Encoding.remapWire
  split_ifs <;> nlinarith [Nat.sub_le w m]

lemma mappedCode_length_le (m b n j R : ℕ) (hj : j ≤ n) (kind : Fin 4) (a : Fin 3 → ℕ)
    (ha : ∀ i, a i ≤ R) :
    (mappedCode kind a m b n j).length ≤ 20*(n+1)*(m+b+R+1) := by
  have h (i : Fin 3) : Encoding.remapWire m b n j (a i) ≤ (n+1)*(m+b+R+1) :=
    (remapWire_le m b n j (a i) hj).trans (Nat.mul_le_mul_left _ (by have := ha i; omega))
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hk := kind.isLt
  unfold mappedCode mappedWires rawArgs
  split_ifs <;> simp only [List.flatMap_cons,List.flatMap_nil,List.length_append,
    List.length_nil,Nat.add_zero,Main.Encoding.encNat_length] <;> nlinarith

lemma copyBody_length_le (m b n j R : ℕ) (hj : j ≤ n) (rs : List Recipe)
    (ha : ∀ r ∈ rs, ∀ i, r.2 i ≤ R) :
    (copyBody m b n j rs).length ≤ rs.length*(20*(n+1)*(m+b+R+1)) := by
  induction rs with
  | nil => simp [copyBody]
  | cons r rs ih =>
    have ht := mappedCode_length_le m b n j R hj r.1 r.2 (ha r (by simp))
    have hi := ih (by intro s hs; exact ha s (by simp [hs]))
    simp only [copyBody,List.flatMap_cons,List.length_append,List.length_cons] at *
    nlinarith

lemma copiesBody_length_le (m b n R : ℕ) (rs : List Recipe)
    (ha : ∀ r ∈ rs, ∀ i, r.2 i ≤ R) (j r : ℕ) (hjr : j+r ≤ n) :
    (copiesBody m b n rs j r).length ≤ r*(rs.length*(20*(n+1)*(m+b+R+1))) := by
  induction r generalizing j with
  | zero => simp [copiesBody]
  | succ r ih =>
    have ht := copyBody_length_le m b n j R (by omega) rs ha
    have hi := ih (j+1) (by omega)
    simp only [copiesBody,List.length_append]
    nlinarith

lemma andCode_length_le (m b n j o : ℕ) (hj : j ≤ n) :
    (andCode m b n j o).length ≤ 20*(n+1)*(m+b+o+1) := by
  have ht := remapWire_le m b n j o hj
  simp only [andCode,List.length_append,Main.Encoding.encNat_length]
  nlinarith

lemma andBody_length_le (m b n o j r : ℕ) (hjr : j+r ≤ n) :
    (andBody m b n o j r).length ≤ r*(20*(n+1)*(m+b+o+1)) := by
  induction r generalizing j with
  | zero => simp [andBody]
  | succ r ih =>
    have ht := andCode_length_le m b n j o (by omega)
    have hi := ih (j+1) (by omega)
    simp only [andBody,List.length_append]
    nlinarith



lemma fullTime_bound (n m b o L : ℕ) (rs : List Recipe)
    (hres : m+b+o ≤ L) (hlen : rs.length ≤ L)
    (ha : ∀ r ∈ rs, ∀ i, r.2 i ≤ L) :
    fullTime n m b o rs ≤ 1000000*(n+1)^4*(L+1)^2 := by
  let K := (n+1)*(L+1)^2
  have hB : bodyTime n 0 m b rs ≤ 300*K := by
    have ht := bodyTime_le n 0 m b L rs ha
    have hp : rs.length*(100*(n+1)*(m+b+L+1)) ≤ L*(100*(n+1)*(2*L+1)) :=
      Nat.mul_le_mul hlen (Nat.mul_le_mul_left _ (by omega))
    dsimp only [K]
    nlinarith [Nat.zero_le (n*L),Nat.zero_le (n*L^2)]
  have hCopies : copiesTime n m b o rs 1 (n-1) ≤ 310*(n+1)*K := by
    have ht := copiesTime_le n m b o L rs ha 1 (n-1)
    have hp : rs.length*(100*(n+1)*(m+b+L+1)) ≤ L*(100*(n+1)*(2*L+1)) :=
      Nat.mul_le_mul hlen (Nat.mul_le_mul_left _ (by omega))
    have hr : n-1 ≤ n+1 := by omega
    have hs : (m+b+o+3)+(rs.length+2)+rs.length*(100*(n+1)*(m+b+L+1)) ≤ 310*K := by
      dsimp only [K]
      nlinarith [Nat.zero_le (n*L),Nat.zero_le (n*L^2)]
    exact ht.trans ((Nat.mul_le_mul hr hs).trans (le_of_eq (by ring)))
  have hHeader : headerTime n m b o ≤ 70*K := by
    have ht := sumTime_static_le n m b b .headerOutput (copies_le n _)
    unfold headerTime
    dsimp only [K]
    nlinarith [Nat.zero_le (n*L^2)]
  have hSuffix : suffixTime n m b o ≤ 300*(n+1)*K := by
    have ht := sumTime_static_le n m b b .flagX (copies_le n _)
    have hs := andSeriesTime_le n m b o 0 n
    unfold suffixTime
    dsimp only [K]
    nlinarith [Nat.zero_le (n^2*L^2),Nat.zero_le (n*L^2)]
  have hCopiesLength : (copiesBody m b n rs 0 n).length ≤ 50*(n+1)*K := by
    have ht := copiesBody_length_le m b n L rs ha 0 n (by omega)
    have hp : rs.length*(20*(n+1)*(m+b+L+1)) ≤ L*(20*(n+1)*(2*L+1)) :=
      Nat.mul_le_mul hlen (Nat.mul_le_mul_left _ (by omega))
    have hs : rs.length*(20*(n+1)*(m+b+L+1)) ≤ 50*K := by
      dsimp only [K]
      nlinarith [Nat.zero_le (n*L^2)]
    exact ht.trans ((Nat.mul_le_mul (by omega : n≤n+1) hs).trans (le_of_eq (by ring)))
  have hAndLength : (andBody m b n o 0 n).length ≤ 20*(n+1)*K := by
    have ht := andBody_length_le m b n o 0 n (by omega)
    dsimp only [K]
    have hp := Nat.mul_le_mul_left (n*(20*(n+1))) hres
    nlinarith [Nat.zero_le (n^2*L^2),Nat.zero_le (n*L^2)]
  have hFlagLength : (flagCode m b n).length ≤ 3*K := by
    simp only [flagCode,List.length_append,Main.Encoding.encNat_length]
    have hp := Nat.mul_le_mul_left n hres
    dsimp only [K]
    nlinarith [Nat.zero_le (n*L^2)]
  have hTargetHeader : (targetHeader m b n).length ≤ 6*K := by
    simp only [targetHeader,List.length_append,Main.Encoding.encNat_length]
    have hp := Nat.mul_le_mul_left (2*n) hres
    dsimp only [K]
    nlinarith [Nat.zero_le (n*L^2)]
  have hCount : targetCount n rs ≤ 2*K := by
    have hp := Nat.mul_le_mul_left n hlen
    unfold targetCount
    dsimp only [K]
    nlinarith [Nat.zero_le (n*L^2)]
  have hFinalLength : (finalBody m b n o rs).length ≤ 73*(n+1)*K := by
    simp only [finalBody,List.length_append]
    nlinarith
  have hbound : fullTime n m b o rs ≤ 2000*(n+1)*K := by
    unfold fullTime packetTime
    dsimp only [K] at *
    nlinarith [Nat.zero_le (n*L^2)]
  change fullTime n m b o rs ≤ _ at hbound
  have hn : n+1 ≤ (n+1)^3 := by nlinarith [Nat.zero_le (n^3)]
  have hp := Nat.mul_le_mul_left (2000*K) hn
  dsimp only [K] at *
  nlinarith [Nat.zero_le ((n+1)^4*(L+1)^2)]

end QMAPerfectCompleteness.Main.Repetition.CompilerTM


