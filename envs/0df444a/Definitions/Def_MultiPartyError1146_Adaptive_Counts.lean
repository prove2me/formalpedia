-- Prove2me | Definitions.Def_MultiPartyError1146_Adaptive_Counts
-- name    : MultiPartyError1146_Adaptive_Counts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T18:34:41.055176+00:00
-- url     : https://prove2.me/theorems/0e58ea42-91c1-4915-be9e-1ba0c3e72367
-- title:
--   Execution-derived F, G, errors, true votes and exceptional sets
-- statement:
--   All counters are computed from an Algorithm 1 execution on an input and a received-symbol matrix. The true vote $\gamma_k^*$ sums the signed values in actual sent packets. The true duration vote $\xi_k^*$ uses thresholds $\pm L/90$, whereas local counters use $\pm L/100$.
--
--   $E_i$ counts earlier blocks decoded wrongly or not decoded at speaker $i$; $E_k'$ consists of speakers initially wrong about bit $k$. The subsets $E'_{k,\tau}$ use the true signed vote immediately after a speaker. $F$ counts the two source conditions and $G$ all five conditions on printed p.25. Predicate arguments represent exact levels and partial sums, avoiding infinite sums and truncated signed subtraction.
--
--   $S_1$ is the canonical set of coordinates wrong at at least $1/100$ of receivers after phase 1. $S_2$ is the canonical set of receivers with a wrong or unsure coordinate outside $S_1$ after phase 2. The definitions contain none of the bounds the milestones assert.
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Section 4.1; canonical exceptional sets pp.22–23, printed p.25, PDF p.27

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Algorithm

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

noncomputable def beforeSpeaker {n R : ℕ} (D : AlgorithmData n R) (r : Fin R) (j : Fin n) : ℕ :=
  iterationStart D r.val + j.val * (D.forwardCode r).length

noncomputable def sentPacket {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (j : Fin n) : Packet n (width n R r.val) :=
  packet r (prepare (.forward r j) (snapshot D x A (beforeSpeaker D r j) j))

/-- Actual signed broadcasts of the first p speakers in this iteration. -/
noncomputable def trueGamma {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (p : ℕ) (k : Fin n) : ℤ :=
  ((List.finRange n).filter (fun j => j.val < min p (prefixSize n R r.val))).foldl
    (fun g j => addPacket g (sentPacket D x A r j)) (fun _ => 0) k

noncomputable def trueXi {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (k : Fin n) : ℤ :=
  ((List.range (prefixSize n R r.val)).map fun p =>
    let g : ℝ := trueGamma D x A r (p + 1) k
    if (leadScale n R : ℝ) / 90 ≤ g then (1 : ℤ) else
    if g ≤ -(leadScale n R : ℝ) / 90 then -1 else 0).sum

noncomputable def decodedPacket {n R : ℕ} (D : AlgorithmData n R) (_x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (i j : Fin n) :
    Option (Packet n (width n R r.val)) :=
  (D.forwardCode r).decode (fun l =>
    let t := beforeSpeaker D r j + l.val
    if h : t < duration D then A ⟨t,h⟩ i else none)

/-- Earlier messages decoded incorrectly or not decoded, counted once per actual block. -/
noncomputable def decodingErrors {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => j.val < min i.val (prefixSize n R r.val) ∧
    decodedPacket D x A r i j ≠ some (sentPacket D x A r j)

noncomputable def wrongSpeakers {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (k : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => j.val < prefixSize n R r.val ∧
    (snapshot D x A (iterationStart D r.val) j).estimate k ≠ x k 0

noncomputable def signedGamma {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (j k : Fin n) : ℤ :=
  sign (x k 0) * trueGamma D x A r (j.val + 1) k

noncomputable def wrongAtLevel {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (k : Fin n) (τ : ℤ) : Finset (Fin n) := by
  classical
  exact (wrongSpeakers D x A r k).filter fun j => signedGamma D x A r j k = τ

noncomputable def selectedBy {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (j k : Fin n) : Prop :=
  k ∈ selected r (prepare (.forward r j) (snapshot D x A (beforeSpeaker D r j) j))

/-- The two conditions defining F, evaluated immediately after the speaker. -/
noncomputable def Fcount {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (k : Fin n) (test : ℤ → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => j.val < prefixSize n R r.val ∧
    (selectedBy D x A r j k ∨ j ∈ wrongSpeakers D x A r k) ∧
    test (signedGamma D x A r j k)).card

/-- All five conditions defining G. Tests implement exact levels and partial sums. -/
noncomputable def Gcount {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (k k' : Fin n)
    (first second : ℤ → Prop) (errors : ℕ → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => j.val < prefixSize n R r.val ∧
    (¬ selectedBy D x A r j k ∧ j ∉ wrongSpeakers D x A r k) ∧
    first (signedGamma D x A r j k) ∧ selectedBy D x A r j k' ∧
    second (signedGamma D x A r j k') ∧ errors (decodingErrors D x A r j).card).card

noncomputable def lowLeadCount {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (k : Fin n) (τ : ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => j.val < prefixSize n R r.val ∧ signedGamma D x A r j k ≤ τ).card

noncomputable def totalDecodingErrors {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) : ℕ :=
  ((List.finRange n).filter fun i => i.val < prefixSize n R r.val).foldl
    (fun z i => z + (decodingErrors D x A r i).card) 0

noncomputable def otherWrongCount {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (k : Fin n) : ℕ :=
  ∑ k' : Fin n, if k' = k then 0 else (wrongSpeakers D x A r k').card

end MultiPartyError1146.Adaptive


