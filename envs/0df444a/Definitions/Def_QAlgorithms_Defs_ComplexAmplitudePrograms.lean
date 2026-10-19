-- Prove2me | Definitions.Def_QAlgorithms_Defs_ComplexAmplitudePrograms
-- name    : QAlgorithms_Defs_ComplexAmplitudePrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:19:41.09773+00:00
-- url     : https://prove2.me/theorems/0d77f84c-7fd5-4ed2-80d5-815fa41602a7
-- title:
--   ComplexAmplitudePrograms
-- statement:
--   ComplexAmplitudePrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ComplexAmplitudePrograms.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

namespace QAlgorithms.TwoBasisCertification

variable {n m d k b w M K N c out : ℕ}

/-- Classical exact amplitude oracle, 2602.11616 p.7 Definition 1.
false=std; true=full-register had. This is not coherent oracle access. -/
def amplitudeOracle (psi : EuclideanSpace ℂ (Qubits n)) (had : Bool) (z : Qubits n) : ℂ :=
  if had then act (hadamardN n) psi z else psi z

/-- Ideal complex-register arithmetic and actual classical amplitude reads,
2602.11616 pp.7–9. Division/square roots are explicitly guarded. -/
inductive AmplitudeInstruction (n k : ℕ) where
  | constant (dst : ℕ) (value : ℂ)
  | read (dst src : ℕ)
  | add (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | div (dst a b : ℕ)
  | conjugate (dst a : ℕ)
  | sqrt (dst a : ℕ)
  | amplitude (dst : ℕ) (had : Bool) (z : Qubits n)
  | arg (dst src : ℕ)
  | acos (dst src : ℕ)
  | sin (dst src : ℕ)
  | cos (dst src : ℕ)
  | phase (dst src : ℕ)
  | gateOne (q : Fin k) (entries : Bool → Bool → ℕ)
  | gateTwo (a b : Fin k) (hab : a ≠ b) (entries : (Bool × Bool) → (Bool × Bool) → ℕ)

/-- Executable ideal numerical amplitude-query program, 2602.11616 pp.7–9.
The program contains no target/lab vector, free state-preparation oracle,
or arbitrary classical answer-dependent computation. -/
inductive AmplitudeProgram (n k : ℕ) where
  | done
  | step (op : AmplitudeInstruction n k) (next : AmplitudeProgram n k)
  | branchZero (address : ℕ) (zero nonzero : AmplitudeProgram n k)
  | loop (count : ℕ) (body rest : AmplitudeProgram n k)

/-- Actual memory, query and numerical instruction trace,
2602.11616 pp.7–9. Failure preserves the work/query trace. -/
structure AmplitudeExecution (n k : ℕ) where
  memory : ℕ → ℂ
  queries : List (Bool × Qubits n)
  instructions : ℕ
  failed : Bool
  circuit : Circuit oneTwoQubitGateSet k

/-- Execute one scalar/query instruction, 2602.11616 pp.7–9. -/
def AmplitudeInstruction.execute {n k : ℕ} (oracle : Bool → Qubits n → ℂ)
    (op : AmplitudeInstruction n k) (s : AmplitudeExecution n k) : AmplitudeExecution n k :=
  if s.failed then s else
    let st := { s with instructions := s.instructions+1 }
    let set (dst : ℕ) (v : ℂ) := { st with memory := Function.update st.memory dst v }
    match op with
    | .constant dst v => set dst v
    | .read dst src => set dst (s.memory src)
    | .add dst a b => set dst (s.memory a+s.memory b)
    | .mul dst a b => set dst (s.memory a*s.memory b)
    | .div dst a b => if s.memory b = 0 then { st with failed := true }
        else set dst (s.memory a/s.memory b)
    | .conjugate dst a => set dst (star (s.memory a))
    | .sqrt dst a => if 0 ≤ (s.memory a).re ∧ (s.memory a).im = 0 then
        set dst (Real.sqrt (s.memory a).re) else { st with failed := true }
    | .amplitude dst had z =>
        { st with
          memory := Function.update st.memory dst (oracle had z)
          queries := st.queries ++ [(had,z)] }

    | .arg dst src => set dst (Complex.arg (s.memory src))
    | .acos dst src => if (s.memory src).im = 0 ∧ |(s.memory src).re| ≤ 1 then
        set dst (Real.arccos (s.memory src).re) else { st with failed := true }
    | .sin dst src => if (s.memory src).im = 0 then
        set dst (Real.sin (s.memory src).re) else { st with failed := true }
    | .cos dst src => if (s.memory src).im = 0 then
        set dst (Real.cos (s.memory src).re) else { st with failed := true }
    | .phase dst src => if (s.memory src).im = 0 then
        set dst (Complex.exp (Complex.I * s.memory src)) else { st with failed := true }
    | .gateOne q entries =>
        open Classical in
        let g := Gate.ofMatrix1 (Matrix.of fun a b => s.memory (entries a b))
        if h : g.IsUnitary then
          { st with
            instructions := st.instructions + 4
            circuit := st.circuit ++ [⟨g,⟨Or.inl rfl,h⟩,Stabilizer.wire1 q⟩] }
        else { st with failed := true }
    | .gateTwo a b hab entries =>
        open Classical in
        let g := Gate.ofMatrix2 (Matrix.of fun x y => s.memory (entries x y))
        if h : g.IsUnitary then
          { st with
            instructions := st.instructions + 16
            circuit := st.circuit ++ [⟨g,⟨Or.inr rfl,h⟩,Stabilizer.wire2 a b hab⟩] }
        else { st with failed := true }

/-- Operational numerical law with actual exact-answer reads, 2602.11616 pp.7–9.
All quantum measurement probabilities are handled separately by outcomeLaw. -/
def amplitudeProgramLaw {n k : ℕ} (oracle : Bool → Qubits n → ℂ) :
    AmplitudeProgram n k → AmplitudeExecution n k → AmplitudeExecution n k
  | .done, s => s
  | .step op next, s => amplitudeProgramLaw oracle next (op.execute oracle s)
  | .branchZero a z nz, s =>
      if s.memory a = 0 then
        amplitudeProgramLaw oracle z { s with instructions := s.instructions+1 }
      else amplitudeProgramLaw oracle nz { s with instructions := s.instructions+1 }
  | .loop k body rest, s =>
      amplitudeProgramLaw oracle rest
        ((List.range k).foldl (fun st _ => amplitudeProgramLaw oracle body st) s)

/-- The actual suffix-amplitude read pass of Lemma 1, 2602.11616 p.8.
Exactly 2^k classical amplitude queries are executed at the observed prefix. -/
def suffixReadProgram (r k : ℕ) (had : Bool) (z : Qubits r) : AmplitudeProgram (r+k) k :=
  (List.finRange (2^k)).foldr (fun j next =>
    .step (.amplitude j.val had (Fin.append z ((bitsEquivFin k).symm j))) next) .done

/-- Public initialization, 2602.11616 pp.7–9: no target-dependent state
or circuit is placed in the initial numerical/quantum-code memory. -/
def initialAmplitudeExecution (n k : ℕ) : AmplitudeExecution n k :=
  ⟨fun _ => 0,[],0,false,[]⟩

/-- Straight-line numerical compilation, 2602.11616 pp.7–9. -/
def amplitudeSteps {n k : ℕ} (ops : List (AmplitudeInstruction n k)) : AmplitudeProgram n k :=
  ops.foldr (fun op next => .step op next) .done

/-- Sequential source-program composition, 2602.11616 pp.7–9. -/
def amplitudeThen {n k : ℕ} : AmplitudeProgram n k → AmplitudeProgram n k → AmplitudeProgram n k
  | .done, Q => Q
  | .step op next, Q => .step op (amplitudeThen next Q)
  | .branchZero a z nz, Q => .branchZero a (amplitudeThen z Q) (amplitudeThen nz Q)
  | .loop count body rest, Q => .loop count body (amplitudeThen rest Q)

/-- Counted oracle-answer reconstruction, suffix Hadamard correction and
guarded normalization, 2602.11616 pp.8–10. Corrected coefficients occupy
D,...,2D-1; address 2D+2 is the zero/nonzero-fiber flag. -/
def conditionalAmplitudeProgram (r k : ℕ) (had : Bool) (z : Qubits r) :
    AmplitudeProgram (r+k) k :=
  let D := 2^k
  let correction := if had then
      (List.finRange D).flatMap fun y =>
        [.constant (D+y.val) 0] ++ (List.finRange D).flatMap fun w =>
          [.constant (2*D+3) (hadamardN k ((bitsEquivFin k).symm y) ((bitsEquivFin k).symm w)),
            .mul (2*D+4) (2*D+3) w.val, .add (D+y.val) (D+y.val) (2*D+4)]
    else (List.range D).map fun j => .read (D+j) j
  let normOps := [.constant (2*D) 0] ++ (List.range D).flatMap (fun j =>
    [.conjugate (2*D+3) (D+j), .mul (2*D+4) (2*D+3) (D+j),
      .add (2*D) (2*D) (2*D+4)]) ++ [.sqrt (2*D+1) (2*D)]
  amplitudeThen (suffixReadProgram r k had z)
    (amplitudeThen (amplitudeSteps correction)
      (amplitudeThen (amplitudeSteps normOps)
        (.branchZero (2*D+1) (amplitudeSteps [.constant (2*D+2) 0])
          (amplitudeSteps ([.constant (2*D+2) 1] ++ (List.range D).map
            (fun j => .div (D+j) (D+j) (2*D+1)))))))

/-- A CNOT emitted from fixed known entries, used for exact small-block
measurement synthesis (2602.11616 pp.8–9). -/
def amplitudeCnot {n k : ℕ} (a b : Fin k) (h : a ≠ b) (zero one : ℕ) :
    AmplitudeInstruction n k :=
  .gateTwo a b h (fun x y => if x.1 = y.1 ∧ x.2 = xor y.2 y.1 then one else zero)

/-- Emit Ry(theta) from a computed real angle using elementary numerical
instructions and one one-qubit gate (2602.11616 pp.8–9).
Scratch cells s,...,s+4 are overwritten; constants half and minusOne are public. -/
def amplitudeRy {n k : ℕ} (q : Fin k) (angle s half minusOne : ℕ) :
    List (AmplitudeInstruction n k) :=
  [.mul s angle half, .cos (s+1) s, .sin (s+2) s, .mul (s+3) (s+2) minusOne,
    .gateOne q (fun a b => if a = b then s+1 else if a then s+2 else s+3)]

/-- Exact elementary synthesis of the normalized computed suffix vector
(2602.11616 pp.8–9). Multiplexed Ry angles use a Gray-code Walsh
decomposition; a Walsh diagonal phase circuit supplies complex phases.
Both decompositions act only on k suffix wires. Global phase is irrelevant
to the projector. All target-dependent entries come from numerical memory. -/
def suffixSynthesisProgram (r k : ℕ) : AmplitudeProgram (r+k) k := by
  classical
  let D := 2^k
  let zero := 2*D+6
  let one := 2*D+7
  let minusOne := 2*D+8
  let half := 2*D+9
  let tmp := 2*D+10
  let angles := 3*D+32
  let coeffs := 4*D+32
  let phases := 5*D+32
  let setup : List (AmplitudeInstruction (r+k) k) :=
    [.constant zero 0,.constant one 1,.constant minusOne (-1),.constant half (1/2)]
  let rotations := (List.finRange k).flatMap fun q =>
    let c := q.val
    let anglePrograms := (List.range (2^c)).map fun node =>
      let left := (List.finRange D).filter (fun j => j.val / 2^(k-c-1) = 2*node)
      let right := (List.finRange D).filter (fun j => j.val / 2^(k-c-1) = 2*node+1)
      let sums : List (AmplitudeInstruction (r+k) k) :=
        [.constant tmp 0,.constant (tmp+1) 0] ++
        (left.flatMap fun j => [.conjugate (tmp+2) (D+j.val),.mul (tmp+3) (tmp+2) (D+j.val),
          .add tmp tmp (tmp+3)]) ++
        (right.flatMap fun j => [.conjugate (tmp+2) (D+j.val),.mul (tmp+3) (tmp+2) (D+j.val),
          .add (tmp+1) (tmp+1) (tmp+3)]) ++ [.add (tmp+4) tmp (tmp+1)]
      amplitudeThen (amplitudeSteps sums)
        (.branchZero (tmp+4) (amplitudeSteps [.constant (angles+node) 0])
          (amplitudeSteps [.div (tmp+5) tmp (tmp+4),.sqrt (tmp+6) (tmp+5),
            .acos (tmp+7) (tmp+6),.constant (tmp+8) 2,.mul (angles+node) (tmp+7) (tmp+8)]))
    let walsh : List (AmplitudeInstruction (r+k) k) := (List.range (2^c)).flatMap fun j =>
      [.constant (coeffs+j) 0] ++ (List.range (2^c)).flatMap fun i =>
        [.constant tmp (if dotBits (natToBits c i) (natToBits c (Nat.xor j (j/2)))
          then -((2:ℂ)^c)⁻¹ else ((2:ℂ)^c)⁻¹),
          .mul (tmp+1) tmp (angles+i),.add (coeffs+j) (coeffs+j) (tmp+1)]
    let gates : List (AmplitudeInstruction (r+k) k) := (List.range (2^c)).flatMap fun j =>
      amplitudeRy q (coeffs+j) tmp half minusOne ++
        (if hc : 0 < c then
          let diff := Nat.xor (Nat.xor j (j/2))
            (Nat.xor ((j+1) % (2^c)) (((j+1) % (2^c))/2))
          let bit := ((List.finRange c).find? (fun bit => diff.testBit bit.val)).getD ⟨0,hc⟩
          let control : Fin k := ⟨(Fin.rev bit).val, by have := (Fin.rev bit).isLt; omega⟩
          [amplitudeCnot control q (by
            intro h
            have hh := congrArg Fin.val h
            change (Fin.rev bit).val = q.val at hh
            have hb := (Fin.rev bit).isLt
            change (Fin.rev bit).val < q.val at hb
            omega) zero one]
        else [])
    [anglePrograms.foldr amplitudeThen .done,
      amplitudeSteps walsh,amplitudeSteps gates]
  let phaseOps : List (AmplitudeInstruction (r+k) k) :=
    (List.range D).map (fun j => .arg (phases+j) (D+j))
  let diagonals : List (AmplitudeInstruction (r+k) k) :=
    (List.finRange D).flatMap fun idx =>
      let bits := (bitsEquivFin k).symm idx
      let support := (List.finRange k).filter (fun j => bits j)
      match hs : support with
      | [] => []
      | pivot::rest =>
          let cnots := rest.attach.map (fun q => amplitudeCnot q.val pivot
            (by
              have nodup := (List.nodup_finRange k).filter (fun j => bits j)
              have hrest := (List.nodup_cons.mp (by rw [← hs]; exact nodup)).1
              intro h
              exact hrest (h ▸ q.property)) zero one)
          [.constant (coeffs+idx.val) 0] ++ (List.finRange D).flatMap (fun j =>
            [.constant tmp (if dotBits bits ((bitsEquivFin k).symm j) then -(D:ℂ)⁻¹ else (D:ℂ)⁻¹),
              .mul (tmp+1) tmp (phases+j.val),.add (coeffs+idx.val) (coeffs+idx.val) (tmp+1)]) ++
          cnots ++ [.phase (tmp+2) (coeffs+idx.val),.mul (tmp+3) minusOne (coeffs+idx.val),
            .phase (tmp+4) (tmp+3),
            .gateOne pivot (fun a b => if a = b then (if a then tmp+4 else tmp+2) else zero)] ++
          cnots.reverse
  exact .branchZero (2*D+2) .done
    (amplitudeThen (amplitudeSteps setup)
      (amplitudeThen (rotations.foldr amplitudeThen .done)
        (amplitudeThen (amplitudeSteps phaseOps) (amplitudeSteps diagonals))))

/-- Whole counted conditional-measurement preprocessing and elementary
suffix-circuit construction, 2602.11616 pp.8–9. -/
def conditionalMeasurementProgram (r k : ℕ) (had : Bool) (z : Qubits r) :
    AmplitudeProgram (r+k) k :=
  amplitudeThen (conditionalAmplitudeProgram r k had z) (suffixSynthesisProgram r k)

/-- Accepting effect of the emitted physical suffix circuit, 2602.11616 p.8.
A zero fiber always rejects. -/
def compiledSuffixEffect (r k : ℕ) (had : Bool) (z : Qubits r)
    (oracle : Bool → Qubits (r+k) → ℂ) : Matrix (Qubits k) (Qubits k) ℂ :=
  let result := amplitudeProgramLaw oracle (conditionalMeasurementProgram r k had z)
    (initialAmplitudeExecution (r+k) k)
  if result.failed ∨ result.memory (2*(2^k)+2) = 0 then 0
  else pureDensity (act result.circuit.unitary (zeroKet k))

/-- Structural resources of the source one-copy test, 2602.11616 pp.8–9:
one lab copy, r prefix measurements, actual amplitude reads, and numerical
instructions plus elementary gates. No query or gate count is supplied by hand. -/
def testResources (r k : ℕ) (had : Bool) (z : Qubits r)
    (oracle : Bool → Qubits (r+k) → ℂ) : Fin 4 → ℕ :=
  let result := amplitudeProgramLaw oracle (conditionalMeasurementProgram r k had z)
    (initialAmplitudeExecution (r+k) k)
  ![1,r,result.queries.length,r+result.instructions+result.circuit.size+1]

/-- Sanity check for the modeled source objects (arxiv-2602.11616v1, PDF pp.3,7,8,9). -/
example {n k : ℕ} (oracle : Bool → Qubits n → ℂ) (s : AmplitudeExecution n k) :
    amplitudeProgramLaw oracle .done s = s := rfl

/-- Sanity check for the modeled source objects (arxiv-2602.11616v1, PDF pp.3,7,8,9). -/
example (psi : EuclideanSpace ℂ (Qubits n)) (z : Qubits n) :
    amplitudeOracle psi false z = psi z := rfl

/-- Sanity check for the modeled source objects (arxiv-2602.11616v1, PDF pp.3,7,8,9). -/
example (n k : ℕ) : (initialAmplitudeExecution n k).circuit.size = 0 := rfl

/-- Sanity check for the modeled source objects (arxiv-2602.11616v1, PDF pp.3,7,8,9). -/
example : compiledSuffixEffect 0 0 false (fun _ => false) (fun _ _ => 0) = 0 := by
  simp [compiledSuffixEffect,conditionalMeasurementProgram,conditionalAmplitudeProgram,
    suffixReadProgram,amplitudeThen,amplitudeSteps,suffixSynthesisProgram,
    amplitudeProgramLaw,AmplitudeInstruction.execute,initialAmplitudeExecution,
    List.finRange_succ]

end QAlgorithms.TwoBasisCertification


