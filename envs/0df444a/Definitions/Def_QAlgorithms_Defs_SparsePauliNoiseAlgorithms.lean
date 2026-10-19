-- Prove2me | Definitions.Def_QAlgorithms_Defs_SparsePauliNoiseAlgorithms
-- name    : QAlgorithms_Defs_SparsePauliNoiseAlgorithms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:28:19.289043+00:00
-- url     : https://prove2.me/theorems/184cb4a3-0c9d-4527-af7b-682e9369663c
-- title:
--   SparsePauliNoiseAlgorithms
-- statement:
--   SparsePauliNoiseAlgorithms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SparsePauliNoiseAlgorithms.lean

import Definitions.Def_QAlgorithms_Defs_SparsePauliNoiseData
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.SparsePauliNoise

/-- Flat bin-array address, with c then offset t then b-bit bin j
(2007.07901 pp.12-14, Algorithms 2-3). -/
def binAddress {n : ℕ} (D : RecoveryDesign n) (c t j : ℕ) : ℕ :=
  (c*(D.P1+D.P2)+t)*2^D.b+j

/-- Eq.(13)-compatible query address J_n M_c l+d. The bin transform is an ordinary
b-bit WHT, so no ill-typed printed J_b is multiplied in
(2007.07901 pp.12-13, Algorithm 2 and proof of Lemma 1). -/
def subsamplingAddress {n : ℕ} (D : RecoveryDesign n) (c : Fin D.groups)
    (t : Fin (D.P1+D.P2)) (l : Fin (2^D.b)) : Label n :=
  let v := splitLabel ((D.hashMatrix c).mulVec fun j =>
    if natToBits D.b l.val j then 1 else 0)
  (v.2,v.1)+D.offset c t

/-- Algorithm 2 as executable reads and in-place butterfly WHT instructions.
Every read is recorded; every butterfly and the final 1/B normalization are charged.
All groups/offsets are returned, following the surrounding prose
(2007.07901 pp.12-13). The dimensional correction is stated in subsamplingAddress. -/
def subsamplingProgram {n : ℕ} (D : RecoveryDesign n) : OracleProgram n :=
  let scratch := D.groups*(D.P1+D.P2)*2^D.b
  let reads := (List.finRange D.groups).flatMap fun c =>
    (List.finRange (D.P1+D.P2)).flatMap fun t =>
      (List.finRange (2^D.b)).map fun l =>
        OracleInstruction.query (binAddress D c.val t.val l.val) (subsamplingAddress D c t l)
  let transform := (List.finRange D.groups).flatMap fun c =>
    (List.finRange (D.P1+D.P2)).flatMap fun t =>
      (List.range D.b).flatMap fun bit =>
        ((List.range (2^D.b)).filter fun j => !j.testBit bit).flatMap fun j =>
          let a := binAddress D c.val t.val j
          let b := binAddress D c.val t.val (j+2^bit)
          [OracleInstruction.add scratch a b,.sub b a b,.add a scratch (scratch+1)]
  let normalize := (List.range scratch).map fun j => OracleInstruction.div j j (scratch+2)
  oracleSteps (reads ++ [.constant (scratch+1) 0,.constant (scratch+2) ((2^D.b : ℕ) : ℝ)] ++
    transform ++ normalize)

/-- Sparse-output success under the joint support/design/Gaussian law.
The labels are recovered exactly and all coordinates have the source 2xi/sqrt(B)
error after zero extension. No positivity or normalization is imposed on estimates
(2007.07901 pp.8,15-16, Theorem 1). -/
def recoveryEvent {n : ℕ} (D : RecoveryDesign n) (p : Label n → ℝ)
    (xi : ℝ) (_nonnegative : 0 ≤ xi) (s : OracleState n) : Prop :=
  s.failed = false ∧ (s.output.map Prod.fst).Nodup ∧
    (s.output.map Prod.fst).toFinset = Finset.univ.filter (fun a => p a ≠ 0) ∧
    ∀ a : Label n,
      |((s.output.map fun entry => if entry.1 = a then entry.2 else 0).sum)-p a| ≤
        2*xi/Real.sqrt ((2 : ℝ)^D.b)

example {n : ℕ} (D : RecoveryDesign n) :
    binAddress D 0 0 0 = 0 := by simp [binAddress]

example {n : ℕ} (D : RecoveryDesign n) (p : Label n → ℝ) (xi : ℝ) (hxi : 0 ≤ xi)
    (s : OracleState n) (h : recoveryEvent D p xi hxi s) :
    s.failed = false := h.1


/-- Decode the private binary decoder's reported bits by charged comparisons.
Nonbinary outputs fail explicitly instead of being silently rounded
(2007.07901 pp.14-15, Decode interface). -/
def decodedLabelBranches {n : ℕ} (bitBase zero one : ℕ)
    (next : Label n → OracleProgram n) :
    List (Fin (n+n)) → (Fin (n+n) → ZMod 2) → OracleProgram n
  | [], bits => next (splitLabel bits)
  | i::rest, bits =>
      .step (.compare (bitBase+i.val) zero) fun leZero =>
        if leZero then .step (.compare zero (bitBase+i.val)) fun geZero =>
          if geZero then decodedLabelBranches bitBase zero one next rest (Function.update bits i 0)
          else .fail
        else .step (.compare (bitBase+i.val) one) fun leOne =>
          if leOne then .step (.compare one (bitBase+i.val)) fun geOne =>
            if geOne then decodedLabelBranches bitBase zero one next rest (Function.update bits i 1)
            else .fail
          else .fail

/-- Private scratch addresses follow all source bins and variance trackers
(2007.07901 pp.14-15, Algorithms 3-4). -/
def detectorScratch {n : ℕ} (D : RecoveryDesign n) : ℕ :=
  D.groups*(D.P1+D.P2)*2^D.b+D.groups*2^D.b+
    D.decoderWorkspace+D.P2+(n+n)+20

/-- Bin detector with explicit zero-ton check, coded sign decoding, signed average,
and singleton residual check. Status at scratch is 0/1/2 for zero/single/multi;
the singleton rate is at scratch+1. All operations have RAM semantics.
Decoder workspace conventions are public (2007.07901 p.15, Algorithm 4). -/
def binDetectorCore {n : ℕ} (D : RecoveryDesign n) (c : Fin D.groups)
    (j : Fin (2^D.b)) (xi : ℝ) (_hxi : 0 ≤ xi)
    (done : OracleProgram n) (single : Label n → ℕ → OracleProgram n) : OracleProgram n :=
  let B := 2^D.b
  let binSize := D.groups*(D.P1+D.P2)*B
  let decoderBase := binSize+D.groups*B
  let T := binSize+c.val*B+j.val
  let s := detectorScratch D
  let signedRate := fun a : Label n =>
    oracleSteps ([.constant (s+1) 0] ++
      (List.finRange D.P1).flatMap (fun t =>
        [.constant (s+3) ((-1 : ℝ)^(symplecticPairing (D.offset c (Fin.castAdd D.P2 t)) a).val),
          .mul (s+4) (s+3) (binAddress D c.val t.val j.val),.add (s+1) (s+1) (s+4)]) ++
      [.mul (s+1) (s+1) (s+6),.constant (s+2) 0] ++
      (List.finRange D.P1).flatMap (fun t =>
        [.constant (s+3) ((-1 : ℝ)^(symplecticPairing (D.offset c (Fin.castAdd D.P2 t)) a).val),
          .mul (s+4) (s+3) (s+1),.sub (s+4) (binAddress D c.val t.val j.val) (s+4),
          .mul (s+4) (s+4) (s+4),.add (s+2) (s+2) (s+4)]) ++
      [.mul (s+2) (s+2) (s+6),.constant (s+3) ((1+D.gamma2)*xi^2/(B : ℝ)),
        .mul (s+5) T (s+3)])
  let candidate := fun a => (signedRate a).then
    (.step (.compare (s+2) (s+5)) fun verified =>
      if verified then (oracleSteps [.constant s 1]).then (single a (s+1))
      else (oracleSteps [.constant s 2]).then done)
  let readSigns : OracleProgram n := (List.finRange D.P2).foldr (fun t rest =>
    .step (.compare (s+7) (binAddress D c.val (D.P1+t.val) j.val)) fun nonnegative =>
      (oracleSteps [.constant (decoderBase+t.val) (if nonnegative then 0 else 1)]).then rest) .halt
  let decode := readSigns.then ((D.decoder.relocate decoderBase).then
    ((oracleSteps [.constant (s+7) 0,.constant (s+8) 1]).then
      (decodedLabelBranches (decoderBase+D.P2) (s+7) (s+8) candidate (List.finRange (n+n)) 0)))
  (oracleSteps ([.constant (s+2) 0,.constant (s+6) ((D.P1 : ℝ)⁻¹),.constant (s+7) 0] ++
    (List.finRange D.P1).flatMap (fun t =>
      [.mul (s+4) (binAddress D c.val t.val j.val) (binAddress D c.val t.val j.val),
        .add (s+2) (s+2) (s+4)]) ++
    [.mul (s+2) (s+2) (s+6),.constant (s+3) ((1+D.gamma1)*xi^2/(B : ℝ)),
      .mul (s+5) T (s+3)])).then
    (.step (.compare (s+2) (s+5)) fun zeroTon =>
      if zeroTon then (oracleSteps [.constant s 0]).then done else decode)

/-- Named Algorithm 4, including failure and non-singleton branches
(2007.07901 p.15). It never assumes that Decode finds the correct label. -/
def binDetectorProgram {n : ℕ} (D : RecoveryDesign n) (c : Fin D.groups)
    (j : Fin (2^D.b)) (xi : ℝ) (hxi : 0 ≤ xi) : OracleProgram n :=
  binDetectorCore D c j xi hxi .halt (fun a rate => .emit a rate .halt)

/-- Named Algorithm 3: initialize T=1, call Algorithm 4 on each bin, append a
singleton and subtract its signed rate from every other group, with the printed
tracker increment T_source/P1+(P1-1)B/(P1*N). Retire the recovered source
bin by zeroing all its offsets: the graph-removal argument requires each peeled
edge to disappear, although printed Algorithm 3 omits this assignment
(2007.07901 pp.13-14,18-19). Return after all I rounds, as the proof uses.
No output positivity, successful detections or runtime guarantee is assumed. -/
def peelingProgram {n : ℕ} (D : RecoveryDesign n) (xi : ℝ) (hxi : 0 ≤ xi) : OracleProgram n :=
  let B := 2^D.b
  let binSize := D.groups*(D.P1+D.P2)*B
  let s := detectorScratch D
  let bins := (List.finRange D.groups).flatMap fun c =>
    (List.finRange B).map fun j => (c,j)
  let init := oracleSteps ((List.range (D.groups*B)).map fun k => .constant (binSize+k) 1)
  let body := bins.foldr (fun cj rest =>
    binDetectorCore D cj.1 cj.2 xi hxi rest (fun a rate =>
      let updates := (List.finRange D.groups).filter (fun c => decide (c ≠ cj.1)) |>.flatMap fun c =>
        let hashBits := (D.hashMatrix c).transpose.mulVec (Fin.append a.1 a.2)
        let j := bitsToNat (fun i => decide (hashBits i = 1))
        [.constant (s+9) ((D.P1 : ℝ)⁻¹),
          .mul (s+10) (binSize+cj.1.val*B+cj.2.val) (s+9),
          .constant (s+11) (((D.P1-1 : ℕ) : ℝ)*B/((D.P1 : ℝ)*(4 : ℝ)^n)),
          .add (s+10) (s+10) (s+11),
          .add (binSize+c.val*B+j) (binSize+c.val*B+j) (s+10)] ++
        (List.finRange (D.P1+D.P2)).flatMap fun t =>
          [.constant (s+9) ((-1 : ℝ)^(symplecticPairing (D.offset c t) a).val),
            .mul (s+10) rate (s+9),
            .sub (binAddress D c.val t.val j) (binAddress D c.val t.val j) (s+10)]
      let retire := (List.finRange (D.P1+D.P2)).map fun t =>
        OracleInstruction.constant (binAddress D cj.1.val t.val cj.2.val) 0
      .emit a rate ((oracleSteps (updates ++ retire)).then rest))) .halt
  init.then (.loop D.iterations body .halt)

example {n : ℕ} (next : Label n → OracleProgram n) (bits : Fin (n+n) → ZMod 2) :
    decodedLabelBranches 0 1 2 next [] bits = next (splitLabel bits) := rfl

end QAlgorithms.SparsePauliNoise


