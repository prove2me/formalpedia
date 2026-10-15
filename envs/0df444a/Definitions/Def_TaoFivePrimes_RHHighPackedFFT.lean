-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighPackedFFT
-- name    : TaoFivePrimes_RHHighPackedFFT
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T02:02:40.384632+00:00
-- url     : https://prove2.me/theorems/aa71d7d7-3a1e-4fcc-bb40-601daaeb364d
-- title:
--   Fixed positive-frequency packed FFT arithmetic
-- statement:
--   Transparent integer arithmetic for a16384-sample Bluestein transform, producing its first2048 Fourier values. The definition alone asserts no correctness, accuracy, sign or zero-count result.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
set_option autoImplicit false
namespace RHHighPackedFFT
noncomputable def pair (bits : Nat) : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x::y::xs => (x+Nat.shiftLeft y bits)::pair bits xs
noncomputable def pack : Nat → Nat → List Nat → Nat
  | 0, _, xs => xs.headD 0
  | n+1, bits, xs => pack n (bits*2) (pair bits xs)
noncomputable def digits : Nat → Nat → Nat → List Nat
  | 0, bits, p => [p &&& (Nat.shiftLeft 1 bits-1)]
  | n+1, bits, p =>
      let h:=Nat.shiftLeft bits n
      digits n bits (p &&& (Nat.shiftLeft 1 h-1))++digits n bits (Nat.shiftRight p h)
noncomputable def windows : Nat → Nat → List Nat → List Nat → List Nat
  | 0, _, _, _ => []
  | n+1, sb, x::xs, y::ys => sb::windows n (sb-x+y) xs ys
  | _, _, _, _ => []
noncomputable def unbias (v b : List Nat) (A C sa sb : Nat) : List Int :=
  let sums:=windows 2048 sb (b.take 2048) (b.drop 16384)
  (v.zip sums).map (fun p => (p.1:Int)-(C:Int)*(sa:Int)-(A:Int)*(p.2:Int)+(16384*A*C:Nat))
noncomputable def convolution (a b : List Nat) (A C : Nat) : List Int :=
  unbias (digits 11 272 (Nat.shiftRight (pack 14 272 a*pack 15 272 b) (272*16383))) b A C a.sum (b.take 16384).sum
noncomputable def combine (rr ii ss : List Int) (chirp : Nat→Int×Int) : List (Int×Int) :=
  ((((rr.zip ii).zip ss).zip (List.range 2048))).map (fun p =>
    let r:=p.1.1.1-p.1.1.2
    let i:=p.1.2-p.1.1.1-p.1.1.2
    let c:=chirp p.2
    ((r*c.1+i*c.2)/1766847064778384329583297500742918515827483896875618958121606201292619776,
     (i*c.1-r*c.2)/1766847064778384329583297500742918515827483896875618958121606201292619776))
noncomputable def output (ar ai br bi bs : List Nat) (chirp : Nat→Int×Int) : List (Int×Int) :=
  combine (convolution ar br (2^166) (2^81)) (convolution ai bi (2^166) (2^81))
    (convolution ((ar.zip ai).map (fun p => p.1+p.2)) bs (2^167) (2^82)) chirp
noncomputable def decode (values : List Nat) : List (Int×Int) := values.map (fun p =>
  (((p%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168,
   ((p/79228162514264337593543950336%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168))
end RHHighPackedFFT
noncomputable def TaoFivePrimes_RHHighPackedFFT : Nat := 16384


