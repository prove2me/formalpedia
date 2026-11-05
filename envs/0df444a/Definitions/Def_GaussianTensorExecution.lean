-- Prove2me | Definitions.Def_GaussianTensorExecution
-- name    : GaussianTensorExecution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/9185e94b-c76a-4907-ad99-68fa708acd8e
-- title:
--   GaussianTensorExecution definitions
-- statement:
--   Finite tensor forward and inverse execution, exact reconstruction, and binary-grid bounds.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
namespace GaussianTensorExecution
open GaussianParity GaussianSynthesis
def Cube : Nat → Type
  | 0 => GInt
  | n+1 => Cube n × Cube n
def cubeMap (f : GInt → GInt) : (n : Nat) → Cube n → Cube n
  | 0, z => f z
  | n+1, z => (cubeMap f n z.1,cubeMap f n z.2)
def cubeZip (f : GInt → GInt → GInt) : (n : Nat) → Cube n → Cube n → Cube n
  | 0, u, v => f u v
  | n+1, u, v => (cubeZip f n u.1 v.1,cubeZip f n u.2 v.2)
def cubeAdd (n : Nat) : Cube n → Cube n → Cube n := cubeZip add n
def cubeI (n : Nat) : Cube n → Cube n := cubeMap mulI n
def cubePi (n : Nat) : Cube n → Cube n := cubeMap mulPi n
def cubePiIter (k n : Nat) : Cube n → Cube n := cubeMap (piIter k) n
def axisForward (n : Nat) (z : Cube n × Cube n) : Cube n × Cube n :=
  (cubeAdd n (cubeI n z.1) z.2,cubeAdd n z.1 (cubeI n z.2))
def axisInverse (n : Nat) (z : Cube n × Cube n) : Cube n × Cube n :=
  (cubeAdd n z.1 (cubeI n z.2),cubeAdd n (cubeI n z.1) z.2)
def forward : (n : Nat) → Cube n → Cube n
  | 0, z => z
  | n+1, z => axisForward n (forward n z.1,forward n z.2)
def inverse : (n : Nat) → Cube n → Cube n
  | 0, z => z
  | n+1, z =>
    let q := axisInverse n z
    (inverse n q.1,inverse n q.2)
end GaussianTensorExecution
namespace GaussianTensorExecution
open GaussianParity GaussianSynthesis
def Path : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Path n
def get : (n : Nat) → Cube n → Path n → GInt
  | 0, z, _ => z
  | n+1, z, p => if p.1 then get n z.2 p.2 else get n z.1 p.2
end GaussianTensorExecution
namespace GaussianTensorExecution
open GaussianParity GaussianSynthesis
def zeroCube : (n : Nat) → Cube n
  | 0 => ⟨0,0⟩
  | n+1 => (zeroCube n,zeroCube n)
def firstPath : (n : Nat) → Path n
  | 0 => ()
  | n+1 => (false,firstPath n)
def lastImpulse : (n : Nat) → Cube n
  | 0 => ⟨1,0⟩
  | n+1 => (zeroCube n,lastImpulse n)
end GaussianTensorExecution
namespace GaussianTensorExecution
open GaussianParity GaussianSynthesis
structure TaggedCube (n : Nat) where
  numerators : Cube n
  exponent : Nat
def executeForward (n : Nat) (x : TaggedCube n) : TaggedCube n :=
  ⟨forward n x.numerators,x.exponent+n⟩
def executeInverse (n : Nat) (x : TaggedCube n) : TaggedCube n :=
  ⟨inverse n x.numerators,x.exponent+n⟩
def coordinate (n : Nat) (x : TaggedCube n) (p : Path n) : Fraction :=
  ⟨get n x.numerators p,x.exponent⟩
end GaussianTensorExecution


