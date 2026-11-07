-- Prove2me | Definitions.Def_FourColorLinear_mainTypes
-- name    : FourColorLinear_mainTypes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:47.451192+00:00
-- url     : https://prove2.me/theorems/07daf264-51eb-4463-b621-362ad1274d1e
-- title:
--   Main types of configurations relative to a batch of Kempe chains
-- statement:
--   Relative to a batch $\vec K$ of Kempe chains, the **main type** of a configuration $Z$ touching some chain of the batch is the set of chains from $\vec K$ that $Z$ touches. This definition is the set of main types occurring in a family of configurations.
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §3, p.20

import Mathlib
import Definitions.Def_FourColorLinear_FaceOf

namespace FourColorLinear

variable {V : Type}

/-- The main types of configurations relative to a batch of Kempe chains, arXiv:2610.39753 (held
version, sha256 4dce39c5…), p.20: "the main type of such a reducible configuration Z is the set of
Kempe chains from K⃗ that Z touches". Only configurations touching some chain of the batch count. -/
def mainTypes (G : SimpleGraph V) (Ks Zs : Set (Set V)) : Set (Set (Set V)) :=
  {T | T.Nonempty ∧ ∃ Z ∈ Zs, T = {K | K ∈ Ks ∧ Touch G K Z}}

end FourColorLinear


