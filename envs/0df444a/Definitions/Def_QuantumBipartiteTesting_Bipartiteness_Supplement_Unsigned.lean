-- Prove2me | Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned
-- name    : QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:12:11.662304+00:00
-- url     : https://prove2.me/theorems/87356ce3-afd4-495d-b32b-e099df34174a
-- title:
--   Unsigned feasible and algebraic acceptance functionals
-- statement:
--   Unsigned color-port responses return the unique matching neighbor, or null when that port is absent. A partial response table determines the union of its prescribed colored edges. It is consistent precisely when these edges form matchings by color and their induced oracle agrees with every prescribed entry, including the dummy-address convention.
--
--   The formal unsigned moment is the immutable published algebraic topology moment on a consistent table and zero otherwise. The formal acceptance functional is its linear extension with the actual circuit's canonical interpolation coefficients. The feasible acceptance functional instead averages the actual circuit acceptance over the actual feasible graph law.
--
--   These are two separately computed quantities. No equality, comparison bound, rationality certificate, positivity assertion or testing promise is part of the definition. Lemma 4.10 is responsible for rationality and comparison. This keeps the inherited algebraic reading of the formal moment visible and prevents a definition from assuming that theorem.
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, §2.4–2.5, printed = PDF pp.10–12; Definition 3.7 p.15 and equations (A.2)–(A.4) pp.30–31; Lemma 4.10 pp.25–26

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Constructions
import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Polynomials

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev UnsignedTable (n c : ℕ) := ResponseTable (Address n c) (Fin n)

def UnsignedPattern {n c : ℕ} (T : UnsignedTable n c) : Finset (ColoredEdge n c) :=
  T.val.biUnion fun az => match az.1.1 with
    | none => ∅
    | some u => {(min u az.2, max u az.2, az.1.2)}

def UnsignedConsistent {n c : ℕ} (T : UnsignedTable n c) : Prop :=
  Consistent (UnsignedPattern T) ∧ ∀ az ∈ T.val,
    LiftOracle (UnsignedResponse (UnsignedPattern T)) az.1 = some az.2

def UnsignedMoment {n c : ℕ} (T : UnsignedTable n c) (M l : ℝ) : ℝ :=
  if UnsignedConsistent T then TopologyMoment (UnsignedPattern T) M l else 0

def UnsignedFormal {n c k w q : ℕ} (E : Encoding (Fin n) k)
    (A : Algorithm (Address n c) k w q)
    (out : (Address n c × Bits k) × Fin w → Bool) (M l : ℝ) : ℝ :=
  ∑ T : UnsignedTable n c, CanonicalCoeff E A out T * UnsignedMoment T M l

def UnsignedFeasible {n c k w q : ℕ} (E : Encoding (Fin n) k)
    (A : Algorithm (Address n c) k w q)
    (out : (Address n c × Bits k) × Fin w → Bool) (M l : ℕ) : ℝ :=
  FeasibleBase n M l fun H => Accept E A out (LiftOracle (UnsignedResponse H))

end
end QuantumBipartiteTesting.Bipartiteness.Supplement


