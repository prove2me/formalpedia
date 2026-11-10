-- Prove2me | Definitions.Def_SmallClassesNeighbourhood_Linear_manyDefects
-- name    : SmallClassesNeighbourhood_Linear_manyDefects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:36:49.808252+00:00
-- url     : https://prove2.me/theorems/66c61cc9-d706-4c24-85e6-0f90ac95d8eb
-- title:
--   Selections and the prescribed restriction in the many-defects case
-- statement:
--   In the canonical setting, suppose the number d of different defects satisfies d ≥ C_0^2|A|. Choose nonempty A_0⊆A∖Q and B_0⊆B_good minimally A_0-diverse in the defect graph with |B_0|=C_0^2|A_0|. Choose B_0′⊆B_0 with |B_0′|≤|A_0|−1 and the bound |Aut(F_defect[A_0,B_0′])| ≤ C^(45|A_0|) stated in this construction after invoking Lemma 14 with parameters C_0^2 and 4C^10. Put Q_0=rep(A_0), and choose a witness R_0⊆R of size at most |Q_0|−1 that is Q_0-diverse. Define
--
--   $$A'=A_0\cup Q_0,\quad B'=B_0\cup R_0,\quad B''=B_0'\cup R_0,\quad n'=2|A_0|.$$
--
--   For H=Aut(F[A′,B″]), H_0 preserves A_0,Q_0,R_0,B_0′ setwise. The raw assignment sends a vertex of A_0∪B_0′ to its image under an element of H. It is defined before proving that it is a defect-graph automorphism. These are the actual selections used in Claim 21; neither its landing property, its multiplicativity nor its stabilizer-triviality conclusion is assumed.
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), §3.2.2, printed pp. 17–19 (PDF pp. 18–20)

import Definitions.Def_SmallClassesNeighbourhood_Linear_canonical

noncomputable section

namespace SmallClassesNeighbourhood.Linear
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The selections made in Section 3.2.2; no conclusion of Claim 21 is a field. -/
structure ManyChoices {C0 : ℕ} {F : SimpleGraph V} (s : CanonicalData C0 F) where
  many : C0 ^ 2 * s.A.card ≤ s.defects.card
  A0 : Finset V
  B0 : Finset V
  Bsmall : Finset V
  R0 : Finset V
  A0_sub : A0 ⊆ s.A \ s.Q
  A0_nonempty : A0.Nonempty
  B0_sub : B0 ⊆ s.Bgood
  minimal : MinimallyDiverse s.defectGraph A0 B0
  B0_size : B0.card = C0 ^ 2 * A0.card
  Bsmall_sub : Bsmall ⊆ B0
  Bsmall_size : Bsmall.card ≤ A0.card - 1
  defect_aut_bound : autCount s.defectGraph A0 Bsmall ≤
    (C0 ^ 4) ^ (45 * A0.card)
  witness : s.Witness A0 R0
  R0_size : R0.card ≤ (s.representativesOf A0).card - 1
  R0_diverse : Diverse F (s.representativesOf A0) R0

namespace ManyChoices
variable {C0 : ℕ} {F : SimpleGraph V} {s : CanonicalData C0 F}
def Q0 (m : ManyChoices s) := s.representativesOf m.A0
def Aprime (m : ManyChoices s) := m.A0 ∪ m.Q0
def Bprime (m : ManyChoices s) := m.B0 ∪ m.R0
def Bcore (m : ManyChoices s) := m.Bsmall ∪ m.R0
def nprime (m : ManyChoices s) := 2 * m.A0.card

def InH0 (m : ManyChoices s) (σ : CoreAut F m.Aprime m.Bcore) : Prop :=
  Preserves (ambientPerm σ) m.A0 ∧ Preserves (ambientPerm σ) m.Q0 ∧
  Preserves (ambientPerm σ) m.R0 ∧ Preserves (ambientPerm σ) m.Bsmall

/-- The prescribed restriction, before its landing and multiplication are proved. -/
def assignment (m : ManyChoices s) (σ : CoreAut F m.Aprime m.Bcore)
    (x : {v : V // v ∈ m.A0 ∪ m.Bsmall}) : V := ambientPerm σ x

end ManyChoices
end SmallClassesNeighbourhood.Linear


