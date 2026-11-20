-- Prove2me | Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
-- name    : EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
-- status  : Definition
-- author  : @parclytaxel
-- created : 2026-11-19T09:17:30.760404+00:00
-- url     : https://prove2.me/theorems/64739c15-3e05-4080-aa47-986609b51310
-- title:
--   Greedy suffix allocation characterized by earlier-agent bounds
-- statement:
--   At each position, the assigned set is a suffix satisfying every earlier agent’s envy bound and containing every suffix satisfying those bounds. This describes greedy maximality without records, transcripts, or choice oracles; it does not assume envy-freeness.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
open EnvyFreeCake104.Divide

def EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1 {ι : Type} (V : ι → Valuation)
    (P : ι → Piece) (ag pc : List ι) (A : ι → Set ℝ) : Prop :=
  ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
    ag.zip pc = before ++ p :: after →
      IsSuffix (A p.1) (P p.2) ∧
      (∀ q ∈ before, (V q.1).value (A p.1) ≤ (V q.1).value (A q.1)) ∧
      ∀ S : Set ℝ, IsSuffix S (P p.2) →
        (∀ q ∈ before, (V q.1).value S ≤ (V q.1).value (A q.1)) →
        S ⊆ A p.1


