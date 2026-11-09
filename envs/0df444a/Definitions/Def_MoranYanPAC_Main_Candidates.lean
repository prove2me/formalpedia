-- Prove2me | Definitions.Def_MoranYanPAC_Main_Candidates
-- name    : MoranYanPAC_Main_Candidates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:05:52.958205+00:00
-- url     : https://prove2.me/theorems/27d4928d-edc9-433e-b00e-4b5f5991b195
-- title:
--   Algorithm 3 candidate union and fixed source witnesses
-- statement:
--   Fix a nonempty class $H$ with $\operatorname{LDim}(H)=d\ge1$. Use its published locally realizable universe $U$, rank $\rho$, rank layers $F_s$, version cells $V_v(S)$, and descending selected sets $D(V)$. A source witness assignment chooses one finite $A_h$ for every $h\in U$, independent of all samples, with the size, exact-dimension and isolation properties of Lemma 6 and with $\operatorname{SOA}_{H[h,A_h]}=h$. Write $Q_h=U[h,A_h]$.
--
--   The **candidate set** of Algorithm 3 is
--
--   $$C(S)=\bigcup_{v\in\{0,1\}^{|S|}}D(V_v(S)).$$
--
--   Every labeling of the sample instances is considered, irrespective of the observed labels. Empty cells contribute nothing. The definition is a set construction and assumes no finiteness, count or coverage result; those are theorems. The witness predicate extends the published witness-assignment predicate only by the missing SOA clause.
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Lemma 6, p. 20; Section 7.2 and Algorithm 3, pp. 21–22 (PDF pp. 20–22)

import Mathlib
import Definitions.Def_PrivLittlestone_selD
import Definitions.Def_PrivLittlestone_selT
import Definitions.Def_PrivLittlestone_versionCell
import Definitions.Def_PrivLittlestone_IsWitnessAssignment
import Definitions.Def_MoranYanPAC_Main_SOA

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Algorithm 3, p. 22. Union over every label vector, regardless of observed labels.
Empty cells contribute the empty set. Finiteness is not an input. -/
def candidates {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (Aw : (X → Bool) → Finset X) (S : List (X × Bool)) : Set (X → Bool) :=
  ⋃ v : Fin S.length → Bool,
    PrivLittlestone.selD H d Aw (PrivLittlestone.versionCell H d S v)

/-- A fixed assignment of the witnesses supplied by Lemma 6, including its SOA clause.
This is used only after witness existence, never as an input to Theorem 1. -/
def SourceWitnesses {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (Aw : (X → Bool) → Finset X) : Prop :=
  PrivLittlestone.IsWitnessAssignment H d Aw ∧
    ∀ h ∈ PrivLittlestone.localUniverse H d,
      SOA (PrivLittlestone.restrictCls H h (Aw h)) = h

end MoranYanPAC.Main


