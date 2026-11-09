-- Prove2me | Definitions.Def_BatchMaxService_Metric_Certificates
-- name    : BatchMaxService_Metric_Certificates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:25:50.807203+00:00
-- url     : https://prove2.me/theorems/9f45e120-c419-4218-a10b-1fb2098b7357
-- title:
--   Request-group identities, ordered windows and two color families
-- statement:
--   A certificate group $G_k$ contains actual request identities and may contain the unique dummy identity at $(s_0,0)$. Its certificate $C_k$ is real and its right endpoint is $T_k$. Within a family the groups have disjoint identities and increasing endpoints $0=T_0<T_1<\cdots<T_m$. The first window is $[0,T_1]$ and every later window is $(T_{k-1},T_k]$. The conditions are
--
--   $$0\le C_k\le T_k-T_{k-1},\qquad C_k\le\operatorname{ST}_X(\{x(q):q\in G_k\}).$$
--
--   Every actual identity in a group belongs to the ambient input and arrives within that group's window. The dummy is free and only fits the first window. Full coverage is imposed separately in Theorem 3.3. For the two-family corollary each color uses just its own groups; unused ambient requests and identities shared between different colors remain legal.
--
--   **Formalization Note** `Option Nat` separates the dummy from every actual label, including label zero. A family is an ordered list, and two ordered lists encode the color partition. Tree bounds use the same ENNReal finite minima as the tree definitions.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), Theorem 3.3, Corollary 3.4 and Remark 3.5, printed pp. 7–8 / PDF pp. 8–9

import Mathlib
import Definitions.Def_BatchMaxService_Metric_RequestInput
import Definitions.Def_BatchMaxService_Metric_Trees

namespace BatchMaxService.Metric

variable {n : ℕ}

/-- `none` is the sole free initial-position dummy; `some q` is an actual identity. -/
def groupArrival (I : RequestInput n) : Option ℕ → ℝ
  | none => 0
  | some q => I.arrival q

def groupLocation (I : RequestInput n) : Option ℕ → Fin n
  | none => I.start
  | some q => I.location q

structure CertificateGroup where
  requests : Finset (Option ℕ)
  value : ℝ
  right : ℝ

/-- Distinct requests within one family; no disjointness is imposed between colors. -/
def GroupDisjoint (gs : List CertificateGroup) : Prop :=
  gs.Pairwise fun g h => Disjoint g.requests h.requests

noncomputable def realGroupIds (gs : List CertificateGroup) : Finset ℕ := by
  classical
  exact (gs.flatMap fun g => g.requests.toList.filterMap id).toFinset

/-- Ordered windows: the first includes time zero, all later ones are left open.
    Dummy admissibility follows from its time zero and strict later left endpoints. -/
noncomputable def WindowConditions [MetricSpace (Fin n)] (I : RequestInput n) :
    Bool → ℝ → List CertificateGroup → Prop
  | _, _, [] => True
  | first, left, g :: rest =>
      left < g.right ∧ g.requests.Nonempty ∧
      (∀ q ∈ g.requests, (match q with | none => True | some r => r ∈ I.ids)) ∧
      (∀ q ∈ g.requests, (if first then left ≤ groupArrival I q else left < groupArrival I q) ∧
        groupArrival I q ≤ g.right) ∧
      0 ≤ g.value ∧ g.value ≤ g.right - left ∧
      ENNReal.ofReal g.value ≤ SteinerCost (g.requests.image (groupLocation I)) ∧
      WindowConditions I false g.right rest

noncomputable def ValidFamily [MetricSpace (Fin n)] (I : RequestInput n)
    (gs : List CertificateGroup) : Prop :=
  GroupDisjoint gs ∧ WindowConditions I true 0 gs

noncomputable def certificateSum (gs : List CertificateGroup) : ℝ :=
  (gs.map CertificateGroup.value).sum

end BatchMaxService.Metric


