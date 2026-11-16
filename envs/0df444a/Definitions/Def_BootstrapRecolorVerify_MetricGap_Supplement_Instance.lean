-- Prove2me | Definitions.Def_BootstrapRecolorVerify_MetricGap_Supplement_Instance
-- name    : BootstrapRecolorVerify_MetricGap_Supplement_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:31:07.371208+00:00
-- url     : https://prove2.me/theorems/c01639cf-8d07-4f1a-b48f-e25f70b0a901
-- title:
--   Part I terminal augmentation and construction-specific gap event
-- statement:
--   Attach a distinct leaf terminal $\widetilde u$ to every vertex $u\in V(G_r)$, with pendant length $L$ and weight $1/L$. Compute the terminal metric from the original multigraph distances before merging any parallel objective edges. On the event that every cloud is connected, these data supply the published generic 0-extension instance $I$: the terminal set is exactly the leaf copy of $V(G_r)$ and parallel objective weights are summed.
--
--   For $\gamma>0$, the successful-history event requires cloud connectedness and, for this computed instance,
--
--   $$I\text{ is valid},\qquad |T|=n^{4^r},\qquad \operatorname{MetricLP}(I)>0,\qquad \frac{\operatorname{OPT}(I)}{\operatorname{MetricLP}(I)}\ge\gamma(\log |T|)^{r/(r+1)}.$$
--
--   The event is evaluated under the original product-uniform matching law. It does not assume expansion, sparsity or a pre-existing gap witness. This ties Theorem 3.1 to the actual random construction rather than an existential family of arbitrary instances.
--
--   **Formalization Note** Nonterminals and leaves are two disjoint copies of the finite vertex type. Extended terminal distances are converted to real values only in the connected-instance interface, whose connectedness proof is part of the successful event. The published retraction optimum and metric-LP definitions are imported unchanged. Both source costs are normalized by $N_r$, which cancels in their ratio.
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), §3 terminal augmentation and Theorem 3.1, p.7; §4 p.8, p.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=7; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_MetricLP
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Supplement_Metrics

open scoped Classical ENNReal

namespace BootstrapRecolorVerify.MetricGap.Supplement

/-- §3 p.7: a separate terminal leaf for EVERY nonterminal. -/
abbrev AugVertex (n r : ℕ) := Vertex n r ⊕ Vertex n r
abbrev AugEdge (n r : ℕ) := Edge n r ⊕ Vertex n r

def augmentedEndpoints {n r : ℕ} (H : History n r) : AugEdge n r → AugVertex n r × AugVertex n r
  | Sum.inl e => (Sum.inl (endpoints H e).1, Sum.inl (endpoints H e).2)
  | Sum.inr u => (Sum.inl u, Sum.inr u)

noncomputable def augmentedWeight {n r : ℕ} (e : AugEdge n r) : ℝ :=
  match e with
  | Sum.inl e => edgeWeight r n (edgeLevel e)
  | Sum.inr _ => 1 / lengthScale r n

/-- Merge parallel edges only in the objective, AFTER computing the multigraph
shortest-path terminal metric. The support graph retains every pair joined by
an original edge, and every pendant pair. -/
def augmentedGraph {n r : ℕ} (H : History n r) : SimpleGraph (AugVertex n r) where
  Adj u v := u ≠ v ∧ ∃ e, augmentedEndpoints H e = (u, v) ∨ augmentedEndpoints H e = (v, u)
  symm := ⟨by
    intro u v h
    exact ⟨Ne.symm h.1, h.2.imp (fun _ he => he.symm)⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

def leafBase {n r : ℕ} : AugVertex n r → Vertex n r
  | Sum.inl u => u
  | Sum.inr u => u

/-- The published generic instance, supplied with the ACTUAL Part I data.
The connectedness proof restricts conversion of the extended terminal distance
to the event where §3 defines a finite instance. It assumes no cost or gap.
This file does not re-define OPT, retractions or the metric relaxation. -/
noncomputable def hierarchyInstance {n r : ℕ} (H : History n r)
    (_hc : AllCloudsConnected H) : ZeroExtensionGap.Instance (AugVertex n r) where
  G := augmentedGraph H
  w e := ∑ a : AugEdge n r,
    if s((augmentedEndpoints H a).1, (augmentedEndpoints H a).2) = e
    then augmentedWeight a else 0
  T := Finset.univ.image Sum.inr
  D a b := (terminalDistance r H (leafBase a.val) (leafBase b.val)).toReal

/-- Theorem 3.1's successful connected-instance event under the RAW law.
Validity, terminal count, positivity and the gap are conclusions in this event;
they are not fields of History or assumptions on sampled matchings. -/
def GapEvent {n r : ℕ} (γ : ℝ) (H : History n r) : Prop :=
  ∃ hc : AllCloudsConnected H,
    let I := hierarchyInstance H hc
    I.IsValid ∧ I.T.card = n ^ (4 ^ r) ∧ 0 < MetricLP I ∧
      γ * Real.rpow (Real.log I.T.card) ((r : ℝ) / ((r : ℝ) + 1)) ≤ I.OPT / MetricLP I

end BootstrapRecolorVerify.MetricGap.Supplement


